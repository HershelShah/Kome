#!/usr/bin/env python3
"""
Kome relay server.

A minimal WebSocket relay that pairs peers into rooms and forwards
binary messages between them. Peers connect, join/create a room via
a short code, and the relay shuttles Kome sync traffic between them.

Protocol (binary WebSocket frames):
    0x01 JOIN       [32-byte fingerprint] [0 or 6 bytes room code]
    0x02 CREATED    [6 bytes room code]
    0x03 PEER_JOIN  [32 bytes peer fingerprint]
    0x04 PEER_LEFT  [32 bytes peer fingerprint]
    0x05 DATA       [32 bytes dest fingerprint] [payload...]
    0x06 ERROR      [UTF-8 message]

Deploy: fly launch / fly deploy, or just: python relay.py
"""

import asyncio
import os
import random
import string
import websockets

MSG_JOIN = 0x01
MSG_CREATED = 0x02
MSG_PEER_JOIN = 0x03
MSG_PEER_LEFT = 0x04
MSG_DATA = 0x05
MSG_ERROR = 0x06

rooms: dict[str, list] = {}  # code -> [websocket, ...]


def make_code() -> str:
    return "".join(random.choices(string.ascii_uppercase + string.digits, k=6))


async def handler(ws):
    room_code = None
    fingerprint = b"\x00" * 32

    try:
        # First message must be JOIN
        msg = await ws.recv()
        if not isinstance(msg, bytes) or len(msg) < 33 or msg[0] != MSG_JOIN:
            await ws.send(bytes([MSG_ERROR]) + b"expected JOIN")
            return

        fingerprint = msg[1:33]
        ws.fingerprint = fingerprint
        code_bytes = msg[33:]

        if len(code_bytes) == 0:
            # Create new room
            room_code = make_code()
            while room_code in rooms:
                room_code = make_code()
            rooms[room_code] = [ws]
            ws.room = room_code
            await ws.send(bytes([MSG_CREATED]) + room_code.encode())
        elif len(code_bytes) == 6:
            room_code = code_bytes.decode()
            if room_code not in rooms:
                await ws.send(bytes([MSG_ERROR]) + b"room not found")
                return
            if len(rooms[room_code]) >= 2:
                await ws.send(bytes([MSG_ERROR]) + b"room full")
                return

            # Notify existing peers
            for peer in rooms[room_code]:
                await peer.send(bytes([MSG_PEER_JOIN]) + fingerprint)
                await ws.send(bytes([MSG_PEER_JOIN]) + peer.fingerprint)

            rooms[room_code].append(ws)
            ws.room = room_code
            await ws.send(bytes([MSG_CREATED]) + room_code.encode())
        else:
            await ws.send(bytes([MSG_ERROR]) + b"invalid room code")
            return

        # Forward messages
        async for msg in ws:
            if not isinstance(msg, bytes) or len(msg) < 1:
                continue
            if msg[0] == MSG_DATA and len(msg) > 32:
                # Forward to other peers in the room
                for peer in rooms.get(room_code, []):
                    if peer is not ws:
                        # Replace dest fingerprint with sender's
                        await peer.send(bytes([MSG_DATA]) + fingerprint + msg[33:])
    except websockets.ConnectionClosed:
        pass
    finally:
        # Cleanup
        if room_code and room_code in rooms:
            peers = rooms[room_code]
            if ws in peers:
                peers.remove(ws)
            # Notify remaining peers
            for peer in peers:
                try:
                    await peer.send(bytes([MSG_PEER_LEFT]) + fingerprint)
                except Exception:
                    pass
            if not peers:
                del rooms[room_code]


async def main():
    port = int(os.environ.get("PORT", 8080))
    print(f"Kome relay listening on :{port}")
    async with websockets.serve(handler, "0.0.0.0", port):
        await asyncio.Future()  # run forever


if __name__ == "__main__":
    asyncio.run(main())
