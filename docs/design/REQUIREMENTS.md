# Kome redesign: the problem, the constraints, the scoring

This is the specification a ground-up redesign must satisfy. It is deliberately
about the problem, not the current code. The current engine is one candidate
solution and is allowed to lose.

## 1. The problem

A person owns structured records (contacts, notes, inventories, settings, small
shared lists) and wants them replicated across their own devices and shared
with explicitly trusted contacts, such that:

- it works offline and converges when devices reconnect, in any order, with
  duplicated or dropped messages;
- there is no central server: devices talk directly, through NAT, or via relays
  that must learn nothing beyond ciphertext and routing;
- only authorized parties can read a collection, and the set of authorized
  parties can change (someone is removed);
- it runs where the person's data lives: phones, laptops, browsers (WASM),
  small devices, with a C-callable API and one vendored crypto dependency.

Out of scope: collaborative rich-text editing. Records, not prose.

## 2. Hard constraints

H1. **Convergence is a theorem, not a test.** Two replicas that hold the same
    set of records must hold the same state. The proof's assumptions must be
    stated and minimal; "clocks are roughly right" is a weak assumption,
    "signatures are unforgeable" is an acceptable one.
H2. **No trusted third party**: no server for ordering, membership, or keys.
    Relays may exist but are untrusted and blind.
H3. **End-to-end encryption** of all record content; relays and strangers learn
    only what is unavoidable (sizes, timing, routing keys).
H4. **Incremental sync**: transfer proportional to the difference, rounds
    logarithmic in the state size, over any byte transport (UDP, TCP, WS,
    BLE), without the two sides sharing history or version vectors of each
    other's past sessions.
H5. **Bounded everything**: every value, key, message, and metadata item has an
    explicit bound; the state model must be expressible in a bounded,
    pointer-free language (SPARK) and its properties in Lean.
H6. **No reserved values and no derived invariants**: illegal states must be
    unrepresentable in the data model (no `{0,0}` sentinels, no "asserted iff
    nonzero", no counter whose wrap means something).
H7. **Deletion that does not grow forever**: deleting records must eventually
    free space on every replica, without a membership oracle, while still
    converging.
H8. **Authorized writers can misbehave**: a device with write access may be
    buggy, have a wrong clock, be restored from a backup, be cloned (same key
    on two devices), or be malicious. The design must state what damage each
    of these can do, and it must be bounded and recoverable; no single record
    may permanently brick a collection or another writer's future writes.

## 3. Lessons from the current engine (what the redesign must make impossible)

| Incident | Root cause class |
|---|---|
| Causal-length counter saturation: one record pins an entity forever | unbounded counter with semantics at its max |
| Same-author same-clock existence equivocation diverges (T-EQUIV) | merge order not total over the element |
| `{0,0}` existence record accepted; exists/digest/snapshot/load disagreed | sentinel-encoded invariant, four derivations of one fact |
| uint32 logical wrap mints the sentinel; truncating restore; sign-converted clock | fixed-width arithmetic at a boundary with reserved meaning |
| Far-future HLC pins a cell against all honest writers (documented, unfixed) | LWW trusts a writer-chosen timestamp |
| Digest depended on map keys, not on the replicated element set | digest defined separately from the sync fingerprint |
| Revocation seen on one side only makes record sets differ | authorization as an accept/reject gate is non-monotone |

## 4. Scoring criteria (each 0–5, with a one-line justification)

C1. Strength of the convergence theorem (fewer, weaker assumptions = higher).
C2. Blast radius of a misbehaving authorized writer; recoverability.
C3. Metadata overhead per record and per replica; GC story without membership.
C4. Sync efficiency and transport independence; relay blindness.
C5. Privacy and revocation: what a removed member can still do or learn.
C6. Provability: size of the trusted core; expressibility in SPARK + Lean.
C7. Footprint: embedded/WASM/C ABI, dependencies, code size.
C8. Application ergonomics: how conflicts and deletes present to the app.
C9. Representation hygiene: H5 and H6 by construction.

A design must also list its **assumptions** (what must hold for the theorems),
its **known weaknesses** (what it gives up), and its **proof obligations**
(the theorems to prove).

## 5. Fixed points (not up for debate)

- Crypto primitives: X25519, Ed25519, BLAKE2b, ChaCha20-Poly1305 (monocypher).
  A design may use them differently (group keys, hash chains) but not add
  primitives outside that set.
- Implementation target: SPARK core behind a C ABI; design theorems in Lean.
