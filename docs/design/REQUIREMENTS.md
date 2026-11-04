# Kome redesign: the problem and the constraints

This is the specification that the design must satisfy. It is about the
problem, not about an implementation.

## 1. The problem

A person owns structured records (contacts, notes, inventories, settings,
small shared lists). The person wants to replicate the records across their
own devices and share them with contacts that they trust explicitly. These
are the requirements:

- It works offline. When devices connect again, the replicas converge, in
  any order and with duplicated or dropped messages.
- There is no central server. Devices talk directly, through NAT, or through
  relays. A relay must learn nothing more than ciphertext and routing.
- Only authorized parties can read a collection. The set of authorized
  parties can change (for example, a person is removed).
- It runs where the person's data is: phones, laptops, browsers (WASM)
  and small devices. It has a C-callable API and one vendored crypto
  dependency.

Out of scope: collaborative rich-text editing. Kome is for records, not for
prose.

## 2. Hard constraints

H1. **Convergence is a theorem, not a test.** If two replicas applied the
    same set of records, and expired tombstones at the same horizon, they
    must hold the same state; before any expiry, the same records alone
    must give the same state. The proof must state its assumptions, and
    the assumptions must be minimal. "Clocks are roughly right" is a weak
    assumption. "Signatures are unforgeable" is an acceptable assumption.
H2. **No trusted third party**: no server for ordering, membership or keys.
    Relays can exist, but they are untrusted and blind.
H3. **End-to-end encryption** of all record content. A relay learns only
    the collection identifier, the padded size bucket of each bundle, the
    timing and its routing key. A stranger on the interactive transport
    learns only that an endpoint answers: no device key, no collection
    identifier and no membership, and nothing that links the endpoint
    across places, networks or collections.
H4. **Incremental sync**: the transfer is proportional to the difference,
    and the number of rounds is logarithmic in the state size. Sync works
    over any byte transport (UDP, TCP, WS, BLE). The two sides must not need
    a shared history or version vectors of each other's past sessions.
H5. **Bounded everything**: every value, key, message and metadata item has
    an explicit bound. It must be possible to express the state model in a
    bounded, pointer-free language (SPARK), and its properties in Lean.
H6. **No reserved values and no derived invariants**: the data model must
    make illegal states unrepresentable. That is: no sentinel values, no
    "asserted iff nonzero", and no counter whose wrap has a meaning.
H7. **Deletion that does not grow forever**: if records are deleted, the
    deletion must eventually free space on every replica. It must do this
    without a membership oracle, and the replicas must still converge.
H8. **Authorized writers can misbehave**: a device with write access can be
    buggy, have a wrong clock, be restored from a backup, be cloned (same
    key on two devices), or be malicious. The design must state what damage
    each of these can do. That damage must be bounded and recoverable. A
    single record must not permanently brick a collection or a different
    writer's future writes.

The design must list its **assumptions** (what must be true for the
theorems), its **known weaknesses** (what it gives up) and its **proof
obligations** (the theorems to prove).

## 3. Failure classes the design must make impossible

- An unbounded counter that has a meaning at its maximum (one record pins
  an entity forever).
- A merge order that is not total over the element (replicas diverge on
  ties).
- One fact derived in several places (existence, digest, snapshot and load
  disagree).
- Fixed-width arithmetic at a boundary with reserved meaning (a wrap makes a
  sentinel, or a restore truncates a value).
- Last-writer-wins on a timestamp that the writer chooses (a far-future
  clock pins a cell against every honest writer).
- A digest defined separately from the sync fingerprint (equal element sets
  have different digests).
- Authorization as a non-monotone accept/reject gate (if only one side sees
  a revocation, the record sets become different).

## 4. Fixed points (not open to debate)

- Crypto primitives: X25519, RFC 8032 Ed25519 (SHA-512 only inside the
  signature), BLAKE2b, XChaCha20-Poly1305 (24-byte nonce), from
  monocypher. A design can use them in different ways (group keys, hash
  chains), but it must not add primitives outside that set.
- Implementation target: a SPARK core behind a C ABI, and the design
  theorems in Lean.
