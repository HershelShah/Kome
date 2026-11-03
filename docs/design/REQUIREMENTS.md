# Kome redesign: the problem, the constraints, the scoring

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
- It runs where the data of the person is: phones, laptops, browsers (WASM)
  and small devices. It has a C-callable API and one vendored crypto
  dependency.

Out of scope: collaborative rich-text editing. Kome is for records, not for
prose.

## 2. Hard constraints

H1. **Convergence is a theorem, not a test.** If two replicas hold the same
    set of records, they must hold the same state. The proof must state its
    assumptions, and the assumptions must be minimal. "Clocks are roughly
    right" is a weak assumption. "Signatures are unforgeable" is an
    acceptable assumption.
H2. **No trusted third party**: no server for ordering, membership or keys.
    Relays can exist, but they are untrusted and blind.
H3. **End-to-end encryption** of all record content. Relays and strangers
    learn only what is unavoidable (sizes, timing, routing keys).
H4. **Incremental sync**: the transfer is proportional to the difference,
    and the number of rounds is logarithmic in the state size. Sync works
    over any byte transport (UDP, TCP, WS, BLE). The two sides must not need
    a shared history or version vectors of the past sessions of each other.
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
    single record must not permanently brick a collection or the future
    writes of a different writer.

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

## 4. Scoring criteria (each 0–5, with a one-line justification)

C1. Strength of the convergence theorem (fewer, weaker assumptions = higher).
C2. Blast radius of an authorized writer that misbehaves; recoverability.
C3. Metadata overhead per record and per replica; GC without membership.
C4. Sync efficiency and transport independence; relay blindness.
C5. Privacy and revocation: what a removed member can still do or learn.
C6. Provability: size of the trusted core; expressibility in SPARK + Lean.
C7. Footprint: embedded/WASM/C ABI, dependencies, code size.
C8. Application ergonomics: how conflicts and deletes show to the app.
C9. Representation hygiene: H5 and H6 by construction.

A design must also list its **assumptions** (what must be true for the
theorems), its **known weaknesses** (what it gives up) and its **proof
obligations** (the theorems to prove).

## 5. Fixed points (not open to debate)

- Crypto primitives: X25519, Ed25519, BLAKE2b, ChaCha20-Poly1305
  (monocypher). A design can use them in different ways (group keys, hash
  chains), but it must not add primitives outside that set.
- Implementation target: a SPARK core behind a C ABI, and the design
  theorems in Lean.
