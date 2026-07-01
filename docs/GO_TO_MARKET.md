# Kome — business applications & go-to-market

*Research compiled July 2026 from ~14 parallel research streams across competitive
landscape, industry verticals, monetization models, and distribution channels.
All load-bearing claims carry source URLs. Figures marked "unverified" could not
be confirmed from primary sources.*

---

## 1. Executive summary

**The category is proven.** Ditto — a proprietary CRDT P2P sync engine
architecturally near-identical to Kome — raised an **$82M Series B in March
2025 at a $462M post-money valuation**, with 30+ customers, ARR +250% YoY,
and a U.S. Air Force SBIR ladder culminating in a seat on a $950M-ceiling
IDIQ ([TechCrunch](https://techcrunch.com/2025/03/12/ditto-lands-82m-to-synchronize-data-from-the-edge-to-the-cloud/)).
Its customers (Chick-fil-A, Delta, Lufthansa, Japan Airlines, Alaska Airlines,
USAF) prove exactly who pays for offline-first P2P sync: **airlines, QSR/POS,
and defense** — environments where offline is the default, not an edge case.

**Kome's quadrant is empty.** Across 17+ vendors surveyed, verified from
their own docs:

- PowerSync, ElectricSQL, Turso, Couchbase, ObjectBox, Zero **all require a
  central sync service**. Only Ditto does serverless P2P mesh — and it
  monetizes its cloud, which processes plaintext.
- **None** of the commercial engines offers operator-blind end-to-end
  encryption (Ditto = TLS/mTLS with a plaintext Big Peer; PowerSync = DIY
  column encryption; Electric = "share keys yourself"). True-E2EE projects
  (Evolu, classic Jazz, DXOS) are TypeScript-only — and Jazz's 2026 v2
  rewrite *retreated* from E2EE to trusted-server policy enforcement.
- **No C-native CRDT sync engine exists anywhere** (crdt.tech confirms the
  ecosystem is JS/Rust; automerge-c and cr-sqlite are Rust cores with C
  surfaces, and none bundles networking/NAT traversal/E2EE). Ditto's C++ SDK
  stops at Linux/iOS — no MCU/RTOS story. ObjectBox Sync is closed-source
  and quote-only.
- The **Willow protocol** — the closest conceptual twin (range-based set
  reconciliation + capabilities + E2EE) — was effectively abandoned in 2025
  (willow-rs archived Oct 2025; iroh-willow never released). Negentropy/NIP-77
  proves RBSR in production at tens-of-millions scale on Nostr, validating
  Kome's sync-algorithm choice.

So Kome's honest, defensible position: **the only MIT-licensed, serverless,
E2EE-by-default, capability-scoped sync engine with a tiny embeddable C core.**
"SQLite of sync" is not a slogan; it's a literally unoccupied quadrant.

**The tailwind is real.** MongoDB killed Atlas Device Sync/Realm (EOL Sept 30,
2025), stranding "hundreds" of high-scale customers (PepsiCo, Emirates, Lotum)
plus tens of thousands of long-tail Realm apps — the third major sync rug-pull
(Parse 2017, Realm Object Server 2018, App Center 2025, Amplify DataStore
EOL 2027). Developers have now been burned repeatedly by *proprietary, vendor-
hosted* sync. An MIT-licensed engine with no required cloud directly answers
the objection every migration survivor now asks first.

**Recommended strategy in one line:** win developer mindshare in the
local-first/embedded communities with the free MIT core (bindings-led
distribution), land the first *paying* customer as a design-partner ISV in a
vertical where offline is existential (field inspection, onboard/event POS,
or a TAK-ecosystem defense integrator), and monetize on the SQLite/wolfSSL
menu (support contracts, paid integration NRE, proprietary add-on modules,
hosted relay) rather than betting on donations or license fees.

---

## 2. Honest product assessment (what we're selling, what's missing)

**Assets** (from the codebase and docs):

- Convergent record store (LWW per field + LWW existence) with an unusually
  rigorous correctness matrix: partition-heal, crash-restart chaos tests with
  real SIGKILLed processes, 250-node mesh convergence, fuzzing, sanitizers,
  OOM tests (`docs/SCENARIOS.md`, `tests/`).
- Full stack in one library: incremental sync (range-based set reconciliation,
  difference-proportional transfer), Noise XX transport, identity, per-namespace
  capabilities, NAT traversal (STUN, hole punch, relay), append-only durable log.
- One vendored dependency (monocypher). MIT. C core + Python and WASM bindings.
- Self-hostable relay/rendezvous daemons and a documented $0-cost real-internet
  deployment runbook (`docs/REAL_NETWORK_FREE_STACK.md`).

**Gaps that buyers will hit** (each maps to a work item in §7):

| Gap | Who hits it | Severity |
|---|---|---|
| No blob/attachment story | Field-inspection ISVs (photos are the bulk of inspection data) | High |
| No mobile SDK packaging (iOS/Android) | Every app ISV; Realm refugees are mobile-first | High |
| No pip wheel / npm package published | Everyone (bindings are the volume layer — see §5) | High |
| IPv6 backlogged; UDP-only transport | Enterprise networks, some carriers | Medium |
| No query layer / indexes | Larger apps | Medium — honest scoping ("records, not queries") is acceptable early |
| Solo-maintainer bus factor, no audit, no LTS policy | Every commercial buyer, disqualifying for OEM/medical | High for revenue, low for adoption |
| Best-effort delete / LWW clock semantics | Compliance-sensitive buyers | Low-medium (documented, deterministic) |

The test rigor is itself a marketable asset — lead with it. The C core with
one dependency is an SBOM reviewer's dream (FDA §524B, DoD SBOM mandates),
but expect memory-safety questions from Rust-curious reviewers; the fuzz/
sanitizer/chaos suite is the counter.

---

## 3. Vetted business applications, ranked

Ranked by (pain × fit × reachability for a solo/early open-source project).

### Tier 1 — pursue now

**A. Component vendor to field-operations ISVs (inspection, EVV, maritime, mining).**
Offline is "non-negotiable" in every field-inspection software roundup; small
ISVs already compete on sync quality (BasinCheck markets "cryptographically
signed operations with conflict resolution, while most tools rely on simple
auto-sync that can silently overwrite data" — i.e., they advertise what Kome
*is*). The buyer is the CTO of a long-tail ISV (Speqtiv/BasinCheck/NestForms
class), not the field operator. Fortune-500 evidence: Halliburton/GE/Exxon
apps run on PowerSync's engine; Micromine built a literal P2P vehicle
data-mule for underground mines. **Path**: 3–5 design-partner conversations;
stranded Realm laggards (still visible in MongoDB forums and realm-* GitHub
discussions) are the warmest list. **Red flags**: photo/blob gap must be
answered first; Starlink is slowly compressing maritime/ag pain.

**B. Defense/tactical edge via the TAK ecosystem (the Ditto playbook, open-source variant).**
DDIL sync is a funded, named DoD problem (CJADC2 $572.8M FY26 R&D, >$2B FY27
ask; Army NGC2 ~$3B/yr with ~$345M specifically in the apps-and-data layer;
DIU's "LightCycle" solicitation described Kome's shape almost verbatim).
The **TAK ecosystem (~500K users) has a documented serverless-sync hole**:
Mission API requires TAK Server; serverless fallback is fire-and-forget UDP
multicast with no store-and-forward or conflict resolution; Meshtastic/LoRa
gateways carry only chat+PLI. TAK.gov's third-party plugin pipeline is **open
to anyone, free** (2–5 day vetting). LoRa's tiny bandwidth actually favors
Kome's compact LWW records over fat document CRDTs. **Path**: ship a
"serverless mission sync" ATAK plugin → AFWERX SBIR Open Topic Phase I
(~$75K, ~700 awards/yr) or Direct-to-Phase-II ($1.25M with a working product)
→ subcontract to TAK/NGC2 integrators (Booz Allen, PAR Government). An
embedded *library* inherits the host program's ATO — no standalone ATO needed;
keep the open core generic to stay export-safe (published OSS with standard
crypto is public-domain for EAR purposes). **Realistic first customer here is
a dual-use startup** (drone/robotics/sensor companies that can't afford Ditto
and won't accept Anduril Lattice lock-in), on commercial terms, faster than
any program office.

**C. Onboard/disconnected retail & POS ISVs (inflight retail, ferries, events, food trucks).**
The Chick-fil-A/Ditto deal validated "cloud-optional POS" (and the July 2024
CrowdStrike outage that closed Starbucks stores is the motivating anecdote
every POS buyer remembers). The big chains are taken; the open niche is
ISVs serving structurally offline retail: inflight retail (Retail inMotion,
Omnevo, GuestLogix must sync catalogs/inventory/orders across crew devices in
an air-gapped cabin — literally Kome's model), ferries, stadiums, festivals.
**Hard rule**: sync orders/menu/inventory/kitchen state — **never card data**
(payments stay in the certified payment stack; PCI DSS).

### Tier 2 — cultivate cheaply in parallel

**D. Embedded/IoT device-state sync (the mbedTLS trajectory).**
A genuine product gap: Zenoh is transport-only pub/sub (no partition-tolerant
state reconciliation); Ditto stops at Linux/iOS; ObjectBox Sync is closed.
Embedded buyers pay 5–6 figures for supported middleware (wolfSSL LTS
$50K/yr; Green Hills ~$150K/yr) but design cycles run 18–36 months and
demand LTS policies, MISRA, audits. **Path**: Zephyr module + ESP-IDF port →
vendor SDK example listings (the littlefs/mbedTLS playbook) → one paid
design win ($20–80K NRE + annual support). Precedent for the endgame:
PolarSSL's solo author → ARM acquisition → TrustedFirmware consortium.

**E. Local-first / privacy developer ecosystem.**
This is a *distribution* channel more than a revenue vertical (nobody pays for
bare CRDT libraries; Syncthing's zero-commercialization history is the
cautionary tale; the vaultwarden effect means self-hosters route around paid
tiers). But it's where credibility, contributors, and inbound ISV leads come
from — and it has real infrastructure: Local-First Conf Berlin (~350, sold
out), Sync Conf SF (2x sold out), localfirst.fm, lofi directories,
r/selfhosted at 792K members. Revenue here = hosted relay/rendezvous
(Iroh charges $19/mo + $0.27/relay-hr on exactly this model; Tailscale's
$2B valuation is managed identity + NAT traversal + relays) plus
**EU grants** (NLnet funded p2panda including a professional security audit —
a realistic €5–50K that also buys the audit credibility §7 requires).

### Tier 3 — long-cycle or grant-funded; engage opportunistically

**F. Global health / humanitarian (ODK, Medic/CHT).** Medic's Community
Health Toolkit publicly acknowledges CouchDB/PouchDB sync pain and just built
a datasource abstraction that makes engine swaps conceivable; ODK's forums
document unmet device-to-device sync demand. But the post-USAID-shutdown
funding climate is the worst in a decade and money arrives as 6–18 month
grants. **Do the cheap thing**: apply for **Digital Public Good certification**
(free; gates UN/UNICEF procurement; standard credibility signal) and answer
ODK's own forum threads with a working P2P demo. Treat as pipeline, not plan.

**G. Healthcare (home-health EVV vendors, medical devices).** Serverless P2P
has a genuinely clean HIPAA story (no third party to BAA with; a relay that
only routes ciphertext plausibly fits the conduit exception; the pending
Security Rule NPRM would make encryption mandatory — an E2EE tailwind). But
incumbents (HCHB/Axxess/WellSky) already own offline, and buyers demand
SOC 2/HITRUST and an entity to sue. Revisit after there's a company wrapper
and an audit.

**Ruled out for now**: direct-to-enterprise (Ditto owns it; 30 customers at
$462M valuation = high-ACV sales machine you can't outspend), consumer apps
(monetization unsolved below the hosted layer), UN/Red Cross direct
(entity vetting), collaborative-editing anything (explicitly out of scope —
cede to Yjs/Automerge and say so; it buys credibility).

---

## 4. Positioning

**One-liner:** *Kome is the SQLite of sync — an MIT-licensed C library that
gives any app serverless, end-to-end-encrypted, offline-first replication of
structured records, with NAT traversal built in and no cloud required.*

Against each alternative (all verified from their own docs/pricing):

| Alternative | Kome's counter |
|---|---|
| Ditto | Open source vs proprietary; E2EE vs plaintext Big Peer; embeddable C vs Linux/iOS SDK floor; no per-connection cloud pricing; no vendor lock-in (the post-Realm objection) |
| PowerSync / Electric / Zero / Turso | No server required at all; true multi-writer offline CRDT; E2EE |
| Couchbase | Tiny footprint vs heavyweight; MIT vs BSL; not PE-owned |
| ObjectBox Sync | Open vs closed; public pricing vs quote-only; below their device-class floor (MCU/RTOS) |
| Iroh | Full data layer (records, CRDT, capabilities, durability) vs transport-only — and Iroh 1.0's momentum can be ridden: "Kome is to your data what Iroh is to your connection" |
| Yjs/Automerge | Records vs documents; built-in identity/transport/NAT vs bring-your-own; C vs JS/Rust |

**Narrative hooks** (each is a documented, sourced story): the vendor
rug-pull history (Parse → Realm ROS → Device Sync → App Center → DataStore);
the CrowdStrike/Starbucks outage; the Willow vacuum; "0 required servers,
$0 stack" (the Oracle-free-tier runbook); the chaos-test matrix as proof of
seriousness.

---

## 5. Distribution plan

Grounded in what measurably worked for comparable projects:

**Packaging first (the volume layer).** Bindings dwarf C cores: PyNaCl does
~227M downloads/month vs raw libsodium's direct C consumption; DuckDB's pip
wheel grew 6M→44M/month in 18 months and *was* the growth engine. Before any
launch: `pip install kome` (self-contained wheel), npm package (WASM),
single-file **amalgamation** (`kome.c`/`kome.h` — stb/SQLite culture makes
this table stakes for the C audience), clean CMake FetchContent, then vcpkg
and Conan ports, PlatformIO registry and a Zephyr module for the embedded
channel.

**The launch (Show HN).** Median Show HN = 2 points; the winners in this
exact space were milestone posts with a demo and a number attached (Iroh 1.0:
1,398 points; Automerge 2.0: 717; ElectricSQL: 617). Best window: Sunday
evening US time. One organic shot plus the second-chance pool
(hn@ycombinator.com). The demo matters more than the post: ElectricSQL's
LinearLite (100K issues in-browser) and Rocicorp's zbugs (2.5M rows,
dogfooded) became the de facto proof artifacts for their engines. **Kome's
equivalent flagship demo**: a two-device offline-first app (shared
inventory/checklist) that syncs phone↔laptop over the real internet with the
relay visibly *unable* to read anything — plus the stress number the test
suite already supports (250-node mesh convergence). The "P2P sync between two
ESP32s, no cloud" demo is a separate Hackaday/HN shot ("Running Iroh on an
ESP32" got its own thread).

**The community circuit (where sync engines actually grew).** PowerSync,
Jazz, and Evolu built their user bases with almost no HN footprint — via
localfirst.fm (every sync founder has guested; pitch an episode), Local-First
Conf / Sync Conf talks, the Landscape/lofi directories, and ecosystem
integrations. Position explicitly against the Ink & Switch seven ideals.
For embedded: a guest deep-dive on Interrupt (Memfault accepts community
posts — "CRDT sync on Cortex-M"), embedded.fm, Handmade Network (a
from-scratch MIT C engine is squarely on-brand), r/C_Programming, Hackaday
tips line.

**Realm-refugee capture (the warmest cold list).** The easy migrations are
done; laggards on frozen SDKs remain findable in MongoDB community forums and
realm-swift/realm-js GitHub discussions. Write the "Realm → Kome" migration
guide (every competitor wrote one; it's also SEO), and answer stranded-user
threads directly.

**What not to expect:** stars→revenue conversion is near zero (5K stars ≈
$93 in donations, documented; PostHog: 90% of users pay nothing). Stars buy
credibility and inbound, not rent. Track downloads and production users
(Scarf-style), not stars.

---

## 6. Monetization

MIT is already given away — that forecloses Qt-style dual licensing (nothing
to escape) but not the models that actually work for embeddable C libraries:

1. **Support/consulting menu (first dollars, SQLite/wolfSSL template).**
   SQLite's published menu: $1,500/yr email advice → $8K–$85K/yr technical
   support → $150K/yr Consortium (23 staff-days; 3–4 anchor members fund a
   team). wolfSSL: $2,600→$50K/yr tiers. curl's Stenberg sells through
   wolfSSL's sales machine rather than solo — partnering with an established
   embedded-tools vendor is a shortcut worth copying. Donations are pocket
   money (Tidelift data); contracts are the business.
2. **Paid integration/design-win NRE.** $20–80K to port/integrate Kome into a
   design partner's product + annual support, royalty-free production license
   (the SEGGER norm embedded buyers expect).
3. **Proprietary add-on modules** (the SQLite SEE model — $2K one-time,
   priced under procurement thresholds): mobile SDK convenience layers, blob
   sync module, fleet admin console, FIPS/certified builds, audit/telemetry
   hooks, KMS/HSM integration. These gate cleanly without violating MIT
   expectations (the Supabase playbook gates SSO/SOC2/HIPAA the same way).
4. **Hosted relay/rendezvous network** (later; Iroh/Tailscale model: free
   rate-limited public relays hardcoded as default = adoption subsidy; paid
   dedicated relays with SLAs ~$19/mo+). Caveat: PartyKit couldn't sustain a
   company on relay hosting alone — this is a complement, not the core.
5. **Defense non-dilutive**: AFWERX Phase I $75K → Phase II/D2P2 $1.25M →
   TACFI/STRATFI $375K–$15M matched (Ditto's exact ladder), NATO DIANA
   (€100K + up to €300K, 150-company 2026 cohort) for EU angle; NLnet/NGI
   grants (€5–50K) that also fund the security audit.

**Do immediately regardless of model**: require a DCO/CLA on all
contributions from day one — without it, every outside contribution
permanently vetoes any future licensing flexibility (the lesson from every
relicensing war: Terraform/OpenTofu, Redis/Valkey, Elastic/OpenSearch).

---

## 7. First-customer plan (90 days, then 12 months)

**Prerequisite work items** (weeks 1–6, roughly in order):

1. Ship `pip install kome`, npm/WASM package, and the amalgamation build.
2. Write the blob/attachment pattern doc (even "content-addressed chunks in
   namespaces + out-of-band fetch" as a documented recipe unblocks the
   inspection-ISV conversation).
3. Publish trust collateral: SECURITY.md is there — add a threat model, an
   LTS/versioning policy, a "bus factor" governance note, signed releases +
   SBOM. Apply for an NLnet grant earmarked for a third-party security audit.
4. Build the flagship demo (offline-first shared inventory, two devices,
   relay provably blind) + a 3-minute video.
5. DCO/CLA in CONTRIBUTING.md.

**Launch (weeks 6–10):** Show HN (Sunday evening, demo-led title), simultaneous
lofi-directory/Landscape listings, localfirst.fm pitch, Realm-migration guide
published, answer 5–10 stranded-Realm and ODK forum threads with working code.

**First-customer motion (weeks 6–13, parallel):** pick **15 named targets**
across Tier 1 — long-tail field-inspection ISVs, inflight/event retail ISVs,
and 3–5 dual-use defense startups (AFWERX awardee lists are public) — and
offer a formal **design-partner deal** on the published benchmarks: 3–6
months, weekly 30-min standups, free/discounted integration help, logo +
case-study rights, and a **hard conversion date** to a paid support contract
($8–25K/yr) or NRE engagement. Charge something even in the pilot ("if you
don't charge, it's not a pilot, it's an extended demo"); well-structured paid
pilots convert at 40–60%. Cold outreach is fine — Sierra's and Strella's
design partners were cold-recruited and converted at 100%.

**Defense track (day 1, slow-burn):** register on TAK.gov (free), start the
ATAK "serverless mission sync" plugin, target the next AFWERX Open Topic
window with a TAK-affiliated end user; form the LLC (SBIR requires a US small
business; a solo LLC qualifies).

**How comparable companies actually got customer #1** (verified accounts):

- **Ditto**: warm intro ("a family connection to one of the major US
  airlines") with a prototype that "barely worked"; over-promised P2P, built
  it before the HQ demo, which crashed — and still won, because the pain was
  that acute ([localfirst.fm #26](https://www.localfirst.fm/26/transcript)).
  Lesson: in verticals where offline is existential, one credible demo beats
  a polished product. Use every warm connection to aviation/field ops.
- **PowerSync**: launched by **answering Supabase's most-upvoted open GitHub
  discussion** (offline support, open since 2020) with a working solution —
  the wedge post *was* the launch ([powersync.com](https://powersync.com/blog/bringing-offline-first-to-supabase)).
  Kome's equivalents: ODK's device-to-device forum threads, stranded-Realm
  discussions, TAK's serverless-sync gap — each is a public, pre-qualified
  demand signal you answer with working code.
- **Tailscale**: first paying customer (VersaBank) predated the product —
  it was a consulting-shaped solution to one company's problem that got
  productized ([tailscale.com](https://tailscale.com/blog/tailscale-launch/)).
  The free tier was explicitly engineered as the referral engine ("you did
  pay us — by talking about us").
- **Turso**: first paid plan ($29/mo) shipped only after beta users *asked*
  to pay for production use — free tier first, price when pulled
  ([turso.tech](https://turso.tech/blog/announcing-the-turso-scaler-plan-404e03c6cbf7)).
- **Pattern**: bottom-up companies (Supabase 1,120-pt HN launch, ElectricSQL
  617, PowerSync 356) used HN + ecosystem wedges; enterprise-vertical
  companies (Ditto) used warm intros + SBIR. Kome needs both tracks — they
  are §5's launch plan and this section's design-partner motion respectively.

**12-month picture:** 1–2 paying design partners converted (≈$20–80K),
one AFWERX Phase I or NLnet grant (≈$50–75K non-dilutive), DPG certification
filed, Zephyr/ESP-IDF port shipped with one embedded design-win conversation
underway, and a decision point: consultancy-shaped business (Kastelo model,
sustainable but small) vs product company (raise on the Ditto-comp narrative
with the traction as proof).

**Success metrics that matter:** production deployments and support-contract
revenue — not stars. Interim: pip/npm downloads, design-partner conversations
started, forum answers that turned into threads.

---

## 8. Top risks

1. **Solo-maintainer trust deficit** in exactly the safety/revenue-critical
   niches where the pain is worst. Mitigation: audit + LTS policy + governance
   doc *before* commercial conversations; partner/sub through integrators.
2. **Ditto moves down-market or Iroh moves up-stack** (iroh-docs growing
   record CRDTs + capabilities). Mitigation: speed in the niches they
   structurally can't serve (MIT/embedded/E2EE); consider Iroh interop rather
   than competition at the transport layer.
3. **Blob gap stalls the best vertical** (inspection photos). Mitigation:
   pattern doc now, module later — it's also a natural paid add-on.
4. **The quiet-market problem**: embedded C sync demand is implied (ObjectBox's
   business exists) but not loudly expressed; it needs evangelism, which takes
   time. Mitigation: the field-ops ISV track carries revenue expectations;
   embedded is the patient second bet.
5. **Free-rider culture** in the local-first/self-hosted community. Accept it:
   that community is the distribution engine, not the revenue engine.
