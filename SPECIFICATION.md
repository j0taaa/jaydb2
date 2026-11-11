JayDB is an in-memory database that executes Bend programs accompanied by proofs. It provides typed data, authentication, and atomic publication of changes. The administrator defines the application's meaning and permissions through laws.

This contract contains the data model and eight English laws mapped to inhabited executable theorems in `contract/Theorems.bend`. The definitions below are part of the contract. The [proof guide](proof/README.md) identifies the witnesses and trusted base T1–T3.

Revision authorized on 2026-10-29: physical memory and time budgets were removed. The earlier contract remains in Git history. The active contract in `contract/` retains the three canonical size limits and the authentication, proof, access, and publication guarantees. Historical files are English translations; their original Portuguese versions remain in Git history.

Prepared execution uses the wire vocabulary in `contract/PreparedProtocol.bend`
and scoped lookup in `contract/PreparedRegistry.bend`. `UnifiedCoreTheorem`
covers the exact request selected by `src/Resolve.bend`, with fresh
authentication and sound admission for that request. Cached universal admission
specialized at lookup is part of T1's source/program/artifact binding.
Preparation and invalidation use the checked `Control` plan/delta.
Artifact IO and delivery of T1 admission tokens remain host obligations.

The native worker executes the checked `Gate`/interpreter/finalizer path;
compiler/runtime preservation and physical host plumbing remain T2/T3.

`HostErrorReplyTheorem` covers the native controller's total exact error-code
classification and canonical response construction, preserving the published
root, last response and prepared registry. `contract/HostErrors.bend` specifies
the certificate-code table; every other code, including `HANDLE` and
`PREPARED_INTEGRITY`, produces `failure`. Rust forwards the observed code and
returned bytes, memoized by exact code. Startup separately prefills `HANDLE`
and `PREPARED_INTEGRITY`; `HostErrorReplyTheorem` states the emitted bytes equal
`Messages.error(HostErrors.status(code))` for every root/last/registry. Memo reuse
therefore preserves the exact checked denial at later roots and adds no process
to prepared denials with those codes. Physical artifact lookup/integrity, detection
of actual failures and preventing execution after a failed integrity check remain
host duties.
If the denial executable/transport itself fails, the host retains the existing
fixed technical failure fallback, diagnosed on stderr and never memoized.
Successful calls use the same execution path.

# Database concept

An instance contains tables and users. A request presents a credential, a program, its arguments, and a proof. The database authenticates the request, checks whether the proof establishes the required obligations for that program, and executes the program when admitted. The program may query data, compute a result, and propose changes.

Every program must satisfy all installed laws. A condition such as “employees may read only their own information” belongs inside a law. JayDB does not select law sets per user, automatically filter records, or grant administrators an implicit exception.

Read control covers information inspected by the program even when it is not returned in the response. An ownership check may authorize a subsequent access provided the check's own reads are permitted. The proof covers paths where the check succeeds and paths where it fails.

# Responsibilities and scope

| The kernel provides | The administrator defines |
| - | - |
| Tables, columns, types, keys, and explicit absence | Concrete schema and data meaning |
| Authenticated identity and a mutable user registry | Who may register, delete, or change users |
| Semantics of data observations and changes | Which observations and changes are allowed |
| Proof checking against every installed law | Ownership, role, privacy, and business laws |
| Faithful execution and atomic publication | Programs and results needed by the application |
| Canonical size limits and defined failures | The three maximum sizes and data organization |

The kernel defines no record ownership, role hierarchy, private fields, self-promotion ban, balance conservation, cross-table relationships, application cryptography, or authorization necessarily based on prior state. Administrator laws may express all of these. Reading and changing are independent permissions.

The service processes requests serially over standard input/output, using native CPU Bend in a fresh child process per call. The host retains published state in RAM; the child receives a private proposal and does not publish directly. Schema and laws remain fixed for the instance; data and users may change. Without opt-in complete-image persistence, exiting loses the data. Persistence reopening checks the frozen configuration without evaluating a seed; durability remains outside the pure source theorems.

Outside this version: a network database daemon, distribution, guaranteed parallel request execution, dynamic schema changes, migrations, configurable indexes, history, auditing, sessions, password recovery, preinstalled programs, mandatory caching, automatic retries, and request deduplication. The database does not generate or repair proofs.

Every transaction uses code and a proof, either supplied in the request or
resolved from an instance-local prepared registration. Preparation is optional
metadata management, not a preinstalled transaction catalog or a user/data
registration operation. There are no separate public query or insertion
commands. The internal data operations below only define what submitted code
may do.

# Common definitions

## Configuration and state

`C` denotes the fixed configuration: schema, laws, definitions they depend on, admitted language and libraries, verifier, and canonical size limits. Fixing a law includes fixing the meaning of its helper functions and dependencies.

A valid configuration has unique names and well-defined types, one primary key per table, well-typed laws and definitions closed under admitted dependencies, a fixed environment, and finite limits consistent with the protocol. The kernel fixes the logical system and its assumptions; laws and proofs do not extend them. Configuration need not prove every desired business operation possible; incompatible laws may prevent operations.

`S` denotes published state: tables and the registry used to authenticate users. Every table is a finite map from keys to rows. This map's physical representation is unrestricted provided it preserves the meaning defined here.

Data obeys the following structural rules:

- Each column has type `TextValue`, `Boolean`, or `Integer` and may be optional. A stored integer lies in −2⁶³ through 2⁶³−1. Text is valid Unicode, compared exactly without implicit normalization.

- Every table has one mandatory, unique textual primary key. Every row contains exactly the schema columns. Optional absence is an explicit value; omitting a column does not fill it with absence.

- Table, column, and record-field names contain 1–64 ASCII characters: a letter or underscore first, followed by letters, digits, or underscores. Names are case-sensitive. Textual keys and values do not have this naming restriction.

- There is no implicit coercion, default value, identifier, timestamp, or randomness. Incompatible values, unknown or repeated fields, and out-of-range integers are invalid. Program computations follow language semantics; the database never silently converts their results to another value.

- Each user has a unique textual identifier and textual type. In published state, their textual credential is nonempty and unambiguous among existing users. No user or privileged role is mandatory, and future identifier reuse is not structurally forbidden.

The registry is a logical collection with mandatory columns `id`, `kind`, and `credential`, keyed by `id`. It uses the same operations as tables, with an address distinguishable from application-table addresses. It receives no special permissions. Additional user data may reside in application tables.

Authentication compares the presented credential with the published registry and produces context `c`, containing the user's identifier and type at that moment. The credential is not automatically added to program arguments. Types, mandatory-field presence, and operation validity are checked on every write. Nonempty, unique credentials are required at initialization and every publication. Working state may temporarily contain empty or duplicate credentials if all administrator laws permit that path. This allows, for example, swapping two credentials atomically. Presenting an empty credential produces an authentication error; a success proposal still containing an empty or duplicate credential produces a data error and preserves prior published state. Refusal discards working state without requiring it to be repaired.

Schema, laws, and limits are public configuration for clients authorized to use the instance. Row values, including identifiers, counts, and registry information, receive no implicit read permission merely because they are metadata.

## Programs and data operations

A request is `r = (credential, p, a, π)`: program `p`, arguments `a`, and proof `π`. Arguments and responses are finite values built from absence, booleans, integers in the same 64-bit range, text, lists, and records. They contain no functions, process references, or opaque database parts.

The program uses the pure, terminating, verifiable fragment of the pinned Bend version. It may define functions, compute, and use recursion admitted by the language. It and its dependencies access no files, network, processes, clock, external randomness, foreign code, or mechanisms escaping verification. Submission checking must not execute arbitrary client effects either. The [official Bend guide](https://github.com/bendlang/bend/blob/main/guide/GUIDE.md) describes purity, termination, and the limits of its proof guarantees.

Execution starts with working state `W = S`. Changes affect only `W` until publication. Later reads in that execution observe working state, including earlier changes from the same call. The program ends by proposing `Success(W, value)` or `Refusal(value)`. The proposal becomes the final outcome only after response preparation and publication conditions.

| Internal logical operation | Exact meaning |
| - | - |
| Observe a cell | Obtain the column value in the current row; a nonexistent row produces `RowAbsent`, distinct from absence in an optional column. |
| Observe metadata | Obtain a row's existence, the row count, or current keys. Enumeration uses lexicographic order of UTF-8 key bytes. |
| Set a complete row | Insert or replace exactly the indicated row without returning its previous content or indicating insertion versus replacement. |
| Set a column | Replace only that column if the row exists, retaining the others. If it does not exist, change nothing. Do not report whether it existed. |
| Remove a row | Remove the indicated row; if it does not exist, preserve state. Do not return its content or report whether it existed. |

Every write receives explicit new values. A complete row's key must match the addressed key. Setting the key column to another value causes a data error; changing a key requires removing the old entry and defining the new one. This also applies to user identifiers. Successive changes at the same position apply in program order; the last determines the final value. Nothing implicitly changes other rows or tables.

A nonexistent table or column, incompatible write, or incomplete row causes a data error and discards the entire proposal. An operation result revealing a data fact, including existence through success or error, is an observation. Writes do not by themselves imply access to the previous value.

These operations specify database behavior without prescribing function names, a query DSL, or internal implementation organization.

## What counts as an observation

An observation occurs when database information becomes available to program computation: a cell value, presence, absence, identifier, count, order, or another property derived from previously unobserved data. Comparison, destructuring, hashing, and serialization cannot create a read path outside this definition.

Preserving opaque untouched state, carrying an unexamined reference, and replacing a value without obtaining its predecessor do not inspect every involved value. Materializing database content for a response is an observation. Internal work needed for authentication and these operations does not automatically expose its data to the program.

`τ` denotes the logical sequence of execution observations and changes. Each event identifies the operation, address, and observed result or supplied new values, including absence and errors when they reveal information. This sequence reconstructs working states and identifies the state of every access. It belongs to proof semantics; it requires neither a stored log nor an audit system.

## One signature for all administrator laws

Every installed law is a proposition `Lᵢ(h)`. Record `h` describes one of these situations:

- `Stable(S)`: published state with no request executing.

- `Executing(S₀, c, p, a, W, τ)`: initial state, authenticated context, code, arguments, working state, and access sequence up to that point.

- `Closed(S₀, c, p, a, W, τ, o)`: the same facts and final outcome `o`, which may be success with a response, program refusal with a response, or interruption before publication with an exact error category defined below.

Every record is submitted to the same complete law list. Conditions on situation, user, type, table, or column belong inside each law. This can require integrity in published states while allowing intermediate computations that do not yet satisfy it; it can also restrict every access, including before interruption.

Rejection before program start follows the kernel contract and creates no user execution. Starting any program always requires the complete conjunction of installed laws.

We use two abbreviations:

```text
Laws(h) = L₁(h) ∧ L₂(h) ∧ ... ∧ Lₙ(h)
Valid(S) = Structure(C, S) ∧ Laws(Stable(S))
```

`Structure` means exactly the structural data rules and state-size limit. An empty law list adds `true`; it creates no hidden permission policy. Laws may be general propositions expressible in the admitted formal system. They need not be a list of runtime boolean checks.

## What each certificate proves

Initialization receives a proof of `Valid(S₀)`. The database checks it; it does not promise to discover automatically whether arbitrary laws hold for initial data.

The certificate may fix context `c` and arguments `a`, or prove a more general statement including them. It covers every valid initial state whose registry produces that context for the authenticated identifier. The verifier uses the context actually obtained in the call. For those states, the certificate establishes:

```text
At every admitted execution prefix and outcome: Laws(h).
Proposal Success(W, v) ∧ FinalTechnicalConditions(C, W, v)
⇒ Valid(W).
```

Final technical conditions are valid structure and types, state/response limits satisfied, and preparation completed without interruption. They do not include runtime testing of administrator laws. The proof establishes those laws for every technically possible publication as well as covering accesses and interruptions. Exceeding a limit can therefore end a call without requiring the program to inspect the whole database to compute its size.

Prefixes require the laws during execution and actual failure. They do not require permission for a hypothetical `limit` termination: state and response limits are checked at finalization, whose actual result remains subject to the laws.

This includes interruptions before publication, even after reads or provisional changes. A law depending on an inevitable future completion may prevent certification of an interruptible program; the kernel does not change that law to accept the request.

There is no arbitrary private premise the client may simply declare true. Conditions not following from established invariants must be handled in the program itself with permitted accesses, including its refusal path. The client may reason symbolically about state without receiving its private values.

# The eight kernel laws

Theorems concern the actual executable functions. Core's four clauses quantify
over valid configuration, valid starting state and a sound admission oracle
for the exact request. T1 supplies admission soundness and source/Book binding;
T2 supplies compiler/runtime preservation; T3 specifies the host's faithful
execution of the numbered plumbing obligations in [the proof guide](proof/README.md).

## Law 1 Faithful initialization and fixed contract

`StartupTheorem` describes the executed `ConfigurationCheck.initialize`:
for the seed whose `Requirements.Valid` declaration was admitted under T1,
it returns success with exactly that seed's encoding iff the configuration
and frozen environment identity check passes; otherwise it returns refusal.
`ConfigurationCheck.recover` accepts iff that same check passes, without
opening a seed. Recovery-byte validity and durability have separate scope.
`assertInitialization` checks the exact closed configuration/seed declaration;
the runtime initializer does not receive or test a proof value. `InitTheorem`
is an abstract seed-admission helper for `FoldTheorem`, which derives validity
of every reached root under the same configuration. T3 installs exactly the
checked root and pins the configuration/source bytes.

`ServiceFoldTheorem` extends validity to interleaved transactions and checked
controls starting with an empty registry, with exact registry transition history
and universally certified live sources. Its public lookup/invalidation clauses
and `ServiceNoRevivalTheorem` show that removal clears scoped entries, preserves
allocation history, and an allocated absent handle stays absent at every later
position. `ControlTheorem` proves the structural controller checks for every
admission token; sound source certification uses the T1 premise in `ServiceRun`.

## Law 2 Representation without changing meaning

`CodecRoundtrip` proves decoding of successful canonical encodings when body
length fits uint64 and the decoder ceiling. `CodecCanonical` proves that every
accepted value re-encodes to the exact original bytes. `FramingRoundtrip`
proves inversion of successful private two-block joins for valid octets.
State representation lemmas in `proof/Representation.bend` connect the actual
state decoder to the canonical state value. `Data.operate` defines the data
operations used by the interpreter. T2 preserves these computations; T3 binds
physical root bytes, public u64 framing, bounds and EOF to those values.

## Law 3 Authentic identity

`CoreTheorem`'s `Admitted` clause proves current-state authentication and an
exact machine start with that context and the request's arguments. `Gate`
authenticates before invoking admission. `UnifiedCoreTheorem` uses the actual
registered resolver, which authenticates before scoped lookup and preserves
credential and arguments. T3 supplies one current snapshot and passes the
selected tuple unchanged; T2 preserves the computed result.

## Law 4 Proof bound to complete behavior

The `Admitted` clause proves that every started machine corresponds to the
exact oracle `Accept` and exact `Core.start`. `OracleSoundness` makes acceptance
establish `Requirements.Certifies` and termination for the actual program,
configuration, context and arguments. T1 binds those targets to exact source,
dependencies and the immutable checked Book compiled for execution, including
purity and host-effect exclusion. A failed client proof rejects whole-Book
admission before Gate runs; the checked controller maps exact observed error
codes to `certificate` or `failure` under `HostErrorReplyTheorem` and the
[contract code table](contract/HostErrors.bend). Detection and exact code/cache
forwarding remain [trusted host duties](proof/README.md#trusted-base).
The 17-code table is a specification, not a proof that it equals the Node tools'
proof-rejection codes; `ORACLE_PROOF`, `ADT` and `INSTANCE_MATCH` map to `failure`.
Gate's `Reject` branch exists for the theorems but is not the production proof
rejection path; `Reject` and `ToolFailure` describe post-admission oracle
verdicts and never start the program. Soundness does not imply that every valid
certificate is accepted.

## Law 5 Faithful execution and complete observations

`CoreTheorem`'s `Safe` clause proves `Requirements.SafetyTrace` at every prefix
of the actual machine. Interpreter fidelity relates those prefixes to
`Semantics.execute`, including reads and provisional writes before refusal or
error. The certificate's prefix/failure/final obligations cover every installed
law. T2 preserves the closed Action interface and observation order in native
execution; T3 runs that checked machine with the exact state and arguments.

## Law 6 Valid atomic and serial publication

The `Completed` clause proves the exact finisher, `Requirements.finalize`,
`Semantics.publish` and validity of the next root. Success selects the whole
working root; every other status preserves the initial root. `FoldTheorem`
derives validity throughout finite serial runs whose steps carry the actual
gate, final-trace and publication equations. T3 performs atomic root/response
replacement only after preparation and cleanup, and feeds exactly that root
to the next request. Physical atomicity and serial dispatch are host obligations.

## Law 7 Exact results and interruptions

The `Completed` clause proves exact final response, exact framed bytes, response
size bound and absence of a generic post-admission `failure`. `Admitted` also
proves bounded framed early responses preserving the initial root.
`IngressTheorem` classifies complete ordinary-body decoding into exact-root
execution or a bounded denial. `Requirements.finalize` determines logical
size/data outcomes. Safety retains observations on failure paths. T3 binds
actual pre-commit failures, cleanup and channel behavior to these results;
a delivery failure after commit retains the committed root and does not turn
success into rollback. OS failure occurrence is outside the pure theorem.

## Law 8 Positive operation

The `Progressing` clause proves that an accepted machine reaches a final trace
and completes. If `WithinLimits` holds for that computed trace (a success or
refusal proposal preserved by finalization), the final response is success or
refusal. Safe terminating programs may still encounter data errors.
`StartupTheorem` proves the initializer's seed encoding and the recovery check;
accepted-start progress comes from Core's `Progressing` clause, with the fold
carrying Core's clauses through the finite run. The real tasks positive fixture
shows valid admission and changed-root success; refutations exclude a
reject-all gate when its oracle returns `Accept`.

T1 soundness is a premise; acceptance of every valid mathematical certificate
requires a separate checker adequacy assumption. Physical resource
availability, scheduling fairness and syscall progress are host/runtime
assumptions. The theorems establish logical termination after acceptance.

# Inputs, outputs, and completion

## Possible outcomes

Processing follows this order: frame and decode the request, authenticate, admit code and check the proof, execute on private state, prepare the response, and publish on success. The first impediment in that order ends the call. A limit or technical failure may interrupt the current stage.

| Status | Meaning and effect |
| - | - |
| `input` | Malformed, incomplete message or invalid fields. Does not execute code. |
| `authentication` | Identity could not be established. Does not execute code. |
| `certificate` | Code, dependencies, or proof not admitted. Does not execute the program. |
| `data` | Structurally invalid operation or proposed state. Discards the proposal. |
| `limit` | Canonical size exceeded the message, state, or response limit. Equality with the ceiling is allowed. Discards any unpublished proposal. |
| `failure` | Actual failure of a tool or resource used according to its contract. Discards any unpublished proposal. |
| `refusal` | The program refused the operation and produced a response subject to the laws. Does not publish changes. |
| `success` | Publishes final state and returns the program result. |

A response contains exactly `status` and `value`. For the six fixed errors, `value` is absence. For the two program outcomes, it is the produced value. The response channel adds no compiler messages, private data, proofs, or variable diagnostics.

Limits are three fixed public parameters: message, published-state, and response sizes. They are finite canonical-byte quantities representable in 64 bits; the response limit accommodates fixed errors. Results are never truncated, data automatically removed, or state partially published to fit a limit.

The kernel neither measures nor imposes physical memory or per-stage time. It does not promise to turn every resource exhaustion into a recoverable response. A mathematically terminating program may occupy the serial instance for a long time; a fatal failure may lose the process and RAM data without a response. Recoverable failures before publication preserve published state. Later delivery failure does not undo publication. Correct execution remains required when the environment permits; implementation may not invent failure or deny processability to hide improper rejection.

External operational protections are optional and outside the database proof. If they terminate the process, they can lose the entire instance. They are not presented as a per-request budget.

EOF between messages or operator-requested shutdown ends service between calls. Incomplete header/body closes the channel with `input`; a declared size above the ceiling closes it with `limit`. These errors are sent when the channel still allows. A complete body within the limit that is malformed produces `input` and permits the next message. A failure making the process unusable ends the instance. Shutdown does not save data, and response delivery is not promised when the channel or process itself fails.

## Minimal canonical encoding

Each ordinary message starts with its byte length as an unsigned 64-bit integer in most-significant-byte-first order, followed by one value. There are no extra bytes within the ordinary message. The optional prepared-program envelope described below reserves a prefix outside the Value tags.

Each value starts with a one-byte tag: `0` for absence, `1` for false, `2` for true, `3` for integer, `4` for text, `5` for list, and `6` for record. Other tags are invalid. Integers use eight bytes of two's complement in the same byte order. Text uses a 64-bit length followed by valid UTF-8. Lists use a 64-bit count followed by values. Records use a 64-bit count followed by name–value pairs; names are valid field texts, unique and in lexicographic ASCII order. Lengths and counts are checked before allocation or excess reading. An external header above the message ceiling produces `limit`. Within an admitted body, impossible internal lengths, truncation, and malformed data produce `input`. A proposal whose state or response exceeds its ceiling produces `limit` without truncation.

A request is a record with exactly `arguments`, `code`, `credential`, and `proof` in that canonical order. The last three are texts; `arguments` is any admitted value. Responses use `status` and `value`. Source and proof are preserved exactly; their interpretation belongs to the fixed Bend environment.

State size is measured using record `{tables, users}`. `tables` is a list of records `{name, rows}` in ASCII name order. `rows` contains complete records in UTF-8 primary-key order. `users` is a list of records `{credential, id, kind}` in UTF-8 `id` order. Message, state, and response sizes count canonical-value bytes, excluding the external eight-byte framing. This order neither dictates in-memory layout nor reorders program-produced lists.

## Optional prepared programs

An instance may register arbitrary admitted source and a certificate universally
quantified over contexts and arguments. The registration freezes the original
program, proof, configuration and dependency closure and owns an ordinary
official native executable. A handle is an instance-local reference to that
registration, not a source string or an authenticated identity. Ordinary
concrete certificates remain supported without registration.

The outer message length and limit cover the complete actual body, including
the `0x07` prefix and operation byte. Prepare and invalidate are authenticated
metadata controls; their size-bounded `prepared` and `invalidated` receipts do
not execute a transaction or replace the published state/response pair. These
receipts are separate from the eight transaction statuses. Lifecycle and exact
wire details are specified in [PREPARED_PROGRAMS.md](tools/service/PREPARED_PROGRAMS.md).

A prepared execution authenticates against the current published state. The
worker's checked resolver preserves that state, context, credential and actual
arguments while substituting the registration's exact original source/proof
identity. The universal certificate specializes to that resolved logical call.
All program observations, administrator laws, private execution, size checks
and atomic publication continue to apply. No checker or compiler is needed on
reuse. An unavailable or altered registration produces a technical/control
failure before execution; it does not establish that a valid proof is false.

The canonical Request in the pure transaction model denotes this resolved
logical call. Its ordinary byte-origin theorem is not a theorem equating a raw
handle envelope with source bytes. `UnifiedCoreTheorem` applies Core to the exact result of executable selection.
Physical prefix dispatch, registry/artifact integrity and control receipts
belong to the T1/T3 integration boundary.

# Implementation obligation

The inhabited theorems establish the executable claims mapped above. A delivered native service must also satisfy T1–T3 for its exact admitted/compiled artifacts and physical inputs, root replacement and responses. The [proof guide](proof/README.md) records the integration status and numbered host obligations.

The proof is relative to the pinned logical system and T1–T3. Durability of persistence, OS failures and checker completeness/adequacy are outside the proved scope. Physical timing and resource-consumption channels are outside the confidentiality guarantee.

A concrete database's rules still come from its administrator. JayDB guarantees their application to admitted programs; it does not invent what owning a car means, which data is private, or what business operations should exist.
