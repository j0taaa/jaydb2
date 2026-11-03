> Historical English translation. This specification predates removal of physical budgets and does not describe the active service. The original Portuguese text remains in Git history.

JayDB is an in-memory database that executes Bend programs accompanied by proofs. It provides typed data, authentication, and atomic publication of changes. The administrator defines the application's meaning and permissions through laws.

This contract contains the kernel definitions and eight general laws. The laws are written as readable mathematical obligations; their Bend translation and mechanically checked proofs belong to the implementation. The definitions below are as much part of the contract as the law statements.

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
| Resource limits and defined failures | Their values and data organization |

The kernel defines no record ownership, role hierarchy, private fields, self-promotion ban, balance conservation, cross-table relationships, application cryptography, or authorization necessarily based on prior state. Administrator laws may express all of these. Reading and changing are independent permissions.

The first version serves one request at a time in a local process over standard input/output, using native CPU Bend. It retains a RAM database. Schema and laws remain fixed for the instance; data and users may change. Exiting the instance loses its in-memory data.

Outside this version: persistence, networking, distribution, guaranteed parallelism, dynamic schema changes, migrations, configurable indexes, history, auditing, sessions, password recovery, preinstalled programs, mandatory caching, automatic retries, and request deduplication. The database does not generate or repair proofs.

Every application interaction uses code and a proof. There are no separate public query, insertion, or registration commands. The internal data operations below only define what that code may do.

# Common definitions

## Configuration and state

`C` denotes the fixed configuration: schema, laws, definitions they depend on, admitted language and libraries, verifier, and resource limits. Fixing a law includes fixing the meaning of its helper functions and dependencies.

A valid configuration has unique names and well-defined types, one primary key per table, well-typed laws and definitions closed under admitted dependencies, a fixed environment, and finite limits consistent with the protocol. The kernel fixes the logical system and its assumptions; laws and proofs do not extend them. Configuration need not prove every desired business operation possible; incompatible laws may prevent operations.

`S` denotes published state: tables and the registry used to authenticate users. Every table is a finite map from keys to rows. This map's physical representation is unrestricted provided it preserves the meaning defined here.

Data obeys the following structural rules:

- Each column has type `TextValue`, `Boolean`, or `Integer` and may be optional. A stored integer lies in −2⁶³ through 2⁶³−1. Text is valid Unicode, compared exactly without implicit normalization.

- Every table has one mandatory, unique textual primary key. Every row contains exactly the schema columns. Optional absence is an explicit value; omitting a column does not fill it with absence.

- Table, column, and record-field names contain 1–64 ASCII characters: a letter or underscore first, followed by letters, digits, or underscores. Names are case-sensitive. Textual keys and values do not have this naming restriction.

- There is no implicit coercion, default value, identifier, timestamp, or randomness. Incompatible values, unknown or repeated fields, and out-of-range integers are invalid. Program computations follow language semantics; the database never silently converts their results to another value.

- Each user has a unique textual identifier, textual type, and nonempty textual credential. Credentials are unambiguous among existing users. No user or privileged role is mandatory, and future identifier reuse is not structurally forbidden.

The registry is a logical collection with mandatory columns `id`, `kind`, and `credential`, keyed by `id`. It uses the same operations as tables, with an address distinguishable from application-table addresses. It receives no special permissions. Additional user data may reside in application tables.

Authentication compares the presented credential with the published registry and produces context `c`, containing the user's identifier and type at that moment. The credential is not automatically added to program arguments. Types and formats are required on writes; credential uniqueness and other state invariants are required in published states. This allows, for example, swapping two credentials atomically.

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

This includes interruptions before publication, even after reads or provisional changes. A law depending on an inevitable future completion may prevent certification of an interruptible program; the kernel does not change that law to accept the request.

There is no arbitrary private premise the client may simply declare true. Conditions not following from established invariants must be handled in the program itself with permitted accesses, including its refusal path. The client may reason symbolically about state without receiving its private values.

# The eight kernel laws

Every law below is universal: it applies to any valid configuration, state, identity, input, program, and execution path within the defined domain.

## Law 1 Faithful initialization and fixed contract

> The instance starts serving only after validating configuration and checking the initial-state validity proof. It starts with exactly that state and preserves configuration meaning throughout its lifetime.

```text
Started(C, S₀) ⇒ ValidConfiguration(C) ∧ Valid(S₀)
Throughout the instance: configuration = C
```

**How it works:** rejected initialization never leaves a partially usable database. Schema, laws, definitions, and dependencies do not change through requests. Users remain mutable because they are data. Initial invariants are established by proof and preserved by subsequent publications, not presumed anew on every call.

## Law 2 Representation without changing meaning

> What is received, stored, and returned represents exactly the values defined by the contract. No representation introduces ambiguity, information loss, conversion, or extra behavior.

```text
representable x ⇒ decode(encode(x)) = x
decode(b) = x ⇒ encode(x) = b
abstract(store(S)) = S
```

**How it works:** canonical encoding is defined below. Invalid inputs are rejected in full. Physical record order, field layout, and optimizations do not change values or results. An out-of-domain integer never silently becomes another integer; a missing field never becomes a default. Data operations have exactly the effects specified in the preceding table.

## Law 3 Authentic identity

> Execution uses exactly the context obtained from the presented credential and state published at call start. No client-supplied content may replace that fact.

```text
Executed(r, S₀, c) ⇒ Authenticate(S₀, r.credential) = c
```

**How it works:** a missing or invalid credential does not start the program. User registration, deletion, and credential changes published by one call affect later authentications. If laws allow changing one's type or deleting one's account, that does not change who started the call. This law does not choose which state or attribute the administrator uses to authorize an operation.

## Law 4 Proof bound to complete behavior

> A request's program starts executing on instance data only after the verifier accepts a proof of the obligations above for that code, its dependencies, authenticated context, and arguments under the actual configuration.

```text
Started(r) ⇒ Verify(C, r.p, c, r.a, r.π) = Accepts
Accepts ⇒ the certificate establishes all required obligations
```

**How it works:** proving a different function, using different laws, or adding an unsupported hypothesis does not enable execution. Administrator laws are obligations to prove, not axioms granted to the client. Definitions, imports, and proof helpers are covered too. A rejected proof and a verifier limit are distinct outcomes; neither permits program execution.

## Law 5 Faithful execution and complete observations

> Actual behavior is the certified program's behavior in the defined semantics, including every observation, provisional change, and outcome. There is no additional path for data access or effects.

```text
actual behavior ∈ admitted executions(C, p, c, a, S₀)
actual observations = observations of the corresponding execution
```

**How it works:** code receives the correct arguments, starts in the correct state, and its operations see the correct working state. Helpers, comparisons, destructuring, and output follow the same read definition. A forbidden access does not become acceptable because the program later returns an error. Different implementations are allowed provided they preserve certified meaning and logical accesses.

## Law 6 Valid atomic and serial publication

> A successful call publishes exactly its valid final state all at once. No provisional change is published before that point. The next call starts with the state left by its predecessor.

```text
Published(W) ⇒ Valid(W) ∧ next state = W
Completed without publication ⇒ next state = S₀
```

**How it works:** multi-table data and user changes are published together. Refusal or failure before publication preserves the entire initial state. A call's reads see its provisional changes; other calls do not. Success may preserve state, as with a query. There are no implicit changes, triggers, or external effects.

## Law 7 Exact results and interruptions

> The response matches the call's defined outcome. Limits and failures use only the specified categories without exposing extra internal data. Complete response preparation and publication conditions are checked before publication.

```text
Final outcome Success(v) ⇒ publish W and prepare response (success, v)
Final outcome Refusal(v) ⇒ preserve S₀ and prepare response (refusal, v)
Error before publication ⇒ preserve S₀ and prepare a fixed error
```

**How it works:** the program response, including refusal, remains subject to the laws. An output limit produces neither a partial response nor partial publication. Interruption does not erase prior observations. If response delivery fails after publication, the change remains; delivery or the channel ends without replacing success with an aborted-operation message. Resending a request starts a new execution.

## Law 8 Positive operation without hidden conditions

> Valid configuration and an initial validity proof start the instance when processable within the limits and without technical failure. Certificates that are valid derivations of the required obligations in the fixed format, fragment, and logical system must be accepted under the same conditions. Admitted requests must run and produce the corresponding outcome.

```text
Conditions satisfied ∧ no specified impediment
⇒ corresponding execution and completion
```

**How it works:** rejecting everything is not a correct implementation. The kernel invents no extra permission, does not ignore laws, and does not replace programs with filtered versions. A technical failure must correspond to a specified actual failure, not an unrestricted excuse to reject. The obligation is to check the supplied certificate, not discover proofs or accept programs without them.

# Inputs, outputs, and completion

## Possible outcomes

Processing follows this order: frame and decode the request, authenticate, admit code and check the proof, execute on private state, prepare the response, and publish on success. The first impediment in that order ends the call. A limit or technical failure may interrupt the current stage.

| Status | Meaning and effect |
| - | - |
| `input` | Malformed, incomplete message or invalid fields. Does not execute code. |
| `authentication` | Identity could not be established. Does not execute code. |
| `certificate` | Code, dependencies, or proof not admitted. Does not execute the program. |
| `data` | Structurally invalid operation or proposed state. Discards the proposal. |
| `limit` | A configured limit was actually reached. Discards any unpublished proposal. |
| `failure` | Actual failure of a tool or resource used according to its contract. Discards any unpublished proposal. |
| `refusal` | The program refused the operation and produced a response subject to the laws. Does not publish changes. |
| `success` | Publishes final state and returns the program result. |

A response contains exactly `status` and `value`. For the six fixed errors, `value` is absence. For the two program outcomes, it is the produced value. The response channel adds no compiler messages, private data, proofs, or variable diagnostics.

Limits are fixed public parameters: message, published-state, and response sizes, processing memory, and per-stage time. Byte limits are finite and fit in 64 bits; the response limit accommodates fixed errors. Physical limits are finite and positive. Logical sizes use canonical encoding; physical limits use the measures specified by the environment. Results are never truncated, data automatically removed, or state partially published to fit a limit.

EOF between messages or operator-requested shutdown ends service between calls. Incomplete header/body closes the channel with `input`; a declared size above the ceiling closes it with `limit`. These errors are sent when the channel still allows. A complete body within the limit that is malformed produces `input` and permits the next message. A failure making the process unusable ends the instance. Shutdown does not save data, and response delivery is not promised when the channel or process itself fails.

## Minimal canonical encoding

Each message starts with its byte length as an unsigned 64-bit integer in most-significant-byte-first order, followed by one value. There are no extra bytes within the message.

Each value starts with a one-byte tag: `0` for absence, `1` for false, `2` for true, `3` for integer, `4` for text, `5` for list, and `6` for record. Other tags are invalid. Integers use eight bytes of two's complement in the same byte order. Text uses a 64-bit length followed by valid UTF-8. Lists use a 64-bit count followed by values. Records use a 64-bit count followed by name–value pairs; names are valid field texts, unique and in lexicographic ASCII order. Lengths and counts are checked before allocation or excess reading. Values whose size exceeds representation or the applicable limit produce `limit` without truncation.

A request is a record with exactly `arguments`, `code`, `credential`, and `proof` in that canonical order. The last three are texts; `arguments` is any admitted value. Responses use `status` and `value`. Source and proof are preserved exactly; their interpretation belongs to the fixed Bend environment.

State size is measured using record `{tables, users}`. `tables` is a list of records `{name, rows}` in ASCII name order. `rows` contains complete records in UTF-8 primary-key order. `users` is a list of records `{credential, id, kind}` in UTF-8 `id` order. Message, state, and response sizes count canonical-value bytes, excluding the external eight-byte framing. This order neither dictates in-memory layout nor reorders program-produced lists.

# Implementation obligation

A correct implementation must establish the eight laws jointly for the complete kernel that transforms inputs into executions, states, and responses, including initialization, authentication, admission, operations, encoding, and publication. There may be many helper lemmas; they add no requirements to the public contract.

The proof is relative to the logical system and declared compiler, verifier, runtime, and environment contracts. Physical timing and resource-consumption channels are outside this scope's confidentiality guarantee.

A concrete database's rules still come from its administrator. JayDB guarantees their application to admitted programs; it does not invent what owning a car means, which data is private, or what business operations should exist.
