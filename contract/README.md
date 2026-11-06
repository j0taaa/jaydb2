# JayDB — specification and laws in Bend

This is the revised JayDB2 contract, authorized on 2026-10-29 to remove physical memory and time budgets. It contains **eight kernel obligations**, reference semantics, and helper lemmas. Laws 2, 7, and 8 were revised within that scope; the guarantees of Laws 1, 3, 4, 5, and 6 were preserved. English translations of the earlier version's 18 files are in [history/contract-v1](../history/contract-v1/); the original Portuguese versions remain in Git history.

On 2026-11-06 the user authorized an additive prepared-program contract. It adds explicit wire, registry, admission and control obligations in `PreparedProtocol.bend`, `PreparedRegistry.bend` and `PreparedLaws.bend`. The existing eight laws, ordinary request encoding and transaction statuses are unchanged; their ordinary-wire composition does not automatically cover the extension.

**Version used for verification: Bend 2.0.39.** These files are Bend code with resolved imports. They contain no ellipses standing in for definitions, unresolved metas, `@unsafe`, or application axioms.

The result is a specification accompanied by an implementation in development. **There is no proof of `Contract(a, k)` for the complete executable.** This distinction is part of the formal content.

## 1. How to read

Start with `LAWS.bend`. It contains the eight propositions `Law1` through `Law8`, their conjunction `Contract`, and the detailed rules each proposition uses. Every rule is defined in that file or a module included in this package.

| File | Contents |
| --- | --- |
| `LAWS.bend` | Eight kernel obligations, detailed rules, and `Contract(a, k)`. |
| `Semantics.bend` | Programs, operations, events, working states, responses, and application of all laws. |
| `Requirements.bend` | Validity, limits, finalization, and the exact type of the client certificate. |
| `Interface.bend` | Required bridge to Bend source, proof derivation, the native artifact, and actual environment facts. |
| `Links.bend` | Correspondence of every real operation with the certified sequence; execution completion. |
| `Data.bend` | Schema, values, users, authentication, and concrete reference operations. |
| `Bytes.bend` | UTF-8, bytes, lengths, and 64-bit words. |
| `Protocol.bend` | Canonical encoding, framing, requests, and responses. |
| `PreparedProtocol.bend` | Additive prepared envelopes, full physical reception, dispatch, and metadata receipt encoding. |
| `PreparedRegistry.bend` | Instance-local entries, exact lookup, fresh insertion, and invalidation. |
| `PreparedLaws.bend` | Prepared admission/readiness, current artifact correspondence, authorized control outcomes, and the additional `ControlLaw` obligation. |
| `Resources.bend` | Framing, logical sizes, incomplete reception, EOF, channels, and actual-failure stages. |
| `Logic.bend` | Logical foundations and proofs: conjunctions, disjunctions, implication, and prefixes. |
| `LEMMAS.bend` | Proved consequences of the contract and semantics. |
| `DataExamples.bend` | Seven closed data-behavior examples. |
| `ProtocolTests.bend` | Seventeen closed protocol and Unicode examples. |
| `VERIFY.bend` | Single entry importing statements, lemmas, and examples. |

`VERIFICATION.json` and `verify.py` are preserved artifacts from the earlier version, now translated into English. Active-contract validation uses `tools/check.py` and the new `tests/proof/` reports.

## 2. Why the eight laws are functions returning `Type`

In Bend, a proposition is a type and a proof is a term of that type. A law parameterized by environment and implementation can be written directly:

```bend
def Law5(-a: I.Environment, -k: String) -> Type:
  @x: I.Scenario -> @t: Nat -> @f: I.Fact ->
    I.Happens(a, k, x, t, f) -> Rule5(f, a, k, x, t)
```

This statement requires **every actual execution fact of that artifact** to satisfy faithful execution. `Rule5` is not an undefined name: the file specifies its cases, including operations, prefixes, completion, forbidden inspections, and out-of-model effects.

`a` is the fixed technical environment. `k` identifies the complete artifact interpreted by it, including dependencies. A standalone name or hash does not establish that bridge.

The implementation proof target is:

```bend
def Contract(-a: I.Environment, -k: String) -> Type:
  L.E<Law1(a, k),
    L.E<Law2(a, k),
      L.E<Law3(a, k),
        L.E<Law4(a, k),
          L.E<Law5(a, k),
            L.E<Law6(a, k), L.E<Law7(a, k), Law8(a, k)>>>>>>>
```

An implementation is to be accompanied by a term of this type for its actual environment and artifact. Defining the type does not supply that term.

Proved lemmas use `law` and a corresponding `def`. For example, this package proves that refusal preserves published state in the model and that a failed operation appends its event to the prior sequence. Lemmas receiving `Contract(a, k)` as a premise prove consequences of that contract; they do not manufacture the premise.

## 3. The eight obligations

### Law 1 — Initialization and configuration

The instance starts only with valid configuration, a valid initial proof, and exactly the certified initial state. Configuration in use remains equal to the scenario's configuration. Rejected initialization cannot also produce a started instance.

Schema, laws, and environment are configuration. Users belong to mutable data.

### Law 2 — Representation and operations

Encoding must match canonical format. Successful decoding must correspond exactly to all bytes; decoding rejection requires that no canonical value match those bytes. Storage abstraction must recover stored state.

Data operations have the effects defined in `Data.bend`. Body reading respects declared length and input limits. Field construction requires a prior length check. `AllocatedField{position, count}` requires an earlier `CheckedLength` with the same position and quantity; it contains no physical-memory quantity.

### Law 3 — Identity

Authentication matches the request credential and registry in initial published state. Starting a program requires that prior authentication. Neither an argument nor a provisional registry change replaces identity.

### Law 4 — Certificate and program

Acceptance requires source and dependencies bound to the pure program, termination, derivation of the correct target, and certification of compliance with every law. Context, arguments, and configuration in that target are the actual ones.

The program starts only after corresponding acceptance. Certificate rejection requires absence of a valid derivation for the admitted program. Logical limits and actual technical failure have their own causes and do not authorize arbitrary rejection of a valid certificate.

### Law 5 — Execution and inspections

Observed states and events must correspond to reference-semantic prefixes. Every actual program operation is tied to its prior state, result, and subsequent event. Two actual operations cannot share one event as justification.

The program starts in valid state, never changes request or identity, never resumes after completion, and never continues after a final path. Inspections and effects outside the model are forbidden. The kernel may perform internal accesses needed for authentication and validation without exposing that data to the program.

### Law 6 — Publication

Publication is unique, valid, and follows complete preparation of the success response. Visible state is initial state before that point and the complete published state afterward.

Non-success completion preserves initial state and cannot contain publication. The next call starts after prior completion and uses the state it left.

### Law 7 — Responses, interruptions, and channel

Response encoding, content, and cause are exact. Fixed errors carry absence. `limit` requires an oversized input message or the logical state/response result of `Requirements.finalize`. `failure` requires an actual impediment with actual origin and severity; it is not a generic rejection of a valid program.

Logical delivery occurs once, complete or interrupted. Interrupted delivery requires actual failure and can have sent only a prefix of the prepared message. It neither turns published success into refusal nor undoes publication. Channel closure follows framing and failure rules.

### Law 8 — Positive operation

Under specified external conditions, valid configurations and initial certificates start the instance; requests receive outcomes; valid certificates are accepted and their programs start. Protocol-required closures must also occur.

`Processable` does not receive the candidate artifact: its interpretation cannot be “the candidate chose to finish.” It represents external operating/resource conditions of the scenario and belongs to the fixed environment of a concrete implementation. Execution depends on available resources, without a physical ceiling, stage deadline, mandatory measurement, or kernel preemption promise. An expensive call can occupy the serial instance for a long time.

## 4. Each request's certificate

`Requirements.Certifies` is universal over valid states containing the same authenticated context. At every execution prefix it requires the complete law list during execution and actual failure. It does not require a hypothetical `limit` termination at every prefix: state and response limits are checked at finalization. The actual `Requirements.finalize` outcome, including `limit` when it occurs, remains subject to the laws. It also requires final-state validity for every technically possible publication.

The semantic number `n` enumerates mathematical prefixes. It is not a public parameter, new quota, or database instruction limit. `ProgramTerminates` remains mandatory without a promised maximum duration. Certification covers the whole abstract semantics and does not use interruption as a premise to authorize a later forbidden inspection.

Administrator laws receive `Stable`, `Executing`, or `Closed`. Every situation receives the same complete law list; conditions belong inside propositions. An empty list gives true conjunction without an extra access policy.

The program receives `Context` and `Value` and produces `Action`. Only the reference interpreter receives `State`. A write returns `UnitValue` to its continuation, even when no row is found to update or remove. It returns neither state, prior contents, nor record existence.

## 5. Concrete representation decisions

Data integers are 64-bit two's complement represented by two `U32`s. This avoids relying on an `I64` type absent from this library version. There is no implicit numeric conversion.

Text must contain valid Unicode scalars. Names, keys, optional columns, credential uniqueness, and ordering follow the earlier contract. Missing rows and absent optional values have distinct constructors.

Encoding uses tags 0–6, big-endian u64 lengths, valid UTF-8, and canonically ordered records. `src/Codec.bend` decodes through the exact inverse encoding relation linked by general proofs in `proof/CodecLaw2.bend`. The parser function was preserved in this revision.

`Semantics.Limits` has exactly three fields:

```bend
type Limits is Data:
  Limits{message: Nat, state: Nat, response: Nat}
```

They are finite canonical-encoding byte counts representable in u64. Equality with the ceiling is allowed. The response ceiling accommodates all six fixed errors. External framing's eight bytes are outside these sizes.

The published-state limit applies to the final proposal. Temporarily larger working state alone does not justify rejection for published-state size. Keeping the same three ceilings preserves the published-state domain: structure, encoding within the state ceiling, and every administrator law.

## 6. Explicit technical boundary

`Interface.Environment` contains relations to instantiate for the chosen backend:

| Relation | Meaning to establish |
| --- | --- |
| `Elaborates` | Source and dependencies represent exactly that pure program without external accesses or native-state captures. |
| `Derives` | Certificate text is a derivation in the fixed logical system for the indicated target. |
| `Happens` | Facts describe complete execution semantics of the actual artifact, not reports the program may omit or invent. |
| `Processable` | Sufficient external conditions exist for the processing required in the scenario. |
| `FailureReal` | The technical impediment actually occurred with the indicated severity. |
| `FailureDeliveryReal` | The channel failed during delivery, justifying interruption. |

Any program inspection escaping the operations must appear as `InspectionNotModeled`; improper external effects must appear as `EffectNotModeled`. Law 5 rejects both. Silencing those facts in external interpretation invalidates the bridge required by the contract.

**The package declares this boundary but does not include its concrete instantiation for compiler, runtime, operating system, and executable.** Textual identity alone does not prove correspondence. This must be filled and justified when constructing the native kernel; it is not a policy chosen by an application administrator.

Logical and technical assumptions remain explicit. Physical timing and resource-consumption channels remain outside the combined confidentiality guarantee. Recoverable failure before publication preserves published state and produces a response when possible. Fatal failure or process termination may produce no response and lose the entire RAM instance. Delivery failure after publication does not undo published success. The kernel may not ignore a known error and continue with incorrect data.

## 7. Verification

```sh
make verify-contract
make verify
```

The first command checks this contract in both official modes. The second checks the general aggregates and causal mutations. Runners do not create a term of `Contract(a,k)` for the complete executable. Development timeouts are not database budgets. Earlier reports and implementations remain in Git history; translated historical copies are in `history/contract-v1/`, while the original Portuguese files remain in Git history.

## 8. Optional prepared-program interface

The user-authorized additive contract of 2026-11-06 covers authenticated
preparation/invalidation controls and prepared execution. The
[extension specification](../tools/service/PREPARED_PROGRAMS.md) describes the
physical `7 || opcode || record` envelope and control metadata receipts.
`PreparedProtocol.Received` requires valid actual reception, canonical inner
bytes and the full prefixed message limit. A raw handle envelope is never
identified with an ordinary request containing the original source.

`PreparedLaws.Ready` binds semantic handle resolution to current authentication,
the exact registered original source/proof, a universal certificate, the fixed
whole-program read certificate when applicable, and artifact validation for
that physical call and time. Unauthorizing scheduler classification may inspect
the registry before authentication. `ControlOutcome` and `ControlLaw` require
exact authorized registry changes, canonical bounded receipts or specifically
justified errors, and an unchanged published state/response pair. Receipt
overflow precedes sealing and registry mutation; invalidation cleanup failure
can return `failure` after removal without restoring the registration. Lost
receipt delivery also does not undo a completed registry change.

[PreparedPrograms.bend](../proof/PreparedPrograms.bend) covers worker resolution
and universal specialization through the actual `Core` publication functions.
[PreparedWire.bend](../proof/PreparedWire.bend),
[PreparedExtension.bend](../proof/PreparedExtension.bend) and
[PreparedControls.bend](../proof/PreparedControls.bend) add general/model proofs
for physical wire relations, registry transitions and authorized control
outcomes. These proofs preserve the ordinary eight-law obligations. They do
not establish `ControlLaw` for every actual host observation or a complete
executable contract. Complete observation coverage, physical ordering, current
artifact/source correspondence, compiler preservation and OS/process/channel
behavior remain explicit integration obligations.

## 9. Language sources

JayDB definitions were written from scratch. Syntax and tool usage were checked against official Bend sources:

- Guide: https://github.com/bendlang/bend/blob/main/guide/GUIDE.md
- Project: https://github.com/bendlang/bend
- Documentation and installation: https://bend-lang.com/

The guide distinguishes propositions, proofs, law files, and the second verifier. JayDB obligations and the interpretation of this package's contract are work of this formalization, not claims taken from Bend documentation.
