# JayDB — specification and laws in Bend

This was a new formalization written from the discussed contract without consulting the earlier JayDB repository. The package contains **eight kernel obligations**, their definitions, reference semantics, and proofs of the included helper lemmas. This archive is an English translation; the original Portuguese files remain in Git history.

**Version used for verification: Bend 2.0.39.** These files are Bend code with resolved imports. They contain no ellipses standing in for definitions, unresolved metas, `@unsafe`, or application axioms.

The result is a specification for an implementation. **This historical package contains neither a JayDB executable nor a proof of `Contract(a, k)` for one.** This distinction is formal content, not merely a caveat about filenames.

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
| `Resources.bend` | Measurements, limits, incomplete reception, EOF, and operator-requested shutdown. |
| `Logic.bend` | Logical foundations and proofs: conjunctions, disjunctions, implication, and prefixes. |
| `LEMMAS.bend` | Proved consequences of the contract and semantics. |
| `DataExamples.bend` | Seven closed data-behavior examples. |
| `ProtocolTests.bend` | Seventeen closed protocol and Unicode examples. |
| `VERIFY.bend` | Single entry importing statements, lemmas, and examples. |

`verify.py` runs checking and records the result, version, and source hashes in `VERIFICATION.json`. Historical outcomes refer to the original sources; translation alone does not rerun those checks.

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

Data operations have the effects defined in `Data.bend`. Body reading respects declared length and input limits. Field allocations require prior length checking and must respect the memory limit.

### Law 3 — Identity

Authentication matches the request credential and registry in initial published state. Starting a program requires that prior authentication. Neither an argument nor a provisional registry change replaces identity.

### Law 4 — Certificate and program

Acceptance requires source and dependencies bound to the pure program, termination, derivation of the correct target, and certification of compliance with every law. Context, arguments, and configuration in that target are the actual ones.

The program starts only after corresponding acceptance. Certificate rejection requires absence of a valid derivation for the admitted program; limits and technical failures are distinct causes.

### Law 5 — Execution and inspections

Observed states and events must correspond to reference-semantic prefixes. Every actual program operation is tied to its prior state, result, and subsequent event. Two actual operations cannot share one event as justification.

The program starts in valid state, never changes request or identity, never resumes after completion, and never continues after a final path. Inspections and effects outside the model are forbidden. The kernel may perform internal accesses needed for authentication and validation without exposing that data to the program.

### Law 6 — Publication

Publication is unique, valid, and follows complete preparation of the success response. Visible state is initial state before that point and the complete published state afterward.

Non-success completion preserves initial state and cannot contain publication. The next call starts after prior completion and uses the state it left.

### Law 7 — Responses, interruptions, and channel

Response encoding, content, and cause are exact. Fixed errors carry absence. A claimed limit must match a limit actually reached. Measurements and failures must be tied to environment facts.

Logical delivery occurs once, complete or interrupted. Interrupted delivery requires actual failure and can have sent only a prefix of the prepared message. It neither turns published success into refusal nor undoes publication. Channel closure follows framing and failure rules.

### Law 8 — Positive operation

Under specified external conditions, valid configurations and initial certificates start the instance; requests receive outcomes; valid certificates are accepted and their programs start. Protocol-required closures must also occur.

`Processable` does not receive the candidate artifact: its interpretation cannot be “the candidate chose to finish.” It represents external operating/resource conditions of the scenario and belongs to the environment to be fixed for a concrete implementation.

## 4. Each request's certificate

`Requirements.Certifies` is universal over valid states containing the same authenticated context. It requires the complete law list at every execution prefix. It also requires final-state validity for every technically possible publication.

The semantic number `n` enumerates mathematical prefixes. It is not a public parameter, new quota, or database instruction limit. Time and memory remain subject to environment measures. Certification covers the complete abstract semantics: a timeout cannot be a premise authorizing a forbidden inspection later in the code.

Administrator laws receive `Stable`, `Executing`, or `Closed`. Every situation receives the same complete law list; conditions belong inside propositions. An empty list gives true conjunction without an extra access policy.

The program receives `Context` and `Value` and produces `Action`. Only the reference interpreter receives `State`. A write returns `UnitValue` to its continuation, even when no row is found to update or remove. It returns neither state, prior contents, nor record existence.

## 5. Concrete representation decisions

Data integers are 64-bit two's complement represented by two `U32`s. This avoids relying on an `I64` type absent from this library version. There is no implicit numeric conversion.

Text must contain valid Unicode scalars. Names, keys, optional columns, credential uniqueness, and ordering follow the earlier contract. Missing rows and absent optional values have distinct constructors.

Encoding uses tags 0–6, big-endian u64 lengths, valid UTF-8, and canonically ordered records. The production parser was not implemented in this historical package: its obligation is the exact inverse encoding relation. The reference encoder and validity definitions are complete.

Sizes and memory are expressed in bytes; physical deadlines are integer nanoseconds. Sizes exceed a limit when greater than its ceiling; a stage deadline expires when reached. External framing's eight bytes are outside body, state, and response size limits.

The published-state limit applies to the final proposal. Temporarily larger working state alone does not justify rejection for published-state size. The physical memory limit remains applicable during processing.

## 6. Explicit technical boundary

`Interface.Environment` contains relations to instantiate for the chosen backend:

| Relation | Meaning to establish |
| --- | --- |
| `Elaborates` | Source and dependencies represent exactly that pure program without external accesses or native-state captures. |
| `Derives` | Certificate text is a derivation in the fixed logical system for the indicated target. |
| `Happens` | Facts describe complete execution semantics of the actual artifact, not reports the program may omit or invent. |
| `Processable` | Sufficient external conditions exist for the processing required in the scenario. |
| `MeasurementReal` | Consumption corresponds to the actual measure defined by the environment. |
| `FailureReal` | The technical impediment actually occurred with the indicated severity. |
| `FailureDeliveryReal` | The channel failed during delivery, justifying interruption. |

Any program inspection escaping the operations must appear as `InspectionNotModeled`; improper external effects must appear as `EffectNotModeled`. Law 5 rejects both. Silencing those facts in external interpretation invalidates the bridge required by the contract.

**The package declares this boundary but does not include its concrete instantiation for compiler, runtime, operating system, and executable.** Textual identity alone does not prove correspondence. This must be filled and justified when constructing the native kernel; it is not a policy chosen by an application administrator.

Logical and technical assumptions remain explicit. Physical timing and resource-consumption channels remain outside the combined confidentiality guarantee.

## 7. What was checked

There are 31 general proved lemmas and 24 closed examples proved by reduction. All modules, including the type of the eight obligations, passed the Bend 2.0.39 primary checker in the historical run.

```text
ALL PROOFS CHECK
Use --verdict for mathematical validity.
```

This result confirms the types of definitions/statements and included proofs. It does not mean the eight laws were proved for a native kernel: this package has no term of `Contract(a, k)`. It also does not replace review that definitions express the project's intent.

The second check, `--verdict`, did not complete in that environment. Preparing the BendTT kernel encountered a Lean 4.34.0 executable failure: SIGSEGV, exit 139, even on a minimal file. This historical package is not presented as validated in that mode.

To repeat primary checking from this folder:

```sh
bend VERIFY.bend --check-only
```

Or to generate a report with hashes as well:

```sh
python3 verify.py --bend bend
```

The delivered `VERIFICATION.json` records the outcome actually obtained on the original sources. Checking must be repeated for another Bend version or for these translated sources.

## 8. Language sources

JayDB definitions were written from scratch. Syntax and tool usage were checked against official Bend sources:

- Guide: https://github.com/bendlang/bend/blob/main/guide/GUIDE.md
- Project: https://github.com/bendlang/bend
- Documentation and installation: https://bend-lang.com/

The guide distinguishes propositions, proofs, law files, and the second verifier. JayDB obligations and the interpretation of this package's contract are work of this formalization, not claims taken from Bend documentation.
