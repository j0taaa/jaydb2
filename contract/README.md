# JayDB executable contract

Start with [`Theorems.bend`](Theorems.bend). Its statements concern the actual
executable gate, interpreter, finalizer, decoder, scoped prepared resolver and
private error-code denial.
Every public theorem type has an inhabited witness checked by official Bend
2.0.39 and BendTT. The [proof guide](../proof/README.md) maps each theorem to
its witness, non-vacuity evidence and trusted base T1–T3.

The native worker executes the checked `Gate`/interpreter/finalizer path;
compiler/runtime preservation and physical host plumbing remain T2/T3.

| Module | Purpose |
| --- | --- |
| `Theorems.bend` | Executed startup/recovery; abstract Init; four Core clauses (admission, safety, completion, progress); ordinary ingress; unified direct/registered selection; finite transaction and mixed service folds; prepared-control clauses; host-error replies; codec/framing statements. |
| `Requirements.bend` | Valid configuration/state, full client certification, prefix/failure/final safety and exact logical finalization. |
| `Semantics.bend` | Closed program/action interface, operations, working states, traces, responses and publication. |
| `Data.bend` | Schema, values, users, current-state authentication and reference operations. |
| `RequestFacts.bend` | Pure request projections, termination, decoding, fixed error payload and operation-transition predicates. |
| `Bytes.bend`, `Protocol.bend` | Unicode/octets, uint64 lengths, canonical value/request/response encoding and public frames. |
| `PreparedProtocol.bend` | Prepared envelope prefixes/dispatch and exact control receipt encoding. |
| `PreparedRegistry.bend` | Scoped entries and lookup used by `src/Resolve.bend`. |
| `HostErrors.bend` | Total exact error-code classification: the 17 admission refusals are `certificate`, every other string is `failure`. Executed by the native controller. |
| `PreparedHandles.bend` | Canonical 64-character lowercase hexadecimal handle shape used by allocator proofs. |
| `Resources.bend` | Pure reception, logical message bounds and channel disposition rules. |
| `ReadOnlyContract.bend` | Whole-program read predicate retained for public query libraries and applications. |
| `Logic.bend` | Logical foundations and constructive helpers. |
| `DataExamples.bend`, `ProtocolTests.bend` | Closed examples for data behavior and canonical encoding. |
| `VERIFY.bend` | Definitions, examples and executable theorem witnesses. |

Core assumes valid configuration and initial state plus `OracleSoundness` for
the exact selected tuple. Its clauses prove actual authenticated start, safety
at every prefix, exact finalization/publication/response bytes and accepted
execution progress. `FoldTheorem` derives reached-state validity from an
Init-accepted seed and computed finite-run steps. Registered selection uses
fresh authentication; cached universal admission specialized at lookup falls
under T1's exact source/program/artifact binding.

The theorem composition covers direct and registered execution and checked
prepare/invalidate transitions. `StartupTheorem` concerns the executed
`ConfigurationCheck.initialize`/`recover`; T1 admits the exact closed seed-validity
declaration before initialization runs. `InitTheorem` remains the abstract
seed-admission helper for `FoldTheorem`. `ServiceFoldTheorem` covers mixed
transactions/controls from an empty registry, including exact registry history,
live-source certification, scoped removal and allocation history.
`ServiceNoRevivalTheorem` keeps an allocated absent handle absent throughout
any later mixed run. `ControlTheorem` needs no
admission-soundness premise for its structural checks; the mixed fold needs
that premise to derive universal certification of registered sources.
`HostErrorReplyTheorem` covers private error-code replies executed by
`ControlBridge.run` (via `HostErrors.native_error_branch`): exact classification,
bounded canonical denial bytes and
unchanged root/last-response/registry. `HostErrors` witnesses check every named
certificate row and the default, including prepared map/integrity failures.
`HostErrorReply` states that emitted bytes equal
`Messages.error(HostErrors.status(code))` for every root/last/registry, permitting
checked replies to be memoized by exact code. Startup prefills `HANDLE` and
`PREPARED_INTEGRITY` separately for offline prepared denials. The host still
detects failures, forwards the actual code/current snapshot (or the exact
memoized reply for that code), and prevents execution after an integrity failure. Failure of the denial
executable/transport retains a fixed host technical fallback, diagnosed on stderr
and never memoized. The 17-code table specifies the contract; it is not proved
equal to the Node tools' proof-rejection codes. `ORACLE_PROOF`, `ADT` and
`INSTANCE_MATCH`, for example, map to `failure`.
Artifact IO, admission-token delivery, physical IO and atomic root replacement
remain host obligations. The proof guide numbers the required host
plumbing; compiler/runtime preservation is T2. Durability, OS failures and
checker completeness/adequacy have separate scope.

Run `make verify-contract` for both official modes; `make verify` adds complete
maintained import coverage, public library proofs and causal negatives.
`contract.sha256.json` and `tools/admission/contract.lock.json` pin active Bend
sources. `verify.py --verdict` refreshes `VERIFICATION.json` with checker
results, source hashes and the inhabited witness inventory.
