# JayDB executable contract

Start with [`Theorems.bend`](Theorems.bend). Its statements concern the actual
executable gate, interpreter, finalizer, decoder and scoped prepared resolver.
Every public theorem type has an inhabited witness checked by official Bend
2.0.39 and BendTT. The [proof guide](../proof/README.md) maps each theorem to
its witness, non-vacuity evidence and trusted base T1–T3.

Native worker integration of `Gate` is in progress.

| Module | Purpose |
| --- | --- |
| `Theorems.bend` | Init; four Core clauses (admission, safety, completion, progress); ordinary ingress; unified direct/registered selection; finite-run fold; codec/framing statements. |
| `Requirements.bend` | Valid configuration/state, full client certification, prefix/failure/final safety and exact logical finalization. |
| `Semantics.bend` | Closed program/action interface, operations, working states, traces, responses and publication. |
| `Data.bend` | Schema, values, users, current-state authentication and reference operations. |
| `RequestFacts.bend` | Pure request projections, termination, decoding, fixed error payload and operation-transition predicates. |
| `Bytes.bend`, `Protocol.bend` | Unicode/octets, uint64 lengths, canonical value/request/response encoding and public frames. |
| `PreparedProtocol.bend` | Prepared envelope prefixes/dispatch and exact control receipt encoding. |
| `PreparedRegistry.bend` | Scoped entries and lookup used by `src/Resolve.bend`. |
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

The theorem composition covers direct and registered execution. Preparation
and invalidation host controllers, physical IO and atomic root replacement
remain integration obligations. The proof guide numbers the required host
plumbing; compiler/runtime preservation is T2. Durability, OS failures and
checker completeness/adequacy have separate scope.

Run `make verify-contract` for both official modes; `make verify` adds complete
maintained import coverage, public library proofs and causal negatives.
`contract.sha256.json` and `tools/admission/contract.lock.json` pin active Bend
sources. `verify.py --verdict` refreshes `VERIFICATION.json` with checker
results, source hashes and the inhabited witness inventory.
