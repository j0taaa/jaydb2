# Replacement contract: implementation status

Implemented statements live in `contract/Theorems.bend` (the name avoids the
flat staging collision with `src/Core.bend`). `Init.init_theorem` inhabits
`InitTheorem`. `Gate` proves authentication before admission, exact Reject and
ToolFailure results, and exact accepted starts. `WireTheorems` inhabits
`CodecRoundtrip`, `CodecCanonical` and `FramingRoundtrip` using existing proofs.
`CoreClauses.core_theorem` inhabits `CoreTheorem`, `Ingress.ingress_theorem` and
`Ingress.unified_core_theorem` inhabit `IngressTheorem` and `UnifiedCoreTheorem`,
and `Iteration.fold_theorem` inhabits `FoldTheorem`, all in both official modes.

`src/Gate.bend` and `src/Resolve.bend` are the normative executable prototypes
moved to tracked source. Registered requests authenticate against current state,
require empty raw proof, perform scoped lookup, and retain unknown-handle
`failure`. A cached universal admission oracle is an instance of trusted T1: the scoped
registry binds the exact loaded program/artifact to immutable configuration,
source/dependency bytes, `@ctx -> @args -> R.Certifies(...)`, and universal
termination. Lookup specializes those proofs at current context/arguments.
T1 also binds the checked elaborated program to the very Book compiled for
execution; source labels, handles and hashes alone establish none of these
facts. There is no separate cache-refinement requirement or re-admission claim
here.

`RequestFacts` extracts the existing pure request, termination, decoding,
payload and operation-transition predicates. Existing pure-only imports are
retargeted; Interface temporarily forwards its shared helpers to the canonical
module while its old model remains. Native entry behavior is unchanged.

`tests/proof/Positive.bend` retains the real tasks policy/client proof, exact
logical oracle premise, authentication and changed-root success. Its checked
fixture is tracked without a generation step. Refutations and clause negatives
are permanent; parser or missing-name errors do not count as negative evidence.

## Statement adjustment

The design's `SeedAccept{-valid: R.Valid(c, seed)}` became
`SeedAccept{valid: R.Valid(c, seed)}`. `Init` returns this validity proof in an
ordinary `Logic.E` field, so the official quantity checker requires it to be
retained. The acceptance condition is stronger operationally; no logical
validity obligation is removed. Init's full original conclusion is proved.
`InitAt` only factors its computed configuration Boolean. The unused
`CertifiedVerdict` alternative is omitted, as authorized.

## Core split and the affine-reuse resolution

`CoreTheorem` is `@k: Clause -> CoreClauseTheorem(k)` over four clauses
(`Admitted`, `Safe`, `Completed`, `Progressing`) with identical universal
premises: exactly the conjunction of four separately proved theorems. Each
clause consumes its own copy of the oracle-soundness and validity premises, so
the single affine certificate is never reused. The redundant `Accepted` field
is dropped; it follows from `Admission` and `OracleSoundness`. Ingress,
UnifiedCore and the fold are indexed the same way; the fold additionally has a
`Reached` aspect (validity of the root before step j) and quantifies over every
step index j. The configuration is opened once per proof; its law list is used
live only by the oracle call. One pass over the actual program yields both
reference fidelity and absence of generic failure, consuming the program once.

## Open work

Old-model deletion and final trust-base/specification rewriting remain. The
old model and its roots are retained until then. Native Gate integration and
the prepare/invalidate controller are later phases.
