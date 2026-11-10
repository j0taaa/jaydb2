# Replacement contract: partial implementation

Implemented statements live in `contract/Theorems.bend` (the name avoids the
flat staging collision with `src/Core.bend`). `Init.init_theorem` inhabits
`InitTheorem`. `Gate` proves authentication before admission, exact Reject and
ToolFailure results, and exact accepted starts. `WireTheorems` inhabits
`CodecRoundtrip`, `CodecCanonical` and `FramingRoundtrip` using existing proofs.

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

## Blocker and open work

`CoreTheorem`, `IngressTheorem` and `UnifiedCoreTheorem` remain statement types,
without inhabitants. M2/M3, composed M4, pure M7, old-model deletion and final
trust-base/specification rewriting remain unfinished. English Law 8 already
states tool adequacy as an assumption, independently of the missing Core proof. The old model and its
roots are retained until the replacement composition can be checked.

The attempted Core construction reused a `Type` certificate/Accepted proof for
its retained Accepted field, all-prefix safety, Finals and Progress. Official
Bend rejects copying that affine value. Closed template declarations can reopen
proofs, but they cannot accept the universally quantified local configuration,
program and soundness arguments required by CoreTheorem. An erased Evidence
wrapper experiment also failed: matching inside the ghost constructor is not a
permitted match position; matching an erased argument in a normal helper is
rejected as a live scrutinee, including an attempted `Kind(&0)` wrapper. No weaker Core statement, new premise or axiom was
substituted. Failed source attempts and diagnostics are under the gitignored
`.build/implementation-blocked/` directory for review, outside verify roots.

This records an implementation blocker, not a proof that CoreTheorem is
uninhabitable or a semantic counterexample. In particular, no counterexample to
NoFailure was established. The next phase needs a quantity-correct universal
proof composition before replacing the old model or claiming the eight laws
for the new executable boundary.
