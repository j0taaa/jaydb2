# Project review and verification status

Review started from merged `main` revision `1598ed4`. The earlier integration
and accessory records remain historical evidence; this review did not rewrite
their results. The eight ordinary transaction laws and historical snapshot remain
unchanged. After the initial review, the user authorized the additive prepared
protocol contract described below on 2026-11-06.
The reviewed repairs and new proofs are recorded in commit `0552c76`.

## Validated repairs

| Finding | Repair and causal evidence |
| --- | --- |
| TypeScript calls could remain pending after silent request-pipe closure or attachment after response EOF | Observe terminal request-pipe events and already closed streams. Bounded before/after probes reproduce the hangs and their repair. |
| The demo watchdog began after a blocking request write | Nonblocking partial writes now share the existing adapter request/response deadline. A real nonreading subprocess and 4 KiB pipe reproduce the defect; a live-reader control receives exact bytes. This changes the demo adapter, not database deadlines. |
| Repeated workload arguments could overwrite paired benchmark records | Reject duplicate iteration counts before creating outputs or starting measurement. The regression requires this diagnostic specifically. Old measurements are unchanged. |
| Default library verification omitted receipt helpers and law templates | Import both `Receipts` and `ReceiptLaws` directly in `library/VERIFY.bend`. |
| Future core/library modules could miss the checked roots unnoticed | `make verify` now checks the transitive local import graph and rejects orphaned `src`, `proof` or `library` modules. Controls cover transitive inclusion, three orphan areas, missing imports, unsupported syntax and outside-root paths. |
| Key roundtrip theorem covered internal chosen fuel but not the public decoder | Constructively derive sufficient fuel from the actual encoded string length, then prove `decode(encode(parts)) == Some(parts)` for every finite list. An always-None decoder fails at its intended proof obligation in both official modes. |
| Structural comparison and signed-order properties lacked general helper theorems | Optional `ComparisonProofs` proves structural equality soundness/completeness and actual signed-comparison strict total order. Constant-true equality and constant-false order controls fail at the intended obligations. Runtime helper code/imports remain unchanged. |
| Prepared-wire mismatch was documented without a direct checked exclusion theorem | `PreparedPrograms` now proves tag-7 exclusion from ordinary request encodings, `RequestReceived`, and ordinary authentication justification for the same raw scenario. A forged encoding control fails in both modes. |

The initial review import inventory reached all **16 source, 132 proof and 22
library modules**, 209 transitive modules in total. The authorized extension adds
three contract and three proof modules; its updated inventory is recorded in
the validation summary. It detects omitted checking; it does not
establish an unstated functional theorem about every imported function.
Application/generated roots, deliberately rejected fixtures, native effects and
historical experiment variants have their separately documented scopes.

Independent passes covered host framing/process ownership, persistence,
scheduling, prepared admission, native effects, source freezing, library
algorithms/application certificates, TypeScript and Python framing, the web
adapter, and benchmark provenance. No additional demonstrated defect in the
ordinary-core proof construction was found. Existing algorithms and archived evidence were retained where
removing or replacing them had no validated benefit.

## Completed checks and current gate

- Baseline `make verify-integration`: both official modes and all eight
  aggregate negative controls passed.
- Final amended library aggregate and public key theorem: both modes passed.
- Library false arithmetic, hidden-write, public-decoder and comparison
  controls: ten intended rejections across both modes passed.
- Smoke: exit zero, including all 43 Rust tests, formatting, strict Clippy,
  TypeScript/package/accessory/starter checks and benchmark oracles.
- Real demo: seven tests passed. Native TypeScript integration: eleven checked
  ordinary/prepared responses passed.
- Article numbers: reconstruct all displayed throughput, burst median, pooled
  nearest-rank p95 and maximum sampled RSS values from the retained raw bursts.
  Verify unique burst identities, eight responses per burst, elapsed-time
  throughput and paired ratios before compiling the documents.
- `bash tools/ci/check.sh full`: **exit zero**, about 47 minutes. Its 436
  recorded source/test/configuration inputs remained unchanged throughout.
  This included the complete native/application/recovery/demo gate.
- Subsequent additions are proof modules, verification fixtures and the
  both-mode negative runner. Promoted `PreparedPrograms` and amended library
  aggregates passed both official modes; final `make verify-integration`
  passed against their combined roots, including all nine core negative
  controls in both modes. The earlier full native result is
  not relabeled as having run after these proof-only additions.

The user-authorized prepared extension subsequently passed every combined
contract/root/test/library aggregate in both modes, all **14 core negative
controls per mode**, and the idempotency root. The 21 admission/verifier tests
and both real prepared service suites passed on **463 unchanged recorded
inputs**. Updated coverage reaches **215 modules**, including 135 proof modules.
These are follow-up results, not a relabeling of the earlier full-release run.

Current raw logs and manifests stay ignored under `.build/review/`, including
`full.log`, `full-inputs.json`, `full-result.json`, `promoted-proofs.log` and
`final-proofs.log`. No
compiled binaries, repeated historical outputs or page-render caches are added
to Git. See [verification.md](verification.md) for reproduction commands.
The small [validation summary](review-validation.json) retains the successful
exit statuses, evidence digests and exact scope of the proof-only follow-up.

## Reassessment after the quality review

The presentation was incorrectly delivered in English. The defense is now
Portuguese, including its speaker notes; the article remains English. The
article now states research questions, a reproducible method, the concrete
ownership/index case and the actual boundaries of each experiment.

The earlier prepared extension must be read as component specifications and
proofs. `ControlLaw` is a target without a complete service inhabitant.
`PreparedControls` constructs selected outcomes from supplied admission facts;
it does not establish temporal order, delivery, closure, progress or complete
native-event coverage. `Ready` plus a Core execution equation is not a native
refinement proof. The ordinary eight-law theorem has not become a theorem for
the whole prepared service. Naming and helper comments were tightened to avoid
implying admission was proved from a freshness/size check alone.

Demonstrated integration defects were repaired:

- The demo could reap its exited process-group leader during a liveness check,
  leaving compiler/native descendants and a stderr-drain thread alive after
  reset. Exit checks now preserve the waitable leader until cleanup signals
  its owned group, then reap it. Real-process controls cover exited, active and
  stalled leaders, repeated close and a reused unrelated group number.
  Constructor cleanup also releases the group, descriptors, listener and
  temporary directory if either observer thread cannot start.
- `PreparedLaws` imported an implementation path that production public
  flattening could not resolve. The unchanged whole-program read predicate now
  lives in `contract/ReadOnlyContract.bend`; compatible implementation wrappers
  retain the prior targets. Both specification and wrapper are pinned, and
  positive staging plus transitive-tampering controls exercise the real boundary.

A real valid history proof also exposed a verifier-pipeline disagreement.
After primary acceptance, a rejection of the translated Book was labeled as a
false source certificate. Admission now fails closed as technical infrastructure
failure and retains the kernel diagnostic. The causal before/after test checks
that exact classification at the real kernel boundary; it never bypasses a
verifier or admits the disputed Book.

The registry lifecycle proof now instantiates the generic entry invariant with
actual existential mode-certificate evidence. Induction over insertion and
invalidation can recover the exact registered certificate at lookup, beginning
with the empty registry. It remains an abstract history result: authentication,
current artifact integrity, temporal ordering and correspondence with the actual
host still require their separate proofs.

The external point-operation table uses the original raw comparison, the
published audited result and its linked provenance audit. The original global
inventory-guard failure remains visible. Numerical reconstruction checks exact
outputs, sample identities and per-fixture medians; it does not turn unequal
policy/deployment configurations into an equivalent-engine comparison.

This correction passed `make verify-integration` in both official modes,
including 15 intended core rejections per mode; 23 admission/verifier tests;
four real prepared/concurrency tests; seven demo lifecycle/transport tests; and
six quantitative-evidence controls. The article and defense build successfully,
and all 12 article pages and 18 slides were visually inspected. These follow-up
checks do not replace the historical full-release run or close the proof
obligations below. Exact evidence and artifact digests are recorded in
`review-validation.json`.

## What remains unproved

The checked `ContractService.contract_of_service` target is exactly the unchanged
eight-law `LAWS.Contract` for the **ordinary serial service model**, conditional
on the explicit source/tool/communication premises. The
[integration contract](../proof/SERVICE_CONTRACT.md) identifies those premises.
It is not an unconditional proof of the complete executable.

Prepared raw/control frames, read-batch scheduling and persistence have narrower
pure results and explicit operational bridges. Their Rust/Node/C implementation,
official translations, IO, filesystem and hardware assumptions remain trusted.
Full concrete refinement of these boundaries remains a substantial proof task;
neither module reachability nor passing fault tests discharges it.

There is also a structural protocol boundary, not just an unfinished proof:
prepared bodies begin with tag `7`, outside the canonical value tags `0..6`.
The host strips that prefix before authentication (`server/main.rs`,
`SerialService.propose`). The unchanged `Interface.RequestReceived` instead
requires an ordinary request's canonical encoding to equal the actual received
body. For example, an authentication response to an invalid credential in such
a prepared body cannot satisfy `Interface.ResponseJustified(Authentication)`
for that raw ordinary scenario. Successful `prepared`/`invalidated` control
statuses are also outside the original `Semantics.Status` type.

Consequently, silently normalizing raw bytes is not a proof of the original
whole-wire contract. On 2026-11-06 the user authorized careful law changes when
necessary to retain the prepared features. The chosen extension preserves all
eight ordinary transaction laws and adds three explicit contract modules:

- `PreparedProtocol`: exact `7 || opcode || canonical record` bodies, valid
  physical reception, full prefixed lengths, canonical control receipts.
- `PreparedRegistry`: immutable instance-scoped entries, authenticated lookup,
  fresh insertion, invalidation, and general preservation/recovery of arbitrary
  registered-entry invariants.
- `PreparedLaws`: fresh current authentication, genuine universal/read
  derivations, per-call/time artifact integrity, original source identity, exact
  authorized control effects, response bounds, and unchanged published pairs.

`PreparedWire`, `PreparedExtension`, and `PreparedControls` construct the new
wire/control obligations and connect readiness to the actual resolver and Core
conclusion proof. They do not assume final-state validity or publication
permission. The original encoding-exclusion theorems remain valid and checked.
Five additional negative fixtures cover unauthenticated resolution, invalidated
handle reuse, oversized receipt mutation, source substitution, and false
physical length. Each must fail for its intended proof obligation in both modes.

The control contract distinguishes unknown handles from mathematical proof
rejection and actual technical failure. Receipt overflow happens before sealing
or registry mutation. Invalidation may remove a handle before directory cleanup
fails, while preserving database state. Unauthorizing scheduling classification
may consult the registry before authentication; semantic resolution still
requires current authentication. Current artifact validation is indexed by the
same physical call and time, rather than trusting a reusable cached Boolean.

The design choice is resolved; formal compatibility of the complete extended
service and a complete executable proof are still open.
The new `ControlLaw` states an obligation over all actual control observations.
Its full host instantiation, physical event order, delivery/closure refinement,
and compiler/OS/hardware bridge have not been mechanized. Pure transition
proofs and tests do not discharge those obligations. No result is relabeled as
an unconditional whole-project contract theorem.

Ordinary transparent caching remains a possible alternative, but would change
ahead-of-time admission, invalidation, cross-client handles, and message-size
behavior. The additive extension avoids imposing those compatibility changes.

The optional arithmetic library now proves checked addition, subtraction,
multiplication and division against independent mathematical integers represented
as differences of unbounded naturals. Each public theorem covers arbitrary actual
operands: successful results have the exact mathematical meaning, and rejection
excludes every representable result. Division also proves the ordinary equation,
strict absolute remainder bound, truncation toward zero and dividend-sign
remainder, including zero divisors and INT64_MIN/-1. Its actual 64-step algorithm
is connected to those properties without output or loop-invariant premises.
The small `divide_count` extraction preserves the previous algorithm; checked
branch equations and the exact 64-step delegation accompany the proof.
General list proofs also establish sum, count, integer mean and count/total
summary, including complete rejection conditions. Sum retains the documented
right-fold overflow behavior: representability is required for each right-hand
suffix, rather than only for the final unbounded sum. Average additionally
requires nonempty input and representable length; its positive count cannot
cause division overflow.
Further general proofs now cover independent signed order and extrema,
exact filtering/pagination, tied-class sort stability, unique complete ordered
groups, full occurrence-based inner/left joins, and exact key/value/record
acceptance and lookup domains. Total read/query/selection proofs now cover every input, including exact
histories and first failure; canonical responses are derived from structured
source state. General filter-map order/projection follows from local contextual
visitor contracts, discharged for a real one-cell visitor. Total action/mutation proofs now cover ordered writes, evolving working state,
conditional insert/replace/CAS, checked counters and finalized Core rollback.
Original schema/address/value conditions are explicit, and arbitrary callbacks
are not falsely treated as read-only. Summary storage and total index execution
are now proved, including complete independent source-scan origins, payloads,
ranks, multiplicity and order. Complete index state-maintenance invariants,
receipt helpers and broader business functional specifications remain open. These algorithm contracts are distinct from the transaction
authorization/publication laws. No result here is labeled "100% proved for the
entire project."

The latest combined maintained gate passed both official modes and all 307
intended core rejections per mode on unchanged recorded inputs. Its import
inventory reaches 381 modules, including 151 library modules; this inventory
still measures checked reachability, not whole-project correctness.

A real read-batch progress defect was also repaired. A later worker spawn
failure previously discarded replies from the already started prefix. The
executor now emits that prefix until an actual join/delivery obstruction,
joins every started worker and retains the first error. A causal harness runs
the exact original and repaired executor with the earlier worker returning
before the injected spawn error. All 52 Rust tests, strict Clippy, formatting,
debug/release builds and six real concurrency/scheduling/timing tests pass.
Preserving this prefix does not establish complete per-call Law 8 under every
shared failure; that broader obligation remains open.

Preparation also rejected valid clients when a comment or string contained
the concrete certificate-target text: a whole-file substring count found the
text inside `Bindings.code()` as well as the declaration. Staging now matches
the exact generated declaration span. Four prepare/read × comment/literal
regressions preserve the actual client/proof bytes and admit the staged
manifests with both real tools. The complete 28 admission/staging/verifier tests
and six real ordinary/prepared service tests passed on 88 unchanged recorded
inputs. The preserved old stage fails at `TARGET`; those same source programs
independently pass both official admission tools. This native follow-up does
not relabel the preceding proof-only gate. The existing exact runtime binding
still applies to persistent stores; no migration or binding relaxation is added.

## Proof obligations by scope

| Scope | Checked witness or evidence | Remaining obligation |
| --- | --- | --- |
| Complete extended service | No complete unified contract composition or witness is present | Compose ordinary/prepared execution and controls, all physical events, ordering, delivery, closure and progress; preserve ordinary guarantees. |
| Ordinary serial eight-law model | `ContractService.contract_of_service`, with its five explicit premise families | Concrete complete execution/source/IO correspondence; the theorem is not unconditional native correctness. |
| Prepared logical execution | `PreparedPrograms`, `PreparedExtension`, actual resolver and Core conclusion | Connect every actual prepared call and program event to that model. |
| Physical prepared controls | `PreparedProtocol.Received`, `PreparedControls` constructors | A complete `ControlLaw` inhabitant, temporal order, delivery, closure and progress composition. |
| Registered certificates | `PreparedRegistryHistory` induction and lookup recovery | Correspondence of its admitted abstract history with every actual registry mutation; current integrity remains per-call. |
| Certified concurrent reads | `ReadBatches`, fixed whole-program predicate and wrapper equality | Concrete scheduler, snapshot, barriers and FIFO refinement. |
| Persistent state | Pure validity/origin results and fault tests | Complete crash/filesystem/OS trace refinement and compiler/runtime assumptions. |
| Optional algorithms | Independent-integer scalar arithmetic/order/extrema; arbitrary-list sum/count/mean/summary; exact sequence/group/join occurrences and key/value/record domains | Stateful helper/application functional specifications; native compiler correspondence. |

The open rows are required work. They are not discharged by compiling imports,
counting laws, adding tests, or naming a new contract type.

## GPU decision and TCC

Optional GPU execution is plausible for large explicitly parallel pure work.
The existing `experiment-gpu` heavy trial measured 715.124 ms CPU versus
215.706 ms CUDA, while its small control measured 5.756 versus 174.945 ms.
Those are historical branch results, two complete samples per case, with eight
CPU workers, one GPU-worker cap and a 512 MiB corpus on an RTX 3080 Ti. They do
not establish general database acceleration or a mainline integration.

Retaining CPU-only mainline avoids importing the old branch's missing
combinations: current read batches require GPU exclusivity; artifact sealing,
persistence identity, timing and failure behavior need combined validation.
Compiler/CUDA semantic preservation would still remain an explicit assumption.
The laws were not changed to accommodate GPU behavior.

The English [TCC and editable slides](../paper/README.md) identify Gabriel Jota
Lizardo and PUC Minas, document the actual proof boundary, and derive quantitative
results from existing raw evidence. Their article and Portuguese eighteen-slide
PDFs are generated under `.build/tcc/output/`; only the small editable source
set is tracked. Rendered pages and an independent factual review were checked.
The specific course template, advisor and defense metadata remain for local
confirmation before submission.
