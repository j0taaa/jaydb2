# Old-model removal report

Starting commit: `00bbfce5d19b374ab82d7340643900bfde06b939` on `restructure`.

## Removed paths

The import audit recorded original importers for every removed path, retargeted
shared helpers, and checked all retained maintained local edges. The local audit
artifacts are `.build/cleanup-imports.json` and `.build/cleanup-deletions.json`.
Historical immutable measurement inventories under `paper/evidence/` retain
their original paths and hashes. Their provenance is documented in `paper/README.md`.

### Old contract surface

- `contract/Interface.bend`
- `contract/LAWS.bend`
- `contract/LEMMAS.bend`
- `contract/Links.bend`
- `contract/PreparedLaws.bend`

### Service and host model proofs

- `proof/ChannelService.bend`
- `proof/ClosuresService.bend`
- `proof/ConclusionService.bend`
- `proof/ContractService.bend`
- `proof/ExecutionService.bend`
- `proof/FieldsService.bend`
- `proof/HistoryService.bend`
- `proof/HostHistory.bend`
- `proof/HostInvalidation.bend`
- `proof/HostTransitions.bend`
- `proof/InputRefusals.bend`
- `proof/InputService.bend`
- `proof/Law1Service.bend`
- `proof/Law2Service.bend`
- `proof/Law34Service.bend`
- `proof/Law5Service.bend`
- `proof/Law6Service.bend`
- `proof/Law7Service.bend`
- `proof/Law8Service.bend`
- `proof/LinkageService.bend`
- `proof/ModelService.bend`
- `proof/PhasesService.bend`
- `proof/PreparedAuthority.bend`
- `proof/PreparedControlDispatch.bend`
- `proof/PreparedControlTrace.bend`
- `proof/PreparedControls.bend`
- `proof/PreparedDispatch.bend`
- `proof/PreparedExtension.bend`
- `proof/PreparedInvalidationDispatch.bend`
- `proof/PreparedProgress.bend`
- `proof/PreparedRegistryHistory.bend`
- `proof/PreparedRejects.bend`
- `proof/PreparedServiceHistory.bend`
- `proof/PrimitivesService.bend`
- `proof/ProtocolService.bend`
- `proof/PublicationService.bend`
- `proof/RefinementService.bend`
- `proof/Resources.bend`
- `proof/RoutesService.bend`
- `proof/ScenariosService.bend`
- `proof/SchedulingRefinement.bend`
- `proof/SourceService.bend`
- `proof/VisibilityService.bend`
- `proof/service/specification/ServiceLaws.bend`

### Read-batch proofs

- `proof/ReadBatchCollection.bend`
- `proof/ReadBatchExecution.bend`
- `proof/ReadBatchSelection.bend`
- `proof/ReadBatches.bend`

### Superseded proof documents

- `proof/IMPLEMENTATION_STATUS.md`
- `proof/SERVICE_CONTRACT.md`

### Old-model proof tests and negative controls

- `tests/proof/InputLimit.bend`
- `tests/proof/InputRefusals.bend`
- `tests/proof/ReceptionLimits.bend`
- `tests/proof/rejected/HostHistoryOmittedTransition.bend`
- `tests/proof/rejected/PreparedDeliveryRollback.bend`
- `tests/proof/rejected/PreparedInvalidationProofBypass.bend`
- `tests/proof/rejected/PreparedInvalidationReuse.bend`
- `tests/proof/rejected/PreparedMutationBeforeReceipt.bend`
- `tests/proof/rejected/PreparedReceiptLimit.bend`
- `tests/proof/rejected/PreparedRevokedAuthority.bend`
- `tests/proof/rejected/PreparedSealBeforeLimit.bend`
- `tests/proof/rejected/PreparedUnauthenticatedRegistration.bend`
- `tests/proof/rejected/PreparedUnauthenticatedResolution.bend`
- `tests/proof/rejected/PreparedUncertifiedHistory.bend`
- `tests/proof/rejected/SchedulingBarrierSkip.bend`
- `tests/proof/rejected/SchedulingConcurrentArrivalLost.bend`
- `tests/proof/rejected/SchedulingEmitAfterJoinFailure.bend`
- `tests/proof/rejected/SchedulingLoseStartedPrefixAfterSpawnFailure.bend`
- `tests/proof/rejected/SchedulingReaderLimitExceeded.bend`
- `tests/proof/rejected/SchedulingSkipJoinsAfterDeliveryError.bend`

### Read-batch host fixtures and unused admission lock

- `tests/service/fixtures/Read.bend`
- `tests/service/fixtures/ReadProof.bend`
- `tools/admission/read-only.lock.json`

## Retained helpers and ReadOnly decision

`RequestFacts` already contained the shared request, termination, decoding and
operation-transition predicates. `Machine` and generated bindings now use it.
The pure serial induction formerly in `HistoryService` moved byte-for-byte to
`History.bend` for the retained optional persistence lemmas. Handle-format
predicates moved unchanged from `PreparedLaws` into `PreparedHandles` for the
concrete allocator proofs.

`PreparedRegistry` retains its entry layout, source/proof projections and scoped
`lookup`, used by `Resolve`. Unused mutation/resolution/property machinery was
removed. `PreparedProtocol` retains host wire encoding/dispatch/receipts, with
obsolete prepare-read opcode 3 removed; `PreparedWire.opcode_three_rejected`
proves rejection matching the current host. `Resources` retains actual pure
reception/bounds/disposition definitions used by wire proofs and controls;
old failure-stage and delivery types were removed.

Kept `src/ReadOnly.bend`, `contract/ReadOnlyContract.bend` and
`library/ReadProgram.bend`: the tasks query application, indexed application and
public query-library modules/proofs still import them. Deleted
`tools/admission/read-only.lock.json`: no retained admission or host code reads
that separate lock. The retained contract predicate remains pinned by the active
contract manifests. Read-batch proofs and host fixtures were removed.

## Merge-sensitive JavaScript lines

These are every changed line in the three specified files; no generated worker
logic, native source, `src/Execution.bend`, `compile.mjs` or server file was edited.

```diff
diff --git a/tools/admission/index.mjs b/tools/admission/index.mjs
index a89c289..34774de 100644
--- a/tools/admission/index.mjs
+++ b/tools/admission/index.mjs
@@ -80 +80 @@ function assertBindings(B, book, plan, mustBeOpen) {
-    [bind + ':terminates']: app(canonical.contractPrefix + 'Interface:ProgramTerminates', inst + ':config', client + ':program'),
+    [bind + ':terminates']: app(canonical.contractPrefix + 'RequestFacts:ProgramTerminates', inst + ':config', client + ':program'),
diff --git a/tools/admission/preflight.mjs b/tools/admission/preflight.mjs
index 0e3efcf..611abca 100644
--- a/tools/admission/preflight.mjs
+++ b/tools/admission/preflight.mjs
@@ -97 +97 @@ export function preflight({ submissionDir, entry, dependencies, openTargets, can
-    for (const file of kernelOnly ? [] : ['Requirements.bend', 'Interface.bend']) {
+    for (const file of kernelOnly ? [] : ['Requirements.bend', 'RequestFacts.bend']) {
diff --git a/tools/service/stage.mjs b/tools/service/stage.mjs
index b4eac78..7437aa2 100644
--- a/tools/service/stage.mjs
+++ b/tools/service/stage.mjs
@@ -276 +276 @@ function stage(environment, directory, purpose, metadata) {
-  const entries = executing ? ['Main.bend', 'Interface.bend'] : ['Main.bend'];
+  const entries = executing ? ['Main.bend', 'RequestFacts.bend'] : ['Main.bend'];
@@ -309 +309 @@ function stage(environment, directory, purpose, metadata) {
-      : 'import Base\nimport ./Bindings.bend as Bindings\nimport ./ClientProof.bend as ClientProof\nimport ./Interface.bend as I\n';
+      : 'import Base\nimport ./Bindings.bend as Bindings\nimport ./ClientProof.bend as ClientProof\nimport ./RequestFacts.bend as I\n';
```

## Verification and build updates

`make test`, `test-native` and `test-integration` now depend on `build`.
Other targets that launch the normal release binary already depended on build;
fault-injection targets build their own selected binary explicitly.
All verification roots dropped deleted modules. Import coverage now includes
`contract/` as well as `src/`, `proof/` and `library/`, with an orphan-module
negative control for each directory. The existing `.build/rehash.py` mechanism
regenerated both manifests after replacing their source inventories.

`proof/README.md` supersedes `IMPLEMENTATION_STATUS.md` and gives the inhabited
theorem map, non-vacuity and numbered T1–T3 boundary. Specification, repository,
admission/service/application docs, demo references and manuscript/slides were
updated to the retained executable theorems. Native Gate integration remains
a one-line status statement marked in progress.

## Validation

Commands run with the shared heavy-work lock and unlimited stack:

```sh
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make verify-contract'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make verify'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; python3 -B contract/verify.py --verdict'
bash -c 'ulimit -s unlimited; make smoke'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make test'
```

`make smoke` takes the same heavy lock internally in `tools/ci/check.sh`, so
its caller does not take a second lock. All four requested targets passed:

| Target | Result and key evidence |
| --- | --- |
| `make verify-contract` | PASS: separate `OK --check-only` and `OK --verdict` for `contract/VERIFY.bend`. |
| `make verify` | PASS: complete maintained coverage; all three roots pass both modes; tasks source/proof bindings and coverage controls pass; 356 fixtures / 712 intended rejections. |
| `make smoke` | PASS: TypeScript/client/SQL/accessory checks, 7 tasks and 3 starter tests; Rust 39 passed / 0 failed; formatting and Clippy pass. |
| `make test` | PASS: first line `cargo build --locked --release`; admission/verifier 29 passed / 0 failed; native 10 tests OK; Rust 39 passed / 0 failed; integration 16 tests in 351.295s, OK. |
| `contract/verify.py --verdict` | PASS: both modes `ALL PROOFS CHECK`; all 16 report source hashes match the final files. |

Start inventory: 373 negative fixtures (746 checker invocations). Removed 17
controls whose only targets were removed model/controllers or read batches.
Retained: 356 fixtures, each checked separately in both official modes. The
runner requires nonzero exit, `SOME PROOFS FAIL`, `Location: false` and explicit
expected/observed diagnostics, and rejects undefined-name/unfilled-proof errors.
Both complete runs passed all 712 intended rejections; the final run includes
the last prepare-read opcode removal.

Coverage: contract 16 modules, src 18 modules, proof 131 modules, library 175
modules. All three positive roots passed both modes in both runs.
The separate report records all eight inhabited witnesses and no pending
public theorem. Both manifests have exactly 16 active contract source hashes.
The retained-edge audit checks 4,433 local imports with zero missing targets.
Protected theorem/requirements/data/semantics/Core/Execution sources match the
starting commit byte-for-byte. No proof axiom, hole or unsafe escape was added.

The documentation build `make -C paper` passed, producing the article and
18-slide deck without overfull boxes. Historical evidence JSON is unchanged.
Raw local logs: `.build/cleanup-validation/` (ignored build artifacts).

## Change size

Since the starting commit: `135 files changed, 695 insertions(+), 25412 deletions(-)`.
