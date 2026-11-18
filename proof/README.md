# Executable contract proofs

`contract/Theorems.bend` states the contract over the functions in
`src/Gate.bend`, `src/Resolve.bend` and the actual interpreter and finisher.
All public theorem types below have witnesses checked by official Bend 2.0.39
and BendTT. The four Core clauses share the same universal premises: valid
configuration, valid starting state, and sound admission for the exact request.

The theorem table includes the reference worker and its private packet.
The live service uses `src/Remote.bend` and the refinement below.

## Theorems and witnesses

| Bend name | What it proves | Witness |
| --- | --- | --- |
| `StartupTheorem` | Given the exact T1-admitted seed-validity declaration, the executed `ConfigurationCheck.initialize` succeeds iff configuration and frozen identity pass, with exactly the seed encoding; recovery accepts iff the same check passes, without a seed. | `Configuration.startup_theorem`, `Configuration.bend` |
| `InitTheorem` | Abstract typed seed-admission helper for `FoldTheorem`; this helper is not executed by the service. | `Init.init_theorem`, `Init.bend` |
| `CoreTheorem` — `Admitted` | A started machine has the current authenticated context, exact oracle acceptance and exact `Core.start` state/arguments. A halted gate has the computed rejection and bounded, correctly framed response preserving the root. | `CoreClauses.core_theorem`, `CoreClauses.bend`; gate equations in `Gate.bend` |
| `CoreTheorem` — `Safe` | Every prefix of the actual machine satisfies all installed laws, including failure closures. | `CoreClauses.core_theorem`, `CoreClauses.bend` |
| `CoreTheorem` — `Completed` | Every final trace has an actual finisher result: exact `Requirements.finalize`, exact `Semantics.publish`, a valid next root, exact framed bytes and a bounded response, without a generic `failure`. | `CoreClauses.core_theorem`, `CoreClauses.bend` |
| `CoreTheorem` — `Progressing` | An accepted machine reaches a final trace and completes. If that trace has a success/refusal proposal preserved by finalization (`WithinLimits`), the response is success/refusal. Data errors remain possible. | `CoreClauses.core_theorem`, `CoreClauses.bend` |
| `IngressTheorem` | Complete ordinary body decoding keeps the exact root and applies Core to the decoded request, or produces a bounded framed denial; it cannot produce a private transport error. | `Ingress.ingress_theorem`, `Ingress.bend` |
| `UnifiedCoreTheorem` | Direct and registered request selection applies Core to the exact selected request, or returns a bounded denial. Registered selection authenticates first, requires empty raw proof and uses scoped lookup. | `Ingress.unified_core_theorem`, `Ingress.bend` |
| `FoldTheorem` | Starting from Init-accepted seed, every reached root is valid and each step satisfies every Core clause, provided the finite run records the actual gate/interpreter/finisher results and sound admissions. | `Iteration.fold_theorem`, `Iteration.bend` |
| `WorkerBridge` | Finite execution emits exactly the Gate/Ingress/Unified composition. The literal prepared packet supplies the complete decoded control registry, with selected source/proof bound to the artifact by generated `matches` and T1; the artifact guard adds defense in depth. | `WorkerBridge.worker_body_equals_ingress_composition`, `WorkerBridge.worker_unified_equals_gate_composition`, `WorkerBridge.prepared_packet_equals_real_registry_selection` |
| `CertifiedWorker` | The actual prepared packet satisfies UnifiedCore over its decoded registry and emits that composition's exact finite result, using the generated checked oracle and sound artifact guard. | `CertifiedWorker.checked_prepared`, `CertifiedWorker.artifact_checked` |
| `DispatchBridge` | Every tag-0 Dispatch reply equals the corresponding Ingress/Unified early branch, with the same bounded framed denial and unchanged root. Prepare/invalidate replies come from the controller under `ControlTheorem`, not the worker denial branch; this bridge does not establish controller reply correspondence. | `DispatchBridge.dispatch_denials_equal_ingress_unified_early` |
| `WorkerDecision` | Keep is exactly the non-success publication path and preserves the starting root; Commit carries the exact theorem next root and bytes. Success may commit a root equal to the starting root. | `WorkerDecision.completion_emits_exact_decision`, `WorkerDecision.keep_iff_non_success` |
| `HostErrorReplyTheorem`, `PreparedHostErrorsTheorem` | The total, exact case-sensitive error-code table computes a bounded canonical denial through the native controller, preserving root, last published response and registry. All 17 certificate codes have checked rows; every other code is `failure`, including `HANDLE` and `PREPARED_INTEGRITY`. `HostErrorReply` states exact emitted bytes independent of root/last/registry, justifying a memo keyed by exact observed code; both prepared codes are prefilled at startup. | `HostErrors.host_error_reply_theorem`, `HostErrors.prepared_host_errors_theorem`, `HostErrors.native_error_branch`, `HostErrors.emitted_frame`, `HostErrors.other_codes_fail`, `HostErrors.row_*` |
| `ControlTheorem` | Controls authenticate against the current root; prepare compares the exact admission tuple and checks lifetime freshness. Receipts are bounded and precede deltas; root/last response are preserved. These structural conclusions need no admission-soundness premise. | `ControlClauses.control_theorem` |
| `ServiceFoldTheorem` | Mixed transactions/controls preserve root validity, exact registry transition history and sound universal sources for live lookups from an empty registry. Invalidation removes scoped entries and preserves allocation history; every later position refuses reuse of an allocated handle, and `ServiceNoRevivalTheorem` preserves its absence. Controls carry the exact T1 admission-soundness premise. | `ControlHistory.service_fold_theorem` |
| `ControlRegistryBytes` | Successfully encoded and framed controller metadata yields exactly its next registry through the prepared worker's `ControlBridge.decode_registry`, given representable byte length within its uint64 ceiling and octet blocks. This connects the mixed fold's registry to reference worker selection when forwarded unchanged. | `ControlRegistryBytes.control_output_registry_decodes`, `ControlRegistryBytes.registry_bytes_decode` |
| `CodecRoundtrip` | A successful canonical encoding decodes to the same value when its body length is representable in uint64 and within the decoder ceiling. | `WireTheorems.codec_roundtrip`, `WireTheorems.bend` |
| `CodecCanonical` | Every accepted value re-encodes to exactly the original bytes. | `WireTheorems.codec_canonical`, `WireTheorems.bend` |
| `FramingRoundtrip` | A successfully joined private two-block packet separates into the original octet blocks. This is the reference worker packet format; the public frame is specified by `Protocol.frame`. | `WireTheorems.framing_roundtrip`, `WireTheorems.bend` |

`RequestFacts` contains shared pure request/termination predicates.
The supporting proofs cover authentication, interpreter fidelity, finalization,
publication, codecs, representation and source generation. Optional library,
queue, preprocessing and persistence transition lemmas have separate scope.
Prepared controls use the checked `Control` plan/delta and exact wire receipts.
The registry fold follows actual control transitions and scoped removal;
artifact IO and the exact T1 admission-token delivery remain host plumbing.

`Main.checked_oracle` packages the actual oracle with `generated_oracle_sound`.
`CertifiedWorker.checked_ingress` and `checked_unified` consume that checked
package and prove both the corresponding Ingress/UnifiedCore clause and the
exact finite worker result, with no separate oracle premise.
`checked_ingress_core` and `checked_unified_core` give the contract clauses
from configuration/root validity alone, without a completion index. Their finite
completion index is the existing bridge index; Core's Progressing clause
supplies completion for accepted starts. These generic corollaries are checked
with the repository proofs, rather than imported into every admission Book:
inlining the full bridge graph into a generated Book exhausts the pinned
BendTT default fuel in `worker_body_equals_ingress_composition.qv_1`.

## Live worker refinement

- [RemoteRefinement.bend](RemoteRefinement.bend) connects the live worker's
  operation request and reply continuation to `S.step`. The host must apply
  `D.operate` to the current working state and supply the matching reply.
- [RemoteReplyBytes.bend](RemoteReplyBytes.bend) proves the ordered answer
  encoding round trip. [RemoteCount.bend](RemoteCount.bend) covers the count
  conversion for representable nonnegative results.
- [RemoteTrace.bend](RemoteTrace.bend) lifts the step result to finite
  prefixes. `all_remote_prefixes_refine_execute` preserves the working
  state, operation events and terminal proposal. `certificate_covers_remote_prefixes`
  transfers the certificate to those prefixes from a valid initial state
  with the authenticated context present.

Each exchange must fit its wire and count bounds. The proofs begin from the
logical program start. Native authentication, Rust decoding and encoding,
final host checks, scheduling and publication require the trusted bridge below.

## Non-vacuity and checking

`tests/proof/Positive.bend` uses the real tasks policy, program, client proof
and valid seed. It proves current authentication, the exact oracle premise,
the exact accepted machine start, changed-root success and valid saved state.
The driver verifies that relocated application bodies and source literals
match the application's checked sources. `Instances.bend` instantiates Core,
unified ingress and the finite-run fold with real oracle evidence.

`Refutations.bend` proves that spoofed identity, uncertified starts, publication
on refusal and rejecting an accepted program cannot satisfy the relevant
clauses. `Controls.bend` and `WrongSteps.bend` provide concrete inputs and
mutations. Every remaining `rejected/*.bend` fixture must fail at its named
`false` proof with expected/observed diagnostics in **both** official modes.
Every diagnostic location must name exactly `false`; a helper co-failure,
missing name or unfinished proof rejects the fixture. `InputLimit.bend` and
`InputRefusals.bend` cover forged internal lengths in physically bounded bodies
and the distinct rejection of actual excess body bytes.
`HostError*.bend` negatives invert every certificate-code row and the prepared
and compile-failure defaults; `HostReply*.bend` mutate both prepared denial
frames, and `HostErrorPublishesRoot.bend` mutates the preserved root.
`HostReplyDependsOnLast.bend` rejects serialization depending on the last
response. Native service tests exercise exact controller bytes for all 17 certificate codes,
technical defaults and unknown/case-different codes, then compare actual
map/integrity replies with the checked worker's not-found denial.

```sh
make verify-contract
make verify
```

`make verify` checks import coverage of every maintained module in `contract/`,
`src/`, `proof/` and `library/`, checks the positive roots separately in both
modes, and runs the causal negative controls. Import coverage is inventory
hygiene; the theorem statements above determine the guarantees.

## Trusted base

**T1 — official checker soundness, exact Book binding and source/purity audit.**
The generated Book proves `generated_oracle_sound`: for every request, its
actual `admit` satisfies the exact `Theorems.OracleSoundness(C.config(), r, admit)`
premise, using the checked client certificate and termination proof. Concrete
matching uses proved String/context/structural-value equality; universal
certificates specialize at the current context and arguments. T1 still trusts
the soundness of both pinned official checkers, the source/target/purity audit
(including isolation from host effects), and that the very checked Book is the
Book passed to C compilation and bound to the loaded artifact. T1 also binds
the exact checked migration function and its preservation proof to the
executable run during cutover. The
[service release boundary](../tools/service/SIMPLE_SERVICE.md#admission-and-artifact-release)
describes concurrent checking/building, seals and receipt/hash gates.
Reported failures discard provisional files. Hard kills or uncatchable OOM
can bypass cleanup. Initialization uses `assertInitialization` to require a
filled checked declaration
with exactly `Requirements.Valid(configuration(), state())` and closed pure
configuration/seed definitions before the startup Book can run. The initializer
receives no proof value and cannot detect whether admission ran. `StartupTheorem`
uses that admitted declaration as its validity premise. Recovery checks only
configuration/identity; recovered-byte provenance remains a host/persistence
obligation. Handles and hashes identify artifacts but do
not supply proofs. Oracle guard soundness and certificate specialization are
now checked propositions, rather than additional admission assumptions.

**T2 — Bend-to-C compiler/runtime preservation.** Compilation of that exact
Book, native ABI and runtime preserve the proved pure transitions, values,
integer/Unicode behavior and observation ordering. The process boundary and
executable provenance are part of this bridge. Compiler preservation is trusted.
With experimental CUDA enabled, T2 grows to include the official CUDA code
path in the emitted runtime, NVRTC, the CUDA driver, managed memory, and GPU
hardware. These CUDA headers/libraries come from the host environment; their
resolved paths and hashes are recorded, not pinned like the Bend toolchain.
No Bend compiler, runtime or emitted C is patched. CPU and GPU
programs must discharge identical certificate, termination, access/RLS and size
obligations on the same sealed Book, through both official checkers. CUDA
compilation and prebuild begin after both accept. CPU and GPU use the same
checked live entry and host validation. With CUDA, executable and prebuilt
cubin hashes are checked before the exchange
and before accepting the result. CUDA prepared calls also check the exact
sealed bytes. CPU prepared workers are validated at launch. Runtime rebuilds
and artifact changes fail with no publication. These checks are T1/T3 bridge
obligations, not a proof of T2. CPU/GPU differential tests and independent
numeric oracles provide evidence, not proof of CUDA implementation correctness.
See [measured scope and limitations](../paper/evidence/gpu-programs.md).

**T3 — live host and physical integration.**

1. Pin the checked configuration, source, tool and executable bytes for
   each epoch. Install exactly the checked seed or the recovered snapshot.
   Export the matching schema and keep private state out of admission files.
2. Apply the active message limit to the complete original body, including
   prepared opcode bytes, with the specified framing and EOF behavior.
   Keep FIFO order per session. Supply checked dispatch and controls with
   the schema and matching user projected from the attempt's snapshot.
3. Admit the exact authenticated tuple and launch the exact checked Book.
   For prepared execution reuse only workers loaded from the matching
   admitted artifact. Check sealed bytes before launching a CPU prepared
   worker, and before and after CUDA prepared execution.
4. Run the private framed `Native.serve` loop. Bind authentication to the
   attempt's snapshot and answer one operation at a time against its
   working state, with the same results and changes as `D.operate`.
   Preserve ABI tags, field order and wire bounds. The worker has no
   publication capability. A worker crash or protocol violation discards
   its transaction and retires that worker.
5. Forward the original prepared request body and only the controller-issued
   entry for the requested live handle. An absent entry must never resolve
   to a program. Give controls the full current registry and exact T1
   admission tuple. Install only the checked delta for a matching epoch,
   registry and authentication view. Preserve allocated-handle history and
   keep artifacts and live workers consistent with invalidation. A delivery
   failure does not undo a control.
6. Validate success proposals against the serial commit order. Check tracked
   row reads and writes, collection membership and credentials against later
   versions. Pin versions needed by running attempts. Retry conflicts on a
   new snapshot, using exclusive execution after three conflicts. Read-only
   outcomes use their published snapshot. Validate structure and canonical
   state size so state errors take precedence over response-check errors.
7. Publish only a validated success. Finish direct-worker execution and
   cleanup before publication. In durable mode, sync each accepted WAL
   batch before publishing its final snapshot and releasing its replies.
   Recovery must restore the matching checkpoint and replay the committed
   prefix in order. WAL write or sync failure stops the process.
8. Run the exact checked migration on the latest state under exclusive
   execution. Validate its output and sync the epoch record in durable
   mode. Switch snapshot, schema, limits, authentication and control as one
   cutover for client work. Retire registrations and workers while retaining
   allocated-handle history.
9. Use the exact observed code for checked denials and cache only the checked
   bytes by that code within its epoch. Prefill `HANDLE` and
   `PREPARED_INTEGRITY` for each epoch. A failing denial executable or
   transport uses a fixed technical fallback outside the memo.
10. Deliver the selected framed response once the outcome is ready. Preserve
    a commit if delivery fails. EOF between messages closes the session.
    Timing and inspection must preserve execution and publication ordering.

`contract/HostErrors.bend` lists `IMPORT`, `IMPORT_CYCLE`, `DEPENDENCY`, `PARSE`,
`META`, `UNSAFE`, `FOREIGN`, `IO`, `OPEN_LAW`, `SHADOW`, `REDEFINITION`,
`PRIMARY_CHECK`, `BENDTT_CHECK`, `TARGET`, `SOURCE_BINDING`, `HOST_CAPTURE`,
`KERNEL_CAPTURE` as `certificate`; all other exact strings map to `failure`.
`compile.mjs` preserves a failed pure-admission code; successful pure admission
followed by a worker-check failure reports `HOST_COMPILE`. Native-build errors
(`phase: compile`) occur only after both checkers accept, skip pure rechecking
and report `HELPER`; both map to `failure`.
These failures reject before the submitted program runs. The host supplies the
actual observed code; checked code does not prove the tool produced it.
The 17-code certificate table is a contract specification. Nothing proves
that it equals the set of codes the Node tools use for proof rejection;
`ORACLE_PROOF`, `ADT` and `INSTANCE_MATCH`, for example, map to `failure`.
`tests/admission/error_codes.test.mjs` cross-checks literal codes in the Node
admission/service tools against the table and deliberate failure classifications;
it detects inventory drift, not semantic equivalence or dynamically supplied codes.
The controller computes `HANDLE` and `PREPARED_INTEGRITY` replies separately
for each epoch. `HostErrorReplyTheorem` quantifies over every root, last response
and registry and states that emitted bytes equal `Messages.error(HostErrors.status(code))`.
This justifies memoizing checked replies by exact code for later roots.
Other observed codes, including `HOST_IO`, use their own memo entry or invoke
the controller with that exact code. No extra child runs on prepared map/integrity
failures with the prefilled codes. An artifact-map miss can indicate an absent registration
or an unavailable live artifact. The integrity denial is a technical failure, not evidence
against the original certificate. Neither denial executes that artifact.

## Scope

The error-reply theorem and `HostErrors.native_error_branch` bridge cover the
native controller's decoded private text metadata branch, typed transition and
exact serialization. They prove denial, bounded framing and root preservation. Physical failure
detection, artifact integrity, process execution and publication remain T3.

Durability of persistence, OS failures and physical resource availability,
and checker completeness/adequacy are outside the proved theorems. Accepted
logical termination is conditional on T1; acceptance of every mathematical
proof requires a separate adequacy assumption. Syscall progress and scheduling
require host/runtime assumptions. The pure persistence lemmas concern supplied
transitions and recovered bytes, not device durability.

In durable mode the host stores checksummed checkpoints and WAL batches.
Checkpoints and migration records carry their epoch's environment descriptor.
Write records contain row changes. Read-only successes use an already durable
snapshot. Prepared registrations, allocation history and responses are
instance-local; durable recovery does not replay responses.
