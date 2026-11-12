# Executable contract proofs

`contract/Theorems.bend` states the contract over the functions in
`src/Gate.bend`, `src/Resolve.bend` and the actual interpreter and finisher.
All public theorem types below have witnesses checked by official Bend 2.0.39
and BendTT. The four Core clauses share the same universal premises: valid
configuration, valid starting state, and sound admission for the exact request.

The native worker computes its result through `Gate` (see `WorkerBridge` below).

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
| `WorkerBridge` | `result_driver_preserves_exact_execution` and `routed_packet_lifts_registered` lift the original exact decision into the checked route/principal envelope; metadata is derived from the same fresh authentication and complete registry selection. Finite execution emits exactly the Gate/Ingress/Unified composition. The literal prepared packet supplies the complete decoded control registry, with selected source/proof bound to the artifact by generated `matches` and T1; the artifact guard adds defense in depth. | `WorkerBridge.worker_body_equals_ingress_composition`, `WorkerBridge.worker_unified_equals_gate_composition`, `WorkerBridge.prepared_packet_equals_real_registry_selection` |
| `CertifiedWorker` | `checked_routed_prepared` covers the actual metadata-bearing entry with its closed generated oracle package, preserving the same UnifiedCore clause and exact decision. The actual prepared packet satisfies UnifiedCore over its decoded registry and emits that composition's exact finite result, using the generated checked oracle and sound artifact guard. | `CertifiedWorker.checked_prepared`, `CertifiedWorker.artifact_checked` |
| `DispatchBridge` | Every tag-0 Dispatch reply equals the corresponding Ingress/Unified early branch, with the same bounded framed denial and unchanged root. Prepare/invalidate replies come from the controller under `ControlTheorem`, not the worker denial branch; this bridge does not establish controller reply correspondence. | `DispatchBridge.dispatch_denials_equal_ingress_unified_early` |
| `WorkerDecision` | Keep is exactly the non-success publication path and preserves the starting root; Commit carries the exact theorem next root and bytes. Success may commit a root equal to the starting root. | `WorkerDecision.completion_emits_exact_decision`, `WorkerDecision.keep_iff_non_success` |
| `HostErrorReplyTheorem`, `PreparedHostErrorsTheorem` | The total, exact case-sensitive error-code table computes a bounded canonical denial through the native controller, preserving root, last published response and registry. All 17 certificate codes have checked rows; every other code is `failure`, including `HANDLE` and `PREPARED_INTEGRITY`. `HostErrorReply` states exact emitted bytes independent of root/last/registry, justifying a memo keyed by exact observed code; both prepared codes are prefilled at startup. | `HostErrors.host_error_reply_theorem`, `HostErrors.prepared_host_errors_theorem`, `HostErrors.native_error_branch`, `HostErrors.emitted_frame`, `HostErrors.other_codes_fail`, `HostErrors.row_*` |
| `ControlTheorem` | Controls authenticate against the current root; prepare compares the exact admission tuple and checks lifetime freshness. Receipts are bounded and precede deltas; root/last response are preserved. These structural conclusions need no admission-soundness premise. | `ControlClauses.control_theorem` |
| `ServiceFoldTheorem` | Mixed transactions/controls preserve root validity, exact registry transition history and sound universal sources for live lookups from an empty registry. Invalidation removes scoped entries and preserves allocation history; every later position refuses reuse of an allocated handle, and `ServiceNoRevivalTheorem` preserves its absence. Controls carry the exact T1 admission-soundness premise. | `ControlHistory.service_fold_theorem` |
| `ControlRegistryBytes` | Successfully encoded and framed controller metadata yields exactly its next registry through the prepared worker's `ControlBridge.decode_registry`, given representable byte length within its uint64 ceiling and octet blocks. This connects the mixed fold's registry to worker selection when forwarded unchanged. | `ControlRegistryBytes.control_output_registry_decodes`, `ControlRegistryBytes.registry_bytes_decode` |
| `CodecRoundtrip` | A successful canonical encoding decodes to the same value when its body length is representable in uint64 and within the decoder ceiling. | `WireTheorems.codec_roundtrip`, `WireTheorems.bend` |
| `CodecCanonical` | Every accepted value re-encodes to exactly the original bytes. | `WireTheorems.codec_canonical`, `WireTheorems.bend` |
| `FramingRoundtrip` | A successfully joined private two-block packet separates into the original octet blocks. This is the private packet format; the public frame is specified by `Protocol.frame`. | `WireTheorems.framing_roundtrip`, `WireTheorems.bend` |

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

The checked worker also specializes the common 65,536-byte ceiling through
`LimitWords.convert_equals_reference`, with a canonical `Number64` literal
witness derived from the existing checked u64-addition proof in bounded steps.
The comparison peels bounded Nat blocks, avoiding intermediate u64 values.
`common_guard_hits` proves that the cached branch is taken at 65,536; block
soundness and `convert_equals_reference` cover every Nat. This avoids closed
large-Nat expansion during proof conversion. Other ceilings use the
unchanged `Bytes.nat64`, including its overflow behavior. The staging layer
relocates this proof dependency closure into each admitted Book.
`Execution.finish_equals_reference` proves that retaining the canonical state
encoding used by finalization emits exactly the existing preparation,
publication and Commit/Keep composition, including every failure branch.
`ExecutionAdapter` uses that equality for the actual stopped-machine step.
These are pure checked refinements; T1–T3 and the private result ABI are unchanged.

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
Book passed to C compilation and bound to the loaded artifact. The
[service release boundary](../tools/service/SIMPLE_SERVICE.md#admission-and-artifact-release)
describes concurrent checking/building, seals and receipt/hash gates. T1 rests
on those gates, not on cleanup; on every reported failure provisional files
are discarded, while hard kills or uncatchable OOM can bypass cleanup. Initialization
validity uses `assertInitialization`: it requires a filled checked declaration
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
The dynamic loader, libc, libm, loader configuration and inherited loader
variables remain trusted as before; the old per-call executable/source checks
also did not protect these dependencies. Kernel memfd seal enforcement and
/proc/self/fd execution now explicitly enforce admitted-image immutability;
they are OS assumptions, not new checked Bend theorems.

**T3 — host plumbing for the serial in-memory service.**

1. Pin configuration, source and tool bytes after initialization; use exactly
   the checked seed root. Keep private state separate from client inputs.
2. Read one bounded outer u64 frame with the specified EOF behavior. Supply
   the complete original body and one current-root snapshot to the checked
   decoder/controller; count prepared opcode bytes in the input limit.
3. Ordinary admission and preparation admit only the tuple selected by checked
   authentication/dispatch; controls retain checked Dispatch/Control routing.
   Prepared execution may tentatively locate
   an already admitted artifact with the bounded total host envelope parser;
   this is routing, not authentication or authoritative registry selection.
   Forward the complete original body, current root and latest registry unchanged.
   Before accepting any candidate proposal, parse its checked result envelope,
   require the returned environment to equal the frozen instance environment, the
   raw handle to equal the candidate, the selected registration's source/proof
   to match that artifact, and the original authentication metadata to be ready.
   On parser doubt, missing artifact, integrity/transport/worker failure or identity mismatch, discard the
   candidate and run the original checked-dispatch path before publication.
   This retry is required for routing completeness: the artifact guard alone
   does not establish observational equivalence of a wrong candidate. Compile
   and load the exact selected checked program and gate with immutable
   dependencies; preserve context, arguments and proof between checking and launch.
4. Run a fresh private worker through the checked gate/advance/finalizer using
   the trusted native loop. Give it no publication capability. A worker may
   be pre-executed, but is single-use: deliver no state, registry, credentials
   or request until selection, and supply only that call's current packet.
   Keep each idle process bound to its exact admitted image and runtime policy;
   asynchronously refill at most one idle slot per live prepared image and one
   for the authenticator. Reap a dead idle child and fall back to fresh spawn;
   kill/reap idle children and join refill work on invalidation and shutdown.
   Refill owns no publication authority and does not change serial publication.
   Preserve the logical observation trace on interruption.
5. Collect the complete result/response and finish rollback-capable cleanup
   before publication. Discarded tentative candidates retry under duty 3;
   their intermediate results are neither published nor delivered. An actual
   tool/process/transport failure on the final authoritative path keeps
   the prior root and emits the fixed failure frame when possible; fatal loss
   may stop the process without a reply. Supply admission/other observed error
   codes, current root and registry to the checked controller and forward its
   denial; a memo hit forwards the checked bytes for that exact observed code.
   If that executable or transport itself fails, the fixed technical fallback
   remains host plumbing; it cannot produce a certificate rejection.
6. Atomically publish exactly the accepted checked Commit root and paired response;
   otherwise preserve the prior root. Send no reply before this decision.
   Start the next transaction with the resulting root.
7. Supply prepared execution exactly the latest controller-emitted registry
   bytes unchanged and the original root/body; before any control, the registry
   is the empty byte string, decoded as the empty registry. These canonical
   bytes are unauthenticated. "Invalidated means not executable" and the
   correspondence between a handle and its registered program hold only while
   the host forwards those latest bytes unchanged. Stale or fabricated registry bytes can break those
   properties; executed programs remain universally certified under T1 and the
   generated source/proof matching regardless. Supply controls the exact T1
   universal-admission tuple, original body, current root and latest registry;
   install only the checked registry delta and manage the matching artifact.
   Preserve allocated history and the root/last-response pair. Receipt delivery
   never rolls back a control. Keep the physical artifact-map lookup. At load,
   copy the released ELF into an owned CLOEXEC memfd, install and verify
   F_SEAL_WRITE/GROW/SHRINK/SEAL, then hash the sealed contents against the
   admitted executableSha256. Fail closed on any mismatch/seal failure and
   execute that exact retained fd. The trust changes from rereading/comparing
   physical artifacts every call to verification once plus kernel-enforced
   memfd immutability. Staged source/C/manifest/executable copies are diagnostic
   after load and may change without affecting an existing worker. Before each
   future compilation, compare the frozen public/runtime and environment metadata
   against the original in-memory bytes; both-checker release remains mandatory.
   Host-owned compilation storage must remain unchanged during validation/use,
   as at the existing release boundary. Those observations, fd ownership and
   fail-before-execution ordering remain trusted. Cache
   only controller-emitted bytes by exact observed code, prefilling `HANDLE` and
   `PREPARED_INTEGRITY` separately at startup. `HostErrorReplyTheorem` states
   output independence from root, last response and registry; limits remain
   immutable for the instance. Never cache a technical fallback.
8. Deliver exactly the returned bytes. After a post-commit delivery failure,
   retain the committed root and stop/close as appropriate. EOF or shutdown
   between requests terminates the channel rather than creating a transaction.

`WorkerBridge.prepared_readiness_is_same_fresh_dispatch_authentication` also
binds a checked readiness flag to the original `Messages.authentication` output.
Tag 2 (including `Generate.instance` or metadata-frame failure) is not ready;
the host must discard that candidate and use the original path. This preserves
technical metadata failure behavior without an unproved claim that argument
reification always succeeds. It retains that checked metadata computation inside
the worker, while eliminating the separate root decode/process. Principal
metadata from an unready candidate is never accepted for logging.

The prepared-worker envelope adds explicit T3 parsing/comparison and retry
obligations to duty 3 and explicitly scopes duty 5's final technical failure
policy after tentative retries; it adds no host authentication or status authority.
`Messages.worker_principal_is_authenticated_id`, the WorkerBridge metadata
laws and DispatchBridge's proof-validation law bind the logged principal to the
same current-root authentication as selection. The selected source/proof
comparison is shared with the actual oracle guard; WorkerBridge proves its Gate
entry equals the original artifact guard and `CertifiedWorker.matched_checked`
retains universal oracle soundness for that bit. An authenticated empty ID is
`Some{""}`. Timing/inspection remain trusted effects: only accept a candidate's
principal with its complete checked result. A technical candidate failure first
retries the original authenticator path, retaining that authenticator's principal
even if the fallback worker also crashes. Retry can run two private workers;
neither may publish until the final accepted decision. See SERVICE_TIMING.md.

The status table and construction of admission, handle-miss and integrity
replies moved from Rust into checked Bend under `HostErrorReplyTheorem`.
The eight items above reorganize the host obligations; they do not represent a
reduction from eleven to eight trusted duties. Detection of handle-map misses
and integrity failures, passing the exact observed code, cache forwarding and
the technical fallback remain trusted, folded into duties 5 and 7.
`contract/HostErrors.bend` lists `IMPORT`, `IMPORT_CYCLE`, `DEPENDENCY`, `PARSE`,
`META`, `UNSAFE`, `FOREIGN`, `IO`, `OPEN_LAW`, `SHADOW`, `REDEFINITION`,
`PRIMARY_CHECK`, `BENDTT_CHECK`, `TARGET`, `SOURCE_BINDING`, `HOST_CAPTURE`,
`KERNEL_CAPTURE` as `certificate`; all other exact strings map to `failure`.
`compile.mjs` preserves a failed pure-admission code; successful pure admission
followed by a worker-check failure reports `HOST_COMPILE`. Native-build errors
(`phase: compile`) occur only after both checkers accept, skip pure rechecking
and report `HELPER`; both map to `failure`.
These failures reject before the request's Gate runs. The host supplies the
actual observed code; checked code does not prove the tool produced it.
The 17-code certificate table is a contract specification. Nothing proves
that it equals the set of codes the Node tools use for proof rejection;
`ORACLE_PROOF`, `ADT` and `INSTANCE_MATCH`, for example, map to `failure`.
`tests/admission/error_codes.test.mjs` cross-checks literal codes in the Node
admission/service tools against the table and deliberate failure classifications;
it detects inventory drift, not semantic equivalence or dynamically supplied codes.
The controller computes `HANDLE` and `PREPARED_INTEGRITY` replies separately
at startup. `HostErrorReplyTheorem` quantifies over every root, last response
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
exact serialization. It
proves denial, framing/bounds and root preservation, not physical failure
detection, artifact integrity, process execution or publication. Healthy ordinary
success and prepared calls run no additional child or checker.

Durability of persistence, OS failures and physical resource availability,
and checker completeness/adequacy are outside the proved theorems. Accepted
logical termination is conditional on T1; acceptance of every mathematical
proof requires a separate adequacy assumption. Syscall progress and scheduling
require host/runtime assumptions. The pure persistence lemmas concern supplied
transitions and recovered bytes, not device durability.

The optional durable host stores canonical state, immutable environment binding
and limits, plus a checksum. It does not persist the instance-local last response
or prepared registry/allocation history. Host duties 6 and 7 still require the exact
root/response pair in RAM, including on equal-root successful transactions and
controls. A byte-identical state Commit may reuse an already durable complete
image while publishing its new paired response. Create establishes durability;
open synchronizes the validated authoritative file and directory before serving;
every changed state (including an application receipt row) completes its durable
protocol before publication: one slot `fdatasync`, or file sync, replacement and
directory sync when creating/growing the file. Equal-root reuse changes no T3
duty and adds no response-replay promise across restart. The slot protocol's
additional physical assumptions are listed below.

## Durable slots and physical assumptions

`DurableCommit.bend` retains the four-call replacement model for initialization
and growth and adds the actual prepare/slot-write/fdatasync transition order.
`slot_commit_classifies_every_return` proves that acknowledgement requires a
successful data sync and that safe failure preserves the previous publication;
errors from slot writing onward are uncertain.
`every_slot_crash_cut_recovers_a_certified_state` composes each crash choice
with `History`'s actual certified publication origin. Existing replacement
theorems and negative controls remain; slot premature acknowledgement and
unsafe rollback have separate rejection controls.

The [storage protocol](../docs/durable-storage.md) specifies the two initialized,
4096-byte-aligned slots, parity, consecutive sequences, growth and size bounds.
Recovery durably zeroes a nonzero invalid peer before reusing its sequence,
preventing resurrection of an earlier failed candidate by a later torn write.
`repaired_peer_is_stable_before_sequence_reuse` checks the clear/file-sync/directory-sync
order; `repair_crash_recovers_previous_or_certified_failed_candidate` requires
that earlier candidate's actual certified origin, including crashes during clearing.
These are trusted Rust/OS obligations, tested with exhaustive byte cuts,
mutations, stale-header/payload combinations, sector/block subsets and real
process crash/error boundaries. They are not proved by the abstract model.
New physical assumptions are successful Linux/ext4 `fdatasync` durability,
isolation of the current slot's synced filesystem blocks during writes to the
other slot, and detection of torn sequence/payload contents by SHA-256
(undetected collisions excluded). No sector or block atomicity is assumed.
Atomic rename/directory fsync remain needed for initialization/growth and after
recovery; device flush honesty, protected storage and exact environment binding
remain required. Unrelated media corruption or malicious rewriting is outside
the crash-only model. A checksum is neither a certificate nor proof of disk
provenance: corruption of an acknowledged newest slot cannot be distinguished
from an interrupted peer overwrite under a stronger fault model.
