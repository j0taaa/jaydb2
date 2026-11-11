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
| `WorkerBridge` | Finite execution emits exactly the Gate/Ingress/Unified composition. The literal prepared packet supplies the complete decoded control registry, with selected source/proof bound to the artifact by generated `matches` and T1; the artifact guard adds defense in depth. | `WorkerBridge.worker_body_equals_ingress_composition`, `WorkerBridge.worker_unified_equals_gate_composition`, `WorkerBridge.prepared_packet_equals_real_registry_selection` |
| `CertifiedWorker` | The actual prepared packet satisfies UnifiedCore over its decoded registry and emits that composition's exact finite result, using the generated checked oracle and sound artifact guard. | `CertifiedWorker.checked_prepared`, `CertifiedWorker.artifact_checked` |
| `DispatchBridge` | Every tag-0 Dispatch reply equals the corresponding Ingress/Unified early branch, with the same bounded framed denial and unchanged root. Prepare/invalidate replies come from the controller under `ControlTheorem`, not the worker denial branch; this bridge does not establish controller reply correspondence. | `DispatchBridge.dispatch_denials_equal_ingress_unified_early` |
| `WorkerDecision` | Keep is exactly the non-success publication path and preserves the starting root; Commit carries the exact theorem next root and bytes. Success may commit a root equal to the starting root. | `WorkerDecision.completion_emits_exact_decision`, `WorkerDecision.keep_iff_non_success` |
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

**T3 — host plumbing for the serial in-memory service.**

1. Pin configuration, source and tool bytes after initialization; use exactly
   the checked seed root. Keep private state separate from client inputs.
2. Read one bounded outer u64 frame with the specified EOF behavior. Supply
   the complete original body and one current-root snapshot to the checked
   decoder/controller; count prepared opcode bytes in the input limit.
3. Admit only the tuple selected by checked authentication/dispatch. Compile
   and load its exact checked program and gate with immutable dependencies;
   preserve context, arguments and proof between checking and launch.
4. Run a fresh private worker through the checked gate/advance/finalizer using
   the trusted native loop. Give it no publication capability. Preserve the
   logical observation trace on interruption.
5. Collect the complete result/response and finish rollback-capable cleanup
   before publication. An actual pre-commit tool/process/transport failure keeps
   the prior root and emits the fixed failure frame when possible; fatal loss
   may stop the process without a reply.
6. Atomically publish exactly the checked Commit root and paired response;
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
   never rolls back a control.
8. Deliver exactly the returned bytes. After a post-commit delivery failure,
   retain the committed root and stop/close as appropriate. EOF or shutdown
   between requests terminates the channel rather than creating a transaction.
9. Host maps admission failure codes to response statuses as follows: `IMPORT`,
   `IMPORT_CYCLE`, `DEPENDENCY`, `PARSE`, `META`, `UNSAFE`, `FOREIGN`, `IO`, `OPEN_LAW`,
   `SHADOW`, `REDEFINITION`, `PRIMARY_CHECK`, `BENDTT_CHECK`, `TARGET`,
   `SOURCE_BINDING`, `HOST_CAPTURE`, `KERNEL_CAPTURE`
   map to `certificate`; every other code maps to `failure`. A failed proof
   rejects whole-Book admission before Gate runs. `compile.mjs` uses the pure
   admission error when that check fails; after successful pure admission it
   reports `HOST_COMPILE` for a failed worker check. Native-build errors
   (`phase: compile`) occur after both checkers accept, skip pure rechecking,
   and report `HELPER` (still client `failure`). This table
   and classification are trusted host decisions, not the checked Gate Reject
   branch.
10. On an authenticated execute request with empty proof, a host artifact-map
    miss (unknown/invalidated handle, `HANDLE`) preserves the root and sends the
    fixed `failure` frame. For an absent registry lookup this equals the checked
    not-found denial. If the map lacks a live registration's artifact, it is a
    host availability failure. This Rust-only reply is a T3 obligation.
11. On prepared artifact-integrity failure (`PREPARED_INTEGRITY`), preserve the
    root and send the same fixed `failure` frame without executing the artifact.
    This Rust-only check/reply is a T3 obligation, not a checked worker verdict
    or evidence against the original certificate. Service tests compare both
    Rust-only replies byte-for-byte with a checked worker not-found denial for
    the same root.

## Scope

Durability of persistence, OS failures and physical resource availability,
and checker completeness/adequacy are outside the proved theorems. Accepted
logical termination is conditional on T1; acceptance of every mathematical
proof requires a separate adequacy assumption. Syscall progress and scheduling
require host/runtime assumptions. The pure persistence lemmas concern supplied
transitions and recovered bytes, not device durability.

The optional durable host stores canonical state, immutable environment binding
and limits, plus a checksum. It does not persist the instance-local last response
or prepared registry/allocation history. T3.6 and T3.7 still require the exact
root/response pair in RAM, including on equal-root successful transactions and
controls. A byte-identical state Commit may reuse an already durable complete
image while publishing its new paired response. Create establishes durability;
open synchronizes the validated authoritative file and directory before serving;
every changed state (including an application receipt row) completes file sync,
replacement and directory sync before publication. This optimization changes no
T3 duty and adds no response-replay promise across restart.
