# Composition of the eight laws

[ContractService.bend](ContractService.bend) constructs exactly
`LAWS.Contract(a,k)`, composing all eight current laws for the Bend kernel and
its ordinary serial protocol. It neither changes the laws nor receives their
conclusions as premises. `make verify` includes this composition in both
official verifiers.

The result is **conditional on the tool and integration contracts below**.
The protocol uses actual `src` functions; correspondence between its steps
and the Rust/Node/C blocks is an explicit operational assumption supported by
review and tests. This is not a mechanized proof of Rust, Node, C, or the
compiler.

## One proof per law

| Law | Establishing term | Code and property established |
| --- | --- | --- |
| 1 — initialization/configuration | `Law1Service.law1_of_model` | `Configuration.is_valid` and seed checking: startup only after the initial proof; configuration preserved; rejection excludes startup. |
| 2 — representation/operations | `Law2Service.law2_of_model` | `Codec`, `Input`, `State`, `Transport`, `Core`: exact bytes and operations, framed reads, and length checks before field construction. |
| 3 — identity | `Law34Service.law3_of_model` | `Data.authenticate` over the request and published snapshot: reception before authentication and correct authentication before the program. |
| 4 — certificate | `Law34Service.law4_of_model` | Judgments of exact declarations: source, configuration, context, and arguments bound to the certificate; authentication before admission, admission before execution. |
| 5 — execution/observations | `Law5Service.law5_of_model` | `Core.advance/traverse`: faithful steps, ordered observations, each operation tied to its corresponding transition, a single start, and no step after completion. |
| 6 — publication | `Law6Service.law6_of_model` | `Core.prepare/conclude`: preparation before unique publication, validity derived from the certificate, rollback of non-success, and continuation with current published state. |
| 7 — responses/failures/channel | `Law7Service.law7_of_model` | `Requirements.finalize`, preparation, and error branches: correct causes, complete content, actual prefix of interrupted delivery, and correct closure. |
| 8 — progress | `Law8Service.law8_of_model` | `ProgramTerminates`, incremental machine, and protocol phases: startup, admission, and completion under the original `Processable` conditions using primitive returns. |

`HistoryService` derives current-state validity by induction from the seed
and prior `Core` conclusions. Post-publication validity is not supplied by
the host. `ClosuresService` and `LinkageService` connect facts to the same
execution path, including failures before publication, later fatal failures,
and incomplete deliveries. Delivery failure does not undo a store.

## Explicit premises

`ContractService.Premises` contains five groups; their definitions expose the
obligations rather than hiding them in a callback that asserts a law:

- `Initial`: judgment of the closed seed-validity declaration actually used
  for initialization.
- `Observations`: Codec results, copies, and framing of actual bytes, including
  declared lengths and protocol limits.
- `SourcesExecution`: configuration, seed, history, and execution of checked
  sources. Each step refers to computed authentication and equations of actual
  `Core` functions. `JudgmentRefused` requires correct rejection of the
  declaration within the admitted domain; no verdict or tool exhaustion does
  not establish absence of a certificate.
- `Communication`: byte origin, actual errors, written prefixes, and IO-operation
  returns. It supplies neither `ResponseJustified` nor `Rule7`.
- `AvailabilityOfModel`: under `Processable`, checking, execution, cleanup,
  and IO primitives return according to their contracts. It does not supply
  `Concluded`, `ProgramStarted`, or publication.

`reopen` denotes the same closed declaration of these premises; equality of
its type with `Premises` is required. It allows proof reuse without copying
affine values or introducing axioms.

`Processable` is the original external predicate, preserved by the model. It
is not “what the server accepted” or “what finished.” The official tool's
fragment and ordinary limits remain declared. There is no promise of a
physical deadline or RAM consumption.

## Bridge to the executed server

| Concrete block | Integration contract used by composition |
| --- | --- |
| `stage.freeze/reopen`, admission, and `emitC` | Same public sources, dependencies, and declarations; frozen configuration; official judgments of exact targets; no private state in client compilation. |
| `packet`, `Program::run`, `Native.read/write` | Pipes preserve bytes and carry the published snapshot and actual body. Partial output or an unsuccessful process is not a complete proposal. |
| `Native.loop` and `Execution.advance` | Each step and effect corresponds to the indicated Bend function, without omitting relevant operations, reads, constructions, or errors. |
| `checked_proposal`, `request.remove`, `Published::finish` | The complete proposal is the result of `Core.conclude`; child exit and cleanup precedes the sole store. Other branches do not perform that store. |
| `FrameQueue`, `coordinate`, `SerialService`, `write_all/flush` | Complete frames selected and responses emitted in FIFO order; authentication uses current published state at service time. Read-ahead terminal events follow complete frames. Failed publication/delivery prevents later selection; cancellation joins the reader. No implicit reconnection. |
| Official tools, processes, and IO | Checker correctness and compiler/runtime semantic preservation; primitive progress under the specified external conditions. |

These contracts must cover **all** relevant facts of actual execution, without
choosing a convenient trace that hides accesses or failures. History is a
proof structure, not a new server log. `Stored` refers to serialization/copy
boundaries of published states; working states may contain temporarily empty
or duplicate credentials when administrator laws permit.

The executable conclusion is therefore: **under the explicit tool and
integration contracts, the kernel and ordinary protocol satisfy the eight laws**.
Hashes identify sources and tests support the operational bridge; neither
alone proves those contracts. A mechanized proof of the Rust/Node/C bridge
remains outside this result.

The bounded framing reader is a host refinement of serial service: receipt and
enqueue may precede earlier execution, but selection, authentication, admission,
execution, cleanup, publication and response delivery remain serial. The
existing serial theorem does not mechanize the Rust queue, byte reservations,
poll/cancellation or their refinement. These are additional explicit host
contracts supported by deterministic and real CLI tests; see the
[scheduling report](../experiments/scheduling/REPORT.md). A fallible publication
hook allows fatal commit errors to end service without an invented response;
it does not by itself establish durability or extend the serial theorem to a
persistent host.

## Additive prepared-program contract

`PreparedPrograms.bend` checks the universal-certificate specialization and
uses the actual `src/Prepared.bend` resolver invoked by prepared workers. It
proves preservation of current authentication, state, context and arguments,
and derives faithful preparation/valid publication through `Call` and `Core`.
The proof supplies neither final validity nor permission to publish as a premise.

The user authorized an additive contract for this interface on 2026-11-06.
`contract/PreparedProtocol.bend`, `PreparedRegistry.bend` and
`PreparedLaws.bend` add precise prepared obligations. The ordinary eight-law
composition above and its source files are unchanged. Control metadata receipts
remain outside `Semantics.Response`; prepared transactions use the resolved
logical request. `Interface.RequestReceived`'s ordinary encoding equation does
not hold for a raw handle body.

`PreparedProtocol.Received` requires valid actual reception and the exact
physical prefix, canonical inner record and full message limit.
`PreparedLaws.Ready` requires current authentication before semantic authority
resolution, exact registered source/proof, universal admission, the fixed
whole-program read proof for read-marked entries, and artifact correspondence
indexed by the actual call and time. The scheduler's earlier candidate lookup
only classifies a possible read batch; it grants no authority.

`ControlOutcome` binds actual result bytes to bounded canonical receipts or
specific error causes, exact authorized registry deltas and an unchanged
published state/response pair. Preparation receipt overflow occurs before
sealing or insertion. Invalidation checks its receipt before removal; a real
cleanup failure for the selected directory can then replace the receipt with
`failure` without restoring registration. Delivery failure does not roll back a
registry change. The additional `ControlLaw` quantifies over its declared
metadata observations. There is no complete actual observer instantiation:
sent prefixes, delivery completion, closure and progress are not composed into
this type. The separate `Delivery` predicate is not used by `ControlLaw`.

`PreparedWire.bend` adds general physical-wire/ordinary-wire separation and
receipt-encoding proofs. `PreparedExtension.bend` connects prepared readiness
to the actual worker resolver and Core theorem, and proves full abstract
registration/invalidation result equations and receipt bounds.
`PreparedControls.bend` constructs authorized control outcomes from reception,
authentication, admission, current artifacts, bounds and specific failure
premises; it does not assume those outcomes as premises. These general/model
results supplement the existing `PreparedPrograms` proofs.

`PreparedRegistryHistory.bend` instantiates the generic registry invariant with
actual mode-certificate evidence, propagates it from the empty registry through
admitted abstract history, and recovers the exact certificate on lookup. The
history still needs correspondence with all real host mutations; fresh
authentication and current artifact integrity remain separate obligations.

There is still no proof of the complete actual `ControlLaw` or the complete
executable contract. Coverage of every host observation, physical ordering of
receipt preparation and registry mutation, exact current artifact binding,
compiler preservation and Rust/Node/C/OS/process/channel correspondence remain
explicit bridge obligations supported by focused tests and review. Neither the
normalization proof nor the new model proofs silently extends the legacy
ordinary-wire eight-law theorem to the full prepared executable.

## Execution, source generation and interleaved history

`ExecutionAdapter` proves finite runs of the actual `Execution.advance` adapter,
including its preparation branch. Its productive-call theorem derives a complete
private output packet, faithful preparation and a valid computed conclusion from
termination, the administrator certificate, initial validity and authentication.
`PreparedExtension.ready_call_reaches_complete_actual_adapter_output` obtains
termination and the specialized certificate from `Ready`; a completed execution
is no longer an input to this new theorem.

`PreparedControlDispatch`, `PreparedInvalidationDispatch` and
`PreparedControlTrace` construct complete decoded-control outcomes, response
framing, receipt-before-mutation order, exact registry-event replay and
delivery-prefix/closure consequences of primitive send returns.
`PreparedServiceHistory` derives database validity and exact registered
mode-certificate recovery over one interleaved history from a valid seed and an
empty registry. Its source facts do not contain the resulting state invariant.
It does not assert that this history captures every physical host mutation.

`HandleAllocation` proves the concrete entropy-first allocator always returns a
fresh, literally absent, contract-valid handle. The fallback checks the inclusive
descending range from registry cardinality to zero. Its cardinality proof uses
the independently decoded byte/nibble encoder, not random fairness or an assumed
injective generator. The native host enforces the counter's 64-bit type domain.
Prepared artifact revalidation retains and compares exact original bytes; it
does not infer byte equality from SHA256 equality.

`GeneratedLiterals` and `GeneratedContext` prove general escaping, literal and
context recovery, unchanged trailing source, and composition with actual argument
reification. `GeneratedInstance` additionally proves actual U32 division by ten,
decimal printing and exact high/low length-token recovery. Every representable,
measured value actually generates source; correctness is not vacuous on failure.
These proofs use an independent parser for the emitted grammar. Agreement with
the actual JavaScript frontend and compiler remains a distinct obligation. None of these results supplies an actual
native observer or the whole extended eight-law contract witness.

`GeneratedModule` parses context and arguments together from the complete
actual instance source, without receiving the expected context as parser input.
It also proves that `Generate.links` preserves the exact client code literal
and the complete certificate/termination declaration suffix.

`EnvironmentBinding` proves exact descriptor framing is injective in every
name, content and position, and valid UTF-8 source-byte equality implies exact
source-text equality. Storage creates and syncs this immutable descriptor once
before its first image and requires exact comparison on reopen. This removes
the hash-injectivity gap in configuration binding; filesystem protection and
actual source/compiler correspondence remain explicit obligations.

For replacement of an existing certified image, `DurableCommit` models the
four-call write/sync/replace/directory-sync order, admitting errors both before
and after each effect. It proves that
ordinary rollback errors cannot recover a new image, acknowledgment requires
directory sync, and any modeled crash recovers the old certified state or the
certified actual Core candidate. It derives candidate validity from
`History.Origin`, rather than receiving post-validity or trusting a checksum.
Atomic rename/fsync semantics and native call-by-call correspondence are the
filesystem/implementation boundary of this model.

`HostTransitions` derives shared database validity and original preparation
provenance through actual pure Core/register/invalidate transitions.
`HostHistory` constructs every completed-call edge and proves exact replay,
linkage and inclusion. Its closed factory supplies original source judgments
and primitive Core equations; its fields do not supply resulting validity or
an observer satisfying the laws. Cached calls reopen the original declaration
from current registry provenance instead of receiving a new certificate.

`HostInvalidation` and `PreparedDispatch` derive selection from the real pure
authentication, proof-field and current-lookup computations. `PreparedProgress`
derives complete adapter output from the original termination certificate.
`PreparedAuthority` obtains current validity, full `Ready` and certification of
the actual arguments from a proved seed and interleaving plus exact current
artifact binding. `PreparedRejects` proves concrete rejection causes and
complete bounded wire responses. A full phase observer and the entire extended
eight-law witness still need composition.

`SchedulingRefinement` includes reservation accounting, FIFO conservation,
conditional head selection, producer interleavings during read collection,
fixed worker batches, complete joining after failures, and constructive finite
queue progress. Collected frames form a bounded classified reception prefix,
including arrivals during collection. These models prove their outcomes from
transitions and primitive returns. A later worker-spawn failure preserves the
already-started FIFO response prefix and is returned after all owned handles
are joined. A join or delivery failure stops later output while remaining
workers are still joined; the first recorded error is preserved. Primitive
successful join and send receipts derive completion of the entire started
prefix even when a later spawn failed. These receipts must be connected to the
same actual calls and output bytes by the source/IO bridge.

This finite cleanup and prefix result does not establish per-call Law8 for
every selected request after shared batch failures. The concrete external
`Processable` predicate and artifact-independent availability interpretation
must justify which calls a real shared failure impedes; the owner's failed
flag cannot define that condition. Semantic observations and both real-failure
predicates must also refer to the same actual global event times. Actual Rust atomic effects, integer
representation, classifier correspondence and OS/IO progress remain separate
bridges; finite individual EINTR returns alone do not establish termination.

## Complete chronological source

[`service/VERIFY.bend`](service/VERIFY.bend) checks the operational source
separately from the ordinary conditional composition above, under the same
pinned checkers and existing verification timeout. Its supplemental
[`ServiceLaws`](service/specification/ServiceLaws.bend) is an obligation for one
ordinary/prepared observer, not an inhabitant of that contract. The canonical
laws and their manifests are unchanged.

`Engine.run` computes each retained block from the same indexed request and
primitive returns through the real decode, dispatch, preparation, invalidation
and pure Core functions. It retains prior calls, pending phases, failures and
the exact database/response/registry snapshots. A real publication has both
its mutation fact and its core publication fact at the same instant.
`GeneratedBlocks` proves the connection to the same script job; a caller does
not supply a completed trace or choose the observed outcome.

`InitialBoot` proves the complete boot clause of Rule1 for any full event
history: the exact initial snapshot, the preceding instance-start event and
unique boot time/scenario. Its proof also excludes a forged boot through a
publication cofact, without assuming a history free of publications. This
establishes boot identity and ordering; the initial certificate and native
initialization correspondence are separate obligations.

The source is a finite prefix. Its delivery renderer does not yet represent
the native transition to a selected subsequent call as `NextCall`; complete
coverage of native observations remains an open correspondence obligation.
Prefix exhaustion does not establish progress.

The phase controls reject registration before receipt preparation, mutation
rollback after delivery or cleanup failure, erasure of an invalidation during
pending cleanup, and events after closure. Boot controls reject changed time
and response data. These checks do not complete the extended eight-law
witness, genuine progress, concurrent scheduling or recovery refinement.

## Optional administrator service timing

[`SERVICE_TIMING.md`](../tools/service/SERVICE_TIMING.md) specifies the opt-in
elapsed-service observer. It adds no quota policy, status, admission restriction
or application-state field. The ordinary serial eight-law composition above is
unchanged. The read-batch refinement retains its separately stated scope.

`Messages.principal_is_authenticated_id` and
`Messages.authentication_binds_principal_and_instance` connect the explicit
private principal prefix and certificate instance to the actual same
`Input.Analysis.Received` context. Both exclusive and concurrent-read consumers
use that format; identity is never parsed from generated source. These are
checked definitions of the native metadata emitter, not proofs of Rust timing,
the OS clock, log delivery or thread scheduling.

Exclusive timing completes at `publish_with_ready`, after durable and RAM
publication and before final inspection or delivery. Fatal returns before that
hook record the elapsed attempt once without acknowledging rollback. Read
workers stamp completion after validation, native execution, cleanup, proposal
checking and discarded duplicate state, before FIFO emission. Their independent
administrator writes also run for completed workers drained after a delivery
failure. The log mutex serializes record bytes; time waiting for it is excluded.
Controlled-clock and real-worker tests support these host contracts. Timing
supplies neither permission for an operation nor permission to publish a state.
