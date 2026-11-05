# Composition of the eight laws

[ContractService.bend](ContractService.bend) constructs exactly
`LAWS.Contract(a,k)`, composing all eight current laws for the Bend kernel and
its serial protocol. It neither changes the laws nor receives their
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
integration contracts, the kernel and protocol satisfy the eight laws**.
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

## Prepared-program adapter

`PreparedPrograms.bend` checks the universal-certificate specialization and
uses the actual `src/Prepared.bend` resolver invoked by prepared workers. It
proves preservation of current authentication, state, context and arguments,
and derives faithful preparation/valid publication through `Call` and `Core`.
The proof supplies neither final validity nor permission to publish as a premise.

The ordinary eight-law composition above is unchanged. Prepared control frames
and metadata receipts are an explicit interface extension, not ordinary
`Semantics.Response` events. For prepared transactions the pure model consumes
the resolved logical request. `Interface.RequestReceived`'s ordinary encoding
equation does not hold for the raw handle body. Binding that body and its full
physical size to the stored original source/proof, as well as registration,
invalidation and receipt delivery, remains a host refinement contract supported
by focused real tests. The normalization proof does not claim to mechanize the
whole Rust registry or extend the old raw-protocol theorem silently.
