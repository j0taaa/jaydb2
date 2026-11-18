# Prepared programs (optional protocol extension)

An instance can check and compile arbitrary client Bend source with a universal
certificate once, then execute it in persistent native workers.
The ordinary four-field submission and its concrete proof remain supported.
There is no transaction catalog, alternate checker, or modified runtime.

## Wire and lifecycle

Ordinary bodies remain canonical encoded records with exactly `arguments`,
`code`, `credential`, and `proof`. An extended body is `0x07 || opcode || record`,
where `record` is the same canonical four-field record, without another length
prefix. The outer frame is `u64be(full_body_byte_length) || full_body`.
The checked dispatcher/controller checks the full actual prefixed body against the message limit before
routing it; the extra two bytes count. Tag 7 is reserved for this explicit
extension and is outside the ordinary Value encoding. Unknown/truncated opcodes
return `input`. Ordinary malformed records remain malformed.

| Opcode | Meaning of `code` | `proof` | `arguments` | Result |
| --- | --- | --- | --- | --- |
| 0 prepare | Original source | Universal proof source | Public value, ignored | `prepared`, value = handle |
| 1 execute | Handle | Empty string | Actual call arguments | Ordinary transaction response |
| 2 invalidate | Handle | Empty string | Public value, ignored | `invalidated`, value = null |

All three operations authenticate the actual credential against current
published state before admission, semantic handle resolution, or invalidation.
Handles are bearer capabilities: anyone holding a handle may execute it, but
every execution re-authenticates and runs the universally certified program
under the caller's identity.
A handle grants no actor identity; another authenticated user can execute the program under
their own context. Unknown, invalidated, and other-instance handles return
`failure`; nonempty handle-call proofs and malformed opcodes return `input`.
These are protocol/control failures, not mathematical proof rejections. An
invalid credential returns `authentication` before semantic handle
resolution/proof-field validation. Malformed inner records are rejected before
authentication. Control failures leave the published state/response pair
unchanged. Invalidation removes the registration before deleting its directory;
if cleanup fails, the checked `invalidated` receipt is still returned and
the cleanup error is logged.

`prepared` and `invalidated` are **control metadata receipts**, outside
`Semantics.Status`. They do not execute a transaction, publish working state,
or replace the host's published state/response pair. Their canonical encoded
bodies obey the response limit: `prepared` with a 64-character handle is 128
bytes, and `invalidated` is 59 bytes, excluding the outer length. Receipt size
is checked before either registry mutation and, for preparation, before sealing
the admitted artifacts. If a receipt exceeds the limit,
`limit` is returned with no registration/invalidation or publication. This
includes configurations whose fixed errors fit but whose handle receipt does
not; the rejected preparation need not leave a sealed artifact behind. Handle
IDs use host-supplied random 256-bit candidates, encoded as 64 lowercase
hexadecimal characters. `Control` checks the shape and rejects a candidate
already live or ever allocated, including an invalidated handle. Entropy is
not an authority or a fairness assumption; a collision returns `failure`.
The registry and allocated-handle history are instance-local and in memory.
They disappear on instance exit. Migration retires the live registrations
and retains allocated-handle history. Losing a receipt does not roll back a
registration or invalidation.

The client supports `--prepare --code FILE --proof FILE --credential TOKEN`,
`--handle HANDLE --credential TOKEN --arguments JSON`, and
`--invalidate HANDLE --credential TOKEN`. Python callers can use
`prepared_frame(opcode, code_or_handle, credential, arguments=None, proof='')`.
Responses use the normal frame decoder. Keep the same server session open.

## Checked controls

`src/Control.bend` implements prepare/invalidate as a pure plan followed by a
registry delta. `ControlTheorem` (`proof/ControlClauses.bend`) proves current
authentication, the exact universal admission tuple, candidate freshness,
exact bounded receipt preparation, the specified delta, and preservation of
the database root and last published response pair. Denials keep the registry.
`ControlHistory.service_fold_theorem` extends finite runs with controls:
transactions preserve the registry, controls preserve the root, every reached
root stays valid, and live lookups have accepted-prepare provenance.
Scoped removal eliminates the named lookup; allocated history prevents revival.

Initialization/recovery compile a separate native control executable through
the same official checked-Book mechanism as other service programs.
`ControlBridge.packet` receives the original body, an authentication
projection from the snapshot and the full registry. It calls `Control.control`
and serializes the result. For preparation, Rust supplies the exact source,
proof and certificate mode from completed admission, plus an entropy candidate.
Bend compares the tuple with the decoded request. Preparation stages and
compiles against a pinned environment in a separate pool. Installation is
exclusive and requires the same epoch, registry and authentication view.
If they changed, the host discards the registration and returns `failure`.
Invalidation runs exclusively. Rust installs the checked registry delta,
manages the artifact and forwards the receipt.
No registry/certificate/receipt decision is inferred from public status text.
The same executable accepts canonical private text error codes. Rust separately
supplies `HANDLE` and `PREPARED_INTEGRITY` during startup and memoizes their
checked replies by exact code. `HostErrorReplyTheorem` states that emitted bytes
equal `Messages.error(HostErrors.status(code))` for every root/last/registry.
These entries therefore remain valid for later roots without another child,
including with the controller offline. Other observed codes (including `HOST_IO`)
use their own entry or invoke the controller with that exact code.
The theorem also proves unchanged root/last response/registry and bounded
framing. Map availability and physical integrity observations, exact code
and cache forwarding, and stopping before artifact execution remain trusted
host obligations. Startup fails if either prefilled denial cannot be computed.
If the denial executable or transport fails for an uncached code, the host emits
the technical fallback with an explicit stderr diagnostic and never memoizes it.
The 17-code certificate table specifies the contract; no theorem equates it to
the Node tools' proof-rejection codes (`ORACLE_PROOF`, `ADT` and `INSTANCE_MATCH`
map to `failure`). Prefilled denials need no controller launch. Artifact
integrity and physical cleanup remain host obligations.

## Proof target and capture boundary

Only a host manifest with `certificateMode: 'universal'` enables preparation.
The exact host-generated target (binder names `ctx` and `args`) is:

```bend
law certificate:
  @ctx: D.Context -> @args: D.Value ->
    R.Certifies(I.config(), code(), Client.program(), ctx, args)

law terminates:
  F.ProgramTerminates(I.config(), Client.program())
```

`Certifies` still quantifies over every valid compatible initial state, present
context, and execution prefix. All eight administrator/technical obligations
retain their meaning, including all observations before refusal. Termination
already quantifies over states, contexts, and arguments. An implementation
starts `def B.certificate(ctx, args, s, valid, identity, n): ...`.
Concrete-only certificates cannot be reused through this route. Their existing
per-call target and behavior remain unchanged.

Both official primary checking and original BendTT run on the pure closure and
the executable closure, with identical dependencies and certificate mode.
The exact checked Book goes to the official C compiler. The original source
must equal the AST literal `Bindings.code`, and universal proof source must
equal the AST literal `Bindings.proof_source`; these checks are additional to hashes,
not a claim that hashes prove semantic linkage. No metas, axioms, unsafe code,
foreign capabilities, or unregistered dependencies are admitted.

The universal client closure may not reach `Instance.context` or
`Instance.arguments`, even in types, erased terms, unused helpers, library
aliases, or checked specializations. The reference graph is audited before
and after checking and tracks specialization origins. The generated Instance
contains only public preparation metadata and configuration; it contains no
seed/current state. A universal proof must use its quantified parameters, and
the compiled body must obtain per-call context/arguments through `S.start`.

## Stored identity and actual execution

The Rust registration owns its temporary directory, executable path/hash,
immutable original source bytes, universal proof bytes, and hashes of the
prepared files and frozen public/runtime environment. The directory retains
the exact dependencies, manifests, bindings, emitted C and native artifact.
Before spawning a worker, the host checks that sealed files remain regular
and byte-identical. Warm CPU workers reuse their validated, loaded executable.
CUDA also checks sealed bytes before and after each exchange. The host starts
workers on demand and keeps at most one idle worker per execution slot across
all handles. It evicts the least recently used idle worker when the pool is
full. Invalidation and migration retire the affected workers.

For raw execute request `r` and registration `p`, the resolved logical request
is `{code:p.original_code, proof:p.universal_proof,
credential:r.credential, arguments:r.arguments}`. The host sends the
original prepared request body and a registry projection containing only the
controller-issued entry for that handle. The checked worker decodes the
body, asks the host for the user matching the credential, and authenticates
that row before resolving the handle. It binds the resolved source and proof
to the loaded artifact and runs with the current context and arguments.

The normal authenticated execute path uses the host credential index to
locate the artifact. Other request shapes may use the checked preprocessing
helper. Prepared execution uses no checker or compiler. The persistent worker
exchanges data operations with the host using the attempt's snapshot and
private writes. The host validates and publishes the result. A conflict may
rerun the request on a new snapshot. Refusal and worker failure discard
the private writes.

## Evidence and scope

`make test-integration` includes real universal preparation against the access
example's per-user credential read/write law, successive argument/user/state
changes, refusal/native failure rollback, invalidation and other-instance
rejection, original-file changes, sealed source/dependency/native/tooling
tampering, and concrete/invalid proof, captures, foreign capability and missing
dependency rejection. Its causal gate disables Node after successful real
preparation: handle executions still work without attempting Node, while an
ordinary submission reaches that disabled gate and fails. Admission tests
also exercise exact universal targets/source linkage and transitive captures.

`src/Remote.bend` implements the active direct and prepared entries.
[The remote refinement proofs](../../proof/README.md#live-worker-refinement)
cover its data exchanges under faithful host replies. The separate
`proof/PreparedPrograms.bend` checks the reference source/proof resolution,
authentication, certificate specialization and Core publication lemmas.

`contract/PreparedProtocol.bend` specifies prepared prefixes, valid physical
reception and exact receipt encodings. `contract/PreparedRegistry.bend` retains
the scoped lookup used by `src/Resolve.bend`. `UnifiedCoreTheorem` applies the
four Core clauses to the exact selected request or gives a bounded denial.
Registered selection authenticates against current state before lookup and
requires empty raw proof. T1 binds cached universal certification/termination
to the exact loaded program/artifact and specializes it at current context
and arguments. `proof/PreparedWire.bend` checks full-prefixed reception and
receipt sizes; `PreparedPrograms` retains pure resolution/specialization and
actual Core preparation/publication lemmas.

`ControlTheorem` covers prepare/invalidate decisions, exact bounded receipts
before mutation, lifetime freshness and scoped registry changes. The mixed
service fold preserves root validity and accepted-admission lookup provenance.
Artifact integrity, T1 admission-result delivery, forwarding the selected
live entry and physical receipt delivery remain integration obligations. The
[proof guide](../../proof/README.md) lists T1–T3 and the native worker bridge.
