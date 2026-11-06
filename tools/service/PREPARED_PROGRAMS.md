# Prepared programs (optional protocol extension)

An instance can check and compile arbitrary client Bend source with a universal
certificate once, then execute its frozen official native executable repeatedly.
The ordinary four-field submission and its concrete proof remain supported.
There is no transaction catalog, alternate checker, or modified runtime.

The user authorized the additive prepared contract on 2026-11-06. Its wire,
registry and control obligations supplement the unchanged eight core laws;
the legacy ordinary-wire aggregate does not automatically prove this interface.

## Wire and lifecycle

Ordinary bodies remain canonical encoded records with exactly `arguments`,
`code`, `credential`, and `proof`. An extended body is `0x07 || opcode || record`,
where `record` is the same canonical four-field record, without another length
prefix. The outer frame is `u64be(full_body_byte_length) || full_body`.
The host checks the full actual prefixed body against the message limit before
routing it; the extra two bytes count. Tag 7 is reserved for this explicit
extension and is outside the ordinary Value encoding. Unknown/truncated opcodes
return `input`. Ordinary malformed records remain malformed.

| Opcode | Meaning of `code` | `proof` | `arguments` | Result |
| --- | --- | --- | --- | --- |
| 3 prepare read | Original source | Universal proof plus whole-program read proof | Public value, ignored | `prepared`, value = handle |
| 0 prepare | Original source | Universal proof source | Public value, ignored | `prepared`, value = handle |
| 1 execute | Handle | Empty string | Actual call arguments | Ordinary transaction response |
| 2 invalidate | Handle | Empty string | Public value, ignored | `invalidated`, value = null |

All four operations authenticate the actual credential against current
published state before admission, semantic handle resolution, or invalidation.
The read scheduler may inspect a candidate registration before authentication
to classify a batch; that lookup grants no execution authority. A handle grants
no actor identity; another authenticated user can execute the program under
their own context. Unknown, invalidated, and other-instance handles return
`failure`; nonempty handle-call proofs and malformed opcodes return `input`.
These are protocol/control failures, not mathematical proof rejections. An
invalid credential returns `authentication` before semantic handle
resolution/proof-field validation. Malformed inner records are rejected before
authentication. Control failures leave the published state/response pair
unchanged. Invalidation removes the registration before deleting its directory;
if that cleanup fails, the host returns `failure` and the handle remains removed.

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
IDs are random 256-bit strings, encoded as 64 lowercase hexadecimal characters,
in an instance-local in-memory map;
they do not survive instance exit. Losing a receipt does not roll back a
registration or invalidation, and this interface has no deduplication.

The client supports `--prepare --code FILE --proof FILE --credential TOKEN`,
`--handle HANDLE --credential TOKEN --arguments JSON`, and
`--invalidate HANDLE --credential TOKEN`. Python callers can use
`prepared_frame(opcode, code_or_handle, credential, arguments=None, proof='')`.
Responses use the normal frame decoder. Keep the same server session open.

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
All sealed existing files must remain regular and byte-identical on reuse;
missing/changed artifacts return a technical `failure` before execution. An
artifact integrity failure does not establish that the original certificate
is mathematically invalid. Original administrator/client
input paths may change after freezing without affecting the instance.

For raw execute request `r` and registration `p`, the resolved logical request
is `{code:p.original_code, proof:p.universal_proof,
credential:r.credential, arguments:r.arguments}`. **The handle is never the
executed source identity.** The worker receives a private packet consisting of
current state bytes plus the decoded ordinary raw handle request (the control
prefix is removed). Its existing `Input.analyze` authenticates that credential
again and obtains context from this same state. The checked
`Prepared.resolve_analysis` then replaces only code/proof with the exact frozen
`Bindings.code()` and `Bindings.proof_source()` literals. It preserves the
state, credential, context and arguments, and leaves rejections unchanged.
The entry passes those actual arguments
to `E.start(Client.program(), ctx, arguments, state)`. Its compiled
`Client.program` is the original admitted AST. The code/proof fields of that
raw handle request select no Bend function and supply no runtime capability.
The universal certificate specializes to this actual context/arguments/state,
with the registration's original source identity.

No checker, BendTT, Node staging helper, or C compiler runs on prepared
executions. The existing native authenticator still emits public metadata
strings; handle calls discard these instead of writing/checking sources.
Host integrity hashing still runs, and native
authentication/execution children run normally. The authenticator itself
decodes first; there is no separate decode child. Both children remain fresh
processes, and the execution child retains its own current input analysis.
The private worker
proposal is accepted only after complete output, child exit, transport/size
checks, and the ordinary atomic publication step. A later refusal or native
failure preserves the previous published root. The admitted directory stays
alive until invalidation or instance exit rather than being deleted per call.

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

`src/Prepared.bend` is used by the universal entry, while ordinary submissions
keep their original entry. `proof/PreparedPrograms.bend`, included in the
general aggregate, proves source/proof resolution, preserved current
authentication/state/context/arguments, specialization of the universal
certificate, and faithful preparation/valid publication using the actual Core
functions. Its premises include the current state and actual execution result;
they do not assume final-state validity or publication permission.

The additive contract is defined in `contract/PreparedProtocol.bend`,
`contract/PreparedRegistry.bend` and `contract/PreparedLaws.bend`.
`PreparedProtocol.Received` binds valid actual reception to the exact prefixed
canonical bytes and full physical message limit. `PreparedLaws.Ready` binds a
call to fresh authentication, exact original source/proof, universal admission,
the fixed read certificate for read-marked entries, and current per-call
artifact validation. `ControlOutcome` specifies exact authorized registry
deltas and unchanged published pairs, including receipt limits, unknown-handle
errors and cleanup failure after invalidation. The additional `ControlLaw`
requires those obligations for all actual control observations; the fixed
environment must account for every result and registry mutation, including
lost delivery.

`proof/PreparedWire.bend`, `proof/PreparedExtension.bend` and
`proof/PreparedControls.bend` add general/model proofs of the wire relations,
resolver/admission connection and control transitions. They cover exact receipt
encoding, fresh registration, invalidation, receipt overflow and authorized
outcomes without supplying the outcome as a premise. The existing
`PreparedPrograms` adapter continues to cover the logical transaction through
the actual Core functions.

The ordinary eight-law composition remains ordinary-wire only: tag 7 was
previously malformed and control receipts are outside `S.Status`.
`Interface.RequestReceived` must not be applied directly to a raw handle body
as if it contained source text. General/model proofs do not establish the
complete actual `ControlLaw`, physical receipt-before-mutation ordering, or
the Rust/Node/C, compiler and OS bridge. These remain explicit obligations
supported by review and tests; hashes alone do not prove them. Official
fragment/translation and physical failure limitations remain. This extension
adds no runtime, quota, deadline or persistent prepared handles. Optional
database-state persistence is provided separately.

The optional [certified read-batch extension](READ_BATCHES.md) adds opcode 3;
ordinary preparation and execution retain their original certificate requirements.
