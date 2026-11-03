# Prepared programs (optional protocol extension)

An instance can check and compile arbitrary client Bend source with a universal
certificate once, then execute its frozen official native executable repeatedly.
The ordinary four-field submission and its concrete proof remain supported.
There is no transaction catalog, alternate checker, or modified runtime.

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
| 0 prepare | Original source | Universal proof source | Public value, ignored | `prepared`, value = handle |
| 1 execute | Handle | Empty string | Actual call arguments | Ordinary transaction response |
| 2 invalidate | Handle | Empty string | Public value, ignored | `invalidated`, value = null |

All three operations authenticate the actual credential against current
published state before admission, lookup, or invalidation. A handle grants no
actor identity; another authenticated user can execute the program under their
own context. Unknown, invalidated, and other-instance handles return
`failure`; nonempty handle-call proofs and malformed opcodes return `input`.
These are protocol/control failures, not mathematical proof rejections. An
invalid credential returns `authentication` before handle lookup/proof-field
validation. Failure
leaves published state unchanged. Invalidation removes the registration/files.

`prepared` and `invalidated` are **control metadata receipts**, outside
`Semantics.Status`. They do not execute a transaction, publish working state,
or replace the host's published state/response pair. Their canonical encoded
bodies obey the response limit: `prepared` with a 64-character handle is 128
bytes, and `invalidated` is 59 bytes, excluding the outer length. Receipt size
is checked before either registry mutation. If a receipt exceeds the limit,
`limit` is returned with no registration/invalidation or publication. This
includes configurations whose fixed errors fit but whose handle receipt does
not. Handle IDs are random 256-bit strings in an instance-local in-memory map;
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
decode/authentication/execution children run normally. The private worker
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

The old protocol aggregate does not automatically prove this extension: tag 7
was previously malformed and control receipts are outside `S.Status`. The
normalization/specialization adapter covers the logical transaction; physical
prefix dispatch, registry identity/lifecycle and receipt delivery remain
explicit host integration contracts. In particular, the ordinary
`Interface.RequestReceived` equation must not be applied directly to a raw
handle body as if it contained the source text.
The Rust/Node/C bridge and compiler semantic preservation remain an explicit
trusted boundary supported by review/tests, not a mechanized proof of the
complete executable. Official fragment/translation and physical failure
limitations remain. There is no new runtime, quota, deadline, or persistence.
