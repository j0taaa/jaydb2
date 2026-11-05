# Idempotency experiment

Base: `5925c57febd978d44fa24000233647a59e7898a6`.
Original reference: `9b751fab3c7c349ff473a2d11a7133573b6c4df2`.
Accepted integration prerequisite (next): persistence/preprocessing checkpoint
`83a9f3703345c234fe3b14363e6e14e15cb88b80`.

Implementation checkpoint; final verification and restart integration are still
pending. This paragraph will be replaced with actual final results.

## Supported behavior

Ordinary optional `library/Receipts.bend` provides bound input/version/result
lookup, a scalar full-row writer, and explicit operation-specific continuations.
No host admission/publication/authentication behavior is replaced. The actual
voucher application writes a business row and a separate immutable receipt row
in one call. Authenticated principal tables partition request IDs; prefixes
`r:`/`v:` partition receipts/effects. Exact canonical input includes the text
and cancellation flag. Operation `voucher.issue/v1` is stable across instances,
independent of prepared handles. Same input returns the small voucher ID only
after current authorization; changed input refuses. Principal registry access
is prohibited, so IDs cannot be deleted/reused even after retirement.

Explicit `retire` atomically deletes both rows and ends protection. Retention is
unbounded until retirement or the normal state ceiling. The example gate is
self-managed per principal: owners can disable/re-enable their own application
permission; hit and miss both consult its current value. No helper privilege,
receipt lock, arbitrary response cache, retry, cleanup worker or concurrency
protocol is introduced. Only existing scalar columns are used.

Examples and CLI: [application README](../../applications/vouchers/README.md).

```sh
flock /tmp/jaydb2-experiments-heavy.lock make test-idempotency
# After merging the accepted persistence prerequisite:
flock /tmp/jaydb2-experiments-heavy.lock python3 -B applications/vouchers/check.py --restart
```

## Laws, proofs and trust boundary

`ReceiptLaws.Rule` is an administrator-frozen semantic protocol refinement
law template, not a source allowlist. `Reachable`/`At` bind every actual prefix's
working state and operation/effect history to a reference execution.
`Closed`/`Success` require completed reference success before success is allowed.
Stable `State` constructively witnesses provenance from receipt-free initial
application tables through complete reference calls. `extend` proves preservation
by adding the actual transaction to the erased witness. `finalized` and
`finalize_equivalent` connect technical finalization without assuming final
validity. The witness is mathematical proof data; it is neither emitted as
runtime history nor persisted or replayed by the host.

The instantiated reference `Voucher` binds exact canonical input/version/result,
creates effect and receipt together, never rewrites live receipts, and allows
only paired retirement deletion. Its table initialization predicate leaves
registry values abstract; no private state is written to public checking files.
The existing task `Policy`/`Ownership`/`Proofs` foundation separately proves
principal ownership, registry nonaccess and actual per-operation permissions.
`ClientProof.program_safe`, `certify`, `trace`, `publication_cases` and the actual
`Bindings.certificate`/`Bindings.terminates` targets compose these properties at
all prefixes and final publication. Temporary effect/receipt mismatch is
permitted inside the specified path; incomplete paths cannot publish success.

The administrator must freeze a correct operation specification and initial
predicate. Arbitrary specifications do not acquire idempotency merely by using
the template. This is a serial/library extension under the existing host bridge,
not a new serial-host theorem. Native bytes, compiler/checker/runtime fidelity,
fresh authentication, publication, and persistence filesystem/flush assumptions
remain those of the existing contracts and accepted persistence prerequisite.
Storage hashes alone are neither authorization nor law-validity proofs.

## Validation record (checkpoint)

- Local `cargo build --locked --release`: passed under the shared lock.
- Bounded per-file official primary `--check-only`: new helper/law/model modules
  and the staged full application/proof/seed package passed after fixes.
- Python byte compilation and `git diff --check`: passed.
- Full primary+BendTT and native sessions are queued; no completed full-check
  claim is made at this checkpoint.

Functional model targets in `experiments/idempotency/VERIFY.bend` cover exact
hits, changed input, version conflict, unchanged hit state, actual second-write
data error and rollback, and state/response-size rollback. The native harness
adds distinct principals, current hit/miss permissions, cancellation after both
writes, explicit retirement/reuse, Unicode/delimiter/empty/64/65-ID boundaries,
forged/changed receipt bodies, foreign reads, permission bypass, principal
deletion rejection, actual technical-size rollback and optional real restart.
All temporary/build/storage paths are worktree-local. `.tools` points to the
shared immutable pinned official distribution; no toolchain change is made.

## Costs and limitations

A miss executes permission read, receipt-input read and two full-row writes.
A hit executes permission, input, operation and result reads. Retirement executes
one permission read and two deletes. Input is duplicated into the business row
and canonical receipt; total state is subject to the existing canonical ceiling.
The small result is a voucher key (at most 66 Unicode scalars), not an arbitrary
cached response. Default message/state/response limits remain 32768/65536/32768.
Performance is unmeasured; proof/check/compile cost is not a throughput claim.

The supplied app fixes Alice/Bob tables and freezes principal lifetimes; it
provides no principal-registration API, expiry clocks, opaque incarnation IDs,
external effects, mutable vouchers, or arbitrary multi-operation receipts.
Different operations must define their own stable identity, exact encoding,
result/permission policy and certified specification. Protection ends on
retirement; RAM mode ends it at process exit. Persistence mode adds restart
survival only in the accepted exact environment with protected storage. No
process-kill test establishes power-loss or hardware flush correctness.
