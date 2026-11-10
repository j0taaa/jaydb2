# Certified receipt example

Run from the checkout root (after `make build`):

```sh
flock /tmp/jaydb2-experiments-heavy.lock python3 -B applications/vouchers/check.py
```

The Python file packages public Bend dependencies and exercises the actual host;
all decisions, effects, permission checks and proofs are Bend. It reuses the
existing task ownership foundation rather than importing another experiment.

Calls use the ordinary credential/code/proof/arguments protocol. Arguments:

- `["issue", "request-1", "coffee", false]`: create voucher `v:request-1` and
  immutable receipt `r:request-1` in the authenticated principal's own table.
  The small result is `"v:request-1"`. The ID may contain arbitrary Unicode
  (including delimiters and the empty string), up to 64 Unicode scalars.
- Repeat the same request/input: return that result after current permission
  and exact input/operation checks. Another input or cancellation flag refuses.
- `["inspect", "request-1"]`: inspect the actual voucher's original text input.
- `["issue", "cancelled", "coffee", true]`: perform the real two writes, then
  refuse. Neither row is published.
- `["retire", "request-1"]`: explicitly remove both voucher and receipt in one
  transaction. This ends protection of the ID; a later issue is a new lifetime.
- `["permission", false]`: disable one's own application access. Even receipt
  hits now refuse. Owners may explicitly re-enable via `["permission", true]`.
  This simple self-managed demonstration gate is independent of host identity.

Alice and Bob have separate tables and public demonstration credentials
`alice-token` and `bob-token`. Receipt lookup is always by authenticated context
ID plus caller request ID. `r:` and `v:` prefixing are disjoint injective key
encodings within a principal table; no concatenated multi-principal key exists.
The canonical input is `0:` or `1:` followed by the exact text input (false/true
cancellation flag). No Unicode normalization or hashes are used. The frozen
operation identity is `voucher.issue/v1`; prepared handles play no role.

`library/Receipts.bend` is the reusable optional helper: `bound(owner, key,
operation, canonical_input, missing_action, result_continuation)` performs actual
input/operation/result reads. The caller supplies an operation-specific result
handler and business action. `put` performs one ordinary full-row write.
Helpers confer no permissions, make no hidden transactions, and do not cache
arbitrary responses. A new operation must supply its own canonical encoding,
small scalar receipt schema, miss/result actions and administrator laws/proof.
Current authorization belongs before the lookup, never to a cached response.

The administrator freezes `Voucher.bend` as the reference protocol. The
`ReceiptLaws.Rule` template requires actual prefix state/events to refine that
protocol and requires completed reference success before a success response.
Its stable-state law constructively witnesses provenance from receipt-free
application tables through complete reference calls. The witness is an erased
proof, not an executed retry log, saved history, or runtime replay mechanism.
Registry values remain abstract proof variables; credentials/private state are
never copied into public verification files. Existing ownership laws apply to
all operations, including failed/filtered reads and eventual refusals. They
also forbid every registry access/write; this deployment's principal IDs can
never be deleted or reused. No receipt locks or new host privilege exist.

Business and receipt rows may temporarily differ after the first write or
retirement delete. Only the complete specified path can publish success.
Other programs can be certified if they prove the same observable protocol;
a bare final-state assertion cannot authorize early reads or incomplete writes.
Retention is explicit and unbounded until retirement or the ordinary state size
limit. There is no expiration clock, cleanup worker, retry loop, response cache,
concurrent host protocol or guarantee after retirement. Restart protection uses the accepted persistence extension and protected
authoritative state. Run the real create/open receipt check with:

```sh
flock /tmp/jaydb2-experiments-heavy.lock python3 -B applications/vouchers/check.py --restart
```

Open uses the same frozen environment/controller and no seed.

## Checked lifetime proofs

`proof/VERIFY.bend` checks an independent bidirectional invariant over every
request ID and principal table. The actual frozen reference preserves it for
all execution fuels and complete replay histories, including real cancellation
writes followed by rollback, retirement and permission changes. The proofs also
establish exact live-hit reads/results and input/cancellation conflict refusal.
The existing seed and actual installed configuration laws imply the invariant.

`check.py` runs both official proof modes and 56 deliberate false-proof controls
in one temporary copy of the public namespace, then checks the original complete
native certificate. Application verification files stay under `proof/` and are
not copied into the runtime package. `ReceiptLaws.State` is existential reference
reachability; these results do not establish actual observed request/history
provenance or a complete native service proof.

## Lost-response recovery check

Run the focused durability test under the common heavy lock:

```sh
flock /tmp/jaydb2-experiments-heavy.lock make test-idempotency-recovery
```

It kills the opt-in fault-build service after the issue/receipt pair is durable
but before a response, then performs a seed-free reopen, identical retry and
conflicting reuse check. A native trace oracle on the recovered bytes verifies
the receipt-hit path performs no business/receipt writes, with a fresh-state
positive write control. Hooks are absent from normal builds.
