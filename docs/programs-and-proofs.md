# Write a program and its proof using the existing application patterns

A request contains Bend program source, Bend proof source, a credential and
arguments. The administrator's existing configuration determines which reads,
writes and working states are permitted. The tools in this guide package and
check applications; they do not change JayDB2, its protocol, laws, compiler or
checker.

Start with a [copyable starter](../examples/starter/README.md). It exports the
actual checked task application, so the first program already has useful
successful operations and a policy stronger than “deny everything.” Keep one
export unedited as a positive reference while changing a second copy.

## Find the smallest example for your operation

| You need | Copy/read | What you must still establish |
| --- | --- | --- |
| Read selected cells from your own row | `title_received` / `resume_title` and `title_safe` in exported CRUD `Client.bend` / `ClientProof.bend` | Every cell read is authorized; every typed return continuation is safe |
| Create or replace an owned row | `fields`, the `Save` branch and its `command_safe` branch | The table is the authenticated user's; the complete row carries the matching owner; structure and publication checks still succeed |
| Read, then update | `conclude_received`, `conclude_title` and `conclude_safe` | The read and possible write are each authorized, including the missing-row branch |
| Delete your row | `Remove` and its `command_safe` branch | The remove operation addresses the authenticated user's table |
| Refuse after provisional work | `Save{..., cancel}` / `saved` and `saved_safe` | Earlier reads/writes remain lawful; refusal does not excuse a forbidden prefix |
| Insert only if absent | Conditional profile `Insert`, `M.insert_if_absent`, `inserted_safe` | Existence observation is authorized; the true-write continuation supplies a lawful owned row |
| Replace when a cell matches | Conditional `Replace` / `Cas`, `M.replace_if` / `M.compare_exchange`, and `replace_safe` / `cas_safe` | Both the tested read and any full-row write obey the same ordinary permissions |
| Visit a finite collection | Conditional `visit_safe`, `reads_safe`, `G.write_rows` | A permission for every actual access and a depth witness covering the entire continuation |
| Deduplicate a business operation | [Voucher application](../applications/vouchers/README.md), `Receipts` and `ReceiptLaws` | Current result permission, exact identity/operation/input binding, receipt policy and business effect in the same transaction |

`M.compare_exchange` is an optional ordinary program helper. It reads a selected
cell and conditionally writes the supplied full row within the existing
transaction. It adds no atomic primitive, hidden index, privilege or lock.

The supplied ownership policy permits only the authenticated person's table and
requires stored row owners to match that person. Do not copy the reflexivity
proof `{==}` into an unrelated access: it works in these branches because the
operation was deliberately constructed with the same `id` as the authenticated
context. An operation on a different table needs the actual administrator's
permission, which this policy will not grant.

## A useful edit loop

1. Export `crud` for basic operations or `conditional` for query/mutation helpers.
   Run the unedited template's complete check first.
2. Change the argument parser and `Client.command` for the operation you want.
   Keep all database access explicit as `S.Access` or existing ordinary helpers.
3. Add the corresponding `command_safe` branch. Each access provides its real
   `P.Allowed` proof and a proof for **every** typed continuation result. For a
   row write, construct the entire correctly typed, correctly owned row.
4. Reuse the supplied `certify` composition. It connects local permissions to
   every actual execution prefix, the owner-preserving working state and the
   actual final publication obligation. It does not assert a desired final
   state as a new premise.
5. Adjust the finite depth witness only when your longest complete action path
   changes. The supplied CRUD witness is `3n`; the conditional witness is `5n`.
   These are proofs of finite action depth, not time, memory or server quotas.
   Collection helpers use structural finite-list recursion, not a general
   higher-order `Action.bind` rejected by the pinned termination checker.
6. Regenerate the prepared wrapper if you changed `ClientProof.bend`, then check
   the exact current source again. The ordinary and universal targets differ:
   the latter quantifies over every context/argument pair and does not capture
   a particular request. See the wrapper commands below.
7. Exercise a successful operation, a legitimate refusal/missing case, a second
   identity and an attempted unauthorized access. After each failed admission
   or refusal, verify the previously published data remains.

The starter's `check.py` checks the supplied program **universally**, not just
`null` arguments that select an empty refusal branch. It also performs actual
admission/native requests against the host-generated target and live public
configuration. The temporary pure-check environment is a development fixture;
it is never substituted for a running database's environment or private state.

After editing the ordinary proof, update just the prepared wrapper explicitly:

```sh
python3 - <<'PY'
from pathlib import Path
import sys
sys.path.insert(0, 'examples/starter')
from create import universal_proof
app = Path('build/my-tasks')
(app / 'PreparedProof.bend').write_text(universal_proof((app / 'ClientProof.bend').read_text()))
PY
```

That transformation only changes the final `B.certificate` binder/application:

```bend
# Ordinary concrete request:
def B.certificate(s, valid, identity, n):
  certify(I.context(), I.arguments(), B.code(), s, valid, identity, n)

# Preparation: same lemma, universally quantified request inputs:
def B.certificate(ctx, args, s, valid, identity, n):
  certify(ctx, args, B.code(), s, valid, identity, n)
```

This is not a general proof generator. If your proof captures concrete
`Instance.context()` / `Instance.arguments()` elsewhere or otherwise does not
establish the universal target, changing this wrapper cannot make it valid.
Preparation runs the normal independent administrator and termination checks.

## Know what the reusable proof establishes

The task proof establishes administrator-law compliance across the actual
prefixes, preservation of its owner invariant and the required publication and
termination properties. It does not prove every functional claim one might
make about the application. The example sessions separately check that saves,
reads, conditional updates and deletes return their specified results. If an
application needs a mathematical functional theorem, state and prove that
additional contract rather than inferring it from “the safety certificate
checks.” The library documents the scope of its [own helper
proofs](../library/README.md).

A modified source must be admitted with a proof for that actual source. Some
proofs legitimately cover more than one source implementation; the important
negative control changes an access or owner that violates the installed law.
The starter confirms that those edits fail at actual proof obligations, rather
than because a dependency is missing or a parser failed.

## Receipts stay an application concern

For idempotency, reuse the existing [voucher flow](../applications/vouchers/README.md)
as a separate recipe. The caller supplies a request ID; the operation compares
its exact bound inputs and returns the retained result on a receipt hit. The
application laws constrain creation, mutation and paired retirement. A receipt
helper alone cannot constrain unrelated admitted programs.

Keep the receipt and business effect in the same ordinary transaction, check
current permission to read a retained result, and choose an explicit retention
policy. Deleting/retiring a receipt ends its deduplication protection. The
example uses fixed principal identities; applications allowing identifier reuse
must define a suitable principal-incarnation or equivalent namespace policy.
Persist the database for restart survival. Prepared handles themselves remain
instance-local and must be prepared again explicitly after restart.

The TypeScript client returns ordinary refusal/authentication/certificate
responses as responses. A transport failure may leave the commit outcome
unknown. It does not silently retry writes; retry only an operation whose
application-level receipt protocol makes the retry appropriate.
