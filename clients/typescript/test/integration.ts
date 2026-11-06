/** Real ordinary/prepared gate. Caller owns the common heavy-work lock. */
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { Client } from '../src/index.ts';
import type { Response } from '../src/index.ts';

const root = resolve(process.env.JAYDB_ROOT ?? fileURLToPath(new URL('../../../', import.meta.url)));
const example = join(root, 'examples/access');
const code = readFileSync(join(example, 'Client.bend'), 'utf8');
const proof = readFileSync(join(example, 'ClientProof.bend'), 'utf8');
const oldTarget = 'def B.certificate(s, valid, identity, n):';
assert.ok(proof.includes(oldTarget), 'Existing access-example proof target changed; review the fixture adapter');
// Identical fixture adaptation to tests/service/test_prepared.py. Only the
// certificate wrapper becomes universal; actual ordinary permission proof and
// program remain unchanged and both official checkers still verify the target.
const universal = proof.replace(oldTarget,
  'def B.certificate(ctx, args, s, valid, identity, n):\n  +ctx = ctx\n  +args = args')
  .replaceAll('I.context()', 'ctx').replaceAll('I.arguments()', 'args');
const active = new Set<Client>();
const watchdog = setTimeout(() => {
  console.error('TypeScript native test exceeded its development-only 5 minute watchdog');
  for (const client of active) client.abort();
}, 300_000);
watchdog.unref();
let checked = 0;
function expect(actual: Response, status: Response['status'], value: Response['value']): void {
  assert.deepEqual(actual, { status, value }); checked++;
}
function open(): Client {
  const client = Client.spawn({ command: join(root, 'jaydb2'), cwd: root,
    args: ['--configuration', join(example, 'Configuration.bend'), '--seed', join(example, 'Seed.bend'), '--threads', '1'] });
  active.add(client); return client;
}

try {
  const client = open();
  let handle = '';
  try {
    expect(await client.request({ credential: 'alice-token', code, proof, arguments: 'alice-from-ts' }), 'success', 'alice-from-ts');
    const prepared = await client.prepare({ credential: 'alice-from-ts', code, proof: universal });
    assert.equal(prepared.status, 'prepared'); assert.equal(typeof prepared.value, 'string');
    handle = prepared.value as string; assert.match(handle, /^[0-9a-f]{64}$/); checked++;
    expect(await client.execute({ credential: 'bob-token', handle, arguments: 'bob-from-ts' }), 'success', 'bob-from-ts');
    const replies = await Promise.all([
      client.execute({ credential: 'alice-from-ts', handle, arguments: 'alice-next' }),
      client.execute({ credential: 'alice-from-ts', handle, arguments: 'must-not-publish' }),
    ]);
    expect(replies[0]!, 'success', 'alice-next'); expect(replies[1]!, 'authentication', null);
    expect(await client.execute({ credential: 'alice-next', handle, arguments: 9223372036854775807n }), 'refusal', 'cancelled');
    expect(await client.execute({ credential: 'alice-next', handle, arguments: null }), 'refusal', 'cancelled');
    expect(await client.execute({ credential: 'alice-next', handle, arguments: 'alice-final' }), 'success', 'alice-final');
    expect(await client.invalidate({ credential: 'alice-final', handle }), 'invalidated', null);
    expect(await client.execute({ credential: 'alice-final', handle, arguments: 'never' }), 'failure', null);
  } finally {
    await client.close(); active.delete(client);
  }
  const restarted = open();
  try {
    expect(await restarted.execute({ credential: 'alice-token', handle, arguments: 'old-instance' }), 'failure', null);
  } finally {
    await restarted.close(); active.delete(restarted);
  }
  console.log(`PASS: TypeScript client checked ${checked} real ordinary/prepared responses, fresh identities, refusal rollback, invalidation and instance-local handles.`);
} finally {
  clearTimeout(watchdog);
  for (const client of active) client.abort();
}
