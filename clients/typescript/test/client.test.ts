import test from 'node:test';
import assert from 'node:assert/strict';
import { PassThrough, Writable } from 'node:stream';
import childProcess from 'node:child_process';
import { syncBuiltinESMExports } from 'node:module';
import { fileURLToPath } from 'node:url';
import { Client, TransportError, ProtocolError, frame, unframe } from '../src/index.ts';
import type { Value } from '../src/index.ts';

const fixture = fileURLToPath(new URL('./fixture.ts', import.meta.url));
const request = (arguments_: Value = null) => ({ code: 'program', proof: 'proof', credential: 'token', arguments: arguments_ });
function pair(options: { maxResponseBytes?: number; maxPendingRequests?: number } = {}) {
  const input = new PassThrough(); const output = new PassThrough();
  const client = new Client({ input, output, ...options });
  return { input, output, client };
}

test('fragmented and coalesced responses preserve FIFO and canonical failure responses', async () => {
  const { input, output, client } = pair();
  const writes: Buffer[] = []; input.on('data', chunk => writes.push(chunk));
  const results = [client.request(request(1)), client.prepare({ ...request(), readOnly: true }), client.execute({ credential: 'other', handle: 'h', arguments: 'x' }), client.invalidate({ credential: 'other', handle: 'h' })];
  assert.deepEqual(unframe(writes[0]!), { ...request(1n) });
  assert.equal(writes[1]![8], 7); assert.equal(writes[1]![9], 3);
  assert.equal(writes[2]![9], 1); assert.equal(writes[3]![9], 2);
  const responses = [{ status: 'success', value: 1n }, { status: 'authentication', value: null }, { status: 'refusal', value: 'cancelled' }, { status: 'failure', value: null }];
  const bytes = Buffer.concat(responses.map(frame));
  for (let start = 0; start < 18; start++) output.write(bytes.subarray(start, start + 1));
  output.end(bytes.subarray(18));
  assert.deepEqual(await Promise.all(results), responses);
  await client.close(); await client.close();
  await assert.rejects(client.request(request()), TransportError);
});

test('a request validation failure writes no bytes', async () => {
  const { input, output, client } = pair(); let writes = 0; input.on('data', () => writes++);
  assert.throws(() => client.request(request(2 ** 60)), /bigint/);
  assert.throws(() => client.request({ ...request(), credential: 1 as unknown as string }), /strings/);
  assert.equal(writes, 0); output.end(); await client.close();
});

test('local outstanding-request bound rejects unsent work without breaking the session', async () => {
  const { output, client } = pair({ maxPendingRequests: 1 });
  const first = client.request(request());
  assert.throws(() => client.request(request()), /not submitted/);
  output.end(frame({ status: 'success', value: null }));
  assert.equal((await first).status, 'success'); await client.close();
});

test('close drains already-submitted responses and prevents new submissions', async () => {
  const { input, output, client } = pair();
  const response = client.request(request()); const closing = client.close();
  await assert.rejects(client.request(request()), /not submitted/);
  assert.equal(input.writableEnded, true);
  output.end(frame({ status: 'success', value: 'done' }));
  assert.equal((await response).value, 'done'); await closing;
});

for (const [name, bytes] of [['EOF before header', Buffer.alloc(0)], ['partial header', Buffer.from([0])], ['partial body', frame(null).subarray(0, 8)]] as const) {
  test(`${name} rejects every pending operation with unknown outcome`, async () => {
    const { output, client } = pair();
    const pending = Promise.allSettled([client.request(request()), client.request(request())]);
    output.end(bytes);
    for (const result of await pending) {
      assert.equal(result.status, 'rejected');
      if (result.status === 'rejected') { assert.ok(result.reason instanceof TransportError); assert.equal(result.reason.outcome, 'unknown'); }
    }
    await assert.rejects(client.close(), TransportError);
  });
}

test('oversized response declaration rejects before body allocation', async () => {
  const { output, client } = pair({ maxResponseBytes: 64 });
  const rejected = assert.rejects(client.request(request()), ProtocolError);
  const header = Buffer.alloc(8); header.writeBigUInt64BE((1n << 64n) - 1n); output.write(header);
  await rejected; await assert.rejects(client.close(), ProtocolError);
});

for (const value of [null, {}, { status: 'unknown', value: null }, { status: 'success', value: null, extra: true }] as Value[]) {
  test(`malformed response ${JSON.stringify(value)} is a client protocol failure`, async () => {
    const { output, client } = pair(); const rejected = assert.rejects(client.request(request()), ProtocolError);
    output.write(frame(value)); await rejected; await assert.rejects(client.close(), ProtocolError);
  });
}

test('write and readable errors reject pending requests instead of hanging', async () => {
  const output = new PassThrough();
  const input = new Writable({ write(_chunk, _encoding, callback) { callback(new Error('broken pipe')); } });
  const client = new Client({ input, output });
  await assert.rejects(client.request(request()), TransportError); await assert.rejects(client.close(), TransportError);
  const other = pair(); const rejected = assert.rejects(other.client.request(request()), TransportError);
  other.output.destroy(new Error('failed reader')); await rejected; await assert.rejects(other.client.close(), TransportError);
});

test('spawned fake peer supports preparation, current credentials, invalidation, pipelining and drain', async () => {
  const client = Client.spawn({ command: process.execPath, args: [fixture], stderr: 'ignore' });
  try {
    const prepared = await client.prepare({ credential: 'token', code: 'program', proof: 'proof' });
    assert.equal(prepared.status, 'prepared'); assert.equal(typeof prepared.value, 'string');
    const handle = prepared.value as string;
    const reads = [client.execute({ credential: 'token', handle, arguments: 'slow' }), client.execute({ credential: 'wrong', handle, arguments: 'x' }), client.execute({ credential: 'other', handle, arguments: 9223372036854775807n })];
    assert.deepEqual(await Promise.all(reads), [{ status: 'success', value: 'slow' }, { status: 'authentication', value: null }, { status: 'success', value: 9223372036854775807n }]);
    assert.equal((await client.invalidate({ credential: 'token', handle })).status, 'invalidated');
    assert.equal((await client.execute({ credential: 'token', handle, arguments: null })).status, 'failure');
  } finally { await client.close(); }
});

test('process death and invalid process launch are transport errors, with no retries', async () => {
  const client = Client.spawn({ command: process.execPath, args: [fixture], stderr: 'ignore' });
  const outcomes = await Promise.allSettled([client.request(request('exit')), client.request(request('never-run'))]);
  for (const outcome of outcomes) { assert.equal(outcome.status, 'rejected'); if (outcome.status === 'rejected') assert.ok(outcome.reason instanceof TransportError); }
  await assert.rejects(client.close(), TransportError);
  const missing = Client.spawn({ command: '/no/such/jaydb2', stderr: 'ignore' });
  await assert.rejects(missing.request(request()), TransportError); await assert.rejects(missing.close(), TransportError);
});

test('abort terminates an owned session and rejects pending work as uncertain', async () => {
  const client = Client.spawn({ command: process.execPath, args: [fixture], stderr: 'ignore' });
  const rejected = assert.rejects(client.request(request('slow')), TransportError);
  client.abort(); await rejected; await assert.rejects(client.close(), TransportError);
});

test('invalid spawn limits reject before the actual launch boundary', t => {
  let launches = 0;
  const reachedLaunch = new Error('launch boundary reached');
  t.mock.method(childProcess, 'spawn', () => { launches++; throw reachedLaunch; });
  syncBuiltinESMExports();
  try {
    assert.throws(() => Client.spawn({ command: process.execPath, maxResponseBytes: 0 }), RangeError);
    assert.throws(() => Client.spawn({ command: process.execPath, maxPendingRequests: 0 }), RangeError);
    assert.equal(launches, 0);
    // A valid call must reach this same boundary: no asynchronous-marker race.
    assert.throws(() => Client.spawn({ command: process.execPath }), error => error === reachedLaunch);
    assert.equal(launches, 1);
  } finally { t.mock.restoreAll(); syncBuiltinESMExports(); }
});

test('abort after owned process completion never signals a stale process group', async t => {
  const client = Client.spawn({ command: process.execPath, args: ['-e', 'process.stdin.resume()'], stderr: 'ignore' });
  await client.close();
  const signals: unknown[][] = [];
  t.mock.method(process, 'kill', (...args: unknown[]) => { signals.push(args); return true; });
  client.abort();
  assert.deepEqual(signals, []);
  await client.close();
});
