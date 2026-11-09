import assert from 'node:assert/strict';
import test from 'node:test';
import { eq, sql } from 'drizzle-orm';
import { boolean, pgTable, text } from 'drizzle-orm/pg-core';
import { ProtocolError } from '../../typescript/src/index.ts';
import type { Execution, Preparation, Response } from '../../typescript/src/index.ts';
import { compileSql, SqlClient, SqlError, SqlExecutionError } from '../src/index.ts';
import type { SqlTransport } from '../src/client.ts';
import { createDrizzle, drizzleCallback } from '../src/drizzle.ts';

const titleQuery = 'select title from tasks where id=$1';
const idQuery = 'select id from tasks where id=$1';
const successful = (rows: unknown[], rowCount = 1n): Response => ({ status: 'success', value: { rows, rowCount } }) as Response;
const tick = () => new Promise<void>(resolve => setImmediate(resolve));
function deferred<T>() {
  let resolve!: (value: T) => void;
  let reject!: (error: unknown) => void;
  const promise = new Promise<T>((yes, no) => { resolve = yes; reject = no; });
  return { promise, resolve, reject };
}
function fixture() {
  const preparations: Preparation[] = [], executions: Execution[] = [];
  const transport: SqlTransport = {
    async prepare(request) { preparations.push(request); return { status: 'prepared', value: 'a'.repeat(64) }; },
    async execute(request) { executions.push(request); return successful([['value']]); },
  };
  return { preparations, executions, transport };
}

test('a cached query cannot overtake an earlier cold preparation', async () => {
  const f = fixture();
  const client = new SqlClient(f.transport, { credential: 'alice-token' });
  await client.query(titleQuery, ['warm']);
  const preparation = deferred<Response>();
  f.transport.prepare = request => { f.preparations.push(request); return preparation.promise; };
  const earlier = client.query(idQuery, ['earlier']);
  const later = client.query(titleQuery, ['later']);
  await tick();
  assert.deepEqual(f.executions.map(e => e.arguments), [[['warm']]]);
  preparation.resolve({ status: 'prepared', value: 'b'.repeat(64) });
  await Promise.all([earlier, later]);
  assert.deepEqual(f.executions.map(e => e.arguments), [[['warm']], [['earlier']], [['later']]]);
});

test('an unresolved execution prevents every later preparation and execution', async () => {
  const f = fixture();
  const execution = deferred<Response>();
  f.transport.execute = request => { f.executions.push(request); return execution.promise; };
  const client = new SqlClient(f.transport, { credential: 'alice-token' });
  const first = client.query(titleQuery, ['first']);
  const second = client.query(idQuery, ['second']);
  await tick();
  assert.equal(f.preparations.length, 1);
  assert.equal(f.executions.length, 1);
  f.transport.execute = async request => { f.executions.push(request); return successful([['second']]); };
  execution.resolve(successful([['first']]));
  await Promise.all([first, second]);
  assert.deepEqual(f.executions.map(e => e.arguments), [[['first']], [['second']]]);
});

test('queued calls snapshot arguments and credentials when invoked', async () => {
  const f = fixture(); const gate = deferred<Response>();
  f.transport.prepare = request => { f.preparations.push(request); return gate.promise; };
  let credential = 'alice-token';
  const client = new SqlClient(f.transport, { credential: () => credential });
  const firstArgs = ['first'];
  const first = client.query(titleQuery, firstArgs);
  credential = 'bob-token';
  const secondArgs = ['second'];
  const second = client.query(titleQuery, secondArgs);
  firstArgs[0] = 'changed'; secondArgs[0] = 'changed'; credential = 'invalid-token';
  gate.resolve({ status: 'prepared', value: 'a'.repeat(64) });
  await Promise.all([first, second]);
  assert.deepEqual(f.preparations.map(p => p.credential), ['alice-token']);
  assert.deepEqual(f.executions.map(e => [e.credential, e.arguments]), [['alice-token', [['first']]], ['bob-token', [['second']]]]);
});

test('128 generated schedules preserve invocation order across cold and cached shapes', async () => {
  let generatedQueries = 0;
  const schedules = new Set<string>();
  for (let seed = 1; seed <= 128; seed++) {
    let random = seed;
    const next = () => { random = (Math.imul(random, 1664525) + 1013904223) >>> 0; return random >>> 16; };
    const f = fixture();
    f.transport.prepare = async request => { f.preparations.push(request); if (next() & 1) await tick(); return { status: 'prepared', value: 'a'.repeat(64) }; };
    f.transport.execute = async request => { f.executions.push(request); if (next() & 1) await tick(); return successful([['value']]); };
    let credential = 'alice-token';
    const client = new SqlClient(f.transport, { credential: () => credential });
    const expected: [string, unknown][] = [];
    const schedule: unknown[] = [];
    const pending = [];
    for (let i = 0; i < 12; i++) {
      credential = next() & 1 ? 'alice-token' : 'bob-token';
      const query = next() & 2 ? titleQuery : idQuery;
      const key = `${seed}:${i}`;
      expected.push([credential, [[key]]]);
      pending.push(client.query(query, [key])); generatedQueries++;
      const yieldNow = !!(next() & 4);
      schedule.push([credential, query === titleQuery, yieldNow]);
      if (yieldNow) await Promise.resolve();
    }
    await Promise.all(pending);
    assert.deepEqual(f.executions.map(e => [e.credential, e.arguments]), expected, `seed ${seed}`);
    assert.ok(f.preparations.length <= 2);
    schedules.add(JSON.stringify(schedule));
  }
  assert.equal(generatedQueries, 1536);
  assert.equal(schedules.size, 128, 'Seeds must exercise distinct control schedules');
});

test('database rejection statuses preserve their response and do not poison later calls', async () => {
  for (const phase of ['prepare', 'execute'] as const) {
    for (const status of ['input', 'authentication', 'certificate', 'data', 'limit', 'failure', 'refusal'] as const) {
      const f = fixture();
      const response: Response = { status, value: status === 'refusal' ? 'duplicate key' : null };
      if (phase === 'prepare') f.transport.prepare = async () => response;
      else f.transport.execute = async () => response;
      const client = new SqlClient(f.transport, { credential: 'alice-token' });
      await assert.rejects(client.query(titleQuery, ['first']), error => error instanceof SqlExecutionError && error.response === response);
      f.transport.prepare = async request => { f.preparations.push(request); return { status: 'prepared', value: 'a'.repeat(64) }; };
      f.transport.execute = async request => { f.executions.push(request); return successful([['recovered']]); };
      assert.equal((await client.query(titleQuery, ['second'])).rows[0]?.[0], 'recovered', `${phase}:${status}`);
    }
  }
});

test('preparation throws, rejections and malformed handles release capacity without executing', async () => {
  for (const failure of [new Error('sync'), new Error('async'), '', 'a'.repeat(63), 'a'.repeat(65), 'g'.repeat(64), null, 123n]) {
    const f = fixture();
    f.transport.prepare = () => {
      if (failure instanceof Error && failure.message === 'sync') throw failure;
      if (failure instanceof Error) return Promise.reject(failure);
      return Promise.resolve({ status: 'prepared', value: failure });
    };
    const client = new SqlClient(f.transport, { credential: 'alice-token', maxPrepared: 1 });
    await assert.rejects(client.query(titleQuery, ['first']), error => failure instanceof Error ? error === failure : error instanceof ProtocolError);
    assert.equal(f.executions.length, 0);
    f.transport.prepare = async () => ({ status: 'prepared', value: 'b'.repeat(64) });
    assert.equal((await client.query(idQuery, ['second'])).rowCount, 1n);
  }
});

test('transport execution failure is never retried and does not silently recreate handles', async () => {
  for (const synchronous of [true, false]) {
    const f = fixture(); const failure = new Error('connection lost; outcome unknown');
    f.transport.execute = request => { f.executions.push(request); if (synchronous) throw failure; return Promise.reject(failure); };
    const client = new SqlClient(f.transport, { credential: 'alice-token' });
    await assert.rejects(client.query(titleQuery, ['x']), error => error === failure);
    assert.equal(f.preparations.length, 1);
    assert.equal(f.executions.length, 1);
  }
});

test('malformed success responses reject impossible counts, cell types and structures', async () => {
  const malformed = [
    null, [], {}, { rows: [], rowCount: 0 }, { rows: [], rowCount: -1n }, { rows: [['x']], rowCount: 0n },
    { rows: [], rowCount: 1n }, { rows: [['x'], ['y']], rowCount: 2n }, { rows: [['x']], rowCount: 2n },
    { rows: [['x']], rowCount: 1n, extra: true }, { rows: [['x', 'y']], rowCount: 1n },
    { rows: [null], rowCount: 1n }, { rows: ['x'], rowCount: 1n }, { rows: [[null]], rowCount: 1n },
    { rows: [[true]], rowCount: 1n }, { rows: [[1n]], rowCount: 1n }, { rows: [['\ud800']], rowCount: 1n },
    { rows: Array(1), rowCount: 1n }, { rows: [Array(1)], rowCount: 1n },
  ];
  for (const value of malformed) {
    const f = fixture(); f.transport.execute = async () => ({ status: 'success', value }) as Response;
    const client = new SqlClient(f.transport, { credential: 'alice-token' });
    await assert.rejects(client.query(titleQuery, ['x']), ProtocolError, JSON.stringify(value, (_key, v) => typeof v === 'bigint' ? v.toString() : v));
  }
  for (const value of [{ rows: [['false']], rowCount: 1n }, { rows: [[false]], rowCount: 0n }]) {
    const f = fixture(); f.transport.execute = async () => ({ status: 'success', value });
    await assert.rejects(new SqlClient(f.transport, { credential: 'alice-token' }).query('select completed from tasks where id=$1', ['x']), ProtocolError);
  }
  for (const value of [{ rows: [], rowCount: 0n }, { rows: [], rowCount: 2n }]) {
    const f = fixture(); f.transport.execute = async () => ({ status: 'success', value });
    await assert.rejects(new SqlClient(f.transport, { credential: 'alice-token' }).query('insert into tasks (id,title) values ($1,$2)', ['x', 'y']), ProtocolError);
  }
});

test('bounded queue rejects excess work before transport and reopens after completion', async () => {
  const f = fixture(); const gate = deferred<Response>();
  f.transport.execute = request => { f.executions.push(request); return gate.promise; };
  const client = new SqlClient(f.transport, { credential: 'alice-token', maxPendingQueries: 1 });
  const first = client.query(titleQuery, ['first']);
  await assert.rejects(client.query(titleQuery, ['not submitted']), error => error instanceof SqlError && error.code === '54000');
  await tick();
  assert.equal(f.executions.length, 1);
  f.transport.execute = async request => { f.executions.push(request); return successful([['last']]); };
  gate.resolve(successful([['first']])); await first;
  assert.equal((await client.query(titleQuery, ['last'])).rows[0]?.[0], 'last');
  assert.deepEqual(f.executions.map(e => e.arguments), [[['first']], [['last']]]);
  for (const maxPendingQueries of [0, -1, 1.5, Number.NaN, Infinity]) {
    assert.throws(() => new SqlClient(f.transport, { credential: 'alice-token', maxPendingQueries }), RangeError);
  }
});

test('cache-limit rejection leaves existing shapes usable and aliases share exact source', async () => {
  const f = fixture();
  const client = new SqlClient(f.transport, { credential: 'alice-token', maxPrepared: 1 });
  await client.query(titleQuery, ['first']);
  await assert.rejects(client.query(idQuery, ['not submitted']), error => error instanceof SqlError && error.code === '54000');
  assert.equal((await client.query("select title as renamed from tasks where id='literal'")).columns[0], 'renamed');
  assert.equal(f.preparations.length, 1);
  assert.equal(f.executions.length, 2);
});

const tasks = pgTable('tasks', {
  id: text('id').primaryKey(), title: text('title').notNull(),
  completed: boolean('completed').notNull().default(false),
  owner: text('owner').notNull().default(sql`current_user`),
});

test('real Drizzle named preparations bind placeholders and preserve response types', async () => {
  const f = fixture();
  f.transport.execute = async request => { f.executions.push(request); return successful([[true, 'name']]); };
  const db = createDrizzle(new SqlClient(f.transport, { credential: 'alice-token' }));
  const prepared = db.select({ done: tasks.completed, label: tasks.title }).from(tasks)
    .where(eq(tasks.id, sql.placeholder('key'))).prepare('by_key');
  assert.deepEqual(await prepared.execute({ key: 'one' }), [{ done: true, label: 'name' }]);
  assert.deepEqual(await prepared.execute({ key: 'two' }), [{ done: true, label: 'name' }]);
  assert.equal(f.preparations.length, 1);
  assert.deepEqual(f.executions.map(e => e.arguments), [[['one']], [['two']]]);
});

test('Drizzle raw execution maps labels safely and never swallows backend rejection', async () => {
  const f = fixture(); f.transport.execute = async () => successful([['first', 'second', 'safe']]);
  const client = new SqlClient(f.transport, { credential: 'alice-token' });
  const db = createDrizzle(client);
  const raw = await db.execute(sql`select title as same, title as same, id as "__proto__" from tasks where id=${'x'}`);
  assert.equal(raw.length, 1);
  assert.equal(raw[0]?.same, 'second');
  assert.equal(raw[0]?.__proto__, 'safe');
  assert.equal(Object.getPrototypeOf(raw[0]), Object.prototype);
  assert.ok(Object.hasOwn(raw[0]!, '__proto__'));
  f.transport.execute = async () => ({ status: 'authentication', value: null });
  await assert.rejects(db.select({ title: tasks.title }).from(tasks).where(eq(tasks.id, 'x')),
    error => error instanceof Error && error.cause instanceof SqlExecutionError && error.cause.code === '28000');
  await assert.rejects((drizzleCallback(client) as Function)(titleQuery, ['x'], 'unsupported'), SqlError);
});
