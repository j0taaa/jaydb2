import assert from 'node:assert/strict';
import test from 'node:test';
import { eq, sql as rawSql } from 'drizzle-orm';
import { pgTable, text, boolean } from 'drizzle-orm/pg-core';
import { compileSql, SqlClient, SqlError, SqlExecutionError } from '../src/index.ts';
import { createDrizzle } from '../src/drizzle.ts';
import type { SqlTransport } from '../src/client.ts';
import type { Preparation, Execution, Response } from '../../typescript/src/index.ts';

const tasks = pgTable('tasks', {
  id: text('id').primaryKey(), title: text('title').notNull(),
  completed: boolean('completed').notNull().default(false),
  owner: text('owner').notNull().default(rawSql`current_user`),
});
const success = (rows: unknown[], rowCount = 1n) => ({ status: 'success', value: { rows, rowCount } }) as Response;
function fixture(response: Response = success([['hello']])) {
  const preparations: Preparation[] = [], executions: Execution[] = [];
  const transport: SqlTransport = {
    async prepare(request) { preparations.push(request); return { status: 'prepared', value: 'a'.repeat(64) }; },
    async execute(request) { executions.push(request); return response; },
  };
  return { transport, preparations, executions };
}

test('binding separates SQL values from generated code and checks all types before submission', async () => {
  const compiled = compileSql('insert into tasks (id, title) values ($1, $2) returning title');
  const attack = `'); DELETE FROM tasks; -- 🦊`;
  assert.deepEqual(compiled.bind(['x', attack]), [['x', attack, false]]);
  assert.ok(!compiled.code.includes(attack));
  assert.deepEqual(compileSql('update tasks set completed = $1 where id = $2').bind([true, 'x']), [['x', null, true]]);
  assert.deepEqual(compileSql("select title from tasks where id = 'O''Brien'").bind(), [["O'Brien"]]);
  for (const [query, args] of [
    ['select title from tasks where id = $1', []],
    ['select title from tasks where id = $1', [1]],
    ['select title from tasks where id = $1', [null]],
    ['select title from tasks where id = $1', ['\ud800']],
    ['select title from tasks where id = $1', ['nul\0byte']],
    ['update tasks set completed = $1 where id = $2', ['false', 'x']],
    ['insert into tasks (id) values ($1)', ['x']],
  ] as const) {
    const f = fixture(); const client = new SqlClient(f.transport, { credential: 'alice-token' });
    await assert.rejects(client.query(query, args), SqlError);
    assert.equal(f.preparations.length + f.executions.length, 0);
  }
  assert.throws(() => compileSql('select title from tasks where id = $2'), SqlError);
  assert.throws(() => compileSql("insert into tasks (id,title) values ('1','a'),('2','b'),('3','c')"), /At most 2 rows/);
  const literal = compileSql("select title from tasks where id = 'literal'");
  const parameterized = compileSql('select title from tasks where id = $1');
  assert.equal(literal.code, parameterized.code);
  assert.equal(literal.proof, parameterized.proof);
});

test('one preparation per source shape, concurrent deduplication, fresh credentials', async () => {
  const f = fixture(); let credential = 'alice-token';
  const client = new SqlClient(f.transport, { credential: () => credential });
  await Promise.all(['a', 'b'].map(id => client.query('select title from tasks where id=$1', [id])));
  credential = 'bob-token';
  await client.query("select title from tasks where id='c'");
  assert.equal(f.preparations.length, 1);
  assert.deepEqual(f.executions.map(e => e.credential), ['alice-token', 'alice-token', 'bob-token']);
  assert.deepEqual(f.executions.map(e => e.arguments), [[['a']], [['b']], [['c']]]);
});

test('database and transport errors propagate without write retry or empty success', async () => {
  const f = fixture({ status: 'refusal', value: 'duplicate key' });
  const client = new SqlClient(f.transport, { credential: 'alice-token' });
  await assert.rejects(client.query('insert into tasks (id,title) values ($1,$2)', ['x', 'a']),
    error => error instanceof SqlExecutionError && error.code === '23505');
  assert.equal(f.executions.length, 1);
  const failure = new Error('lost response');
  f.transport.execute = async () => { throw failure; };
  await assert.rejects(client.query('insert into tasks (id,title) values ($1,$2)', ['y', 'b']), error => error === failure);
  assert.equal(f.preparations.length, 1);
});

test('concurrent valid credentials do not inherit a failed preparation authentication', async () => {
  const f = fixture(); let credential = 'bad';
  f.transport.prepare = async request => {
    f.preparations.push(request);
    return request.credential === 'bad' ? { status: 'authentication', value: null }
      : { status: 'prepared', value: 'a'.repeat(64) };
  };
  const client = new SqlClient(f.transport, { credential: () => credential });
  const bad = client.query('select title from tasks where id=$1', ['x']);
  credential = 'bob-token';
  const good = client.query('select title from tasks where id=$1', ['x']);
  await assert.rejects(bad, error => error instanceof SqlExecutionError && error.code === '28000');
  assert.equal((await good).rows[0]?.[0], 'hello');
  assert.deepEqual(f.preparations.map(p => p.credential), ['bad', 'bob-token']);
  assert.equal(f.executions.length, 1);
});

test('failed preparation is not cached and cache is bounded', async () => {
  const f = fixture();
  f.transport.prepare = async request => { f.preparations.push(request); return { status: 'authentication', value: null }; };
  const client = new SqlClient(f.transport, { credential: 'bad', maxPrepared: 1 });
  for (let i = 0; i < 2; i++) await assert.rejects(client.query('select title from tasks where id=$1', ['x']), SqlExecutionError);
  assert.equal(f.preparations.length, 2);
  f.transport.prepare = async () => ({ status: 'prepared', value: 'a'.repeat(64) });
  await client.query('select title from tasks where id=$1', ['x']);
  await assert.rejects(client.query('select id from tasks where id=$1', ['x']), error => error instanceof SqlError && error.code === '54000');
});

test('synchronous transport rejection releases the pending cache slot', async () => {
  const f = fixture();
  f.transport.prepare = () => { throw new RangeError('pending queue full'); };
  const client = new SqlClient(f.transport, { credential: 'alice-token', maxPrepared: 1 });
  await assert.rejects(client.query('select title from tasks where id=$1', ['x']), /pending queue full/);
  f.transport.prepare = async () => ({ status: 'prepared', value: 'a'.repeat(64) });
  f.transport.execute = async () => success([['x']]);
  assert.equal((await client.query('select id from tasks where id=$1', ['x'])).rows[0]?.[0], 'x');
});

test('Drizzle emits supported CRUD SQL and maps positional return values', async () => {
  const f = fixture(success([['x', 'hello', false, 'alice']]));
  const client = new SqlClient(f.transport, { credential: 'alice-token' });
  const db = createDrizzle(client);
  assert.deepEqual(await db.insert(tasks).values({ id: 'x', title: 'hello' }).returning(),
    [{ id: 'x', title: 'hello', completed: false, owner: 'alice' }]);
  f.transport.execute = async request => { f.executions.push(request); return success([[true, 'changed']]); };
  assert.deepEqual(await db.update(tasks).set({ title: 'changed', completed: true }).where(eq(tasks.id, 'x'))
    .returning({ done: tasks.completed, label: tasks.title }), [{ done: true, label: 'changed' }]);
  f.transport.execute = async () => success([['hello']]);
  assert.deepEqual(await db.select({ label: tasks.title }).from(tasks).where(eq(tasks.id, 'x')), [{ label: 'hello' }]);
  assert.deepEqual(await db.delete(tasks).where(eq(tasks.id, 'x')).returning({ title: tasks.title }), [{ title: 'hello' }]);
  await assert.rejects(db.transaction(async () => {}), /Transactions are not supported/);
});

test('malformed program results preserve unknown outcome rather than coercing', async () => {
  for (const response of [success([['too', 'wide']]), success([], -1n), { status: 'success', value: [] } as Response]) {
    const client = new SqlClient(fixture(response).transport, { credential: 'alice-token' });
    await assert.rejects(client.query('select title from tasks where id=$1', ['x']), /Malformed SQL program result/);
  }
});
