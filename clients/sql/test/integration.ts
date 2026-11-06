/** Real proof/admission/compiler/runtime test. Caller owns the heavy-work lock. */
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtempSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { eq, sql as rawSql } from 'drizzle-orm';
import { pgTable, text, boolean } from 'drizzle-orm/pg-core';
import { Client } from '../../typescript/src/index.ts';
import { compileSql, SqlClient, SqlError, SqlExecutionError } from '../src/index.ts';
import { createDrizzle } from '../src/drizzle.ts';

const tasks = pgTable('tasks', {
  id: text('id').primaryKey(), title: text('title').notNull(),
  completed: boolean('completed').notNull().default(false),
  owner: text('owner').notNull().default(rawSql`current_user`),
});
const root = fileURLToPath(new URL('../../../', import.meta.url));
const directory = mkdtempSync(join(tmpdir(), 'jaydb-sql-check-'));
const app = join(directory, 'app'), storage = join(directory, 'db');
let pipe: Client | undefined;
let assertions = 0;
function check(actual: unknown, expected: unknown) { assert.deepEqual(actual, expected); assertions++; }
function hasCode(error: unknown, code: string): boolean {
  if (error instanceof SqlError) return error.code === code;
  return error instanceof Error && error.cause !== undefined && hasCode(error.cause, code);
}
function open(mode: 'create' | 'open') {
  return Client.spawn({ command: process.env.JAYDB_SQL_BINARY ?? join(root, 'jaydb2'), cwd: root,
    args: ['--configuration', join(app, 'Configuration.bend'), '--storage', storage, '--storage-mode', mode,
      ...mode === 'create' ? ['--seed', join(app, 'Seed.bend')] : [], '--threads', '1'] });
}
const watchdog = setTimeout(() => { console.error('SQL integration exceeded its development-only 10 minute watchdog'); pipe?.abort(); }, 600000);
watchdog.unref();
try {
  execFileSync('python3', ['-B', join(root, 'applications/sql/prepare.py'), app]);
  pipe = open('create');
  let credential = 'alice-token';
  const client = new SqlClient(pipe, { credential: () => credential });
  const db = createDrizzle(client);
  const title = `O'Brien; DELETE FROM tasks; -- 🦊`;
  console.log('Checking real Drizzle CRUD, bound text and returning...');
  check(await db.insert(tasks).values({ id: 't1', title }).returning(), [{ id: 't1', title, completed: false, owner: 'alice' }]);
  check(await db.select({ label: tasks.title, owner: tasks.owner }).from(tasks).where(eq(tasks.id, 't1')), [{ label: title, owner: 'alice' }]);
  check(await db.update(tasks).set({ completed: true }).where(eq(tasks.id, 't1')).returning(), [{ id: 't1', title, completed: true, owner: 'alice' }]);
  check(await db.update(tasks).set({ title: 'renamed' }).where(eq(tasks.id, 't1')).returning({ done: tasks.completed, title: tasks.title }), [{ done: true, title: 'renamed' }]);
  check(await client.query('select title, title as duplicate from tasks where id=$1', ['t1']), { columns: ['title', 'duplicate'], rows: [['renamed', 'renamed']], rowCount: 1n });
  check(await client.query('update tasks set title=$1 where id=$2', ['missing', 'absent']), { columns: [], rows: [], rowCount: 0n });
  check(await client.query('delete from tasks where id=$1', ['absent']), { columns: [], rows: [], rowCount: 0n });
  console.log('Checking duplicate-key refusal and rollback after a provisional write...');
  await assert.rejects(db.insert(tasks).values({ id: 't1', title: 'overwrite' }), e => hasCode(e, '23505')); assertions++;
  await assert.rejects(db.insert(tasks).values([{ id: 'provisional', title: 'rollback me' }, { id: 't1', title: 'duplicate' }]).returning(), e => hasCode(e, '23505')); assertions++;
  check(await db.select().from(tasks).where(eq(tasks.id, 'provisional')), []);
  check(await db.select().from(tasks).where(eq(tasks.id, 't1')), [{ id: 't1', title: 'renamed', completed: true, owner: 'alice' }]);
  check(await db.insert(tasks).values([{ id: 'a', title: 'first' }, { id: 'b', title: 'second', completed: true }]).returning({ id: tasks.id, done: tasks.completed }), [{ id: 'a', done: false }, { id: 'b', done: true }]);
  console.log('Checking fresh authentication and owner isolation using shared prepared programs...');
  credential = 'bob-token';
  check(await db.select().from(tasks).where(eq(tasks.id, 't1')), []);
  check(await db.insert(tasks).values({ id: 't1', title: 'Bob' }).returning(), [{ id: 't1', title: 'Bob', completed: false, owner: 'bob' }]);
  credential = 'invalid-token';
  await assert.rejects(client.query('select * from tasks where id=$1', ['t1']), e => e instanceof SqlExecutionError && e.code === '28000'); assertions++;
  credential = 'alice-token';
  check(await db.delete(tasks).where(eq(tasks.id, 'a')).returning({ id: tasks.id, title: tasks.title }), [{ id: 'a', title: 'first' }]);
  check(await db.select().from(tasks).where(eq(tasks.id, 'a')), []);
  console.log('Checking generated-source mutations fail real certificate admission...');
  const select = compileSql('select * from tasks where id=$1');
  const forbidden = select.code.replaceAll('D.Application{owner}', 'D.Application{"bob"}');
  assert.notEqual(forbidden, select.code);
  check(await pipe.prepare({ credential, code: forbidden, proof: select.proof }), { status: 'certificate', value: null });
  const insert = compileSql('insert into tasks (id,title) values ($1,$2)');
  const wrongOwner = insert.code.replace('D.Field{"owner", D.VText{owner}}', 'D.Field{"owner", D.VText{"mallory"}}');
  assert.notEqual(wrongOwner, insert.code);
  check(await pipe.prepare({ credential, code: wrongOwner, proof: insert.proof }), { status: 'certificate', value: null });
  check(await db.select().from(tasks).where(eq(tasks.id, 't1')), [{ id: 't1', title: 'renamed', completed: true, owner: 'alice' }]);
  // A prepared program must reject malformed raw arguments too, independently of TS validation.
  const prepared = await pipe.prepare({ credential, code: insert.code, proof: insert.proof });
  assert.equal(prepared.status, 'prepared'); assert.equal(typeof prepared.value, 'string');
  check(await pipe.execute({ credential, handle: prepared.value as string, arguments: [['bad', 'text', 'not a boolean']] }), { status: 'refusal', value: 'invalid SQL arguments' });
  console.log('Checking durable data after close/reopen and fresh preparation...');
  await pipe.close(); pipe = open('open');
  const recovered = new SqlClient(pipe, { credential: 'alice-token' });
  check((await recovered.query('select * from tasks where id=$1', ['t1'])).rows, [['t1', 'renamed', true, 'alice']]);
  check((await recovered.query('select * from tasks where id=$1', ['provisional'])).rows, []);
  check((await recovered.query('select title from tasks where id=$1', ['b'])).rows, [['second']]);
  check(await pipe.execute({ credential, handle: prepared.value as string, arguments: [['old', 'old', false]] }), { status: 'failure', value: null });
  console.log(`PASS: ${assertions} real SQL/Drizzle checks; universal proofs, native execution, rollback, isolation, certificate rejection and persistence.`);
} finally {
  clearTimeout(watchdog);
  try { await pipe?.close(); } finally { rmSync(directory, { recursive: true, force: true }); }
}
