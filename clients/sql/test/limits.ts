/** Real SQL size-limit and rollback checks. Caller owns the heavy-work lock. */
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { Client } from '../../typescript/src/index.ts';
import { SqlClient, SqlExecutionError } from '../src/index.ts';

const root = fileURLToPath(new URL('../../../', import.meta.url));
const directory = mkdtempSync(join(tmpdir(), 'jaydb-sql-limits-'));
const app = join(directory, 'app'), storage = join(directory, 'db');
let pipe: Client | undefined;
let frontend!: SqlClient;
let checks = 0;
function open(mode: 'create' | 'open') {
  pipe = Client.spawn({ command: process.env.JAYDB_SQL_BINARY ?? join(root, 'jaydb2'), cwd: root,
    args: ['--configuration', join(app, 'Configuration.bend'), '--storage', storage, '--storage-mode', mode,
      ...mode === 'create' ? ['--seed', join(app, 'Seed.bend')] : [], '--threads', '1'] });
  frontend = new SqlClient(pipe, { credential: 'alice-token' });
}
async function limited(sql: string, params: unknown[]) {
  const before = readFileSync(join(storage, 'snapshot'));
  await assert.rejects(frontend.query(sql, params), error => error instanceof SqlExecutionError && error.response.status === 'limit');
  assert.deepEqual(readFileSync(join(storage, 'snapshot')), before, 'A failed statement must not change durable state');
  checks++;
}
async function title(id: string, expected: string | undefined) {
  assert.deepEqual((await frontend.query('select title from tasks where id=$1', [id])).rows,
    expected === undefined ? [] : [[expected]]);
  checks++;
}
const watchdog = setTimeout(() => { console.error('SQL limit test exceeded its development watchdog'); pipe?.abort(); }, 600000);
watchdog.unref();
try {
  execFileSync('python3', ['-B', join(root, 'applications/sql/prepare.py'), app]);
  open('create');
  console.log('Checking maximum projection width across all SQL operation shapes...');
  const wide = Array.from({ length: 4 }, () => 'id,title,completed,owner').join(',');
  const row = (id: string, text: string, completed: boolean) => Array.from({ length: 4 }, () => [id, text, completed, 'alice']).flat();
  assert.deepEqual((await frontend.query(`insert into tasks (id,title,completed) values ($1,$2,$3),($4,$5,$6) returning ${wide}`,
    ['width-a', 'A', false, 'width-b', 'B', true])).rows, [row('width-a', 'A', false), row('width-b', 'B', true)]); checks++;
  assert.deepEqual((await frontend.query(`insert into tasks (id,title) values ($1,$2) returning ${wide}`,
    ['width-c', 'C'])).rows, [row('width-c', 'C', false)]); checks++;
  assert.deepEqual((await frontend.query(`update tasks set title=$1,completed=$2 where id=$3 returning ${wide}`,
    ['A2', true, 'width-a'])).rows, [row('width-a', 'A2', true)]); checks++;
  for (const [id, text, completed] of [['width-a', 'A2', true], ['width-b', 'B', true], ['width-c', 'C', false]] as const) {
    assert.deepEqual((await frontend.query(`delete from tasks where id=$1 returning ${wide}`, [id])).rows, [row(id, text, completed)]); checks++;
  }
  const retained = 'a'.repeat(20000);
  assert.equal((await frontend.query('insert into tasks (id,title) values ($1,$2)', ['retained', retained])).rowCount, 1n); checks++;
  await title('retained', retained);

  console.log('Checking SQL response/state ceilings preserve prior durable state...');
  await limited('insert into tasks (id,title) values ($1,$2) returning title', ['response-overflow', 'b'.repeat(40000)]);
  await title('response-overflow', undefined);
  await limited('update tasks set title=$1 where id=$2 returning title', ['c'.repeat(40000), 'retained']);
  await title('retained', retained);
  await limited('update tasks set title=$1 where id=$2', ['d'.repeat(70000), 'retained']);
  await title('retained', retained);
  await limited('insert into tasks (id,title) values ($1,$2),($3,$4)', ['provisional', 'must roll back', 'state-overflow', 'e'.repeat(70000)]);
  await title('provisional', undefined);
  await title('state-overflow', undefined);

  const emoji = '🦊'.repeat(9000);
  assert.ok(emoji.length < 32768 && Buffer.byteLength(emoji) > 32768);
  await limited('insert into tasks (id,title) values ($1,$2) returning title', ['utf8-overflow', emoji]);
  await title('utf8-overflow', undefined);

  // A large stored row is valid without returning its full text. Narrow
  // projection must succeed even though the program observes that title.
  assert.equal((await frontend.query('insert into tasks (id,title) values ($1,$2)', ['large', 'f'.repeat(40000)])).rowCount, 1n); checks++;
  assert.deepEqual((await frontend.query('select id from tasks where id=$1', ['large'])).rows, [['large']]); checks++;
  await limited('select title from tasks where id=$1', ['large']);
  assert.deepEqual((await frontend.query('select id from tasks where id=$1', ['large'])).rows, [['large']]); checks++;
  assert.equal((await frontend.query('delete from tasks where id=$1', ['large'])).rowCount, 1n); checks++;
  await title('large', undefined);

  await pipe!.close(); open('open');
  await title('retained', retained);
  for (const id of ['response-overflow', 'state-overflow', 'provisional', 'utf8-overflow', 'large']) await title(id, undefined);
  console.log(`PASS SQL limits: ${checks} native checks of byte ceilings, large rows, projection, atomic rollback, continued service and durable recovery.`);
} finally {
  clearTimeout(watchdog);
  try { await pipe?.close(); } finally { rmSync(directory, { recursive: true, force: true }); }
}
