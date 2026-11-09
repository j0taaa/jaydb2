/**
 * Seeded real-service SQL/Drizzle differential and recovery test.
 * Caller owns the heavy-work lock. This starts real official native workers.
 * SQLite is an independent oracle for the common supported SQL semantics; this
 * test does not establish PostgreSQL equivalence outside the documented subset.
 */
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { eq, sql as sqlText } from 'drizzle-orm';
import { boolean, pgTable, text } from 'drizzle-orm/pg-core';
import { Client } from '../../typescript/src/index.ts';
import { SqlClient, SqlError } from '../src/index.ts';
import { createDrizzle } from '../src/drizzle.ts';
import { SqliteTaskOracle, quote, random } from './model.ts';
import type { ModelOutcome, ModelResult } from './model.ts';

type Actor = 'alice' | 'bob';
type Query = { sql: string; params: unknown[] };
type OrmQuery = PromiseLike<unknown> & { toSQL(): Query };
const actors: readonly Actor[] = ['alice', 'bob'];
const allColumns = ['id', 'title', 'completed', 'owner'];
const writableColumns = ['id', 'title', 'completed'];
// Deliberately separate read and write metadata: Drizzle's three writable
// fields emit SQL that SQLite can execute unchanged, without its unsupported
// VALUES(DEFAULT) syntax. Owner defaults are supplied independently by SQLite.
const writes = pgTable('tasks', {
  id: text('id').primaryKey(), title: text('title').notNull(), completed: boolean('completed').notNull(),
});
const tasks = pgTable('tasks', {
  id: text('id').primaryKey(), title: text('title').notNull(), completed: boolean('completed').notNull(),
  owner: text('owner').notNull(),
});
const root = fileURLToPath(new URL('../../../', import.meta.url));
const directory = mkdtempSync(join(tmpdir(), 'jaydb-sql-stress-'));
const app = join(directory, 'app'), storage = join(directory, 'db');
const defaults = [1, 7, 42];
const seeds = process.env.SQL_STRESS_SEEDS === undefined ? defaults : process.env.SQL_STRESS_SEEDS.split(',').map(Number);
const steps = Number(process.env.SQL_STRESS_STEPS ?? '200');
assert.ok(seeds.length > 0 && seeds.length <= 100 && seeds.every(seed => Number.isInteger(seed) && seed >= 0 && seed <= 0xffffffff), 'SQL_STRESS_SEEDS must contain uint32 seeds');
assert.ok(Number.isSafeInteger(steps) && steps >= 1 && steps <= 10000, 'SQL_STRESS_STEPS must be 1..10000');
const summary = {
  status: 'running', seeds, stepsPerSeed: steps, randomizedSteps: 0,
  rawSqlComparisons: 0, drizzleComparisons: 0, duplicateRefusals: 0,
  validationReads: 0, authenticationDenials: 0, concurrentControls: 0,
  preparations: 0, nativeExecutions: 0, distinctPreparedShapes: 0,
  recoveryChecks: 0, elapsedMs: 0, node: process.version,
  keySetAudits: 0, enumerationPreparations: 0,
  startedAt: new Date().toISOString(), failure: null as string | null,
};
const started = Date.now();
const shapes = new Set<string>();
const models = { alice: new SqliteTaskOracle('alice'), bob: new SqliteTaskOracle('bob') };
const keys = new Set<string>();
const keyPool = ['', ...Array.from({ length: 12 }, (_, i) => `slot-${i}`), '🦊', "quote'\";$1", 'a/b', ' spaced ', 'line\nkey', 'é', 'e\u0301'];
const titles = [
  '', 'ordinary', "O'Brien", `'); DELETE FROM tasks; --`, '/* not a comment */ $1',
  'line one\nline two\tend', '🦊 café 中文 العربية', 'é / e\u0301', '\u0001control',
  'x'.repeat(1024),
];
let pipe: Client | undefined;
let listHandle: string | undefined;
let credential = 'alice-token';
let frontend!: SqlClient;
let db!: ReturnType<typeof createDrizzle>;
let context = 'setup';
let failure: unknown;
function hasSqlCode(error: unknown, code: string): boolean {
  if (error instanceof SqlError) return error.code === code;
  return error instanceof Error && error.cause !== undefined && hasSqlCode(error.cause, code);
}
function open(mode: 'create' | 'open'): void {
  listHandle = undefined;
  const session = Client.spawn({ command: process.env.JAYDB_SQL_BINARY ?? join(root, 'jaydb2'), cwd: root,
    args: ['--configuration', join(app, 'Configuration.bend'), '--storage', storage, '--storage-mode', mode,
      ...mode === 'create' ? ['--seed', join(app, 'Seed.bend')] : [], '--threads', '1'] });
  pipe = session;
  frontend = new SqlClient({
    prepare(request) {
      summary.preparations++;
      shapes.add(createHash('sha256').update(request.code).update('\0').update(request.proof).digest('hex'));
      return session.prepare(request);
    },
    execute(request) { summary.nativeExecutions++; return session.execute(request); },
  }, { credential: () => credential });
  db = createDrizzle(frontend);
}
function actor(name: Actor): void { credential = `${name}-token`; }
function expectedResult(outcome: ModelOutcome): ModelResult {
  assert.equal(outcome.kind, 'result', `${context}: expected a successful oracle operation`);
  return (outcome as { kind: 'result'; result: ModelResult }).result;
}
async function raw(name: Actor, query: string, params: unknown[] = [], validation = false): Promise<void> {
  actor(name);
  const expected = models[name].execute(query, params);
  summary.rawSqlComparisons++;
  if (validation) summary.validationReads++;
  const operation = frontend.query(query, params);
  if (expected.kind === 'duplicate') {
    await assert.rejects(operation, error => hasSqlCode(error, '23505'), `${context}: SQL duplicate must refuse`);
    summary.duplicateRefusals++;
  } else assert.deepEqual(await operation, expected.result, `${context}: ${name} ${query}`);
}
async function orm(name: Actor, query: OrmQuery, fields: readonly string[]): Promise<void> {
  actor(name);
  const compiled = query.toSQL();
  const expected = models[name].execute(compiled.sql, compiled.params);
  summary.drizzleComparisons++;
  if (expected.kind === 'duplicate') {
    await assert.rejects(Promise.resolve(query), error => hasSqlCode(error, '23505'), `${context}: Drizzle duplicate must refuse`);
    summary.duplicateRefusals++;
  } else {
    const objects = expected.result.rows.map(row => Object.fromEntries(fields.map((field, index) => [field, row[index]])));
    assert.deepEqual(await query, objects, `${context}: ${name} Drizzle ${compiled.sql}`);
  }
}
async function read(name: Actor, key: string): Promise<void> {
  await raw(name, 'select id, title, completed, owner from tasks where id=$1', [key], true);
}
async function audit(recovery = false): Promise<void> {
  for (const name of actors) {
    actor(name);
    // Query the complete actual key set using the separately certified task
    // program. Checking only attempted SQL keys would miss unintended extra rows.
    if (!listHandle) {
      const concrete = 'def B.certificate(s, valid, identity, n):\n  certify(I.context(), I.arguments(), B.code(), s, valid, identity, n)';
      const universal = 'def B.certificate(ctx, args, s, valid, identity, n):\n  certify(ctx, args, B.code(), s, valid, identity, n)';
      const proof = readFileSync(join(app, 'ClientProof.bend'), 'utf8');
      assert.equal(proof.split(concrete).length, 2, 'Task certificate wrapper changed');
      const prepared = await pipe!.prepare({ credential, code: readFileSync(join(app, 'Client.bend'), 'utf8'), proof: proof.replace(concrete, universal) });
      assert.equal(prepared.status, 'prepared'); assert.equal(typeof prepared.value, 'string');
      listHandle = prepared.value as string;
      summary.enumerationPreparations++;
    }
    const actual = await pipe!.execute({ credential, handle: listHandle, arguments: ['list'] });
    assert.equal(actual.status, 'success'); assert.ok(Array.isArray(actual.value));
    const expected = expectedResult(models[name].execute('SELECT id FROM tasks'));
    assert.deepEqual([...actual.value].sort(), expected.rows.map(row => row[0]).sort(), `${context}: complete ${name} key set`);
    summary.keySetAudits++;
    for (const key of keys) {
      await read(name, key);
      if (recovery) summary.recoveryChecks++;
    }
  }
}
const watchdog = setTimeout(() => {
  console.error(`SQL stress development watchdog expired at ${context}`);
  pipe?.abort();
}, Number(process.env.SQL_STRESS_TIMEOUT_MS ?? '1200000'));
watchdog.unref();

try {
  execFileSync('python3', ['-B', join(root, 'applications/sql/prepare.py'), app]);
  open('create');
  // Explicit controls guarantee important paths even if a randomized seed does
  // not happen to encounter them. SQLite itself decides all retained state.
  context = 'deterministic duplicate/rollback controls';
  keys.add('collision'); keys.add('provisional'); keys.add('self-duplicate'); keys.add('fifo');
  for (const name of actors) {
    await raw(name, 'insert into tasks (id,title) values ($1,$2) returning id,title,completed', ['collision', `${name} original`]);
    await raw(name, 'insert into tasks (id,title,completed) values ($1,$2,$3),($4,$5,$6) returning id,title,completed',
      ['provisional', 'must roll back', false, 'collision', 'must not replace', true]);
    await read(name, 'provisional'); await read(name, 'collision');
    await raw(name, 'insert into tasks (id,title,completed) values ($1,$2,$3),($4,$5,$6) returning id,title,completed',
      ['self-duplicate', 'first provisional', false, 'self-duplicate', 'second duplicate', true]);
    await read(name, 'self-duplicate');
  }
  context = 'maximum supported projection width';
  const wideSql = `select ${Array.from({ length: 4 }, () => allColumns).flat().join(',')} from tasks where id=$1`;
  for (const name of actors) await raw(name, wideSql, ['collision']);
  context = 'concurrent invocation order and credentials';
  await raw('alice', 'insert into tasks (id,title,completed) values ($1,$2,$3)', ['fifo', 'before', false]);
  // An update followed immediately by a read must observe invocation FIFO even
  // when their source shapes are cold; do not await the update before reading.
  actor('alice');
  const updateSql = 'update tasks set title=$1,completed=$2 where id=$3 returning id,title,completed,owner';
  const selectSql = 'select id,title,completed,owner from tasks where id=$1';
  const expectedUpdate = expectedResult(models.alice.execute(updateSql, ['after', true, 'fifo']));
  const expectedRead = expectedResult(models.alice.execute(selectSql, ['fifo']));
  const update = frontend.query(updateSql, ['after', true, 'fifo']);
  const afterUpdate = frontend.query(selectSql, ['fifo']);
  assert.deepEqual(await Promise.all([update, afterUpdate]), [expectedUpdate, expectedRead], context);
  summary.concurrentControls++;
  credential = 'invalid-token';
  const denied = frontend.query(selectSql, ['collision']);
  actor('bob');
  const allowed = frontend.query(selectSql, ['collision']);
  await assert.rejects(denied, error => hasSqlCode(error, '28000'), context);
  assert.deepEqual(await allowed, expectedResult(models.bob.execute(selectSql, ['collision'])), context);
  summary.authenticationDenials++; summary.concurrentControls++;

  // Drizzle named placeholders run through Drizzle's actual prepare/fill path.
  context = 'Drizzle named preparation';
  const preparedSelect = db.select().from(tasks).where(eq(tasks.id, sqlText.placeholder('key'))).prepare('stress_task');
  for (const name of actors) {
    actor(name);
    const expected = expectedResult(models[name].execute(selectSql, ['collision']));
    assert.deepEqual(await preparedSelect.execute({ key: 'collision' }), expected.rows.map(row => Object.fromEntries(allColumns.map((field, index) => [field, row[index]]))), context);
    summary.drizzleComparisons++;
  }

  for (const seed of seeds) {
    const next = random(seed);
    const pick = <T>(items: readonly T[]): T => items[Math.floor(next() * items.length)]!;
    for (let step = 0; step < steps; step++) {
      const name = pick(actors), key = pick(keyPool), title = `${seed}:${step} ${pick(titles)}`, done = next() < 0.5;
      const operation = Math.floor(next() * 10);
      const drizzle = next() < 0.35;
      context = `seed=${seed} step=${step} operation=${operation} actor=${name} key=${JSON.stringify(key)}`;
      keys.add(key);
      switch (operation) {
        case 0: case 1:
          if (drizzle) await orm(name, db.insert(writes).values({ id: key, title, completed: done }).returning(), writableColumns);
          else await raw(name, 'insert into tasks (id,title,completed) values ($1,$2,$3) returning id,title,completed', [key, title, done]);
          break;
        case 2:
          if (drizzle) await orm(name, db.select().from(tasks).where(eq(tasks.id, key)), allColumns);
          else await raw(name, `select id,title,completed,owner from tasks where ((id = ${quote(key)}))`);
          break;
        case 3:
          if (drizzle) await orm(name, db.update(tasks).set({ title, completed: done }).where(eq(tasks.id, key)).returning(), allColumns);
          else await raw(name, updateSql, [title, done, key]);
          break;
        case 4:
          if (drizzle) await orm(name, db.update(tasks).set({ title }).where(eq(tasks.id, key)).returning(), allColumns);
          else await raw(name, 'update tasks set title=$1 where id=$2', [title, key]);
          break;
        case 5:
          if (drizzle) await orm(name, db.update(tasks).set({ completed: done }).where(eq(tasks.id, key)).returning(), allColumns);
          else await raw(name, 'update tasks set completed=$1 where id=$2 returning id,title,completed,owner', [done, key]);
          break;
        case 6:
          if (drizzle) await orm(name, db.delete(tasks).where(eq(tasks.id, key)).returning(), allColumns);
          else await raw(name, 'delete from tasks where id=$1 returning id,title,completed,owner', [key]);
          break;
        case 7:
          await raw(name, 'delete from tasks where id=$1', [key]);
          break;
        case 8: {
          const second = next() < 0.5 ? key : pick(keyPool);
          keys.add(second);
          if (drizzle) await orm(name, db.insert(writes).values([{ id: key, title, completed: done }, { id: second, title: 'second ' + title, completed: !done }]).returning(), writableColumns);
          else await raw(name, 'insert into tasks (id,title,completed) values ($1,$2,$3),($4,$5,$6) returning id,title,completed', [key, title, done, second, 'second ' + title, !done]);
          // Immediate checks detect provisional writes surviving any refusal,
          // independently of what a later random operation might overwrite.
          await read(name, key); if (second !== key) await read(name, second);
          break;
        }
        case 9:
          await raw(name, `insert into tasks (title,id) values (${quote(title)},${quote(key)}) returning id,title,completed`);
          break;
      }
      summary.randomizedSteps++;
      if (summary.randomizedSteps % 100 === 0) console.log(`SQL stress: ${summary.randomizedSteps}/${seeds.length * steps} random steps; ${summary.nativeExecutions} native executions; ${summary.duplicateRefusals} expected duplicate refusals.`);
    }
  }
  context = 'full retained-state audit before restart';
  await audit();
  context = 'durable close/reopen';
  await pipe!.close();
  open('open');
  await audit(true);
  summary.status = 'passed';
  console.log(`PASS SQL stress: ${summary.randomizedSteps} seeded random steps, ${summary.rawSqlComparisons} raw SQL and ${summary.drizzleComparisons} Drizzle comparisons, ${summary.duplicateRefusals} expected duplicates, ${summary.recoveryChecks} durable recovered rows/absences checked.`);
} catch (error) {
  failure = error; summary.status = 'failed';
  summary.failure = `${context}: ${error instanceof Error ? error.stack ?? error.message : String(error)}`;
  throw error;
} finally {
  clearTimeout(watchdog);
  summary.distinctPreparedShapes = shapes.size;
  try { await pipe?.close(); } catch (error) {
    if (!failure) {
      summary.status = 'failed';
      summary.failure = `Closing final session: ${error instanceof Error ? error.stack ?? error.message : String(error)}`;
      throw error;
    }
  }
  finally {
    summary.elapsedMs = Date.now() - started;
    for (const name of actors) models[name].close();
    if (process.env.SQL_STRESS_REPORT) {
      mkdirSync(dirname(process.env.SQL_STRESS_REPORT), { recursive: true });
      writeFileSync(process.env.SQL_STRESS_REPORT, JSON.stringify(summary, null, 2) + '\n');
    }
    rmSync(directory, { recursive: true, force: true });
  }
}
