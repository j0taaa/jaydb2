import assert from 'node:assert/strict';
import test from 'node:test';
import { parseSql } from '../src/parser.ts';
import { SqlError } from '../src/plan.ts';
import { drizzle } from 'drizzle-orm/pg-proxy';
import { boolean, pgTable, text } from 'drizzle-orm/pg-core';
import { sql } from 'drizzle-orm';

const literal = (value: string | boolean | bigint | null) => ({ kind: 'literal', value });
const parameter = (index: number) => ({ kind: 'parameter', index });

test('Drizzle SELECT quoting, qualified fields, aliases and parameters', () => {
  assert.deepEqual(parseSql('select "tasks"."id", "tasks"."title" as "displayName", "completed" from "tasks" where "tasks"."id" = $1'), {
    kind: 'select', table: 'tasks', columns: [
      { column: 'id', alias: 'id' }, { column: 'title', alias: 'displayName' }, { column: 'completed', alias: 'completed' },
    ], key: parameter(0),
  });
});

test('SQL strings contain SQL punctuation without becoming statements', () => {
  const title = "O'Brien; -- not a comment /* either */";
  assert.deepEqual(parseSql("INSERT INTO tasks (id, title, completed) VALUES ($2, 'O''Brien; -- not a comment /* either */', false), ('second', $1, DEFAULT) RETURNING title, id;"), {
    kind: 'insert', table: 'tasks', columns: ['id', 'title', 'completed'],
    rows: [[parameter(1), literal(title), literal(false)], [literal('second'), parameter(0), { kind: 'default' }]],
    returning: [{ column: 'title', alias: 'title' }, { column: 'id', alias: 'id' }],
  });
});

test('UPDATE and DELETE preserve assignments and RETURNING order', () => {
  assert.deepEqual(parseSql('UPDATE tasks SET "title" = $1, "completed" = true WHERE ("tasks"."id" = $2) RETURNING "completed", "title"'), {
    kind: 'update', table: 'tasks', assignments: [{ column: 'title', value: parameter(0) }, { column: 'completed', value: literal(true) }],
    key: parameter(1), returning: [{ column: 'completed', alias: 'completed' }, { column: 'title', alias: 'title' }],
  });
  assert.deepEqual(parseSql("DELETE FROM tasks WHERE 'x' = id RETURNING tasks.*"), {
    kind: 'delete', table: 'tasks', key: literal('x'), returning: ['id', 'title', 'completed', 'owner'].map(column => ({ column, alias: column })),
  });
});

test('parenthesized predicates and operands, case folding, comments and repeated parameters', () => {
  for (const predicate of ['id = $1', '(id = $1)', '((id = $1))', '(id) = ($1)', '((id)) = (($1))', '($1 = id)', '((($1)) = ((id)))']) {
    assert.deepEqual(parseSql(`/* one /* nested */ block */ SELECT TITLE label FROM TASKS WHERE ${predicate}; -- end`), {
      kind: 'select', table: 'tasks', columns: [{ column: 'title', alias: 'label' }], key: parameter(0),
    });
  }
  const repeated = parseSql('insert into tasks (id, title) values ($1, $1)');
  assert.equal(repeated.kind, 'insert');
  if (repeated.kind === 'insert') assert.deepEqual(repeated.rows, [[parameter(0), parameter(0)]]);
});

test('star expands in logical schema order and duplicate projections remain ordered', () => {
  const statement = parseSql('SELECT *, title as id FROM tasks WHERE id = \'x\'');
  assert.equal(statement.kind, 'select');
  if (statement.kind !== 'select') return;
  assert.deepEqual(statement.columns, [
    ...['id', 'title', 'completed', 'owner'].map(column => ({ column, alias: column })), { column: 'title', alias: 'id' },
  ]);
});

test('literal values keep booleans, absence and large integers exact', () => {
  assert.deepEqual(parseSql('INSERT INTO tasks (id, title, completed) VALUES (9223372036854775807, NULL, TRUE)'), {
    kind: 'insert', table: 'tasks', columns: ['id', 'title', 'completed'],
    rows: [[literal(9223372036854775807n), literal(null), literal(true)]], returning: [],
  });
});

test('reject unsupported syntax, scans, extra clauses and multiple statements', () => {
  for (const sql of [
    '', 'select * from tasks', 'select * from tasks where title = $1',
    'select * from tasks where id = $1 and completed = false', 'select * from tasks where id = $1 limit 1',
    'select * from tasks where id = $1; delete from tasks where id = $2',
    'select count(*) from tasks where id = $1', 'select * from tasks t where t.id = $1',
    'select * from tasks where id <> $1', 'select * from tasks where id = $1::text',
    'select * from tasks join other on tasks.id = other.id where id = $1',
    'insert into tasks (id, title) values ($1)', 'insert into tasks (id, id) values ($1, $2)',
    'insert into tasks (owner, id, title) values ($1, $2, $3)',
    'insert into tasks (id, title) values ($1, $2) on conflict do nothing',
    'update tasks set id = $1 where id = $2', 'update tasks set owner = $1 where id = $2',
    'update tasks set title = $1, title = $2 where id = $3', 'update tasks set title = default where id = $1',
    'delete from tasks', 'begin', 'create table tasks (id text)',
  ]) assert.throws(() => parseSql(sql), SqlError, sql);
});

test('reject malformed lexemes and unknown identifiers with PostgreSQL-style error codes', () => {
  for (const sql of ["select title from tasks where id = 'unterminated", 'select title from tasks where id = $0',
    'select title from tasks where id = $9999999999999999999999999', 'select title from tasks where id = $$foo$$',
    'select title from tasks where id = $1 /* unfinished', 'select title from tasks where id = 1.5',
    'select title from tasks where id = E\'hello\'', 'select title from tasks where id = $1;;']) {
    assert.throws(() => parseSql(sql), SqlError, sql);
  }
  for (const [sql, code] of [
    ['select title from secrets where id = $1', '42P01'], ['select private from tasks where id = $1', '42703'],
    ['select "Title" from tasks where id = $1', '42703'], ['select other.title from tasks where id = $1', '42P01'],
    ['select title from "Tasks" where id = $1', '42P01'],
  ]) assert.throws(() => parseSql(sql!), (error: unknown) => error instanceof SqlError && error.code === code, sql);
});


test('Drizzle full schema INSERT permits owner DEFAULT and preserves owner RETURNING', () => {
  const tasks = pgTable('tasks', {
    id: text('id').primaryKey(), title: text('title').notNull(), completed: boolean('completed').notNull().default(false),
    owner: text('owner').notNull().default(sql`current_user`),
  });
  const db = drizzle(async () => { throw new Error('Building SQL must not execute'); });
  const query = db.insert(tasks).values([{ id: 'first', title: 'One' }, { id: 'second', title: 'Two', completed: true }]).returning().toSQL();
  assert.deepEqual(query.params, ['first', 'One', 'second', 'Two', true]);
  assert.deepEqual(parseSql(query.sql), {
    kind: 'insert', table: 'tasks', columns: ['id', 'title', 'completed', 'owner'],
    rows: [[parameter(0), parameter(1), { kind: 'default' }, { kind: 'default' }],
      [parameter(2), parameter(3), parameter(4), { kind: 'default' }]],
    returning: ['id', 'title', 'completed', 'owner'].map(column => ({ column, alias: column })),
  });
  for (const value of ["'alice'", '$3', 'NULL', "'DEFAULT'"]) {
    assert.throws(() => parseSql(`insert into tasks (id, title, owner) values ($1, $2, ${value})`), SqlError);
    assert.throws(() => parseSql(`insert into tasks (id, title, owner) values ($1, $2, default), ($4, $5, ${value})`), SqlError);
  }
});

test('predicate parsing bounds nesting and handles adversarial ambiguous wrappers without backtracking', () => {
  const wrappers = (depth: number, value: string) => '('.repeat(depth) + value + ')'.repeat(depth);
  assert.equal(parseSql(`select title from tasks where ${wrappers(64, 'id = $1')}`).kind, 'select');
  assert.equal(parseSql(`select title from tasks where ${wrappers(64, 'id')} = ${wrappers(64, '$1')}`).kind, 'select');
  for (const depth of [65, 1000, 10_000]) {
    assert.throws(() => parseSql(`select title from tasks where ${wrappers(depth, 'id = $1')}`),
      (error: unknown) => error instanceof SqlError && error.code === '54001');
  }
  for (const value of ['id =', 'id', '(id) = ($1) and title = $2']) {
    assert.throws(() => parseSql(`select title from tasks where ${wrappers(64, value)}`), SqlError);
  }
});

test('numeric and parameter lexemes cannot run into identifiers; punctuation in values stays opaque', () => {
  for (const key of ['$1AND', '$1foo', '$1$2', '1foo', '1true', '123_id', '1e3', '-2text', '+2foo']) {
    assert.throws(() => parseSql(`select title from tasks where id = ${key}`), SqlError, key);
  }
  for (const key of [';', 'returning', '(', ')']) {
    const statement = parseSql(`select title from tasks where id = '${key}'`);
    assert.equal(statement.kind, 'select');
    if (statement.kind === 'select') assert.deepEqual(statement.key, literal(key));
  }
});
