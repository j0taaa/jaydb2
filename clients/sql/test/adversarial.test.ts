import assert from 'node:assert/strict';
import test from 'node:test';
import { DatabaseSync } from 'node:sqlite';
import { compileSql } from '../src/compiler.ts';
import { parseSql } from '../src/parser.ts';
import { SqlError } from '../src/plan.ts';
import type { Column, Expression, Projection, Statement } from '../src/plan.ts';

// Fixed seeds make every failure reproducible without a fuzzing dependency.
function random(seed: number) {
  let state = seed >>> 0;
  return (size: number): number => {
    state = (Math.imul(state, 1664525) + 1013904223) >>> 0;
    return state % size;
  };
}
const names: Column[] = ['id', 'title', 'completed', 'owner'];
const textValues = [
  '', 'plain', "O'Brien", '"quoted"', '; DROP TABLE tasks; --', '/* nested /* comment */ */',
  'returning', '($999)', '\\', '\n\t\r', '🦊🚀', '漢字', 'e\u0301', 'é', '\u2028\u2029', '\ufeff',
];
const quoted = (value: string): string => `'${value.replaceAll("'", "''")}'`;
const ident = (value: string): string => `"${value.replaceAll('"', '""')}"`;
const literal = (value: string | boolean): Expression => ({ kind: 'literal', value });
function shuffle<T>(items: readonly T[], draw: (size: number) => number): T[] {
  const result = [...items];
  for (let i = result.length - 1; i > 0; i--) {
    const j = draw(i + 1); [result[i], result[j]] = [result[j]!, result[i]!];
  }
  return result;
}
function variants(draw: (size: number) => number) {
  const keyword = (value: string) => draw(2) ? value.toUpperCase() : value;
  const identifier = (value: string) => draw(2) ? ident(value) : draw(2) ? value.toUpperCase() : value;
  const column = (value: Column) => draw(2) ? `${identifier('tasks')}.${identifier(value)}` : identifier(value);
  const space = () => [' ', '\t', '\n', '/**/', ' /* comment */ ', ' -- comment\n'][draw(6)]!;
  const wrap = (value: string) => { const depth = draw(6); return '('.repeat(depth) + value + ')'.repeat(depth); };
  const predicate = (value: string) => {
    const left = wrap(column('id')), right = wrap(value);
    return wrap(draw(2) ? `${left}=${right}` : `${right} = ${left}`);
  };
  const projection = (): { sql: string; columns: Projection[] } => {
    const cols: Projection[] = [];
    const rendered: string[] = [];
    for (let i = 0, size = 1 + draw(6); i < size; i++) {
      const name = names[draw(names.length)]!;
      const alias = ['label', 'MixedCase', 'quote"name', '名前', name][draw(5)]!;
      const useAlias = draw(2);
      cols.push({ column: name, alias: useAlias ? alias : name });
      rendered.push(column(name) + (useAlias ? `${space()}${keyword('as')}${space()}${ident(alias)}` : ''));
    }
    return { sql: rendered.join(','), columns: cols };
  };
  return { keyword, identifier, space, predicate, projection };
}

// These tests generate queries from known data and an independent grammar. They
// do not derive expectations by interpreting the parser's output.
test('2,048 generated SELECT spellings retain values, projection order and labels', () => {
  const draw = random(0x53514c31);
  for (let i = 0; i < 2048; i++) {
    const v = variants(draw), projection = v.projection();
    const key = textValues[draw(textValues.length)]! + i;
    const parameter = draw(2);
    const query = `${v.keyword('select')}${v.space()}${projection.sql}${v.space()}${v.keyword('from')}${v.space()}${v.identifier('tasks')}${v.space()}${v.keyword('where')}${v.space()}${v.predicate(parameter ? '$1' : quoted(key))}${draw(2) ? '; -- finished' : ''}`;
    const expected: Statement = { kind: 'select', table: 'tasks', columns: projection.columns,
      key: parameter ? { kind: 'parameter', index: 0 } : literal(key) };
    const compiled = compileSql(query);
    assert.deepEqual(compiled.statement, expected, query);
    assert.deepEqual(compiled.columns, projection.columns.map(p => p.alias), query);
    assert.deepEqual(compiled.bind(parameter ? [key] : []), [[key]], query);
  }
});

test('2,048 generated INSERTs preserve column permutations, defaults and all row arguments', () => {
  const draw = random(0x53514c32);
  for (let i = 0; i < 2048; i++) {
    const v = variants(draw);
    const columns = shuffle<Column>(['id', 'title', ...draw(2) ? ['completed' as const] : [], ...draw(2) ? ['owner' as const] : []], draw);
    const params: unknown[] = [], rows: Expression[][] = [], rendered: string[] = [], normalized: unknown[][] = [];
    for (let row = 0, count = 1 + draw(2); row < count; row++) {
      const key = `key-${i}-${row}`, title = textValues[draw(textValues.length)]!;
      let completed = false;
      const expressions: Expression[] = [], sql: string[] = [];
      for (const column of columns) {
        if (column === 'owner' || (column === 'completed' && draw(3) === 0)) {
          expressions.push({ kind: 'default' }); sql.push(v.keyword('default')); continue;
        }
        const value = column === 'id' ? key : column === 'title' ? title : Boolean(draw(2));
        if (column === 'completed') completed = value as boolean;
        if (draw(2)) {
          expressions.push({ kind: 'parameter', index: params.length }); params.push(value); sql.push(`$${params.length}`);
        } else { expressions.push(literal(value)); sql.push(typeof value === 'string' ? quoted(value) : v.keyword(String(value))); }
      }
      rows.push(expressions); rendered.push(`(${sql.join(',')})`); normalized.push([key, title, completed]);
    }
    const projection = v.projection();
    const query = `${v.keyword('insert')}${v.space()}${v.keyword('into')}${v.space()}${v.identifier('tasks')}(${columns.map(v.identifier).join(',')})${v.space()}${v.keyword('values')}${v.space()}${rendered.join(',')}${v.space()}${v.keyword('returning')}${v.space()}${projection.sql}`;
    const compiled = compileSql(query);
    assert.deepEqual(compiled.statement, { kind: 'insert', table: 'tasks', columns, rows, returning: projection.columns }, query);
    assert.deepEqual(compiled.bind(params), normalized, query);
  }
});

test('2,048 generated UPDATE/DELETE queries retain assignment and predicate parameter positions', () => {
  const draw = random(0x53514c33);
  for (let i = 0; i < 2048; i++) {
    const v = variants(draw), projection = v.projection(), params: unknown[] = [];
    const key = `key-${i}`, title = textValues[draw(textValues.length)]!, completed = Boolean(draw(2));
    const expression = (value: string | boolean): { ast: Expression; sql: string } => {
      if (draw(2)) { const ast: Expression = { kind: 'parameter', index: params.length }; params.push(value); return { ast, sql: `$${params.length}` }; }
      return { ast: literal(value), sql: typeof value === 'string' ? quoted(value) : v.keyword(String(value)) };
    };
    let expected: Statement, query: string, bound: unknown[][];
    if (i % 2) {
      const chosen = shuffle<Column>(draw(3) === 0 ? ['title', 'completed'] : draw(2) ? ['title'] : ['completed'], draw);
      const assignments: { column: Column; value: Expression }[] = [], rendered: string[] = [];
      for (const column of chosen) {
        const value = expression(column === 'title' ? title : completed);
        assignments.push({ column, value: value.ast }); rendered.push(`${v.identifier(column)}=${value.sql}`);
      }
      const predicate = expression(key);
      query = `${v.keyword('update')}${v.space()}${v.identifier('tasks')}${v.space()}${v.keyword('set')}${v.space()}${rendered.join(',')}${v.space()}${v.keyword('where')}${v.space()}${v.predicate(predicate.sql)}${v.space()}${v.keyword('returning')}${v.space()}${projection.sql}`;
      expected = { kind: 'update', table: 'tasks', assignments, key: predicate.ast, returning: projection.columns };
      bound = [[key, chosen.includes('title') ? title : null, chosen.includes('completed') ? completed : null]];
    } else {
      const predicate = expression(key);
      query = `${v.keyword('delete')}${v.space()}${v.keyword('from')}${v.space()}${v.identifier('tasks')}${v.space()}${v.keyword('where')}${v.space()}${v.predicate(predicate.sql)}${v.space()}${v.keyword('returning')}${v.space()}${projection.sql}`;
      expected = { kind: 'delete', table: 'tasks', key: predicate.ast, returning: projection.columns }; bound = [[key]];
    }
    const compiled = compileSql(query);
    assert.deepEqual(compiled.statement, expected, query);
    assert.deepEqual(compiled.bind(params), bound, query);
  }
});

test('1,024 SELECT projections agree with an independent SQLite SQL engine', () => {
  const db = new DatabaseSync(':memory:');
  try {
    db.exec("CREATE TABLE tasks (id TEXT PRIMARY KEY, title TEXT NOT NULL, completed INTEGER NOT NULL, owner TEXT NOT NULL)");
    db.prepare('INSERT INTO tasks VALUES (?, ?, ?, ?)').run('present', "O'Brien 🦊", 1, 'alice');
    const fixture: Record<Column, string | number> = { id: 'present', title: "O'Brien 🦊", completed: 1, owner: 'alice' };
    const draw = random(0x53514c34);
    for (let i = 0; i < 1024; i++) {
      const chosen = Array.from({ length: 1 + draw(8) }, () => names[draw(names.length)]!);
      const labels = chosen.map((name, index) => draw(2) ? name : ['duplicate', 'Alias"Name', '名前'][index % 3]!);
      const key = draw(4) ? 'present' : 'missing';
      const query = `SELECT ${chosen.map((name, index) => `${ident('tasks')}.${ident(name)} AS ${ident(labels[index]!)}`).join(',')} FROM tasks WHERE ${i % 2 ? 'id = $1' : '$1 = id'}`;
      const compiled = compileSql(query), oracle = db.prepare(query);
      oracle.setReturnArrays(true);
      assert.deepEqual(oracle.columns().map(column => column.name), compiled.columns, query);
      assert.deepEqual(oracle.all({ $1: key }), key === 'present' ? [chosen.map(name => fixture[name])] : [], query);
      assert.deepEqual(compiled.bind([key]), [[key]], query);
    }
  } finally { db.close(); }
});

test('2,048 unsupported suffixes are rejected rather than silently changing query meaning', () => {
  const suffixes = ['ORDER BY id', 'LIMIT 1', 'OFFSET 1', 'AND completed = true', 'OR id = \'other\'',
    'UNION SELECT title FROM tasks', 'RETURNING title', '; DELETE FROM tasks WHERE id = \'x\'',
    'FOR UPDATE', 'GROUP BY title', 'HAVING true', '::text', '|| \'tail\'', '+ 1', '; SELECT 1', 'WHERE id=\'x\''];
  for (let i = 0; i < 2048; i++) {
    const query = `SELECT title FROM tasks WHERE ${'('.repeat(i % 8)}id = $1${')'.repeat(i % 8)} ${suffixes[i % suffixes.length]}`;
    assert.throws(() => compileSql(query), SqlError, query);
  }
});

test('20,000 deterministic mutated token streams never escape as parser crashes', () => {
  const draw = random(0x53514c35);
  const tokens = ['select', 'insert', 'update', 'delete', 'tasks', 'title', 'id', 'where', 'from', 'into', 'set', 'values',
    'returning', 'owner', 'default', '$1', '$0', '$2', 'true', 'false', 'null', "'x'", '"*"', '""', '(', ')', '*', '.', '=', ',', ';', '/*', '*/', '--\n'];
  for (let i = 0; i < 20_000; i++) {
    const query = Array.from({ length: 1 + draw(20) }, () => tokens[draw(tokens.length)]!).join(' ');
    try {
      const parsed = parseSql(query);
      assert.equal(parsed.table, 'tasks', query);
    } catch (error) { assert.ok(error instanceof SqlError, `${query}\n${String(error)}`); }
  }
});

test('quoted stars are identifiers, write targets are unqualified, and malformed SQL text is rejected', () => {
  for (const query of [
    'select tasks."*" from tasks where id=$1', "select tasks.'*' from tasks where id=$1",
    'select "tasks"."*" from tasks where id=$1', 'select tasks."." from tasks where id=$1',
    'insert into tasks(tasks.id,title) values ($1,$2)', 'update tasks set tasks.title=$1 where id=$2',
    'select title as "" from tasks where id=$1',
    'select\u00a0title from tasks where id=$1', 'select\ufefftitle from tasks where id=$1',
    'select title from tasks where id=$1 -- \0', 'select title from tasks where id=$1 /* \0 */',
    'select title as "\ud800" from tasks where id=$1', 'select title from tasks where id=$1 -- \udc00',
  ]) assert.throws(() => parseSql(query), SqlError, query);
  assert.equal(parseSql('select "tasks".* from tasks where id=$1').kind, 'select');
});

test('SQL byte/nesting boundaries and non-array bind arguments fail predictably', () => {
  const start = 'SELECT title FROM tasks WHERE id=$1 --';
  const boundary = start + 'x'.repeat(65536 - Buffer.byteLength(start));
  assert.deepEqual(compileSql(boundary).bind(['x']), [['x']]);
  assert.throws(() => compileSql(boundary + 'x'), (error: unknown) => error instanceof SqlError && error.code === '54000');
  assert.throws(() => parseSql(boundary + 'x'), (error: unknown) => error instanceof SqlError && error.code === '54000');
  const unicodeBoundary = start + 'é'.repeat(Math.floor((65536 - Buffer.byteLength(start)) / 2));
  assert.ok(Buffer.byteLength(unicodeBoundary) <= 65536);
  compileSql(unicodeBoundary);
  assert.throws(() => compileSql(unicodeBoundary + 'é'), SqlError);
  for (const params of ['x', { 0: 'x', length: 1 }, null, 1, new Set(['x'])]) {
    assert.throws(() => compileSql('SELECT title FROM tasks WHERE id=$1').bind(params as never), TypeError);
  }
  for (const param of [null, undefined, false, 0, 0n, {}, [], new String('x'), '\0', '\ud800', '\udc00']) {
    assert.throws(() => compileSql('SELECT title FROM tasks WHERE id=$1').bind([param]), SqlError);
  }
  for (const value of textValues) {
    const compiled = compileSql(`INSERT INTO tasks (id,title) VALUES ('id', ${quoted(value)})`);
    assert.deepEqual(compiled.bind(), [['id', value, false]]);
  }
});

test('projection expansion is bounded before Bend generation and compiled metadata cannot change binding', () => {
  const columns = Array.from({ length: 16 }, (_, i) => `title as "column${i}"`).join(',');
  const accepted = compileSql(`SELECT ${columns} FROM tasks WHERE id=$1`);
  assert.equal(accepted.columns.length, 16);
  for (const projection of [columns + ',title', 'title,'.repeat(999) + 'title', '*,*,*,*,*']) {
    assert.throws(() => compileSql(`SELECT ${projection} FROM tasks WHERE id=$1`),
      (error: unknown) => error instanceof SqlError && error.code === '54000');
    assert.throws(() => compileSql(`INSERT INTO tasks (id,title) VALUES ($1,$2) RETURNING ${projection}`), SqlError);
    assert.throws(() => compileSql(`UPDATE tasks SET title=$1 WHERE id=$2 RETURNING ${projection}`), SqlError);
    assert.throws(() => compileSql(`DELETE FROM tasks WHERE id=$1 RETURNING ${projection}`), SqlError);
  }
  const compiled = compileSql('UPDATE tasks SET title=$1 WHERE id=$2 RETURNING title');
  const statement = compiled.statement;
  if (statement.kind !== 'update') throw new Error('Expected UPDATE');
  assert.throws(() => { statement.assignments[0]!.value = literal('tampered'); }, TypeError);
  assert.throws(() => { statement.assignments.push({ column: 'completed', value: literal(true) }); }, TypeError);
  assert.throws(() => { statement.key = literal('another-key'); }, TypeError);
  assert.throws(() => { (compiled.columns as string[])[0] = 'tampered'; }, TypeError);
  assert.deepEqual(compiled.bind(['original', 'key']), [['key', 'original', null]]);
});
