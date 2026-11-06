import { SqlError } from './plan.ts';
import type { Column, Expression, Projection, Statement } from './plan.ts';

type Token = { kind: 'word' | 'identifier' | 'string' | 'integer' | 'parameter' | 'symbol' | 'end'; text: string; offset: number };
const columns: readonly Column[] = ['id', 'title', 'completed', 'owner'];
const reserved = new Set(['select', 'from', 'where', 'insert', 'into', 'values', 'returning', 'update', 'set', 'delete', 'as', 'and', 'or', 'order', 'limit', 'offset', 'join', 'group', 'having', 'union', 'on', 'conflict']);
function fail(message: string, token: Pick<Token, 'offset'>, code = '0A000'): never {
  throw new SqlError(`${message} at SQL offset ${token.offset}`, code);
}

/** Lex SQL rather than splitting on punctuation: strings and comments are opaque. */
function tokenize(sql: string): Token[] {
  const tokens: Token[] = [];
  let at = 0;
  while (at < sql.length) {
    const start = at;
    const ch = sql[at]!;
    if (/\s/u.test(ch)) { at++; continue; }
    if (sql.startsWith('--', at)) {
      at += 2;
      while (at < sql.length && sql[at] !== '\n' && sql[at] !== '\r') at++;
      continue;
    }
    if (sql.startsWith('/*', at)) {
      at += 2;
      let depth = 1;
      while (at < sql.length && depth) {
        if (sql.startsWith('/*', at)) { depth++; at += 2; }
        else if (sql.startsWith('*/', at)) { depth--; at += 2; }
        else at++;
      }
      if (depth) fail('Unterminated block comment', { offset: start }, '42601');
      continue;
    }
    if (ch === "'" || ch === '"') {
      at++;
      let value = '';
      let closed = false;
      while (at < sql.length) {
        if (sql[at] === ch) {
          if (sql[at + 1] === ch) { value += ch; at += 2; }
          else { at++; closed = true; break; }
        } else value += sql[at++]!;
      }
      if (!closed) fail('Unterminated quoted value', { offset: start }, '42601');
      if (value.includes('\0')) fail('NUL is not valid in SQL text', { offset: start }, '42601');
      tokens.push({ kind: ch === "'" ? 'string' : 'identifier', text: value, offset: start });
      continue;
    }
    if (ch === '$') {
      at++;
      const digits = at;
      while (at < sql.length && /[0-9]/u.test(sql[at]!)) at++;
      if (at === digits) fail('Only numbered $1 parameters are supported', { offset: start });
      if (/[A-Za-z_$]/u.test(sql[at] ?? '')) fail('Parameter index must end before an identifier', { offset: start }, '42601');
      const text = sql.slice(digits, at);
      const n = Number(text);
      if (!Number.isSafeInteger(n) || n < 1) fail('Invalid parameter index', { offset: start }, '42P02');
      tokens.push({ kind: 'parameter', text, offset: start });
      continue;
    }
    if (/[0-9]/u.test(ch) || ((ch === '-' || ch === '+') && /[0-9]/u.test(sql[at + 1] ?? ''))) {
      at++;
      while (at < sql.length && /[0-9]/u.test(sql[at]!)) at++;
      if (/[A-Za-z_$]/u.test(sql[at] ?? '')) fail('Integer must end before an identifier', { offset: start }, '42601');
      tokens.push({ kind: 'integer', text: sql.slice(start, at), offset: start });
      continue;
    }
    if (/[A-Za-z_]/u.test(ch)) {
      at++;
      while (at < sql.length && /[A-Za-z0-9_$]/u.test(sql[at]!)) at++;
      tokens.push({ kind: 'word', text: sql.slice(start, at).toLowerCase(), offset: start });
      continue;
    }
    if ('.,*()=;'.includes(ch)) { at++; tokens.push({ kind: 'symbol', text: ch, offset: start }); continue; }
    fail(`Unsupported SQL character ${JSON.stringify(ch)}`, { offset: start });
  }
  tokens.push({ kind: 'end', text: '', offset: at });
  return tokens;
}

class Parser {
  #tokens: Token[];
  #at = 0;
  #closing = new Map<number, number>();
  constructor(sql: string) {
    this.#tokens = tokenize(sql);
    const opening: number[] = [];
    for (let index = 0; index < this.#tokens.length; index++) {
      const token = this.#tokens[index]!;
      if (token.kind !== 'symbol') continue;
      if (token.text === '(') {
        if (opening.length >= 64) fail('SQL parenthesis nesting exceeds 64 levels', token, '54001');
        opening.push(index);
      } else if (token.text === ')') {
        const start = opening.pop();
        if (start === undefined) fail('Unmatched closing parenthesis', token, '42601');
        this.#closing.set(start, index);
      }
    }
    if (opening.length) fail('Unclosed parenthesis', this.#tokens[opening[0]!]!, '42601');
  }
  peek(): Token { return this.#tokens[this.#at]!; }
  take(): Token { return this.#tokens[this.#at++]!; }
  is(text: string): boolean {
    const token = this.peek();
    return (token.kind === 'word' || token.kind === 'symbol') && token.text === text;
  }
  accept(text: string): boolean { if (!this.is(text)) return false; this.take(); return true; }
  expect(text: string): void { if (!this.accept(text)) fail(`Expected ${text}`, this.peek(), '42601'); }
  identifier(): string {
    const token = this.take();
    if (token.kind !== 'word' && token.kind !== 'identifier') fail('Expected an identifier', token, '42601');
    if (token.kind === 'word' && reserved.has(token.text)) fail('Reserved word requires a quoted identifier', token, '42601');
    return token.text;
  }
  table(): 'tasks' {
    const token = this.peek();
    const name = this.identifier();
    if (name !== 'tasks') fail(`Unknown table ${JSON.stringify(name)}; this adapter exposes tasks`, token, '42P01');
    if (this.is('.')) fail('Schema-qualified table names are not supported', this.peek());
    return 'tasks';
  }
  column(): Column {
    const token = this.peek();
    let name = this.identifier();
    if (this.accept('.')) {
      if (name !== 'tasks') fail(`Unknown table qualifier ${JSON.stringify(name)}`, token, '42P01');
      name = this.identifier();
    }
    if (!columns.includes(name as Column)) fail(`Unknown column ${JSON.stringify(name)}`, token, '42703');
    return name as Column;
  }
  projections(): Projection[] {
    const result: Projection[] = [];
    do {
      if (this.accept('*')) result.push(...columns.map(column => ({ column, alias: column })));
      else if ((this.peek().kind === 'word' || this.peek().kind === 'identifier') && this.peek().text === 'tasks'
        && this.#tokens[this.#at + 1]?.text === '.' && this.#tokens[this.#at + 2]?.text === '*') {
        this.take(); this.take(); this.take();
        result.push(...columns.map(column => ({ column, alias: column })));
      } else {
        const column = this.column();
        let alias: string = column;
        if (this.accept('as')) alias = this.identifier();
        else if (this.peek().kind === 'identifier' || (this.peek().kind === 'word' && !reserved.has(this.peek().text))) alias = this.identifier();
        result.push({ column, alias });
      }
    } while (this.accept(','));
    return result;
  }
  expression(allowDefault = false): Expression {
    const token = this.take();
    switch (token.kind) {
      case 'parameter': return { kind: 'parameter', index: Number(token.text) - 1 };
      case 'string': return { kind: 'literal', value: token.text };
      case 'integer': return { kind: 'literal', value: BigInt(token.text) };
      case 'word':
        if (token.text === 'true' || token.text === 'false') return { kind: 'literal', value: token.text === 'true' };
        if (token.text === 'null') return { kind: 'literal', value: null };
        if (allowDefault && token.text === 'default') return { kind: 'default' };
    }
    fail('Expected a literal or numbered parameter', token);
  }
  operand(): { column: Column } | { expression: Expression } {
    // Parse operand wrappers iteratively: nesting cannot consume the JS stack.
    let depth = 0;
    while (this.accept('(')) depth++;
    const token = this.peek();
    const result = token.kind === 'identifier' || (token.kind === 'word' && !['true', 'false', 'null', 'default'].includes(token.text))
      ? { column: this.column() } : { expression: this.expression() };
    while (depth--) this.expect(')');
    return result;
  }
  predicate(): Expression {
    // Determine the predicate range, then remove only parentheses enclosing the
    // whole equality. Matching pairs avoid recursive, ambiguous backtracking.
    let end = this.#at;
    while (this.#tokens[end]!.kind !== 'end' && !(this.#tokens[end]!.kind === 'symbol' && this.#tokens[end]!.text === ';')
      && !(this.#tokens[end]!.kind === 'word' && this.#tokens[end]!.text === 'returning')) end++;
    const after = end;
    while (this.#closing.get(this.#at) === end - 1) { this.#at++; end--; }
    const left = this.operand(); this.expect('='); const right = this.operand();
    if (this.#at !== end) fail('Only a single equality on the id primary key is supported', this.peek());
    this.#at = after;
    if ('column' in left && left.column === 'id' && 'expression' in right) return right.expression;
    if ('expression' in left && 'column' in right && right.column === 'id') return left.expression;
    fail('Only equality on the id primary key is supported', this.peek());
  }
  where(): Expression {
    if (!this.accept('where')) fail('A WHERE id = value predicate is required; table scans are not supported', this.peek());
    return this.predicate();
  }
  returning(): Projection[] { return this.accept('returning') ? this.projections() : []; }
  parse(): Statement {
    let statement: Statement;
    if (this.accept('select')) {
      const projection = this.projections(); this.expect('from'); const table = this.table();
      statement = { kind: 'select', table, columns: projection, key: this.where() };
    } else if (this.accept('insert')) {
      this.expect('into'); const table = this.table(); this.expect('(');
      const names: Column[] = [];
      do {
        const token = this.peek(); const name = this.column();
        if (names.includes(name)) fail(`Column ${name} is specified twice`, token, '42701');
        names.push(name);
      } while (this.accept(','));
      this.expect(')'); this.expect('values');
      const rows: Expression[][] = [];
      do {
        this.expect('('); const values: Expression[] = [];
        do { values.push(this.expression(true)); } while (this.accept(','));
        this.expect(')');
        if (values.length !== names.length) fail('INSERT column and value counts differ', this.peek(), '42601');
        const owner = names.indexOf('owner');
        if (owner !== -1 && values[owner]?.kind !== 'default')
          fail('owner must be DEFAULT; its value comes from the authenticated database context', this.peek());
        rows.push(values);
      } while (this.accept(','));
      statement = { kind: 'insert', table, columns: names, rows, returning: this.returning() };
    } else if (this.accept('update')) {
      const table = this.table(); this.expect('set');
      const assignments: { column: Column; value: Expression }[] = [];
      do {
        const token = this.peek(); const column = this.column();
        if (column !== 'title' && column !== 'completed') fail(`Column ${column} cannot be updated`, token);
        if (assignments.some(assignment => assignment.column === column)) fail(`Column ${column} is assigned twice`, token, '42701');
        this.expect('='); assignments.push({ column, value: this.expression() });
      } while (this.accept(','));
      statement = { kind: 'update', table, assignments, key: this.where(), returning: this.returning() };
    } else if (this.accept('delete')) {
      this.expect('from'); const table = this.table();
      statement = { kind: 'delete', table, key: this.where(), returning: this.returning() };
    } else fail('Only SELECT, INSERT, UPDATE and DELETE are supported', this.peek());
    this.accept(';');
    if (this.peek().kind !== 'end') fail('Unsupported SQL clause or multiple statements', this.peek());
    return statement;
  }
}

/** Parse a single supported statement; unsupported behavior is never silently ignored. */
export function parseSql(sql: string): Statement {
  if (typeof sql !== 'string') throw new TypeError('SQL must be a string');
  return new Parser(sql).parse();
}
