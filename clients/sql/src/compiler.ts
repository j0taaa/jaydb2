import { compileBend } from './bend.ts';
import { parseSql } from './parser.ts';
import { SqlError } from './plan.ts';
import type { Column, Expression, Scalar, Statement } from './plan.ts';
import type { Value } from '../../typescript/src/index.ts';

export interface CompiledSql {
  statement: Statement;
  code: string;
  proof: string;
  /** Positional output labels; duplicate labels are retained. */
  columns: readonly string[];
  bind(params?: readonly unknown[]): Value;
}

function expressions(statement: Statement): Expression[] {
  switch (statement.kind) {
    case 'insert': return statement.rows.flat();
    case 'update': return [statement.key, ...statement.assignments.map(a => a.value)];
    default: return [statement.key];
  }
}

function value(expr: Expression, params: readonly unknown[], column: Column): Scalar {
  if (expr.kind === 'default') {
    if (column === 'completed') return false;
    throw new SqlError(`Column ${column} has no default`, '23502');
  }
  const result = expr.kind === 'literal' ? expr.value : params[expr.index];
  if (result === null) throw new SqlError(`NULL is not supported for ${column}`, '22004');
  if (typeof result !== (column === 'completed' ? 'boolean' : 'string')) {
    throw new SqlError(`Expected ${column === 'completed' ? 'boolean' : 'text'} for ${column}`, '42804');
  }
  // This also rejects isolated surrogates before preparation or submission.
  if (typeof result === 'string' && (!result.isWellFormed() || result.includes('\0'))) throw new SqlError('Invalid PostgreSQL text', '22021');
  return result as Scalar;
}

/** SQL text controls program shape; SQL values cross only the argument boundary. */
export function compileSql(sql: string): CompiledSql {
  if (Buffer.byteLength(sql, 'utf8') > 65536) throw new SqlError('SQL text exceeds the frontend 64 KiB limit', '54000');
  const statement = parseSql(sql);
  if (statement.kind === 'insert' && statement.rows.length > 2) throw new SqlError('At most 2 rows per INSERT are supported by the pinned proof checker', '54000');
  const refs = expressions(statement).flatMap(e => e.kind === 'parameter' ? [e.index] : []);
  const count = refs.length ? Math.max(...refs) + 1 : 0;
  if (new Set(refs).size !== count) throw new SqlError('Parameter numbers must be contiguous starting at $1', '42P02');
  const program = compileBend(statement);
  return {
    statement, ...program,
    columns: (statement.kind === 'select' ? statement.columns : statement.returning).map(p => p.alias),
    bind(params = []) {
      if (params.length !== count) throw new SqlError(`Expected ${count} parameters, received ${params.length}`, '08P01');
      switch (statement.kind) {
        case 'select': case 'delete': return [[value(statement.key, params, 'id')]];
        case 'update': {
          const title = statement.assignments.find(a => a.column === 'title');
          const completed = statement.assignments.find(a => a.column === 'completed');
          return [[value(statement.key, params, 'id'), title ? value(title.value, params, 'title') : null,
            completed ? value(completed.value, params, 'completed') : null]];
        }
        case 'insert': return statement.rows.map(row => {
          const field = (column: Column): Scalar => {
            const index = statement.columns.indexOf(column);
            return value(index < 0 ? { kind: 'default' } : row[index]!, params, column);
          };
          return [field('id'), field('title'), field('completed')];
        });
      }
    },
  };
}
