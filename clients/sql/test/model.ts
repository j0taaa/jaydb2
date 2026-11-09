/** Independent SQL oracle: execute the original common-subset SQL in SQLite. */
import assert from 'node:assert/strict';
import { DatabaseSync } from 'node:sqlite';
import type { SQLInputValue, SQLOutputValue } from 'node:sqlite';

export type ModelScalar = string | boolean | bigint | null;
export interface ModelResult { columns: string[]; rows: ModelScalar[][]; rowCount: bigint }
export type ModelOutcome = { kind: 'result'; result: ModelResult } | { kind: 'duplicate' };

/**
 * Each actor gets a separate SQL database, matching this adapter's declared
 * owner-isolated logical table. SQLite supplies constraints, statement rollback,
 * filtering, updates, RETURNING, defaults and the retained state independently.
 * No frontend parser, AST, binding or generated Bend is used by this oracle.
 */
export class SqliteTaskOracle {
  readonly #database: DatabaseSync;
  constructor(actor: 'alice' | 'bob') {
    this.#database = new DatabaseSync(':memory:');
    this.#database.exec(`CREATE TABLE tasks (
      id TEXT PRIMARY KEY NOT NULL,
      title TEXT NOT NULL,
      completed INTEGER NOT NULL DEFAULT false CHECK (completed IN (0, 1)),
      owner TEXT NOT NULL DEFAULT '${actor}' CHECK (owner = '${actor}')
    ) STRICT`);
    // SQLite STRICT represents a boolean as checked INTEGER. Identify that
    // column using SQLite's origin metadata below, not its selected alias.
  }
  execute(sql: string, params: readonly unknown[] = []): ModelOutcome {
    const statement = this.#database.prepare(sql);
    const parameters: Record<string, SQLInputValue> = {};
    params.forEach((value, index) => {
      assert.ok(typeof value === 'string' || typeof value === 'boolean', 'Oracle accepts only supported task scalars');
      parameters[`$${index + 1}`] = typeof value === 'boolean' ? Number(value) : value;
    });
    const columns = statement.columns();
    statement.setReturnArrays(true);
    statement.setReadBigInts(true);
    try {
      if (columns.length === 0) {
        const changes = statement.run(parameters);
        return { kind: 'result', result: { columns: [], rows: [], rowCount: BigInt(changes.changes) } };
      }
      const values = statement.all(parameters) as unknown as SQLOutputValue[][];
      const rows = values.map(row => row.map((value, index): ModelScalar => {
        if (columns[index]!.column === 'completed') {
          assert.ok(value === 0n || value === 1n, 'SQLite boolean constraint must hold');
          return value === 1n;
        }
        assert.ok(value === null || typeof value === 'string' || typeof value === 'bigint', 'Unsupported oracle output');
        return value;
      }));
      return { kind: 'result', result: { columns: columns.map(column => column.name), rows, rowCount: BigInt(rows.length) } };
    } catch (error) {
      // SQLITE_CONSTRAINT_PRIMARYKEY / SQLITE_CONSTRAINT_UNIQUE. The original
      // SQL engine, rather than a JS map, decides duplicate/atomic-abort behavior.
      if (error instanceof Error && 'errcode' in error && (error.errcode === 1555 || error.errcode === 2067)) return { kind: 'duplicate' };
      throw error;
    }
  }
  close(): void { this.#database.close(); }
}

export function random(seed: number): () => number {
  let state = seed >>> 0;
  if (state === 0) state = 0x9e3779b9;
  return () => {
    state ^= state << 13;
    state ^= state >>> 17;
    state ^= state << 5;
    return (state >>> 0) / 0x100000000;
  };
}

export function quote(value: string): string { return `'${value.replaceAll("'", "''")}'`; }
