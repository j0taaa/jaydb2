/** The deliberately small PostgreSQL syntax subset understood by this frontend. */
export type Column = 'id' | 'title' | 'completed' | 'owner';
export type Scalar = string | boolean | bigint | null;
export type Expression = { kind: 'parameter'; index: number } | { kind: 'literal'; value: Scalar } | { kind: 'default' };
export interface Projection { column: Column; alias: string }
export type Statement =
  | { kind: 'select'; table: 'tasks'; columns: Projection[]; key: Expression }
  | { kind: 'insert'; table: 'tasks'; columns: Column[]; rows: Expression[][]; returning: Projection[] }
  | { kind: 'update'; table: 'tasks'; assignments: { column: Column; value: Expression }[]; key: Expression; returning: Projection[] }
  | { kind: 'delete'; table: 'tasks'; key: Expression; returning: Projection[] };
export class SqlError extends Error {
  readonly code: string;
  constructor(message: string, code = '0A000') { super(message); this.name = 'SqlError'; this.code = code; }
}
