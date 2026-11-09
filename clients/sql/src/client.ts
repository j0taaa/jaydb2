import type { Execution, Preparation, Response, Value } from '../../typescript/src/index.ts';
import { ProtocolError } from '../../typescript/src/index.ts';
import { compileSql } from './compiler.ts';
import type { CompiledSql } from './compiler.ts';
import { SqlError } from './plan.ts';
import type { Scalar } from './plan.ts';

export interface SqlTransport {
  prepare(request: Preparation): Promise<Response>;
  execute(request: Execution): Promise<Response>;
}
export interface SqlResult { columns: readonly string[]; rows: Scalar[][]; rowCount: bigint }
export class SqlExecutionError extends SqlError {
  readonly response: Response;
  constructor(response: Response) {
    const detail = typeof response.value === 'string' ? `: ${response.value}` : '';
    const code = response.status === 'authentication' ? '28000'
      : response.status === 'certificate' ? '42501'
      : response.status === 'refusal' && response.value === 'duplicate key' ? '23505' : 'JDB01';
    super(`JayDB2 ${response.status}${detail}`, code);
    this.name = 'SqlExecutionError'; this.response = response;
  }
}

function isRecord(value: Value): value is { readonly [key: string]: Value } {
  return value !== null && typeof value === 'object' && !Array.isArray(value);
}
function result(response: Response, compiled: CompiledSql): SqlResult {
  if (response.status !== 'success') throw new SqlExecutionError(response);
  const v = response.value;
  const statement = compiled.statement;
  const projection = statement.kind === 'select' ? statement.columns : statement.returning;
  if (!isRecord(v) || Object.keys(v).sort().join(',') !== 'rowCount,rows'
      || typeof v.rowCount !== 'bigint' || v.rowCount < 0n
      || (statement.kind === 'insert' ? v.rowCount !== BigInt(statement.rows.length) : v.rowCount > 1n)
      || !Array.isArray(v.rows) || (projection.length ? BigInt(v.rows.length) !== v.rowCount : v.rows.length !== 0)
      || !Array.from(v.rows).every(row => Array.isArray(row) && row.length === projection.length
        && Array.from(row).every((cell, index) => projection[index]!.column === 'completed' ? typeof cell === 'boolean'
          : typeof cell === 'string' && cell.isWellFormed()))) {
    throw new ProtocolError('Malformed SQL program result; submitted outcome may be unknown');
  }
  return { columns: compiled.columns, rows: v.rows as Scalar[][], rowCount: v.rowCount };
}

/** One FIFO pipe session, fresh credentials per query, no write retries or reconnects. */
export class SqlClient {
  readonly #transport: SqlTransport;
  readonly #credential: () => string;
  readonly #handles = new Map<string, string>();
  readonly #maxPrepared: number;
  readonly #maxPending: number;
  #pending = 0;
  #tail: Promise<void> = Promise.resolve();
  constructor(transport: SqlTransport, options: { credential: string | (() => string); maxPrepared?: number; maxPendingQueries?: number }) {
    this.#transport = transport;
    const credential = options.credential;
    this.#credential = typeof credential === 'string' ? () => credential : credential;
    this.#maxPrepared = options.maxPrepared ?? 64;
    this.#maxPending = options.maxPendingQueries ?? 64;
    if (!Number.isSafeInteger(this.#maxPrepared) || this.#maxPrepared < 1) throw new RangeError('Invalid maxPrepared');
    if (!Number.isSafeInteger(this.#maxPending) || this.#maxPending < 1) throw new RangeError('Invalid maxPendingQueries');
  }
  async query(sql: string, params: readonly unknown[] = []): Promise<SqlResult> {
    // Snapshot arguments and credentials at invocation, before any queued work.
    const compiled = compileSql(sql);
    const args = compiled.bind(params);
    const credential = this.#credential();
    if (typeof credential !== 'string') throw new TypeError('Expected a credential string');
    if (this.#pending >= this.#maxPending) throw new SqlError('SQL pending-query limit reached; query was not submitted', '54000');
    this.#pending++;
    const operation = this.#tail.then(async () => {
      // The exact sources determine registration, never SQL parameter values.
      const key = compiled.code + '\0' + compiled.proof;
      let handle = this.#handles.get(key);
      if (!handle) {
        if (this.#handles.size >= this.#maxPrepared) throw new SqlError('Prepared program cache is full; open a new SQL client/session', '54000');
        const response = await this.#transport.prepare({ credential, code: compiled.code, proof: compiled.proof });
        if (response.status !== 'prepared') throw new SqlExecutionError(response);
        if (typeof response.value !== 'string' || !/^[0-9a-f]{64}$/.test(response.value)) throw new ProtocolError('Invalid prepared SQL handle');
        handle = response.value;
        this.#handles.set(key, handle);
      }
      return result(await this.#transport.execute({ credential, handle, arguments: args }), compiled);
    });
    // Failed admission, authentication or execution must not poison later work.
    this.#tail = operation.then(() => { this.#pending--; }, () => { this.#pending--; });
    return operation;
  }
}
