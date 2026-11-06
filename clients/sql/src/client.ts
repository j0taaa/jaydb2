import type { Execution, Preparation, Response, Value } from '../../typescript/src/index.ts';
import { ProtocolError } from '../../typescript/src/index.ts';
import { compileSql } from './compiler.ts';
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
function result(response: Response, columns: readonly string[]): SqlResult {
  if (response.status !== 'success') throw new SqlExecutionError(response);
  const v = response.value;
  if (!isRecord(v) || Object.keys(v).sort().join(',') !== 'rowCount,rows'
      || typeof v.rowCount !== 'bigint' || v.rowCount < 0n || !Array.isArray(v.rows)
      || !v.rows.every(row => Array.isArray(row) && row.length === columns.length
        && row.every(cell => cell === null || ['string', 'boolean', 'bigint'].includes(typeof cell)))) {
    throw new ProtocolError('Malformed SQL program result; submitted outcome may be unknown');
  }
  return { columns, rows: v.rows as Scalar[][], rowCount: v.rowCount };
}

/** One pipe session, fresh credentials per query, no write retries or reconnects. */
export class SqlClient {
  readonly #transport: SqlTransport;
  readonly #credential: () => string;
  readonly #handles = new Map<string, string>();
  readonly #preparing = new Map<string, Map<string, Promise<string>>>();
  readonly #maxPrepared: number;
  constructor(transport: SqlTransport, options: { credential: string | (() => string); maxPrepared?: number }) {
    this.#transport = transport;
    const credential = options.credential;
    this.#credential = typeof credential === 'string' ? () => credential : credential;
    this.#maxPrepared = options.maxPrepared ?? 64;
    if (!Number.isSafeInteger(this.#maxPrepared) || this.#maxPrepared < 1) throw new RangeError('Invalid maxPrepared');
  }
  async query(sql: string, params: readonly unknown[] = []): Promise<SqlResult> {
    const compiled = compileSql(sql);
    const args = compiled.bind(params);
    const credential = this.#credential();
    if (typeof credential !== 'string') throw new TypeError('Expected a credential string');
    // The exact sources determine the registration, never SQL parameter values.
    const key = compiled.code + '\0' + compiled.proof;
    const ready = this.#handles.get(key);
    let pending = this.#preparing.get(key)?.get(credential);
    if (!ready && !pending) {
      const shapes = new Set([...this.#handles.keys(), ...this.#preparing.keys()]);
      if (!shapes.has(key) && shapes.size >= this.#maxPrepared) throw new SqlError('Prepared program cache is full; open a new SQL client/session', '54000');
      // Preparation authenticates too. Different credentials must not inherit an
      // in-flight preparation's authentication failure, even for identical code.
      const group = this.#preparing.get(key) ?? new Map<string, Promise<string>>();
      this.#preparing.set(key, group);
      pending = Promise.resolve().then(() => this.#transport.prepare({ credential, code: compiled.code, proof: compiled.proof })).then(response => {
        if (response.status !== 'prepared') throw new SqlExecutionError(response);
        if (typeof response.value !== 'string' || !/^[0-9a-f]{64}$/.test(response.value)) throw new ProtocolError('Invalid prepared SQL handle');
        this.#handles.set(key, response.value);
        return response.value;
      });
      group.set(credential, pending);
      const cleanup = () => { group.delete(credential); if (group.size === 0) this.#preparing.delete(key); };
      void pending.then(cleanup, cleanup);
    }
    return result(await this.#transport.execute({ credential, handle: ready ?? await pending!, arguments: args }), compiled.columns);
  }
}
