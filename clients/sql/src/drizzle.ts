import { drizzle } from 'drizzle-orm/pg-proxy';
import type { DrizzleConfig } from 'drizzle-orm/utils';
import { SqlError } from './plan.ts';
import type { SqlClient } from './client.ts';

/** Drizzle's PostgreSQL proxy supplies parameterized SQL and consumes ordered rows. */
export function drizzleCallback(client: SqlClient) {
  return async (sql: string, params: unknown[], method: 'all' | 'execute') => {
    if (method !== 'all' && method !== 'execute') throw new SqlError('Unsupported Drizzle execution method');
    const result = await client.query(sql, params);
    return { rows: method === 'all' ? result.rows : result.rows.map(row => Object.fromEntries(result.columns.map((name, i) => [name, row[i]]))) };
  };
}

export function createDrizzle<TSchema extends Record<string, unknown> = Record<string, never>>(
  client: SqlClient, config?: DrizzleConfig<TSchema>,
) {
  return drizzle(drizzleCallback(client), config);
}
