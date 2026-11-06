/** Run from the checkout: node clients/sql/examples/tasks.ts */
import { execFileSync } from 'node:child_process';
import { mkdtempSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { eq, sql } from 'drizzle-orm';
import { boolean, pgTable, text } from 'drizzle-orm/pg-core';
import { Client } from '../../typescript/src/index.ts';
import { SqlClient } from '../src/index.ts';
import { createDrizzle } from '../src/drizzle.ts';

// This declaration describes the adapter's fixed schema; it does not run DDL.
const tasks = pgTable('tasks', {
  id: text('id').primaryKey(),
  title: text('title').notNull(),
  completed: boolean('completed').notNull().default(false),
  owner: text('owner').notNull().default(sql`current_user`),
});
const root = fileURLToPath(new URL('../../../', import.meta.url));
const workspace = mkdtempSync(join(tmpdir(), 'jaydb-sql-demo-'));
let pipe: Client | undefined;
try {
  const app = join(workspace, 'app');
  execFileSync('python3', ['-B', join(root, 'applications/sql/prepare.py'), app]);
  pipe = Client.spawn({ command: join(root, 'jaydb2'), cwd: root,
    args: ['--configuration', join(app, 'Configuration.bend'), '--seed', join(app, 'Seed.bend'), '--threads', '1'] });
  const db = createDrizzle(new SqlClient(pipe, { credential: 'alice-token' }));
  console.log('Insert:', await db.insert(tasks).values({ id: 'sql-1', title: 'Try SQL on Bend 2' }).returning());
  console.log('Update:', await db.update(tasks).set({ completed: true }).where(eq(tasks.id, 'sql-1')).returning());
  console.log('Select:', await db.select().from(tasks).where(eq(tasks.id, 'sql-1')));
  console.log('Delete:', await db.delete(tasks).where(eq(tasks.id, 'sql-1')).returning({ id: tasks.id }));
} finally {
  try { await pipe?.close(); } finally { rmSync(workspace, { recursive: true, force: true }); }
}
