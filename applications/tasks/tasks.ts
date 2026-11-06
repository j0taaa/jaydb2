#!/usr/bin/env node
/** A Node/TypeScript task application using the optional JayDB client. */
import { mkdirSync, readFileSync, readdirSync, statSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';
import { Client } from '../../clients/typescript/src/index.ts';

const APP = dirname(fileURLToPath(import.meta.url));
const ROOT = resolve(APP, '../..');
const HELP = `Persistent tasks using JayDB2 and its TypeScript client.

node applications/tasks/tasks.ts --workspace DIR --storage-mode create|open [options] --command COMMAND

Commands: list | view ID | save ID TITLE [true|false] | cancel ID TITLE [true|false] | conclude ID | remove ID
Options before --command:
  --credential TOKEN      Credential on every request (public example default: alice-token)
  --database-root DIR     Installed JayDB2 checkout (default: this repository)
  --threads N             Native worker budget, 1..128 (default: 1)

create requires a new workspace; open never resets it or reads a seed.
Quote task titles using your shell. Without --command, use --help for this text.
`;

function readText(file: string): string {
  return new TextDecoder('utf-8', { fatal: true }).decode(readFileSync(file));
}

function taskCommand(words: string[]): (string | boolean)[] {
  const [command, ...values] = words;
  if ((command === 'save' || command === 'cancel') && (values.length === 2 || values.length === 3)) {
    if (values.length === 3 && values[2] !== 'true' && values[2] !== 'false')
      throw new Error('Use true or false for completed.');
    return [command, ...values.slice(0, 2), values[2] === 'true'];
  }
  if ((command === 'list' && values.length === 0) ||
      (['view', 'conclude', 'remove'].includes(command ?? '') && values.length === 1))
    return words;
  throw new Error('Invalid task command. See --help and quote the title.');
}

function packageWorkspace(workspace: string, mode: string, root: string): string {
  const directory = join(workspace, 'app');
  if (mode === 'create') {
    // Parent folders may be new, but the selected workspace itself must not exist.
    mkdirSync(dirname(workspace), { recursive: true });
    mkdirSync(workspace, { mode: 0o700 });
    mkdirSync(directory, { mode: 0o700 });
    for (const entry of readdirSync(APP)) {
      if (entry.endsWith('.bend')) writeFileSync(join(directory, entry), readFileSync(join(APP, entry)), { flag: 'wx' });
    }
    for (const name of ['Orders', 'Foundations'])
      writeFileSync(join(directory, `${name}.bend`), readText(join(root, 'proof', `${name}.bend`)).replaceAll('../contract/', './'), { flag: 'wx' });
    for (const name of ['Laws', 'Query', 'Action'])
      writeFileSync(join(directory, `${name}.bend`), readText(join(root, 'library', `${name}.bend`)).replaceAll('../contract/', './').replaceAll('../src/', './'), { flag: 'wx' });
  } else {
    for (const name of ['Configuration.bend', 'Client.bend', 'ClientProof.bend']) {
      const file = join(directory, name);
      if (!statSync(file, { throwIfNoEntry: false })?.isFile())
        throw new Error(`Missing task workspace file: ${file}. Use create only for a new workspace.`);
    }
  }
  return directory;
}

async function main(): Promise<void> {
  const argv = process.argv.slice(2), marker = argv.indexOf('--command');
  const { values } = parseArgs({ args: marker < 0 ? argv : argv.slice(0, marker), strict: true,
    options: { workspace: { type: 'string' }, 'storage-mode': { type: 'string' },
      credential: { type: 'string', default: 'alice-token' }, threads: { type: 'string', default: '1' },
      'database-root': { type: 'string', default: ROOT }, help: { type: 'boolean' } } });
  if (values.help) { console.log(HELP); return; }
  if (!values.workspace || !['create', 'open'].includes(values['storage-mode'] ?? ''))
    throw new Error('Use --workspace DIR and --storage-mode create|open. See --help.');
  if (marker < 0) throw new Error('Supply --command after the options. See --help.');
  const arguments_ = taskCommand(argv.slice(marker + 1));
  const threads = values.threads!;
  if (!/^[1-9][0-9]*$/.test(threads) || Number(threads) > 128)
    throw new Error('--threads must be from 1 to 128.');
  const root = resolve(values['database-root']!), workspace = resolve(values.workspace);
  const mode = values['storage-mode']!;
  const directory = packageWorkspace(workspace, mode, root);
  const args = ['--configuration', join(directory, 'Configuration.bend'), '--threads', threads,
    '--storage', join(workspace, 'db'), '--storage-mode', mode];
  if (mode === 'create') args.push('--seed', join(directory, 'Seed.bend'));
  const client = Client.spawn({ command: join(root, 'jaydb2'), args, cwd: root, stderr: 'inherit' });
  try {
    const response = await client.request({ credential: values.credential!,
      code: readText(join(directory, 'Client.bend')), proof: readText(join(directory, 'ClientProof.bend')),
      arguments: arguments_ });
    await client.close();
    console.log(JSON.stringify(response));
    if (response.status !== 'success') process.exitCode = 2;
  } catch (error) {
    try { await client.close(); } catch { /* Preserve the original request error. */ }
    throw error;
  }
}

main().catch((error: unknown) => {
  console.error(`tasks: ${error instanceof Error ? error.message : String(error)}`);
  process.exitCode = 1;
});
