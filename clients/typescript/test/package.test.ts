import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

const packageRoot = fileURLToPath(new URL('../', import.meta.url));

test('packed ESM and declarations work from an independent TypeScript application', () => {
  const folder = mkdtempSync(join(tmpdir(), 'jaydb-ts-consumer-'));
  function run(command: string, args: string[], cwd: string): string {
    const result = spawnSync(command, args, { cwd, encoding: 'utf8', timeout: 120_000 });
    assert.equal(result.status, 0, `${command} ${args.join(' ')}\n${result.stdout}\n${result.stderr}`);
    return result.stdout;
  }
  try {
    run(process.execPath, ['node_modules/typescript/lib/tsc.js', '-p', 'tsconfig.json'], packageRoot);
    const result = JSON.parse(run('npm', ['pack', '--json', '--ignore-scripts', '--pack-destination', folder], packageRoot)) as { filename: string; files: { path: string }[] }[];
    const packed = result[0]!;
    assert.ok(packed.files.some(file => file.path === 'dist/index.js'));
    assert.ok(packed.files.some(file => file.path === 'dist/index.d.ts'));
    assert.ok(packed.files.every(file => file.path.startsWith('dist/') || ['package.json', 'README.md'].includes(file.path)));
    writeFileSync(join(folder, 'package.json'), JSON.stringify({ type: 'module', private: true,
      dependencies: { '@jaydb2/client': `file:./${packed.filename}` },
      devDependencies: { typescript: '5.9.3', '@types/node': '24.19.0' } }));
    // The package's npm ci already cached these exact development tools.
    // This consumer installs the tarball, not a symlink into the repository.
    run('npm', ['install', '--offline', '--ignore-scripts', '--no-audit', '--no-fund'], folder);
    writeFileSync(join(folder, 'tsconfig.json'), JSON.stringify({ compilerOptions: {
      strict: true, target: 'ES2022', module: 'NodeNext', moduleResolution: 'NodeNext', outDir: 'dist',
    }, include: ['app.ts'] }));
    writeFileSync(join(folder, 'app.ts'), `
import { Client, encode, decode, type Value, type Response } from '@jaydb2/client';
import { PassThrough } from 'node:stream';
const value: Value = { exact: 9223372036854775807n };
if (encode(decode(encode(value))).compare(encode(value)) !== 0) throw new Error('roundtrip');
const input = new PassThrough(), output = new PassThrough();
const client = new Client({input,output});
const response: Promise<Response> = client.request({credential:'demo',code:'code',proof:'proof',arguments:value});
const checked = response.then(r => {if (r.status !== 'success') throw new Error('status');});
const {frame} = await import('@jaydb2/client');
output.end(frame({status:'success',value}));
await checked;
await client.close();
console.log('separate consumer passed');
`);
    run(process.execPath, ['node_modules/typescript/lib/tsc.js', '-p', 'tsconfig.json'], folder);
    assert.equal(run(process.execPath, ['dist/app.js'], folder).trim(), 'separate consumer passed');
  } finally { rmSync(folder, { recursive: true, force: true }); }
});
