#!/usr/bin/env node
// Explicit offline build; submitted code cannot trigger compilation.
import fs from 'node:fs';
import path from 'node:path';
import child from 'node:child_process';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { createHash } from 'node:crypto';
import { stripTypeScriptTypes, registerHooks } from 'node:module';
import { instrumentFrontend } from './frontend-observer.mjs';
import { preserveRigidSubterms } from './conversion.mjs';
import { uncapTemplates } from './frontend-resources.mjs';
import { adaptSafeNumerals } from './safe-numerals.mjs';
import { adaptSafeStrings } from './safe-strings.mjs';
import { adaptSafeTemplates } from './safe-templates.mjs';
import { internEquivalentInstances } from './instance-keys.mjs';
import { canonicalTypes } from './safe-canonical.mjs';
import { adaptSafeState } from './safe-state.mjs';

const here = fileURLToPath(new URL('./', import.meta.url));
const hash = b => createHash('sha256').update(b).digest('hex');
const lock = JSON.parse(fs.readFileSync(new URL('./toolchain.lock.json', import.meta.url)));
export const transforms = ['frontend-observer.mjs', 'conversion.mjs', 'frontend-resources.mjs', 'safe-numerals.mjs', 'safe-strings.mjs', 'safe-templates.mjs', 'closed-instances.mjs', 'book-graph.mjs', 'instance-keys.mjs', ...fs.readdirSync(here).filter(f=>f.startsWith('structural-')&&f.endsWith('.mjs')).sort(), 'template-affected.mjs', 'safe-canonical.mjs', 'safe-state.mjs', 'safe-routing.mjs'];

export async function buildFrontend(sourceDir = path.resolve(here, '../../.tools/bend-source-' + lock.version)) {
  const installed = path.join(here, 'installed');
  fs.mkdirSync(installed, { recursive: true });
  const files = {};
  for (const name of ['bend', 'safe', 'safe-structural', 'comp']) {
    const originalName=name==='safe-structural'?'safe':name;
    const original = fs.readFileSync(path.join(sourceDir, 'bend2', originalName + '.ts'));
    if (hash(original) !== lock.files['bend2/' + originalName + '.ts']) throw new Error('Pinned frontend source mismatch: ' + name);
    let source = original.toString('utf8');
    if (name === 'bend') source = internEquivalentInstances(uncapTemplates(preserveRigidSubterms(instrumentFrontend(source))));
    if (originalName === 'safe') {
      source=adaptSafeTemplates(adaptSafeStrings(adaptSafeNumerals(source)));
      if(name==='safe-structural')source=canonicalTypes(source);
      source=adaptSafeState(source,{canonical:name==='safe-structural'});
    }
    const js = stripTypeScriptTypes(source, { mode: 'transform' });
    fs.writeFileSync(path.join(installed, name + '.mjs'), js);
    files[name + '.mjs'] = hash(js);
  }
  // Capture the adapter's exact derived TypeScript without evaluating it.
  // Strip only TypeScript, offline. Runtime relinks the one authenticated Bend
  // import to the already checked module, and checks the normalized source.
  const backendBytes = fs.readFileSync(path.join(here, '../native/generic.mjs'));
  const backend = await import('data:text/javascript;base64,' + backendBytes.toString('base64'));
  const bendImport = 'from ' + JSON.stringify(pathToFileURL(path.join(sourceDir, 'bend2/bend.ts')).href);
  let genericSource;
  const hook = registerHooks({ load(url, context, nextLoad) {
    if (!url.startsWith('file:') || !url.endsWith('/comp.ts') || !fileURLToPath(url).includes('/jaydb-generic-')) return nextLoad(url, context);
    const source = fs.readFileSync(fileURLToPath(url), 'utf8');
    if (source.split(bendImport).length !== 2) throw new Error('Generic Bend import anchor changed');
    genericSource = source.replace(bendImport, 'from "jaydb:pinned-bend"');
    return { format: 'module', source: 'export function io_type(){}; export function compile_book(){}', shortCircuit: true };
  } });
  try { await backend.loadGenericCompiler(path.join(sourceDir, 'bend2')); }
  finally { hook.deregister(); }
  if (!genericSource) throw new Error('Native adapter did not supply its derived compiler');
  const genericJS = stripTypeScriptTypes(genericSource, { mode: 'transform' });
  fs.writeFileSync(path.join(installed, 'generic.mjs'), genericJS);
  files['generic.mjs'] = hash(genericJS);
  const compile = child.spawnSync('/usr/bin/clang++-19', ['-std=c++20', '-O2', '-shared', '-fPIC',
    '-I/usr/include/node', '-fmacro-prefix-map=' + here + '=tools/admission/',
    path.join(here, 'stack.cc'), '-o', path.join(installed, 'stack.node')], { encoding: 'utf8' });
  if (compile.status !== 0) throw new Error('Frontend stack addon build: ' + compile.stderr);
  files['stack.node'] = hash(fs.readFileSync(path.join(installed, 'stack.node')));
  const manifest = { format: 'jaydb-offline-frontend-v1', node: process.version,
    nodeModuleVersion: process.versions.modules, originalFiles: lock.files,
    transforms: Object.fromEntries(transforms.map(f => [f, hash(fs.readFileSync(path.join(here, f)))])),
    stackSourceSha256: hash(fs.readFileSync(path.join(here, 'stack.cc'))),
    stackLoaderSha256: hash(fs.readFileSync(path.join(here, 'stack.cjs'))),
    nativeBackendSha256: hash(backendBytes), nativeSourceNormalizedSha256: hash(genericSource),
    builderSha256: hash(fs.readFileSync(fileURLToPath(import.meta.url))), files };
  const bytes = JSON.stringify(manifest, null, 2) + '\n';
  fs.writeFileSync(path.join(installed, 'manifest.json'), bytes);
  return manifest;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const manifest = await buildFrontend();
  if (process.argv.includes('--write-lock')) fs.writeFileSync(path.join(here, 'frontend.lock.json'), JSON.stringify(manifest, null, 2) + '\n');
  console.log(JSON.stringify(manifest, null, 2));
}
