#!/usr/bin/env node
// Freeze application modules and compile their ordinary Bend entry points.
// Published state is never written here; request staging receives public metadata.
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { sha256 as digest } from '../admission/bootstrap.mjs';
import { header } from '../admission/preflight.mjs';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const utf8 = bytes => new TextDecoder('utf-8', { fatal: true, ignoreBOM: true }).decode(bytes);
const read = name => fs.readFileSync(name);
const write = (name, bytes) => { fs.mkdirSync(path.dirname(name), { recursive: true, mode: 0o700 }); fs.writeFileSync(name, bytes, { flag: 'wx', mode: 0o600 }); };
const json = (name, value) => write(name, JSON.stringify(value));
const fail = (code, message) => { throw Object.assign(new Error(message), { code }); };
const literal = text => '"' + [...text].map(c => c === '"' ? '\\"' : c === '\\' ? '\\\\'
  : c.codePointAt(0) < 32 ? `\\u{${c.codePointAt(0).toString(16).padStart(2, '0')}}` : c).join('') + '"';

const COMMON = `import Base
import ./Native.bend as Native
import ./Data.bend as D
import ./Semantics.bend as S
import ./Configuration.bend as C
`;
const INITIALIZE = COMMON + `import ./Protocol.bend as P
import ./Requirements.bend as R
import ./Seed.bend as Seed
import ./ConfigurationCheck.bend as CheckedConfiguration
import ./Environment.bend as Environment

def result(bytes: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match bytes:
    case None{}:
      [2]
    case Some{bs}:
      Con{1, bs}

def initial(ok: Bool) -> List<&2, U32>:
  match ok:
    case False{}:
      [2]
    case True{}:
      result(P.encode(D.state_value(Seed.state())))

def main() -> IO(Unit):
  Native.write(initial(CheckedConfiguration.is_valid(C.config(), Environment.identity())))
`;
// Recovery validates the frozen configuration but never evaluates a seed or
// claims to execute arbitrary administrator invariant predicates at runtime.
const RECOVER = COMMON + `import ./ConfigurationCheck.bend as CheckedConfiguration
import ./Environment.bend as Environment

def result(ok: Bool) -> List<&2, U32>:
  match ok:
    case True{}: [1]
    case False{}: [2]

def main() -> IO(Unit):
  Native.write(result(CheckedConfiguration.is_valid(C.config(), Environment.identity())))
`;
// Messages.authentication private success: 1 || frame(exact Context.id UTF-8)
// || frame(code) || frame(proof) || frame(instance) || links remainder.
const PREPROCESS = COMMON + `import ./Input.bend as E
import ./Messages.bend as M

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write(M.FUNCTION(E.PARSER(bytes, S.schema(C.config()), S.limits(C.config()))))
`;
const EXECUTE = COMMON + `import ./Protocol.bend as P
import ./Input.bend as Input
import ./Execution.bend as E
import ./Client.bend as Client
import ./ClientProof.bend as ClientProof
import ./Bindings.bend as Bindings

# The function capture owns the provisional state and moves once to the step.
def convert(i: E.Iteration) -> Native.Iteration<(Unit -> E.StateExecution)>:
  match i:
    case E.Continue{s}:
      Native.Continue{u => s}
    case E.Prepare{s}:
      Native.Prepare{u => s}
    case E.FinishOutput{bs}:
      Native.FinishOutput{bs}
    case E.Inconsistent{}:
      Native.Inconsistent{}

def step(state: Unit -> E.StateExecution) -> Native.Iteration<(Unit -> E.StateExecution)>:
  convert(E.advance(state(Unit{}), C.config()))

def launch(input: Input.Analysis) -> IO(Unit):
  match input:
    case Input.Received{s, r, ctx}:
      match r:
        case P.Request{credential, code, arguments, proof}:
          Native.loop((Unit -> E.StateExecution), step, u => E.start(Client.program(), ctx, arguments, s))
    case _:
      Native.write([2])

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    launch(Input.analyze(bytes, S.schema(C.config()), S.limits(C.config())))
`;

function imports(data) {
  const result = [];
  for (const { specifier } of header(utf8(data), 'staging').imports) {
    if (specifier === 'Base') continue;
    if (!/^(?:\.\/)?(?:[A-Za-z_][\w-]*\/)*[A-Za-z_][\w-]*\.bend$/.test(specifier))
      fail('DEPENDENCY', 'The environment must use local imports within its directory');
    result.push(specifier.replace(/^\.\//, ''));
  }
  return result;
}

// Both the executable and its pure check use the same staged import graph.
function sourceClosure(available, entries, missing, reverseImports = true) {
  const selected = new Map(), pending = [...entries];
  while (pending.length) {
    const name = pending.pop();
    if (selected.has(name)) continue;
    if (!available.has(name)) fail('DEPENDENCY', missing + name);
    const data = available.get(name);
    selected.set(name, data);
    const children = imports(data).map(imp => path.posix.normalize(path.posix.join(path.posix.dirname(name), imp)));
    pending.push(...(reverseImports ? children.reverse() : children));
  }
  return selected;
}

function loadAdministrator(configuration, seed, sources) {
  const root = path.dirname(fs.realpathSync(configuration));
  const privateSeed = seed === null ? null : fs.realpathSync(seed);
  const reserved = new Set([...sources.keys(), 'Environment.bend', 'Seed.bend', 'Main.bend',
    'Client.bend', 'ClientProof.bend', 'Instance.bend', 'Bindings.bend', 'Check.bend']);
  const load = (entry, name, initializing = false) => {
    const result = new Map(), pending = [[entry, name]];
    while (pending.length) {
      const [input, target] = pending.pop(), file = fs.realpathSync(input), relative = path.relative(root, file);
      if (!initializing && file === privateSeed) fail('DEPENDENCY', 'Public configuration cannot import the private seed');
      if (relative === '..' || relative.startsWith('../') || path.isAbsolute(relative))
        fail('DEPENDENCY', 'Dependency outside the configuration directory');
      const data = read(file);
      if (result.has(target)) {
        if (!result.get(target).equals(data)) fail('DEPENDENCY', 'Administrator dependency collision');
        continue;
      }
      if (reserved.has(target) && target !== 'Seed.bend') fail('DEPENDENCY', 'Administrator replaced a reserved module: ' + target);
      result.set(target, data);
      const children = [];
      for (const imp of imports(data)) {
        const name = path.posix.normalize(path.posix.join(path.posix.dirname(target), imp));
        if (!sources.has(name) && name !== 'Environment.bend') children.push([path.resolve(path.dirname(file), imp), name]);
      }
      pending.push(...children.reverse());
    }
    return result;
  };
  const publicSources = load(configuration, 'Configuration.bend');
  for (const [name, data] of publicSources) sources.set(name, data);
  return seed === null ? new Map() : load(seed, 'Seed.bend', true);
}

function freeze(workdir, configuration, seed) {
  const sources = new Map();
  for (const folder of ['contract', 'src']) for (const name of fs.readdirSync(path.join(ROOT, folder)).sort()) {
    if (!name.endsWith('.bend')) continue;
    if (sources.has(name)) fail('DEPENDENCY', 'Application/contract module collision');
    const bytes = read(path.join(ROOT, folder, name));
    sources.set(name, folder === 'src' ? Buffer.from(utf8(bytes).replaceAll('../contract/', './')) : bytes);
  }
  sources.set('Native.bend', read(path.join(ROOT, 'native/effects.bend')));
  const seedSources = loadAdministrator(configuration, seed, sources), tooling = new Map();
  for (const folder of ['tools/admission', 'tools/verifier']) for (const name of fs.readdirSync(path.join(ROOT, folder)).sort()) {
    if (/\.(?:mjs|json)$/.test(name)) tooling.set(folder + '/' + name, read(path.join(ROOT, folder, name)));
  }
  for (const name of ['tools/service/stage.mjs', 'tools/service/compile.mjs', 'native/effects.bend', 'native/effects.c',
    'server/main.rs', 'server/capture.rs', 'server/read_batch.rs', 'server/scheduling.rs', 'server/storage.rs', 'server/timing.rs', 'Cargo.toml', 'Cargo.lock']) {
    if (fs.existsSync(path.join(ROOT, name))) tooling.set(name, read(path.join(ROOT, name)));
  }
  // Linux exposes the actual calling controller, not a guessed build path.
  const controller = read(`/proc/${process.ppid}/exe`);
  const identityEntries = [...sources].map(([name, data]) => [name, digest(data)]).sort();
  identityEntries.push(...[...tooling].map(([name, data]) => [name, digest(data)]).sort(), ['server/controller', digest(controller)]);
  const identity = digest(JSON.stringify(identityEntries));
  sources.set('Environment.bend', Buffer.from('import Base\ndef identity() -> String:\n  ' + JSON.stringify(identity) + '\n'));
  for (const [name, data] of sources) write(path.join(workdir, 'public', name), data);
  for (const [name, data] of tooling) write(path.join(workdir, 'runtime', name), data);
  const publicFiles = [...sources].map(([name, data]) => ({ name, sha256: digest(data) }));
  json(path.join(workdir, 'environment.json'), { identity, publicFiles });
  return { sources, seedSources, foreign: tooling.get('native/effects.c') };
}

function reopen(workdir) {
  const environment = JSON.parse(utf8(read(path.join(workdir, 'environment.json')))), sources = new Map();
  for (const record of environment.publicFiles) {
    const bytes = read(path.join(workdir, 'public', record.name));
    if (digest(bytes) !== record.sha256) fail('SOURCE_IO', 'The frozen public environment changed');
    sources.set(record.name, bytes);
  }
  return { sources, seedSources: new Map(), foreign: read(path.join(workdir, 'runtime/native/effects.c')) };
}

function stage(environment, directory, purpose, metadata) {
  fs.mkdirSync(directory, { recursive: true, mode: 0o700 });
  const available = new Map(environment.sources);
  let main;
  if (purpose === 'initialize') { for (const [k, v] of environment.seedSources) available.set(k, v); main = INITIALIZE; }
  else if (purpose === 'recover') main = RECOVER;
  else if (purpose === 'decode' || purpose === 'authenticate') main = PREPROCESS
    .replace('FUNCTION', purpose === 'decode' ? 'framing' : 'authentication')
    .replace('PARSER', purpose === 'decode' ? 'decode' : 'analyze');
  else if (['execute', 'prepare', 'prepare-read'].includes(purpose)) {
    for (const name of ['Client.bend', 'ClientProof.bend', 'Instance.bend', 'Bindings.bend']) available.set(name, read(path.join(metadata, name)));
    if (['prepare', 'prepare-read'].includes(purpose)) {
      const concrete = 'R.Certifies(I.config(), code(), Client.program(), I.context(), I.arguments())';
      const links = utf8(available.get('Bindings.bend'));
      if (links.split(concrete).length !== 2) fail('TARGET', 'Expected the generated concrete certificate target');
      available.set('Bindings.bend', Buffer.from(links.replace(concrete,
        '@ctx: D.Context -> @args: D.Value -> R.Certifies(I.config(), code(), Client.program(), ctx, args)') +
        '\ndef proof_source() -> String:\n  ' + literal(utf8(available.get('ClientProof.bend'))) + '\n'));
    }
    if (purpose === 'prepare-read') available.set('Bindings.bend', Buffer.from('import ./ReadOnly.bend as ReadOnly\n' + utf8(available.get('Bindings.bend')) +
      '\nlaw read_only:\n  ReadOnly.Program(Client.program())\n'));
    main = ['prepare', 'prepare-read'].includes(purpose)
      ? EXECUTE.replace('import ./Input.bend as Input',
          'import ./Input.bend as Input\nimport ./Prepared.bend as Prepared')
        .replace('launch(Input.analyze(bytes, S.schema(C.config()), S.limits(C.config())))',
          'launch(Prepared.resolve_analysis(Input.analyze(bytes, S.schema(C.config()), S.limits(C.config())), Bindings.code(), Bindings.proof_source()))')
      : EXECUTE;
  } else fail('DEPENDENCY', 'Invalid purpose');
  const executing = ['execute', 'prepare', 'prepare-read'].includes(purpose);
  available.set('Main.bend', Buffer.from(main));
  const entries = executing ? ['Main.bend', 'Interface.bend'] : ['Main.bend'];
  const selected = sourceClosure(available, entries, 'Unadmitted dependency: ');
  const manifest = { submissionDir: path.resolve(directory), entry: 'Main.bend', dependencies: [] };
  for (const [name, original] of selected) {
    const data = name === 'Native.bend' && !executing ? original.subarray(0, original.indexOf('\ntype Iteration')) : original;
    write(path.join(directory, name), data);
    let role = 'library', exports = [];
    if (name === 'Native.bend') role = 'kernel';
    else if (['Client.bend', 'ClientProof.bend'].includes(name)) role = 'client';
    else if (['Main.bend', 'Seed.bend'].includes(name) || environment.seedSources.has(name)) role = 'host';
    else if (['Environment.bend', 'Instance.bend', 'Bindings.bend'].includes(name)) {
      role = 'host'; exports = { 'Environment.bend': ['Environment:identity'],
        'Instance.bend': ['Instance:config', 'Instance:context', 'Instance:arguments'],
        'Bindings.bend': ['Bindings:code', 'Bindings:certificate', 'Bindings:terminates'] }[name];
      if (name === 'Bindings.bend' && ['prepare', 'prepare-read'].includes(purpose)) exports.push('Bindings:proof_source');
    } else if (name === 'Configuration.bend' && purpose === 'initialize') role = 'host';
    manifest.dependencies.push({ path: name, role, sha256: digest(data), ...(role === 'host' ? { exports } : {}) });
  }
  const marker = environment.foreign.indexOf('// JayDB iteration effect');
  const foreign = executing ? environment.foreign : environment.foreign.subarray(0, marker < 0 ? undefined : marker);
  write(path.join(directory, 'effects.c'), foreign);
  manifest.kernel = { module: 'Native.bend', primitives: executing ? ['read', 'write', 'loop'] : ['read', 'write'],
    foreign: { path: 'effects.c', sha256: digest(foreign) } };
  if (executing) {
    manifest.readOnly = purpose === 'prepare-read';
    manifest.certificateMode = ['prepare', 'prepare-read'].includes(purpose) ? 'universal' : 'concrete';
    manifest.kernel.loopStep = 'step';
    manifest.openTargets = { 'Bindings:certificate': 'ClientProof.bend', 'Bindings:terminates': 'ClientProof.bend',
      ...(manifest.readOnly ? { 'Bindings:read_only': 'ClientProof.bend' } : {}) };
  } else manifest.purpose = purpose === 'initialize' ? 'initialize' : 'preprocess';
  if (purpose === 'initialize') manifest.initialization = { configuration: 'Configuration:config', state: 'Seed:state', proof: 'Seed:initial_valid' };
  json(path.join(directory, 'manifest.json'), manifest);
  if (purpose === 'initialize' || executing) {
    const check = purpose === 'initialize'
      ? 'import Base\nimport ./Configuration.bend as C\nimport ./Seed.bend as Seed\nimport ./Requirements.bend as R\n'
      : 'import Base\nimport ./Bindings.bend as Bindings\nimport ./ClientProof.bend as ClientProof\nimport ./Interface.bend as I\n';
    write(path.join(directory, 'Check.bend'), check);
    const names = sourceClosure(available, imports(Buffer.from(check)), 'Unadmitted pure dependency: ', false);
    if (names.has('Native.bend')) fail('KERNEL_CAPTURE', 'The pure module set reaches Native');
    const pure = { submissionDir: manifest.submissionDir, entry: 'Check.bend', dependencies: [
      ...manifest.dependencies.filter(d => names.has(d.path)),
      { path: 'Check.bend', role: 'host', exports: [], sha256: digest(check) }],
      ...(purpose === 'initialize' ? { purpose: 'initialize', initialization: manifest.initialization }
        : { openTargets: manifest.openTargets, certificateMode: manifest.certificateMode, readOnly: manifest.readOnly }) };
    json(path.join(directory, 'check-manifest.json'), pure);
  }
}

function command(program, args) {
  const result = spawnSync(program, args, { stdio: ['ignore', 2, 2] });
  if (result.error || result.signal || result.status !== 0) fail('HELPER', `${path.basename(program)}: ${result.error?.message ?? result.signal ?? result.status}`);
}
function compile(environment, directory, purpose, sourceDir, kernelPath, metadata, runtimeRoot) {
  stage(environment, directory, purpose, metadata);
  const source = path.join(directory, 'checked.c');
  try { command(process.execPath, ['--stack_size=65536', path.join(runtimeRoot, 'tools/service/compile.mjs'), path.join(directory, 'manifest.json'), source, sourceDir, kernelPath,
    ...(['initialize', 'execute', 'prepare', 'prepare-read'].includes(purpose) ? [path.join(directory, 'check-manifest.json')] : [])]); }
  catch (e) {
    const errorPath = source + '.error.json';
    if (fs.existsSync(errorPath)) {
      const detail = JSON.parse(utf8(read(errorPath)));
      throw Object.assign(new Error(detail.message), detail);
    }
    throw e;
  }
  const report = JSON.parse(utf8(read(source + '.json'))), original = read(source);
  if (digest(original) !== report.cSha256) fail('SOURCE_IO', 'C differs from the checked Book');
  const limits = report.limits;
  if (Object.keys(limits).sort().join(',') !== 'message,response,state' || Object.values(limits).some(x => !/^(0|[1-9][0-9]*)$/.test(x))) fail('CONFIGURATION', 'Expected three natural logical limits');
  const executable = path.join(directory, report.cSha256 + '.program'), clang = '/usr/bin/clang-19';
  const flags = ['-std=gnu11', '-O2', '-w', '--no-default-config', source, '-o', executable, '-lm', '-pthread'];
  command(clang, flags);
  if (!read(source).equals(original)) fail('SOURCE_IO', 'Checked C changed during compilation');
  json(executable + '.json', { format: 'jaydb-official-c-v1', sourceSha256: digest(original), executableSha256: digest(read(executable)), compiler: clang, compilerSha256: digest(read(clang)), flags });
  return { program: executable, limits, certificateMode: report.admission.certificateMode, readOnly: report.admission.readOnly };
}

export function initialize(workdir, configuration, seed, sourceDir, kernelPath) {
  workdir = path.resolve(workdir); fs.mkdirSync(workdir, { recursive: true, mode: 0o700 });
  const environment = freeze(workdir, configuration, seed), runtimeRoot = path.join(workdir, 'runtime'), programs = {};
  let limits;
  for (const purpose of ['initialize', 'authenticate']) {
    const built = compile(environment, path.join(workdir, purpose), purpose, sourceDir, kernelPath, null, runtimeRoot);
    if (limits && JSON.stringify(limits) !== JSON.stringify(built.limits)) fail('CONFIGURATION', 'Configuration changed during initialization');
    limits = built.limits; programs[purpose] = built.program;
  }
  return { programs, limits, stagePath: path.join(runtimeRoot, 'tools/service/stage.mjs') };
}
export function recover(workdir, configuration, sourceDir, kernelPath) {
  workdir = path.resolve(workdir); fs.mkdirSync(workdir, { recursive: true, mode: 0o700 });
  const environment = freeze(workdir, configuration, null), runtimeRoot = path.join(workdir, 'runtime'), programs = {};
  let limits;
  for (const purpose of ['recover', 'authenticate']) {
    const built = compile(environment, path.join(workdir, purpose), purpose, sourceDir, kernelPath, null, runtimeRoot);
    if (limits && JSON.stringify(limits) !== JSON.stringify(built.limits)) fail('CONFIGURATION', 'Configuration changed during recovery');
    limits = built.limits; programs[purpose] = built.program;
  }
  return { programs, limits, stagePath: path.join(runtimeRoot, 'tools/service/stage.mjs') };
}
export function execute(workdir, directory, metadata, sourceDir, kernelPath, purpose = 'execute') {
  return compile(reopen(workdir), path.resolve(directory), purpose, sourceDir, kernelPath, metadata, path.join(workdir, 'runtime'));
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    const [operation, ...args] = process.argv.slice(2);
    let result;
    if (operation === 'initialize' && args.length === 5) result = initialize(...args);
    else if (operation === 'recover' && args.length === 4) result = recover(...args);
    else if (['execute', 'prepare', 'prepare-read'].includes(operation) && args.length === 5) result = execute(...args, operation);
    else fail('USAGE', 'stage.mjs initialize|execute|prepare|prepare-read WORKDIR CONFIG|REQUEST SEED|METADATA BEND_SOURCE BENDTT; recover WORKDIR CONFIG BEND_SOURCE BENDTT');
    process.stdout.write(JSON.stringify(result) + '\n');
  } catch (error) {
    process.stderr.write(JSON.stringify({ code: error.code ?? 'STAGING', message: error.message }) + '\n');
    process.exitCode = 2;
  }
}
