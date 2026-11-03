import fs from 'node:fs';
import path from 'node:path';
import { AdmissionError, sha256 } from './bootstrap.mjs';

const contract = JSON.parse(fs.readFileSync(new URL('./contract.lock.json', import.meta.url), 'utf8'));
const fail = (code, message) => { throw new AdmissionError(code, 'preflight', message); };
const modulePath = /^(?:[A-Za-z_][\w-]*\/)*[A-Za-z_][\w-]*\.bend$/;

// Same header grammar and stopping rule as Bend 2.0.39 book_load. Only the
// resolve differs: it has no hub, package-name lookup, cache or file fallback.
// Spaces retain byte/line positions; the original source is kept separately.
export function header(text, file) {
  const lines = text.split('\n');
  const imports = [];
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();
    if (!line || line.startsWith('#')) continue;
    if (!/^import(\s|$)/.test(line)) break;
    const m = /^import\s+(\S+)(?:\s+as\s+([A-Za-z_]\w*))?\s*(?:#.*)?$/.exec(line);
    if (!m || (m[2] === undefined && m[1] !== 'Base')) fail('IMPORT', `${file}:${i + 1}: invalid import`);
    if (m[2] !== undefined) {
      // Match official plain local path grammar. Remote/named libraries are
      // never resolved, even when cached or already present on disk.
      if (!m[1].endsWith('.bend') || !/^(?:\.\/)?(?:\.\.\/)*(?:[A-Za-z_][\w-]*\/)*[A-Za-z_][\w-]*\.bend$/.test(m[1])) {
        fail('IMPORT', `${file}:${i + 1}: nonlocal import: ${m[1]}`);
      }
    }
    imports.push({ specifier: m[1], alias: m[2] });
    lines[i] = lines[i].replace(/[^\r]/g, ' ');
  }
  return { imports, body: lines.join('\n') };
}

function snapshot(root, relative, expected, foreign = false) {
  const pattern = foreign ? /^(?:[A-Za-z_][\w-]*\/)*[A-Za-z_][\w-]*\.c$/ : modulePath;
  if (!pattern.test(relative)) fail('PATH', `Invalid source path: ${relative}`);
  const file = path.join(root, relative);
  let cursor = root;
  // No symlink components, hardlinks, FIFOs or devices. The host must own this
  // directory; reading a snapshot makes later request-file changes irrelevant.
  for (const component of relative.split('/')) {
    cursor = path.join(cursor, component);
    const st = fs.lstatSync(cursor);
    if (st.isSymbolicLink()) fail('PATH', `Symbolic link: ${relative}`);
  }
  const last = fs.lstatSync(file);
  if (!last.isFile() || last.nlink !== 1) fail('PATH', `Source is nonregular or hard-linked: ${relative}`);
  const fd = fs.openSync(file, fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK);
  try {
    const st = fs.fstatSync(fd);
    if (!st.isFile() || st.nlink !== 1) fail('PATH', `Source is nonregular or hard-linked: ${relative}`);
    const bytes = fs.readFileSync(fd);
    const digest = sha256(bytes);
    if (digest !== expected) fail('HASH', `Source differs from the host hash: ${relative}`);
    const text = new TextDecoder('utf-8', { fatal: true, ignoreBOM: true }).decode(bytes);
    return { text, sha256: digest, bytes: bytes.length };
  } finally {
    fs.closeSync(fd);
  }
}

/** A manifest is a HOST capability, never an object received from the client. */
export function preflight({ submissionDir, entry, dependencies, openTargets, canonicalRefs = {}, kernel, purpose, initialization }, kernelOnly = false) {
  try {
    const root = fs.realpathSync(submissionDir);
    if (!Array.isArray(dependencies) || !dependencies.length) fail('MANIFEST', 'An explicit dependency set is required');
    if (typeof entry !== 'string' || !modulePath.test(entry) || entry.includes('/')) fail('MANIFEST', 'Entry must be a root-level module');
    if (!canonicalRefs || typeof canonicalRefs !== 'object' || Array.isArray(canonicalRefs)
        || Object.keys(canonicalRefs).some(k => !['contractPrefix', 'bindings', 'instance', 'client'].includes(k))) {
      fail('MANIFEST', 'Invalid canonicalRefs');
    }
    const canonical = { contractPrefix: '', bindings: 'Bindings.bend', instance: 'Instance.bend', client: 'Client.bend', ...canonicalRefs };
    if (!['', 'contract/'].includes(canonical.contractPrefix)
        || ['bindings', 'instance', 'client'].some(k => typeof canonical[k] !== 'string' || !modulePath.test(canonical[k]))
        || new Set([entry, canonical.bindings, canonical.instance, canonical.client]).size !== 4) {
      fail('MANIFEST', 'Invalid or duplicate canonical paths');
    }
    const records = new Map();
    for (const dep of dependencies) {
      if (!dep || !modulePath.test(dep.path) || !/^[a-f0-9]{64}$/.test(dep.sha256)
          || !['host', 'library', 'client', 'kernel'].includes(dep.role) || records.has(dep.path)) {
        fail('MANIFEST', 'Invalid or duplicate dependency');
      }
      if (dep.role === 'host' && (!Array.isArray(dep.exports) || dep.exports.some(k => typeof k !== 'string'))) {
        fail('MANIFEST', `Explicit exports required for host module: ${dep.path}`);
      }
      const contractFile = dep.path.startsWith('contract/') ? dep.path.slice(9) : dep.path;
      if (contract[contractFile] && (dep.path !== canonical.contractPrefix + contractFile
          || dep.role !== 'library' || dep.sha256 !== contract[contractFile])) {
        fail('CONTRACT', `Contract module replaced: ${dep.path}`);
      }
      const data = snapshot(root, dep.path, dep.sha256);
      records.set(dep.path, { ...dep, exports: new Set(dep.exports ?? []), ...data, ...header(data.text, dep.path), ns: dep.path === entry ? '' : dep.path.slice(0, -5) });
    }
    for (const file of kernelOnly ? [] : ['Requirements.bend', 'Interface.bend']) {
      if (!records.has(canonical.contractPrefix + file)) fail('CONTRACT', `Required module missing: ${canonical.contractPrefix + file}`);
    }
    for (const file of kernelOnly ? [] : [canonical.bindings, canonical.instance]) {
      if (records.get(file)?.role !== 'host') fail('MANIFEST', `${file} must be immutable and host-generated`);
    }
    if ((!kernelOnly && records.get(canonical.client)?.role !== 'client') || !['host', 'kernel'].includes(records.get(entry)?.role)) {
      fail('MANIFEST', 'Client module and host/kernel entry are required');
    }
    const bindingsNS = records.get(canonical.bindings)?.ns;
    const targets = [bindingsNS + ':certificate', bindingsNS + ':terminates'];
    if (!kernelOnly && (!openTargets || Object.keys(openTargets).length !== 2 || targets.some(k => records.get(openTargets[k])?.role !== 'client'))) {
      fail('TARGET', 'Both targets must explicitly identify their implementing client modules');
    }
    if (kernelOnly) {
      if (!['initialize', 'preprocess'].includes(purpose) || [...records.values()].some(r => r.role === 'client')
          || (openTargets !== undefined && Object.keys(openTargets).length)) fail('MANIFEST', 'Kernel requires purpose initialize/preprocess, without clients or openTargets');
      openTargets = {};
      if (purpose === 'initialize') {
        const ref = /^(?:[A-Za-z_][\w-]*\/)*[A-Za-z_][\w-]*:[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*$/;
        if (!initialization || Object.keys(initialization).some(k => !['configuration', 'state', 'proof', 'proofFile'].includes(k))
            || ['configuration', 'state', 'proof'].some(k => typeof initialization[k] !== 'string' || !ref.test(initialization[k]))
            || !records.has(canonical.contractPrefix + 'Requirements.bend')) fail('INITIALIZATION', 'Initialization requires exact configuration, state and Valid-proof references');
        for (const k of ['configuration', 'state', 'proof']) {
          const module = initialization[k].split(':')[0] + '.bend';
          if (!['host', 'kernel'].includes(records.get(module)?.role)) fail('INITIALIZATION', `Initialization reference does not belong to host: ${initialization[k]}`);
        }
        initialization = { ...initialization };
        if (initialization.proofFile !== undefined) {
          if (!['host', 'kernel'].includes(records.get(initialization.proofFile)?.role)) fail('INITIALIZATION', 'Invalid administrator proof file');
          openTargets[initialization.proof] = initialization.proofFile;
        }
      } else if (initialization !== undefined) fail('INITIALIZATION', 'Initialization proof requires purpose initialize');
    }
    let kernelPlan = null;
    if (kernel !== undefined) {
      if (!kernel || Object.keys(kernel).some(k => !['module', 'primitives', 'foreign', 'loopStep'].includes(k))
          || records.get(kernel.module)?.role !== 'kernel' || kernel.module === entry
          || !Array.isArray(kernel.primitives) || !kernel.primitives.length
          || new Set(kernel.primitives).size !== kernel.primitives.length
          || kernel.primitives.some(k => !['read', 'write', 'loop'].includes(k))
          || (kernel.primitives.includes('loop') && (typeof kernel.loopStep !== 'string' || !kernel.loopStep.length))
          || (!kernel.primitives.includes('loop') && kernel.loopStep !== undefined)
          || !kernel.foreign || Object.keys(kernel.foreign).some(k => !['path', 'sha256'].includes(k))
          || typeof kernel.foreign.path !== 'string' || !/^[a-f0-9]{64}$/.test(kernel.foreign.sha256)) {
        fail('KERNEL_ABI', 'Kernel boundary requires a host-pinned module, ABI primitives and C source');
      }
      kernelPlan = { module: kernel.module, ns: records.get(kernel.module).ns, primitives: [...kernel.primitives], loopStep: kernel.loopStep,
        foreign: { path: kernel.foreign.path, ...snapshot(root, kernel.foreign.path, kernel.foreign.sha256, true) } };
    } else if ([...records.values()].some(r => r.role === 'kernel')) {
      fail('KERNEL_ABI', 'Kernel role requires an explicit ABI contract');
    }
    if (kernelOnly && purpose !== 'initialize' && !kernelPlan) fail('KERNEL_ABI', 'Preprocessing requires an explicit ABI boundary');
    // All listed files are checked, including unused helpers. No unlisted file
    // is read because an import happens to mention it.
    for (const rec of records.values()) {
      rec.aliases = Object.create(null);
      rec.edges = [];
      for (const imp of rec.imports) {
        if (imp.alias === undefined) continue; // pinned Base, supplied in memory
        if (Object.hasOwn(rec.aliases, imp.alias)) fail('IMPORT', `Duplicate alias: ${rec.path}: ${imp.alias}`);
        const to = path.posix.normalize(path.posix.join(path.posix.dirname(rec.path), imp.specifier));
        if (!records.has(to)) fail('DEPENDENCY', `Unadmitted dependency: ${rec.path} -> ${imp.specifier}`);
        if (rec.role === 'client' && records.get(to).role === 'host' && records.get(to).exports.size === 0) {
          fail('HOST_CAPTURE', `Private host module is not a client dependency: ${rec.path} -> ${to}`);
        }
        rec.aliases[imp.alias] = records.get(to).ns;
        rec.edges.push(to);
      }
    }
    const ordered = [], seen = new Set(), active = new Set();
    function visit(file) {
      if (active.has(file)) fail('IMPORT_CYCLE', `Import cycle: ${file}`);
      if (seen.has(file)) return;
      active.add(file);
      const rec = records.get(file);
      for (const to of rec.edges) visit(to);
      active.delete(file);
      seen.add(file);
      ordered.push(rec);
    }
    visit(entry);
    for (const file of records.keys()) visit(file);
    return { root, records, ordered, entry, canonicalRefs: Object.freeze(canonical), kernel: kernelPlan,
      kernelOnly, purpose: kernelOnly ? purpose : 'submission', initialization, openTargets: { ...openTargets } };
  } catch (cause) {
    if (cause instanceof AdmissionError) throw cause;
    throw new AdmissionError('SOURCE_IO', 'preflight', `Failed to obtain host sources: ${cause.message}`, { cause });
  }
}
