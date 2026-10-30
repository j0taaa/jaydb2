import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { AdmissionError, sha256 } from './bootstrap.mjs';

const fail = message => { throw new AdmissionError('KERNEL_ABI', 'policy', message); };
const shape = (B, t) => JSON.stringify(B.term_lower(t), function (k, v) {
  if (k === 's' || (k === 'k' && ['All', 'Lam', 'Var'].includes(this.$))) return undefined;
  return v;
});

// This is a closed ABI, not a host-supplied proposition or compiler callback.
// Every trusted foreign result is IO; no primitive can assert a theorem.
const signatures = `
type Iteracao<-A: Type> is Type:
  Continuar{estado: A}
  Preparar{estado: A}
  Encerrar{bytes: List<&2, U32>}
  Inconsistente{}

def read() -> IO(List<&2, U32>):
  import "./effects.c"

def write(bytes: List<&2, U32>) -> IO(Unit):
  import "./effects.c"

def loop(-A: Type, step: A -> Iteracao<A>, initial: A) -> IO(Unit):
  import "./effects.c"
`;

export function prepareKernel(B, state) {
  const { plan, book } = state;
  if (!plan.kernel) return null;
  const { ns, primitives, foreign, module } = plan.kernel;
  const expected = B.book_nil();
  for (const k of state.baseNames) expected.tlds[k] = book.tlds[k];
  for (const k of state.baseCtors) expected.ctrs[k] = book.ctrs[k];
  B.parse_book(expected, '/', signatures, ns, Object.create(null));
  for (const name of primitives) {
    const k = ns + ':' + name, t = book.tlds[k], want = expected.tlds[k];
    if (state.owners.get(k)?.path !== module || t?.$ !== 'Def' || t.u || t.l || t.b || t.v !== null
        || t.x !== 0 || t.n !== want.n || !Array.isArray(t.i) || t.i.length !== 1
        || path.resolve(t.i[0]) !== path.join(plan.root, foreign.path) || shape(B, t.T) !== shape(B, want.T)) {
      fail(`Primitiva ABI inválida: ${k}`);
    }
    state.primitives.add(k);
  }
  if (primitives.includes('loop')) {
    const k = ns + ':Iteracao', t = book.tlds[k], want = expected.tlds[k];
    if (state.owners.get(k)?.path !== module || t?.$ !== 'ADT' || t.b || t.n !== want.n
        || shape(B, t.T) !== shape(B, want.T) || t.c.length !== want.c.length
        || t.c.some((c, i) => c.k !== want.c[i].k || c.n !== want.c[i].n || shape(B, c.T) !== shape(B, want.c[i].T))) {
      fail(`Tipo de iteração ABI inválido: ${k}`);
    }
    const step = book.tlds[plan.kernel.loopStep], owner = state.owners.get(plan.kernel.loopStep);
    if (step?.$ !== 'Def' || step.n !== 1 || step.x !== 0 || step.u || step.i !== undefined || step.v === null
        || !(owner?.role === 'kernel' || owner?.path === plan.entry)) fail('loopStep deve ser uma definição fechada de um argumento do kernel/entrada');
  }
  // The official emitter reads foreign snippets. Give it a private copy of the
  // already-authenticated bytes, never a late read of the submission directory.
  // The path is installed BEFORE either checker and is covered by the Book seal.
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'jaydb-admission-abi-'));
  const file = path.join(directory, 'effects.c');
  try {
    fs.writeFileSync(file, foreign.text, { flag: 'wx', mode: 0o400 });
    for (const k of state.primitives) book.tlds[k].i = [file];
  } catch (e) { fs.rmSync(directory, { recursive: true, force: true }); throw e; }
  return { directory, file, sha256: foreign.sha256 };
}

export function auditLoopCalls(B, state) {
  if (!state.plan.kernel) return;
  const loop = state.plan.kernel.ns + ':loop', step = state.plan.kernel.loopStep;
  function visit(t, owner) {
    if (!t || typeof t !== 'object') return;
    if (t.$ === 'App') {
      let head = t, args = [];
      while (head.$ === 'App') { args.unshift(head.x); head = head.f; }
      if (head.$ === 'Ref' && head.k === loop) {
        if (args.length !== 3 || args[1].$ !== 'Ref' || args[1].k !== step) fail(`loop exige o passo fechado fixado pelo host: ${step}`);
        for (const a of args) visit(a, owner);
        return;
      }
    }
    if (t.$ === 'Ref' && t.k === loop) fail('loop não pode ser usado como alias ou valor de primeira classe');
    for (const [k, v] of Object.entries(t)) if (k !== 's' && v && typeof v === 'object') visit(v, owner);
  }
  for (const [k, t] of Object.entries(state.book.tlds)) {
    if (!state.baseNames.has(k) && t.$ === 'Def' && t.v) visit(B.term_lower(t.v), k);
  }
}

export function validateKernelEntry(B, state) {
  if (!state.plan.kernel) return;
  const t = state.book.tlds.main;
  const T = B.App(B.Ref('IO'), B.Ref('Unit'));
  if (t?.$ !== 'Def' || t.n !== 0 || t.u || t.i !== undefined || t.v === null
      || shape(B, t.T) !== shape(B, T)) fail('Entrada kernel deve definir main() -> IO(Unit)');
}

export function validateForeignSnapshot(snapshot) {
  if (!snapshot) return;
  const st = fs.lstatSync(snapshot.file);
  if (!st.isFile() || st.nlink !== 1 || sha256(fs.readFileSync(snapshot.file)) !== snapshot.sha256) {
    throw new AdmissionError('SOURCE_IO', 'compile', 'Snapshot privado da ABI foi modificado');
  }
}

export function removeForeignSnapshot(snapshot) {
  if (snapshot) fs.rmSync(snapshot.directory, { recursive: true, force: true });
}
