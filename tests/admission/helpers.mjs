import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { sha256 } from '../../tools/admission/bootstrap.mjs';

export const repo = fileURLToPath(new URL('../../', import.meta.url));
const fixtureDir = fileURLToPath(new URL('./fixtures/', import.meta.url));
const contractFiles = ['Dados', 'Semantica', 'Logica', 'Bytes', 'Protocolo', 'Requisitos', 'Interface', 'Recursos'];

export function fixture(t) {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'jaydb-admission-test-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  for (const f of contractFiles) fs.copyFileSync(path.join(repo, 'contrato', f + '.bend'), path.join(root, f + '.bend'));
  for (const f of fs.readdirSync(fixtureDir)) fs.copyFileSync(path.join(fixtureDir, f), path.join(root, f));
  const roles = new Map([
    ...contractFiles.map(f => [f + '.bend', 'library']),
    ['Client.bend', 'client'], ['ClientProof.bend', 'client'], ['Instance.bend', 'host'], ['Bindings.bend', 'host'], ['Main.bend', 'host'],
  ]);
  const exports = {
    'Instance.bend': ['Instance:config', 'Instance:contexto', 'Instance:argumentos', 'Instance:NaoObserva'],
    'Bindings.bend': ['Bindings:codigo', 'Bindings:certificado', 'Bindings:termina'],
    'Main.bend': [],
  };
  const read = f => fs.readFileSync(path.join(root, f), 'utf8');
  const write = (f, text, role) => {
    fs.mkdirSync(path.dirname(path.join(root, f)), { recursive: true });
    fs.writeFileSync(path.join(root, f), text);
    if (role) roles.set(f, role);
  };
  return {
    root, read, write, roles,
    bindCode() {
      const text = read('Bindings.bend');
      const beg = text.indexOf('def codigo()');
      const end = text.indexOf('\nlaw certificado:', beg);
      write('Bindings.bend', text.slice(0, beg) + 'def codigo() -> String:\n  ' + JSON.stringify(read('Client.bend')) + '\n' + text.slice(end));
    },
    manifest() {
      return { submissionDir: root, entry: 'Main.bend',
        openTargets: { 'Bindings:certificado': 'ClientProof.bend', 'Bindings:termina': 'ClientProof.bend' },
        dependencies: [...roles].map(([file, role]) => ({ path: file, role, sha256: sha256(fs.readFileSync(path.join(root, file))), ...(role === 'host' ? { exports: exports[file] ?? [] } : {}) })),
      };
    },
  };
}
