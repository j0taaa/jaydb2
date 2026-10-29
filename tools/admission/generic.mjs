import fs from 'node:fs';
import path from 'node:path';
import { registerHooks } from 'node:module';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { AdmissionError, sha256 } from './bootstrap.mjs';
import { loadFrontendCache } from './frontend-cache.mjs';

const backendURL = new URL('../native/generic.mjs', import.meta.url);

export async function loadPinnedGenericCompiler(sourceDir, expected) {
  const bytes = fs.readFileSync(backendURL);
  if (sha256(bytes) !== expected) throw new AdmissionError('BACKEND', 'compile', 'Hash do emissor genérico diverge do pin do host');
  // Import the verified snapshot, not a second read of a potentially changed
  // module. This reviewed adapter uses only node: imports; its generated comp.ts
  // imports the exact same bend.ts URL/instance that checked the Book.
  const backend = await import('data:text/javascript;base64,' + bytes.toString('base64'));
  const cache = loadFrontendCache();
  if (cache.pin.nativeBackendSha256 !== expected) throw new AdmissionError('BACKEND', 'compile', 'Emissor genérico diverge do frontend instalado offline');
  const bendImport = 'from ' + JSON.stringify(pathToFileURL(path.join(sourceDir, 'bend2/bend.ts')).href);
  const hook = registerHooks({ load(url, context, nextLoad) {
    if (!url.startsWith('file:') || !url.endsWith('/comp.ts') || !fileURLToPath(url).includes('/jaydb-generic-')) return nextLoad(url, context);
    const source = fs.readFileSync(fileURLToPath(url), 'utf8');
    const normalized = source.replace(bendImport, 'from "jaydb:pinned-bend"');
    if (source.split(bendImport).length !== 2 || sha256(normalized) !== cache.pin.nativeSourceNormalizedSha256) {
      throw new AdmissionError('BACKEND', 'compile', 'Fonte derivada do emissor diverge da instalação offline');
    }
    return { format: 'module', source: cache.sources.generic.replace('from "jaydb:pinned-bend"', bendImport), shortCircuit: true };
  } });
  let compiler;
  try { compiler = await backend.loadGenericCompiler(path.join(sourceDir, 'bend2')); }
  finally { hook.deregister(); }
  if (typeof compiler?.compile_book !== 'function' || !/^[a-f0-9]{64}$/.test(compiler.sourceSha256)) {
    throw new AdmissionError('BACKEND', 'compile', 'Emissor genérico fixado não implementa a API esperada');
  }
  return compiler;
}
