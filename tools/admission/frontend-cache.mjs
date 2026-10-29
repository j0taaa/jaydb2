import fs from 'node:fs';
import { createHash } from 'node:crypto';
const hash = data => createHash('sha256').update(data).digest('hex');
export function loadFrontendCache() {
  const pin = JSON.parse(fs.readFileSync(new URL('./frontend.lock.json', import.meta.url)));
  if (pin.node !== process.version || pin.nodeModuleVersion !== process.versions.modules) throw new Error('Frontend requires its pinned Node runtime');
  const installed = fs.readFileSync(new URL('./installed/manifest.json', import.meta.url));
  if (JSON.stringify(JSON.parse(installed)) !== JSON.stringify(pin)) throw new Error('Frontend install manifest mismatch');
  for (const [name, expected] of Object.entries(pin.transforms)) {
    if (hash(fs.readFileSync(new URL(name, import.meta.url))) !== expected) throw new Error('Frontend adapter pin mismatch: ' + name);
  }
  for (const [key, name] of [['stackSourceSha256', 'stack.cc'], ['stackLoaderSha256', 'stack.cjs'], ['builderSha256', 'build-frontend.mjs']]) {
    if (hash(fs.readFileSync(new URL(name, import.meta.url))) !== pin[key]) throw new Error('Frontend installation pin mismatch: ' + name);
  }
  const sources = {};
  for (const name of ['bend', 'safe', 'safe-structural', 'comp', 'generic']) {
    const js = fs.readFileSync(new URL('./installed/' + name + '.mjs', import.meta.url));
    if (hash(js) !== pin.files[name + '.mjs']) throw new Error('Frontend compiled artifact pin mismatch: ' + name);
    sources[name] = js.toString('utf8');
  }
  return { pin, sources };
}
