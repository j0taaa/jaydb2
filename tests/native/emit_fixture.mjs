// Test-only emitter. Primary check only; never a production admission path.
import fs from 'node:fs';
import { pathToFileURL } from 'node:url';
import path from 'node:path';
import { loadGenericCompiler } from '../../tools/native/generic.mjs';
const [directory, input, output, mode = 'generic'] = process.argv.slice(2);
const B = await import(pathToFileURL(path.join(directory, 'bend.ts')).href);
const book = B.book_nil();
try {
  await B.book_load(book, path.resolve(input), '', new Map());
  B.book_valid(book);
} catch (error) {
  console.error(error?.$ === 'Err' ? B.err_show(error) : String(error));
  process.exit(1);
}
if (book.hols) throw new Error('fixture has holes');
const C = mode === 'generic' ? await loadGenericCompiler(directory)
  : await import(pathToFileURL(path.join(directory, 'comp.ts')).href);
fs.writeFileSync(output, C.compile_book(book));
