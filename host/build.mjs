// Literal C emitted by the pinned official compiler; no runtime rewriting.
import fs from 'node:fs';
import path from 'node:path';
import {spawnSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';
import {loadToolchain, sha256} from '../tools/admission/bootstrap.mjs';
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const out = path.join(root, 'target/bend-host');
fs.mkdirSync(out, {recursive:true});
const {B,C} = await loadToolchain();
const book = B.book_nil();
try { await B.book_load(book,path.join(root,'host/Main.bend'),'',new Map()); B.book_valid(book); }
catch(e) { console.error(e?.$ === 'Err' ? B.err_show(e) : e); process.exit(1); }
if(book.hols) throw Error('controller has holes');
if(process.argv.includes('--check')) { console.log('Official primary controller check passed'); process.exit(0); }
const c = C.compile_book(book), source = path.join(out,'controller.c'), binary = path.join(out,'controller');
fs.writeFileSync(source,c);
const run = spawnSync('/usr/bin/clang-19',['-std=gnu11','-O2','-w','--no-default-config',source,'-o',binary,'-lm','-pthread'],{stdio:'inherit'});
if(run.status !== 0) process.exit(run.status ?? 1);
if(fs.readFileSync(source,'utf8') !== c) throw Error('emitted C changed');
fs.writeFileSync(binary+'.json',JSON.stringify({executableSha256:sha256(fs.readFileSync(binary)),sourceSha256:sha256(c)}));
console.log('Built official Bend controller '+binary);
