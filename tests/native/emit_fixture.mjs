// Test-only primary check and the unmodified official C compiler.
import fs from 'node:fs';
import path from 'node:path';
import {loadToolchain} from '../../tools/admission/bootstrap.mjs';
const [directory,input,output]=process.argv.slice(2);
const {B,C}=await loadToolchain({sourceDir:path.dirname(directory)});
const book=B.book_nil();
try{await B.book_load(book,path.resolve(input),'',new Map());B.book_valid(book);}
catch(error){console.error(error?.$==='Err'?B.err_show(error):String(error));process.exit(1);}
if(book.hols)throw Error('fixture has holes');
fs.writeFileSync(output,C.compile_book(book));
