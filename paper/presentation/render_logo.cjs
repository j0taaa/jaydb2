// Regenerates assets/jaydb2-*.svg. The wordmark is outlined from Inter SemiBold so it renders as an <img>.
// Usage: npm i opentype.js@1.3.4 (anywhere on NODE_PATH); node render_logo.cjs assets/Inter-SemiBold.otf assets
const opentype=require('opentype.js');const fs=require('fs');
const [,,fontPath,outDir]=process.argv;
const font=opentype.loadSync(fontPath);
function word(text,size,x0,base,track){
  const glyphs=font.stringToGlyphs(text);let x=x0;const parts=[];
  glyphs.forEach((g,i)=>{const p=g.getPath(x,base,size);parts.push(p.toPathData(2));
    x+=g.advanceWidth*size/font.unitsPerEm+track;
    if(i<glyphs.length-1)x+=font.getKerningValue(g,glyphs[i+1])*size/font.unitsPerEm;});
  return {parts,width:x-track-x0};
}
// Mark: a mint gate (the cover's glass frame) around a database cylinder with a check.
const mark=(gate,glass,body,check)=>`<g class="jaydb2-mark">
<rect x="9" y="8" width="46" height="52" fill="${glass}" opacity=".16"/>
<path d="M6.5 60V10.5a4 4 0 0 1 4-4h43a4 4 0 0 1 4 4V60" fill="none" stroke="${gate}" stroke-width="5" stroke-linecap="round"/>
<g fill="none" stroke="${body}" stroke-width="3.6" stroke-linecap="round" stroke-linejoin="round">
<ellipse cx="32" cy="22" rx="13" ry="4.6"/>
<path d="M19 22v26c0 2.6 5.8 4.6 13 4.6s13-2 13-4.6V22"/>
</g>
<path d="M25.5 37.2l4.5 4.5 8-8.5" fill="none" stroke="${check}" stroke-width="3.6" stroke-linecap="round" stroke-linejoin="round"/>
</g>`;
const size=50,base=53;
const a=word('JayDB',size,82,base,-1.6);
const b=word('2',size,82+a.width-1.6,base,0);
const W=Math.ceil(82+a.width-1.6+b.width+2);
const lockup=(gate,glass,body,check,ink,accent,title)=>`<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${W} 64" width="${W*2}" height="128" role="img" aria-label="JayDB2"><title>${title}</title>${mark(gate,glass,body,check)}<path fill="${ink}" d="${a.parts.join('')}"/><path fill="${accent}" d="${b.parts.join('')}"/></svg>\n`;
fs.writeFileSync(outDir+'/jaydb2-logo.svg',lockup('#b4e6c8','#b4e6c8','#f4f1e8','#b4e6c8','#f4f1e8','#b4e6c8','JayDB2 (fundo escuro)'));
fs.writeFileSync(outDir+'/jaydb2-logo-light.svg',lockup('#087869','#087869','#102f3b','#087869','#102f3b','#087869','JayDB2 (fundo claro)'));
fs.writeFileSync(outDir+'/jaydb2-mark.svg',`<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 64 64" width="128" height="128" role="img" aria-label="JayDB2"><title>JayDB2</title>${mark('#b4e6c8','#b4e6c8','#f4f1e8','#b4e6c8')}</svg>\n`);
fs.writeFileSync(outDir+'/jaydb2-mark-light.svg',`<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 64 64" width="128" height="128" role="img" aria-label="JayDB2"><title>JayDB2</title>${mark('#087869','#087869','#102f3b','#087869')}</svg>\n`);
console.log('width',W);
