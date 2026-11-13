'use strict';
/* ───────────────────────── Deck building blocks (API) ─────────────────────────
 Diagrams (inside figure(name, body, height=460, width=1400), an SVG on a 1400-wide grid):
   box(x,y,w,h,title,lines,kind)  kind '' | 'accept' | 'reject'; '|' splits lines
   edge(d,kind)  path with arrowhead; kind 'deny' for coral;  label(x,y,'a|b',cls)
   step(n,svg)   SVG group revealed on the n-th → press (HTML: class="fragment" data-step="n")
 Icons (24×24 line icons, stroke currentColor; names: Object.keys(ICONS)):
   icon(name,{size=40,cls,title})       inline <svg class="icon">; color via cls, e.g. 'tone-green'
   badge(name,{size=64,tone,cls})       icon on a tinted disc; tone green|mint|coral|gold|ink|muted
   iconAt(name,x,y,size=48,cls)         inside a diagram SVG; cls goes on an outer <g> (anim-* safe)
   tones: tone-ink|paper|green|mint|coral|gold|muted (green/coral/gold/muted lighten on .dark slides)
 Logo: logo(variant='dark'|'light'|'mark'|'mark-light', cls) → <img class="deck-logo">.
   Files in assets/: jaydb2-logo.svg, jaydb2-logo-light.svg, jaydb2-mark.svg, jaydb2-mark-light.svg
   (wordmark converted to outlines, so it renders without the font).
 Automatic entry animations: play every time a slide is shown, no key press. Put a class on any
   HTML or SVG element: anim-fade, anim-fade-up, anim-grow-x (bars, from the left), anim-grow-y
   (from the bottom), anim-pop (scale in), anim-draw (stroke draws along the shape; player.js adds
   pathLength="1" when missing, so use it on solid strokes; dash patterns and markers are not drawn).
   Stagger with --d (delay) and override duration with --dur: style="--d:.3s;--dur:1.2s" or ${delay(.3)}.
   Do not put anim-* on an element that has its own transform attribute; wrap it in a <g> instead.
   Inside a step (fragment) the animation waits and starts when the step is revealed, with --d
   counted from the reveal; going back and forward replays it. Prefer anim-* on a child of the
   fragment, not on the fragment element itself.
   Final state is shown in print/PDF, with prefers-reduced-motion, and on slides not currently shown.
 Image assets: save to paper/presentation/assets/ (.webp, .svg; add other types to inline_asset's
   mime map in paper/build_presentation.py) and reference as "assets/<file>" in content.js or CSS;
   the builder inlines every such reference as a data URI, so the deck stays one offline HTML file.
──────────────────────────────────────────────────────────────────────────────── */
const E=window.JAYDB2_EVIDENCE;
const value=name=>{if(!(name in E))throw Error('Missing evidence macro: '+name);return Number(E[name]);};
const pt=(n,d=2)=>Number(n).toLocaleString('pt-BR',{minimumFractionDigits:d,maximumFractionDigits:d});
const repo='https://github.com/j0taaa/jaydb2';
const source=(label,path)=>({label,url:repo+'/blob/main/'+path});
const sources={
  artifact:source('Repositório','README.md'),
  laws:source('Leis e certificados','contract/README.md'),
  evidence:source('Experimentos e reprodução','paper/README.md'),
  rls:source('Aplicação de notas','applications/rls/README.md'),
  proofs:source('Teoremas e base de confiança','proof/README.md'),
  voucher:source('Vouchers e recibos','applications/vouchers/README.md'),
  prepared:source('Programas preparados','tools/service/PREPARED_PROGRAMS.md'),
  gpu:source('Execução GPU e confiança','tools/service/SIMPLE_SERVICE.md'),
  simulation:source('Simulação certificada','applications/simulation/README.md'),
  compute:source('E6: dados e limites','paper/evidence/simulation.md'),
  ai:source('Declaração de uso de IA','paper/main.tex'),
  cpr:{label:'Dinamarca: comunicado oficial, 05/10/2026',url:'https://www.cpr.dk/cpr-nyt/nyhedsarkiv/2026/okt/omfattende-uautoriseret-adgang-til-borgeres-cpr-oplysninger'},
  baldur:{label:'First et al. (2023), Baldur, ESEC/FSE',url:'https://doi.org/10.1145/3611643.3616243'},
  misu:{label:'Misu et al. (2024), Dafny verificado, FSE',url:'https://doi.org/10.1145/3643763'},
  autoverus:{label:'Yang et al. (2025), AutoVerus, OOPSLA',url:'https://doi.org/10.1145/3763174'}
};
// Diagrams describe logical dependencies, not physical scheduling or proved trust layers.
const esc=s=>String(s).replaceAll('&','&amp;').replaceAll('<','&lt;').replaceAll('>','&gt;');
const label=(x,y,lines,cls='')=>`<text x="${x}" y="${y}" class="${cls}">${lines.split('|').map((t,i)=>`<tspan x="${x}" dy="${i?36:0}">${esc(t)}</tspan>`).join('')}</text>`;
const box=(x,y,w,h,title,lines='',kind='')=>`<rect class="box ${kind}" x="${x}" y="${y}" width="${w}" height="${h}" rx="8"/>${label(x+24,y+43,title,'box-title')}${lines?label(x+24,y+85,lines):''}`;
const edge=(d,kind='')=>`<path class="edge ${kind}" d="${d}" marker-end="url(#${kind==='deny'?'deny-tip':'flow-tip'})"/>`;
let figureSequence=0;
const step=(n,svg)=>`<g class="fragment" data-step="${n}">${svg}</g>`;
const figure=(name,body,height=460,width=1400)=>`<svg class="system-figure" viewBox="0 0 ${width} ${height}" role="img" aria-label="${name}"><defs><marker id="flow-tip" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="9" markerHeight="9" orient="auto-start-reverse"><path d="M0 0L10 5L0 10Z" fill="#087869"/></marker><marker id="deny-tip" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="9" markerHeight="9" orient="auto-start-reverse"><path d="M0 0L10 5L0 10Z" fill="#b24a32"/></marker></defs>${body}</svg>`.replaceAll('flow-tip',`flow-tip-${figureSequence}`).replaceAll('deny-tip',`deny-tip-${figureSequence++}`);
// Line icons: 24×24 grid, stroke currentColor, 1.75 stroke, round caps/joins. Dots are zero-length round-capped strokes.
const ICONS={
  database:'<ellipse cx="12" cy="5.5" rx="8" ry="3"/><path d="M4 5.5v13c0 1.66 3.58 3 8 3s8-1.34 8-3v-13"/><path d="M4 12c0 1.66 3.58 3 8 3s8-1.34 8-3"/>',
  table:'<rect x="3" y="4" width="18" height="16" rx="2"/><path d="M3 9.5h18M3 14.75h18M9 9.5V20"/>',
  user:'<circle cx="12" cy="8" r="4"/><path d="M4 21c0-4.1 3.6-7 8-7s8 2.9 8 7"/>',
  users:'<circle cx="9" cy="8.5" r="3.5"/><path d="M2.5 20c0-3.6 2.9-6 6.5-6s6.5 2.4 6.5 6"/><path d="M15.5 5.2a3.5 3.5 0 0 1 0 6.6M18 14.4c2.1.8 3.5 2.8 3.5 5.6"/>',
  admin:'<circle cx="10" cy="7.5" r="3.75"/><path d="M3 20.5c0-3.8 3.1-6.5 7-6.5 1 0 1.9.2 2.7.5"/><path d="M18 12.5l3.75 1.4v2.8c0 2.3-1.6 3.9-3.75 4.8-2.15-.9-3.75-2.5-3.75-4.8v-2.8z"/>',
  'shield-check':'<path d="M12 2.75l7.5 3v5.5c0 4.6-3.1 8.4-7.5 10-4.4-1.6-7.5-5.4-7.5-10v-5.5z"/><path d="M8.75 12.25l2.25 2.25 4.25-4.5"/>',
  lock:'<rect x="4.5" y="10.5" width="15" height="10.5" rx="2"/><path d="M8 10.5V7a4 4 0 0 1 8 0v3.5M12 14.75v2"/>',
  key:'<circle cx="8" cy="15.5" r="4.5"/><path d="M11.2 12.3L20.5 3M16.5 7l3 3M14 9.5l2.25 2.25"/>',
  code:'<path d="M14 3H7a2 2 0 0 0-2 2v14a2 2 0 0 0 2 2h10a2 2 0 0 0 2-2V8z"/><path d="M14 3v5h5M10.25 12l-2.25 2.75 2.25 2.75M13.75 12l2.25 2.75-2.25 2.75"/>',
  proof:'<path d="M14 21H6a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h12a2 2 0 0 1 2 2v5"/><path d="M8 7.5h8M8 11.5h5"/><circle cx="17.5" cy="15" r="3.25"/><path d="M15.75 17.75L15.25 22l2.25-1.25L19.75 22l-.5-4.25"/>',
  check:'<path d="M4.5 12.5l5 5L19.5 7"/>',
  x:'<path d="M6 6l12 12M18 6L6 18"/>',
  warning:'<path d="M10.27 4.03a2 2 0 0 1 3.46 0l7.6 13.2a2 2 0 0 1-1.73 3H4.4a2 2 0 0 1-1.73-3z"/><path d="M12 9.5v4M12 17h0"/>',
  cpu:'<rect x="6" y="6" width="12" height="12" rx="1.75"/><rect x="9.5" y="9.5" width="5" height="5" rx=".5"/><path d="M9.5 2.5V6M14.5 2.5V6M9.5 18v3.5M14.5 18v3.5M2.5 9.5H6M2.5 14.5H6M18 9.5h3.5M18 14.5h3.5"/>',
  gpu:'<rect x="2.5" y="5" width="19" height="12" rx="2"/><circle cx="15" cy="11" r="3.25"/><path d="M15 11h0M6 8.75h3.5M6 13.25h3.5M6 17v3M9.5 17v3M13 17v3"/>',
  clock:'<circle cx="12" cy="13.5" r="7.75"/><path d="M12 9.5v4l2.75 2.25M9.5 2.5h5M12 2.5v3.25M18.5 6.25l1.5-1.5"/>',
  'chart-bars':'<path d="M3 20.5h18"/><rect x="5" y="12" width="3.5" height="8.5" rx=".75"/><rect x="10.25" y="6" width="3.5" height="14.5" rx=".75"/><rect x="15.5" y="9.5" width="3.5" height="11" rx=".75"/>',
  'chart-line':'<path d="M3.5 3.5v17h17"/><path d="M7.5 15.5l4-4.5 3 3 5-6.5"/>',
  layers:'<path d="M12 3l9 5-9 5-9-5z"/><path d="M3 12.5l9 5 9-5M3 16.75l9 5 9-5"/>',
  refresh:'<path d="M20 11.5A8 8 0 0 0 5.6 7.2L4 9"/><path d="M4 4.5V9h4.5M4 12.5a8 8 0 0 0 14.4 4.3L20 15"/><path d="M20 19.5V15h-4.5"/>',
  send:'<path d="M21 3L10.5 13.5"/><path d="M21 3l-6.5 18-4-7.5-7.5-4z"/>',
  arrow:'<path d="M4 12h16M14 6l6 6-6 6"/>',
  'eye-off':'<path d="M3 3l18 18"/><path d="M10.6 6.1A9.6 9.6 0 0 1 12 6c5.5 0 9 6 9 6a16.4 16.4 0 0 1-2.6 3.3M6.6 7.6C4.2 9.2 3 12 3 12s3.5 6 9 6a9 9 0 0 0 4.3-1.1M9.9 9.9a3 3 0 0 0 4.2 4.2"/>',
  globe:'<circle cx="12" cy="12" r="9"/><path d="M3 12h18M12 3c2.4 2.5 3.75 5.7 3.75 9S14.4 18.5 12 21c-2.4-2.5-3.75-5.7-3.75-9S9.6 5.5 12 3z"/>',
  news:'<path d="M4 5h12.5v14a2 2 0 0 0 2 2H6a2 2 0 0 1-2-2z"/><path d="M16.5 9H20v10a2 2 0 0 1-2 2M7.5 9h5.5M7.5 12.5h5.5M7.5 16h3.5"/>',
  sparkle:'<path d="M11 3c.6 4.3 2.7 6.4 7 7-4.3.6-6.4 2.7-7 7-.6-4.3-2.7-6.4-7-7 4.3-.6 6.4-2.7 7-7z"/><path d="M18.5 14.5c.3 1.6.9 2.2 2.5 2.5-1.6.3-2.2.9-2.5 2.5-.3-1.6-.9-2.2-2.5-2.5 1.6-.3 2.2-.9 2.5-2.5z"/>',
  robot:'<rect x="4" y="8" width="16" height="12" rx="3"/><path d="M12 4.5V8M9 13.5h0M15 13.5h0M9.5 17h5M1.75 13v3M22.25 13v3"/><circle cx="12" cy="3.5" r="1"/>',
  hourglass:'<path d="M6 2.75h12M6 21.25h12M7 2.75V6a5 5 0 0 0 2.4 4.3L12 12l2.6-1.7A5 5 0 0 0 17 6V2.75M7 21.25V18a5 5 0 0 1 2.4-4.3L12 12l2.6 1.7A5 5 0 0 1 17 18v3.25"/>',
  infinity:'<path d="M12 12c-2-2.6-3.6-4-5.4-4a4 4 0 0 0 0 8c1.8 0 3.4-1.4 5.4-4zm0 0c2 2.6 3.6 4 5.4 4a4 4 0 0 0 0-8c-1.8 0-3.4 1.4-5.4 4z"/>',
  search:'<circle cx="10.5" cy="10.5" r="6.5"/><path d="M15.25 15.25L21 21"/>',
  branch:'<circle cx="6" cy="5" r="2.25"/><circle cx="6" cy="19" r="2.25"/><circle cx="18" cy="6.5" r="2.25"/><path d="M6 7.25v9.5M18 8.75v1.5a3.5 3.5 0 0 1-3.5 3.5h-5A3.5 3.5 0 0 0 6 17.25"/>',
  terminal:'<rect x="3" y="4" width="18" height="16" rx="2"/><path d="M7 9.5l3 2.5-3 2.5M12.5 15H17"/>',
  'hard-drive':'<rect x="3" y="13" width="18" height="7.5" rx="2"/><path d="M5.25 13l2.2-7.2A2.5 2.5 0 0 1 9.8 4h4.4a2.5 2.5 0 0 1 2.4 1.8l2.2 7.2M7 16.75h0M10 16.75h0"/>',
  server:'<rect x="3.5" y="3.5" width="17" height="7" rx="1.75"/><rect x="3.5" y="13.5" width="17" height="7" rx="1.75"/><path d="M7 7h0M7 17h0M11 7h6M11 17h6"/>',
  scale:'<path d="M12 3.5V21M7.5 21h9M4.5 7h15"/><path d="M4.5 7L2 13.5a2.5 2.5 0 0 0 5 0zM19.5 7L17 13.5a2.5 2.5 0 0 0 5 0z"/>',
  expand:'<path d="M4 9V4h5M20 9V4h-5M4 15v5h5M20 15v5h-5M9 9L4 4M15 9l5-5M9 15l-5 5M15 15l5 5"/>',
  flask:'<path d="M9 3h6M10 3v6.2L4.6 18.5A1.75 1.75 0 0 0 6.1 21h11.8a1.75 1.75 0 0 0 1.5-2.5L14 9.2V3M7 15.5h10"/>',
  gear:'<circle cx="12" cy="12" r="3"/><circle cx="12" cy="12" r="6.75"/><path d="M12 2.75v2.5M12 18.75v2.5M2.75 12h2.5M18.75 12h2.5M5.46 5.46l1.77 1.77M16.77 16.77l1.77 1.77M5.46 18.54l1.77-1.77M16.77 7.23l1.77-1.77"/>',
  play:'<circle cx="12" cy="12" r="9"/><path d="M10 8.5l5.25 3.5L10 15.5z"/>',
  file:'<path d="M14 3H7a2 2 0 0 0-2 2v14a2 2 0 0 0 2 2h10a2 2 0 0 0 2-2V8z"/><path d="M14 3v5h5M8.75 13h6.5M8.75 16.5h4.5"/>'
};
const ICON_ATTRS='fill="none" stroke="currentColor" stroke-width="1.75" stroke-linecap="round" stroke-linejoin="round"';
const iconBody=name=>{if(!(name in ICONS))throw Error('Unknown icon: '+name);return ICONS[name];};
// HTML icon: icon('lock',{size:48,cls:'tone-green'}). Decorative (aria-hidden) unless a title is given.
const icon=(name,{size=40,cls='',title=''}={})=>`<svg class="icon ${cls}" viewBox="0 0 24 24" width="${size}" height="${size}" ${ICON_ATTRS} ${title?`role="img" aria-label="${esc(title)}"`:'aria-hidden="true"'}>${title?`<title>${esc(title)}</title>`:''}${iconBody(name)}</svg>`;
// Icon on a tinted disc: badge('gpu',{size:64,tone:'coral'}); tone ∈ green|mint|coral|gold|ink|muted.
const badge=(name,{size=64,tone='green',cls=''}={})=>`<span class="icon-badge badge-${tone} ${cls}" style="width:${size}px;height:${size}px">${icon(name,{size:Math.round(size*.56)})}</span>`;
// Icon inside a diagram SVG at (x,y) with a size in user units. cls lands on an outer <g>, so anim-* classes are safe there.
const iconAt=(name,x,y,size=48,cls='')=>`<g class="icon ${cls}"><g transform="translate(${x} ${y}) scale(${size/24})" ${ICON_ATTRS}>${iconBody(name)}</g></g>`;
// Stagger for auto entry animations: <rect class="anim-grow-x" ${delay(.3)}/> sets --d.
const delay=s=>`style="--d:${s}s"`;
// Logo <img>; the builder inlines each assets/… reference as a data URI.
const LOGOS={dark:'assets/jaydb2-logo.svg',light:'assets/jaydb2-logo-light.svg',mark:'assets/jaydb2-mark.svg','mark-light':'assets/jaydb2-mark-light.svg'};
const logo=(variant='dark',cls='')=>`<img class="deck-logo ${cls}" src="${LOGOS[variant]}" alt="JayDB2">`;
function admissionFigure(){return figure('Cliente envia programa e prova. Leis do administrador alimentam o verificador. Aceitação permite execução privada; rejeição não executa o programa.',
 box(465,0,470,95,'Administrador','Esquema e leis instaladas')+edge('M700 95V155')+
 box(0,170,375,170,'Cliente','Programa + prova|Argumentos + credencial')+edge('M375 250H465')+
 `<path class="gate" d="M510 155H890L935 250L890 345H510L465 250Z"/>`+label(545,228,'Verificador','box-title')+label(545,271,'Prova e código exatos')+
 step(1,edge('M935 220H1020V155H1050')+label(920,195,'Aceita','edge-label')+box(1050,105,345,145,'Execução privada','Sobre o estado atual','accept'))+
 step(2,edge('M935 285H1020V390H1050','deny')+label(920,337,'Rejeita','deny-label')+box(1050,325,345,115,'Sem execução','Estado preservado','reject')),460);}
function transactionFigure(){return figure('Estado publicado vazio. Na proposta privada cria-se a nota, depois a entrada do diretório. Somente o par completo é publicado.',
 box(0,100,280,175,'Publicado','Sem nota|Diretório vazio')+
 step(1,`<rect class="private-zone" x="345" y="0" width="700" height="330" rx="10"/>`+label(370,40,'Proposta privada · invisível aos demais','box-title')+edge('M280 185H375')+
 box(375,100,290,175,'Cria a nota','Nota n1|Diretório vazio','reject')+label(382,312,'Incompleto aqui','deny-label'))+
 step(2,edge('M665 185H725')+box(725,100,290,175,'Atualiza a lista','Nota n1|Diretório inclui n1'))+
 step(3,edge('M1045 185H1120')+box(1120,100,280,175,'Publicado','Nota n1|Diretório inclui n1','accept')+label(1120,315,'Commit','edge-label'))+
 `<path class="edge" d="M0 385H1400"/>`+label(0,425,'Outros clientes observam o estado anterior até a publicação.'),460);}
function rejectionFigure(){return figure('Dois controles independentes: ler Bob viola acesso; omitir o diretório viola a consistência final. Ambos são recusados antes da execução.',
 box(0,0,300,175,'Ler Bob','Alice: bob/n7')+edge('M300 86H360')+
 box(360,0,380,175,'Acesso','Permissão|não demonstrada','reject')+
 step(1,box(0,255,300,175,'Omitir diretório','Cria sem listar')+edge('M300 340H360')+
 box(360,255,380,175,'Diretório','Consistência final|não demonstrada','reject')+
 label(0,495,'Admissão rejeitada. Estado preservado.','deny-label')),520,740);}

function llmFigure(){return figure('O usuário apresenta a intenção ao LLM. O gerador constrói programa e prova e fica fora da base de confiança. O verificador do banco confere as leis.',
 box(0,0,285,150,'Usuário','Intenção')+edge('M285 75H365')+
 box(365,0,480,170,'LLM + bibliotecas','Programa + prova')+
 label(389,137,'Gerador não confiável','deny-label')+
 step(1,edge('M605 170V240')+box(365,240,480,150,'Verificador do banco','Leis instaladas · T1','accept'))+
 step(2,edge('M365 340H150V215H470V172','deny')+label(165,290,'Rejeita:|corrige','deny-label')),400,850);}

function trustFigure(){return figure('Núcleo provado sob premissas. Camadas confiadas: T1 verificadores e vínculo, T2 compiladores e runtime, T3 trabalho físico do host.',
 `<rect class="trust-layer" x="0" y="0" width="1400" height="550" rx="9"/>`+label(28,50,'T3 · Host: estado atual, processos, registro e publicação exata','box-title')+iconAt('server',1322,20,44,'tone-green')+
 `<rect class="trust-layer" x="35" y="105" width="1330" height="415" rx="9"/>`+label(63,155,'T2 · Compilador e runtime: preservação do comportamento','box-title')+iconAt('cpu',1287,125,44,'tone-green')+
 `<rect class="trust-layer" x="70" y="210" width="1260" height="280" rx="9"/>`+label(98,260,'T1 · Verificadores, vínculo exato e auditoria das fontes','box-title')+iconAt('shield-check',1252,230,44,'tone-green')+
 `<rect class="proved-core" x="105" y="315" width="1190" height="145" rx="9"/>`+label(135,360,'Núcleo Bend · propriedades provadas sob premissas','box-title')+iconAt('proof',1217,335,48,'tone-ink')+
 label(135,405,'Admissão exata · leis em cada passo|Finalização válida · terminação lógica'),550);}

function gpuFigure(){return figure('O mesmo programa certificado usa CPU ou CUDA. CUDA mantém as obrigações e amplia T2 com runtime CUDA, NVRTC, driver, memória gerenciada e GPU.',
 box(0,120,475,240,'Programa + prova','Aceito pelos dois|verificadores antes|do código GPU')+iconAt('code',327,140,56,'tone-green')+iconAt('proof',395,140,56,'tone-green')+edge('M475 240H575V90H685')+
 box(685,0,715,180,'Backend CPU','Runtime Bend|Workers CPU')+iconAt('cpu',1320,20,60,'tone-green')+
 step(1,edge('M575 240V370H685')+box(685,270,715,230,'Backend CUDA','Trecho paralelo na GPU|T2 adicional: runtime CUDA, NVRTC,|driver, memória gerenciada e GPU','reject')+iconAt('gpu',1320,290,60,'tone-coral anim-pop'))+
 step(2,label(0,430,'Mesmas obrigações','box-title')+label(0,474,'e mesmo Gate/finalizador verificado')),510);}

function retryFigure(){return figure('Cliente envia pedido. Serviço publica voucher e recibo, mas a resposta se perde. Repetição idêntica e ainda autorizada recebe o resultado retido sem nova emissão.',
 label(40,35,'Cliente','box-title')+label(700,35,'Serviço de vouchers','box-title')+
 `<path class="lifeline" d="M155 65V440M890 65V440"/>`+
 edge('M155 100H890')+label(220,88,'Pedido: ID + entrada')+
 box(1000,80,395,120,'Publicação','Efeito + resultado retido')+`<path class="edge" d="M890 100H1000"/>`+
 step(1,`<path class="edge deny" d="M890 225H440" stroke-dasharray="10 8"/>`+label(465,209,'Resposta perdida','deny-label')+`<path class="lost" d="M420 208L452 240M452 208L420 240"/>`)+
 step(2,edge('M155 320H890')+label(220,304,'Repetição: mesmo ID e entrada')+
 edge('M890 415H155')+label(220,398,'Resultado retido, se ainda autorizado')+label(915,330,'Sem nova emissão','box-title')),460);}

function reuseChart(){
  const x=n=>335+Math.log10(n)*225;
  const rows=[['Chamada ordinária',value('OrdinaryReadMedianSeconds')*1000,pt(value('OrdinaryReadMedianSeconds'))+' s','#dc6e52'],['Preparação, uma vez',value('RegistrationReadVolatileMedianSeconds')*1000,pt(value('RegistrationReadVolatileMedianSeconds'))+' s','#a1b3a6'],['Chamada preparada',value('PreparedReadVolatileMedianMs'),pt(value('PreparedReadVolatileMedianMs'))+' ms','#087869']];
  return `<svg viewBox="0 0 1400 370" role="img" aria-label="Leitura ordinária: ${pt(value('OrdinaryReadMedianSeconds'))} segundos. Preparação única: ${pt(value('RegistrationReadVolatileMedianSeconds'))} segundos. Leitura preparada volátil: ${pt(value('PreparedReadVolatileMedianMs'))} milissegundos. Eixo logarítmico em milissegundos.">${[1,10,100,1000,10000].map(n=>`<line class="gridline" x1="${x(n)}" y1="20" x2="${x(n)}" y2="285"/><text class="tick" x="${x(n)}" y="320" text-anchor="middle">${pt(n,0)}</text>`).join('')}${rows.map(([label,n,labelValue,color],i)=>{const y=53+i*89;return `<text class="series-label" x="0" y="${y+25}">${label}</text><rect class="anim-grow-x" ${delay(.15+i*.2)} x="335" y="${y}" width="${x(n)-335}" height="35" fill="${color}"/><text class="value anim-fade" ${delay(.95+i*.2)} x="${x(n)+18}" y="${y+26}">${labelValue}</text>`;}).join('')}<text class="axis-label" x="790" y="363" text-anchor="middle">Latência (ms) · escala logarítmica</text></svg>`;
}
function sqlChart(){
  const names=['PostgreSQL','SQLite','JayDB2'];const colors=['#9aaea0','#b9c8b5','#087869'];
  const panels=[{title:'Leitura',values:[value('PostgresPointReadMedianMs'),value('SqlitePointReadMedianMs'),value('JayPointReadMedianMs')]},{title:'Atualização durável',values:[value('PostgresPointUpdateMedianMs'),value('SqlitePointUpdateMedianMs'),value('JayPointUpdateMedianMs')]}];
  return `<svg viewBox="0 0 1400 390" role="img" aria-label="Medianas de leitura e atualização em milissegundos para PostgreSQL, SQLite e JayDB2 preparado. ${pt(value('ScalingSmallRows'),0)} linhas, ${pt(value('ComparisonSamples'),0)} amostras por condição. Eixos logarítmicos.">${panels.map((p,j)=>{const offset=j*730;const x=n=>offset+200+(Math.log10(n)+3)*80;return `<text class="chart-title" x="${offset}" y="32">${p.title}</text>${[.001,.01,.1,1,10,100].map(n=>`<line class="gridline" x1="${x(n)}" y1="64" x2="${x(n)}" y2="290"/><text class="tick" x="${x(n)}" y="324" text-anchor="middle">${n<1?String(n).replace('.',','):n}</text>`).join('')}${p.values.map((n,i)=>{const y=92+i*70;return `<text class="series-label" x="${offset}" y="${y+23}">${names[i]}</text><rect x="${offset+200}" y="${y}" height="29" width="${x(n)-offset-200}" fill="${colors[i]}"/><text class="value" x="${x(n)+10}" y="${y+23}">${pt(n,3)}</text>`;}).join('')}<text class="axis-label" x="${offset+385}" y="372" text-anchor="middle">Latência (ms) · escala logarítmica</text>`;}).join('')}</svg>`;
}
function scaleChart(){
  const series=window.JAYDB2_SCALING;const left=95,top=40,w=1170,h=320;const x=n=>left+n/1150*w,y=n=>top+h-n/60*h;
  return `<svg viewBox="0 0 1400 440" role="img" aria-label="Latência cresce com o número total de linhas. Leitura volátil passa de ${pt(value('ScalingSmallVolatileReadMedianMs'))} para ${pt(value('ScalingMaximumVolatileReadMedianMs'))} milissegundos. Atualização durável passa de ${pt(value('ScalingSmallPersistentUpdateMedianMs'))} para ${pt(value('ScalingMaximumPersistentUpdateMedianMs'))} milissegundos.">${[0,10,20,30,40,50,60].map(n=>`<line class="gridline" x1="${left}" y1="${y(n)}" x2="${left+w}" y2="${y(n)}"/><text class="tick" x="${left-18}" y="${y(n)+7}" text-anchor="end">${n}</text>`).join('')}${[10,300,600,1000,1105].map(n=>`<text class="tick" x="${x(n)}" y="395" text-anchor="middle">${pt(n,0)}</text>`).join('')}${series.map((s,i)=>{const color=i?'#c15c42':'#087869';return `<polyline points="${s.points.map(p=>x(p.rows)+','+y(p.median_ms)).join(' ')}" fill="none" stroke="${color}" stroke-width="4" ${i?'stroke-dasharray="10 7"':''}/>${s.points.map(p=>`<line x1="${x(p.rows)}" y1="${y(p.median_ms-p.lower_ms)}" x2="${x(p.rows)}" y2="${y(p.median_ms+p.upper_ms)}" stroke="${color}" stroke-width="2"/>${i?`<rect x="${x(p.rows)-5}" y="${y(p.median_ms)-5}" width="10" height="10" fill="${color}"/>`:`<circle cx="${x(p.rows)}" cy="${y(p.median_ms)}" r="5" fill="${color}"/>`}`).join('')}`;}).join('')}<text class="axis-label" x="660" y="434" text-anchor="middle">Total de linhas</text><text class="axis-label" transform="translate(25 210) rotate(-90)" text-anchor="middle">Latência (ms)</text><line x1="130" y1="23" x2="170" y2="23" stroke="#087869" stroke-width="4"/><text class="legend-label" x="180" y="30">Leitura volátil</text><line x1="440" y1="23" x2="480" y2="23" stroke="#c15c42" stroke-width="4" stroke-dasharray="10 7"/><text class="legend-label" x="490" y="30">Atualização durável</text></svg>`;
}
function simulationTable(){
  const rows=window.JAYDB2_SIMULATION;
  const cell=c=>c.status==='measured'?pt(c.median_ms,3):c.status==='timeout'?`limite ${pt(c.timeout_s,0)} s`:'não executado';
  return `<table class="data-table compute-table"><thead><tr><th>Caminhos × passos</th><th>CPU-1</th><th>CPU-16</th><th>CUDA</th><th>PostgreSQL</th><th>SQLite</th></tr></thead><tbody>${rows.map(r=>`<tr><td>${pt(r.paths,0)} × ${pt(r.steps,0)}</td>${r.cells.map(c=>`<td>${cell(c)}</td>`).join('')}</tr>`).join('')}</tbody></table>`;
}
function simulationChart(){
  const rows=window.JAYDB2_SIMULATION;
  const series=[
    {backend:'cpu-1',name:'CPU-1',color:'#087869',dash:'9 7',width:3,mark:'circle-open'},
    {backend:'cpu-16',name:'CPU-16',color:'#087869',dash:'',width:5,mark:'circle'},
    {backend:'cuda',name:'CUDA',color:'#d0703a',dash:'',width:5,mark:'square'},
    {backend:'postgresql',name:'PostgreSQL',color:'#6b7c76',dash:'',width:3,mark:'diamond'},
    {backend:'sqlite',name:'SQLite',color:'#6b7c76',dash:'12 6',width:3,mark:'triangle'}
  ];
  const left=120,right=1150,top=70,bottom=350,lo=Math.log10(0.03),hi=Math.log10(20000);
  const x=i=>left+70+i*(right-left-140)/(rows.length-1);
  const y=v=>bottom-(Math.log10(v)-lo)/(hi-lo)*(bottom-top);
  const limitMs=1000*Math.max(...rows.flatMap(r=>r.cells.filter(c=>c.status==='timeout').map(c=>c.timeout_s)),10);
  const marker=(m,cx,cy,color,label)=>{const t=`<title>${label}</title>`;
    if(m==='circle')return `<circle cx="${cx}" cy="${cy}" r="8" fill="${color}" stroke="#f4f1e8" stroke-width="2">${t}</circle>`;
    if(m==='circle-open')return `<circle cx="${cx}" cy="${cy}" r="7" fill="#f4f1e8" stroke="${color}" stroke-width="3">${t}</circle>`;
    if(m==='square')return `<rect x="${cx-8}" y="${cy-8}" width="16" height="16" fill="${color}" stroke="#f4f1e8" stroke-width="2">${t}</rect>`;
    if(m==='diamond')return `<path d="M${cx} ${cy-10}L${cx+10} ${cy}L${cx} ${cy+10}L${cx-10} ${cy}Z" fill="${color}" stroke="#f4f1e8" stroke-width="2">${t}</path>`;
    return `<path d="M${cx} ${cy-10}L${cx+10} ${cy+8}L${cx-10} ${cy+8}Z" fill="${color}" stroke="#f4f1e8" stroke-width="2">${t}</path>`;};
  const ticks=[0.1,1,10,100,1000,10000];
  let svg=ticks.map(n=>`<line class="gridline" x1="${left}" y1="${y(n)}" x2="${right}" y2="${y(n)}"/><text class="tick" x="${left-16}" y="${y(n)+7}" text-anchor="end">${n<1?pt(n,1):pt(n,0)}</text>`).join('');
  svg+=`<line x1="${left}" y1="${y(limitMs)}" x2="${right}" y2="${y(limitMs)}" stroke="#b24a32" stroke-width="2" stroke-dasharray="3 6"/><text class="tick" x="${right+14}" y="${y(limitMs)+7}" fill="#b24a32" style="fill:#b24a32">limite ${pt(limitMs/1000,0)} s</text>`;
  svg+=rows.map((r,i)=>`<text class="tick" x="${x(i)}" y="${bottom+36}" text-anchor="middle">${pt(r.paths,0)} × ${pt(r.steps,0)}</text>`).join('');
  const ends=[];
  for(const s of series){
    const pts=rows.map((r,i)=>{const c=r.cells.find(c=>c.backend===s.backend);return {i,c};}).filter(p=>p.c&&p.c.status!=='not run');
    const measured=pts.filter(p=>p.c.status==='measured');
    svg+=`<polyline points="${measured.map(p=>x(p.i)+','+y(p.c.median_ms)).join(' ')}" fill="none" stroke="${s.color}" stroke-width="${s.width}" ${s.dash?`stroke-dasharray="${s.dash}"`:''}/>`;
    const timeout=pts.find(p=>p.c.status==='timeout');
    if(timeout&&measured.length){const last=measured[measured.length-1];
      svg+=`<line x1="${x(last.i)}" y1="${y(last.c.median_ms)}" x2="${x(timeout.i)}" y2="${y(limitMs)}" stroke="${s.color}" stroke-width="2" stroke-opacity=".55" stroke-dasharray="1 7" stroke-linecap="round"/>`;
      const cx=x(timeout.i),cy=y(limitMs);
      svg+=`<path d="M${cx-9} ${cy-9}L${cx+9} ${cy+9}M${cx+9} ${cy-9}L${cx-9} ${cy+9}" stroke="${s.color}" stroke-width="4"><title>${s.name}: limite de ${pt(timeout.c.timeout_s,0)} s</title></path>`;}
    svg+=measured.map(p=>marker(s.mark,x(p.i),y(p.c.median_ms),s.color,`${s.name}, ${pt(rows[p.i].paths,0)} × ${pt(rows[p.i].steps,0)}: ${pt(p.c.median_ms,3)} ms`)).join('');
    if(measured.length&&measured[measured.length-1].i===rows.length-1){const v=measured[measured.length-1].c.median_ms;ends.push({name:s.name,v,yy:y(v)});}
  }
  ends.sort((a,b)=>a.yy-b.yy);
  for(let k=1;k<ends.length;k++)if(ends[k].yy-ends[k-1].yy<30)ends[k].yy=ends[k-1].yy+30;
  svg+=ends.map(e=>`<text class="series-label" x="${right+14}" y="${e.yy+8}">${e.name} · ${pt(e.v,0)} ms</text>`).join('');
  const legend=series.map((s,k)=>{const lx=left+k*205;return `<line x1="${lx}" y1="18" x2="${lx+44}" y2="18" stroke="${s.color}" stroke-width="${s.width}" ${s.dash?`stroke-dasharray="${s.dash}"`:''}/>${marker(s.mark,lx+22,18,s.color,s.name)}<text class="legend-label" x="${lx+56}" y="26">${s.name}</text>`;}).join('');
  const label=rows.map(r=>`${pt(r.paths,0)} × ${pt(r.steps,0)}: `+r.cells.map(c=>`${c.backend} ${c.status==='measured'?pt(c.median_ms,1)+' ms':c.status==='timeout'?'limite':'não executado'}`).join(', ')).join('; ');
  return `<svg viewBox="0 0 1400 430" role="img" aria-label="Medianas de chamadas completas em milissegundos, eixo logarítmico. ${label}.">${legend}${svg}<text class="axis-label" x="${(left+right)/2}" y="${bottom+70}" text-anchor="middle">Caminhos × passos</text><text class="axis-label" transform="translate(30 ${(top+bottom)/2}) rotate(-90)" text-anchor="middle">ms · escala log</text></svg>`;
}
// ── Group 2 helpers ──
// Slide 10 (metodo): one small pictogram per research question, drawn on a 420×140 grid.
function metodoPictogram(n){
  const pic=body=>`<svg class="metodo-pic" viewBox="0 0 420 160" role="presentation" aria-hidden="true">${body}</svg>`;
  if(n===1)return pic(
    iconAt('proof',6,46,68,'tone-green anim-fade-up')+
    `<path class="metodo-link anim-draw" ${delay(.35)} d="M80 80H116M184 80H218"/>`+
    `<g class="anim-pop" ${delay(.55)}><circle class="metodo-seal" cx="150" cy="80" r="33"/></g>`+iconAt('lock',131,61,38,'tone-ink anim-pop')+
    iconAt('code',222,46,68,'tone-green anim-fade-up')+
    `<path class="metodo-flow anim-draw" ${delay(.75)} d="M298 80H334"/><path class="metodo-tip anim-fade" ${delay(1.1)} d="M326 69L338 80L326 91"/>`+
    iconAt('play',344,46,68,'tone-green anim-fade-up'));
  if(n===2)return pic(
    `<path class="metodo-line anim-draw" d="M10 116H296"/>`+
    [34,108,182,256].map((x,i)=>`<g class="anim-pop" ${delay(.25+i*.15)}><circle class="metodo-dot" cx="${x}" cy="116" r="11"/></g>${iconAt('shield-check',x-21,40,42,'tone-green anim-fade-up')}`).join('')+
    `<path class="metodo-flow anim-draw" ${delay(.9)} d="M296 116H310"/>`+
    `<g class="anim-pop" ${delay(1.05)}><rect class="metodo-final" x="312" y="34" width="100" height="100" rx="14"/></g>`+iconAt('database',331,53,62,'tone-ink anim-pop'));
  return pic(
    `<path class="metodo-line" d="M12 142H196"/>`+
    [[26,74],[80,112],[134,50]].map(([x,h],i)=>`<rect class="metodo-bar anim-grow-y" ${delay(.2+i*.15)} x="${x}" y="${140-h}" width="40" height="${h}" rx="4"/>`).join('')+
    iconAt('clock',218,40,76,'tone-green anim-fade-up')+iconAt('gpu',318,38,86,'tone-coral anim-pop'));
}
// Slide 11 (arquitetura): stage card with an icon, a title and short lines; tag adds a trust-layer chip.
const arqCard=(x,y,w,h,name,title,lines,{kind='',tag=''}={})=>
  `<rect class="box ${kind}" x="${x}" y="${y}" width="${w}" height="${h}" rx="10"/>`+
  iconAt(name,x+24,y+22,44,'tone-green')+
  label(x+82,y+56,title,'box-title')+(lines?label(x+24,y+104,lines):'')+
  (tag?`<rect class="arq-chip" x="${x+w-78}" y="${y+18}" width="60" height="38" rx="19"/><text class="arq-chip-text" x="${x+w-48}" y="${y+46}" text-anchor="middle">${tag}</text>`:'');
function arquiteturaFigure(){return figure('Admissão: Node prepara o Book com programa e prova; Bend e BendTT verificam o mesmo Book; a compilação nativa transforma esse Book em executável, e selos e hashes ligam o executável ao Book verificado (T1). Execução a cada chamada: o worker Bend verificado autentica, interpreta e finaliza; o host Rust executa a decisão Commit ou Keep sobre o estado publicado.',
 label(0,26,'ADMISSÃO · PROGRAMA + PROVA DO CLIENTE','arq-lane')+
 `<g class="anim-fade-up">${arqCard(0,44,420,160,'terminal','Node prepara','stage.mjs monta o Book|com programa e prova')}</g>`+
 `<path class="edge anim-draw" ${delay(.3)} d="M420 124H482" marker-end="url(#flow-tip)"/>`+
 `<g class="anim-fade-up" ${delay(.45)}>${arqCard(490,44,420,160,'shield-check','Bend + BendTT','dois verificadores|checam o mesmo Book')}</g>`+
 step(1,`<path class="edge anim-draw" d="M910 124H972" marker-end="url(#flow-tip)"/>`+
  `<g class="anim-fade-up" ${delay(.2)}>${arqCard(980,44,420,160,'cpu','Compilação','o mesmo Book vira|C e executável (Clang)',{tag:'T2'})}</g>`+
  `<g class="anim-fade-up" ${delay(.6)}><path class="arq-bind-link" d="M700 204V224M1190 204V224"/><rect class="arq-bind" x="490" y="224" width="910" height="66" rx="10"/>`+
  `<text class="arq-bind-text" x="566" y="267">Selos e hashes ligam o executável ao Book verificado</text>`+
  `<rect class="arq-chip" x="1322" y="238" width="60" height="38" rx="19"/><text class="arq-chip-text" x="1352" y="266" text-anchor="middle">T1</text></g>`+
  iconAt('lock',512,237,40,'tone-ink anim-pop'))+
 step(2,`<path class="edge anim-draw" d="M600 290V334" marker-end="url(#flow-tip)"/>`+label(624,322,'executável liberado','edge-label anim-fade')+
  label(0,322,'EXECUÇÃO · CADA CHAMADA','arq-lane anim-fade')+
  `<g class="anim-fade-up" ${delay(.25)}>${arqCard(0,342,620,206,'gear','Worker Bend verificado','',{kind:'accept'})}`+
  [['Gate','autentica e inicia o programa'],['Interpretador','executa cada ação'],['Finalizador','decide Commit ou Keep']].map(([t,d],i)=>
   `<text class="arq-part" x="24" y="${442+i*40}"><tspan class="arq-part-name">${t}</tspan><tspan dx="12">${d}</tspan></text>`).join('')+`</g>`)+
 step(3,`<path class="edge anim-draw" d="M620 445H682" marker-end="url(#flow-tip)"/>`+
  `<g class="anim-fade-up" ${delay(.2)}>${arqCard(690,342,340,206,'server','Host Rust','executa a decisão|Commit: publica|Keep: preserva',{tag:'T3'})}</g>`+
  `<path class="edge anim-draw" ${delay(.5)} d="M1030 445H1092" marker-end="url(#flow-tip)"/>`+
  `<g class="anim-fade-up" ${delay(.65)}>${arqCard(1100,342,300,206,'database','Estado','publicado; base|da próxima chamada')}</g>`),556);}
// Slide 13 (aplicacoes): one card per application.
function aplicacaoCard([name,iconName,what,access,publish,invalid],i){
  return `<section class="aplic-card anim-fade-up" ${delay(.1+i*.15)}><header>${badge(iconName,{size:58,tone:'mint'})}<div><h3>${name}</h3><p class="aplic-what">${what}</p></div></header>`+
  `<div class="aplic-rules"><div><p class="aplic-label">${icon('shield-check',{size:26,cls:'tone-green'})}Em cada acesso</p><p>${access}</p></div><div><p class="aplic-label">${icon('database',{size:26,cls:'tone-green'})}Ao publicar</p><p>${publish}</p></div></div>`+
  `<p class="aplic-invalid">${icon('x',{size:26,cls:'tone-coral'})}<span><strong>Rejeitada:</strong> ${invalid}</span></p></section>`;
}
// Slide 14 (evidencia): three complementary kinds of correctness evidence.
const evidenciaStat=(n,text)=>`<div class="evid-stat"><span class="evid-number">${pt(n,0)}</span><span class="evid-stat-label">${text}</span></div>`;
const evidenciaCheck=text=>`<li>${icon('check',{size:26,cls:'tone-green'})}${text}</li>`;
function evidenciaCard(step,{iconName,tone,title,question,text,body,checker,checkerIcon}){
  return `<section class="evid-card${step?' fragment':''}" ${step?`data-step="${step}"`:''}><div class="anim-fade-up">${badge(iconName,{size:70,tone})}<h3>${title}</h3><p class="evid-question">${question}</p><p class="evid-text">${text}</p></div><div class="evid-body anim-fade-up" ${delay(.25)}>${body}</div><p class="evid-checker">${icon(checkerIcon,{size:28,cls:'tone-muted'})}${checker}</p></section>`;
}
const slides=[
{
 id:'inicio',title:'JayDB2',theme:'dark cover',seconds:25,
 html:`<p class="kicker">Ciência da Computação · PUC Minas</p><h1>JayDB2</h1><p class="cover-subtitle">Um banco de dados<br>que verifica provas<br>antes de executar programas</p><div class="cover-authors">Gabriel Jota Lizardo<br><span class="cover-author-label">Orientador<br>Gabriel Barbosa da Fonseca</span></div>`,
 bottom:'Banco de dados experimental',
 notes:`O JayDB2 é um banco de dados experimental. O cliente envia um programa e uma prova de que ele segue as regras do administrador. O banco verifica essa prova antes da execução. Vou apresentar o problema, acompanhar um pedido simples e mostrar o que foi construído, verificado e medido. Essa proposta se liga ao uso de LLMs para produzir código e provas.`,
 sources:[sources.artifact]
},
{
 id:'contexto',title:'Quem confere o que um programa faz com os dados?',seconds:35,
 html:`<p class="kicker">Motivação</p><h2>Quem confere o que um programa<br>faz com os dados?</h2><div class="motivation"><section class="incident"><p class="small muted">DINAMARCA · 5 OUT 2026</p><h3>Acesso indevido ao registro CPR</h3><p>Dados de cerca de 8,8 milhões<br>de pessoas foram acessados.</p><p class="small">O invasor usou o acesso legítimo<br>de uma empresa.</p></section><section class="fragment" data-step="1"><p class="small muted">IA · ACESSO A DADOS</p><h3>Programas gerados por IA</h3><p>Assistentes de IA são usados para escrever código que lê e altera dados.</p><p class="small spaced">Isso motiva verificar as operações permitidas e as regras de integridade antes da execução.</p></section></div>`,
 bottom:'Fonte: comunicado oficial do CPR. O caso motiva a pergunta; não demonstra prevenção pelo protótipo.',
 notes:`O comunicado oficial do CPR relata acesso indevido a dados de aproximadamente oito milhões e oitocentas mil pessoas por meio do acesso legítimo de uma empresa. Esse incidente motiva distinguir autenticação e comportamento permitido. Em outro contexto, assistentes de IA são usados para escrever programas que acessam dados. O trabalho investiga uma interface que exige um certificado verificável antes de executar esses programas. O caso CPR é uma motivação, sem demonstração de que o protótipo impediria o ataque.`,
 sources:[sources.cpr]
},
{
 id:'o-que-e',title:'O que é o JayDB2',seconds:45,
 html:`<p class="kicker">A ideia</p><h2>O que é o JayDB2</h2><p class="small diagram-intro">O cliente demonstra que seu programa respeita as leis instaladas pelo administrador.</p>${admissionFigure()}`,
 bottom:'Programa e certificado entram juntos na admissão',
 notes:'Há três papéis. O administrador decide como os dados são organizados e quais regras a aplicação exige. O cliente escreve um programa para realizar sua operação e entrega uma prova. O JayDB2 confere se a prova tem o tipo exigido e se está ligada ao programa exato. Se a admissão aceita, o banco executa o programa em um estado de trabalho privado. Uma conclusão bem-sucedida pode publicar o resultado completo. Outros resultados preservam o estado anterior. A prova é uma estrutura formal que um verificador consegue checar. Ela não é uma explicação em linguagem natural nem uma aprovação feita pelo próprio modelo que escreveu o programa.',
 sources:[sources.laws,sources.artifact]
},
{
 id:'pedido',title:'Um pedido comum',seconds:30,
 html:`<p class="kicker">Exemplo: notas compartilhadas</p><h2>Um pedido comum</h2><div class="request-layout"><section><div class="request">Salve uma nota para mim<br>e inclua essa nota<br>na minha lista.</div><div class="ledger"><div class="ledger-line"><span class="owner">Alice</span><code>alice/n1</code></div><div class="ledger-line"><span>Diretório de Alice</span><span>inclui n1</span></div><div class="ledger-line"><span class="owner bob">Bob</span><code>bob/n7</code></div><div class="ledger-line"><span>Dados de Bob</span><span>fora do pedido</span></div></div></section><figure class="illustration"><img src="assets/notes-collections.webp" alt="Ilustração conceitual: notas de dois donos no mesmo recipiente, cada grupo com sua própria ficha de índice."/><figcaption>Uma tabela de notas compartilhada.<br>Um diretório por usuário.</figcaption></figure></div>`,
 bottom:'Pedido e resultado pretendido são ilustrativos. A interface recebe programa e certificado em Bend.',
 notes:`Alice quer salvar uma nota e encontrá-la em seu diretório. A ilustração agrupa as notas por dono dentro de um recipiente compartilhado: no sistema, há uma única tabela de notas e um diretório separado por usuário. Bob também tem notas nessa tabela; seus dados ficam fora do pedido de Alice. O programa deve respeitar o acesso e atualizar nota e diretório antes da publicação. Os identificadores n1 e n7 são ilustrativos. A interface implementada recebe programa e certificado em Bend.`,
 sources:[sources.rls]
},
{
 id:'leis',title:'As regras da aplicação',seconds:30,
 html:`<p class="kicker">O que o administrador exige</p><h2>As regras da aplicação</h2><div class="law-layout"><section><h3>Propriedade</h3><p class="small">A chave de escrita pertence<br>ao usuário autenticado.</p><figure class="code-figure"><img src="assets/write-scope.svg" alt="Trecho literal de Policy.bend: WriteScope exige que key_owner(key) seja id e key_valid(key) seja True."/><figcaption>Trecho literal · applications/rls/Policy.bend</figcaption></figure></section><section class="law-explanation"><h3>Dono da nota</h3><p>A criação usa a identidade<br>autenticada. A atualização<br>preserva o dono.</p><h3>Diretório exato</h3><p>Lista todas as notas do dono<br>e nenhuma de outra pessoa.</p></section></div>`,
 bottom:'A aplicação também define um administrador com leitura ampliada e sem exceção de escrita.',
 notes:`Estas são as regras da aplicação. Cada chave está ligada à identidade atual. O trecho mostra WriteScope: o dono da chave deve ser o id autenticado e a chave deve ser válida. Na criação, o dono gravado deve ser o usuário autenticado. Uma atualização preserva esse dono. O diretório deve listar todas as notas dele e nenhuma de outra pessoa. O administrador pode fazer leituras ampliadas, mas não recebe exceção de escrita. Essas obrigações foram formalizadas e entram no certificado. Os controles negativos tentam quebrar cada uma delas para conferir a rejeição.`,
 sources:[sources.rls]
},
{
 id:'transacao',title:'Uma mudança privada, um resultado completo',seconds:55,
 html:`<p class="kicker">Como a transação funciona</p><h2>Uma mudança privada,<br>um resultado completo</h2>${transactionFigure()}<p class="small diagram-note">Cada acesso precisa ser permitido. A consistência do diretório vale na publicação.</p>`,
 bottom:'A regra de diretório exato vale nos estados publicados; a proposta pode ficar incompleta durante a operação.',
 notes:'A ordem das escritas importa para a explicação. Antes do pedido, não há nota e o diretório está vazio. O programa cria a nota em sua proposta privada. Nesse instante, o diretório ainda não foi atualizado. Isso é permitido como situação intermediária. O programa então acrescenta a entrada correta e conclui. A lei exige que a correspondência seja exata quando o novo estado é publicado. O certificado estabelece essa propriedade sobre o caminho real do programa. Se o programa recusa, a proposta não substitui o estado publicado. E a regra de acesso continua valendo durante todo o processo: uma operação privada não ganha permissão para ler Bob.',
 sources:[sources.rls,sources.laws]
},
{
 id:'rejeicoes',title:'Dois erros, duas obrigações',seconds:45,
 html:`<p class="kicker">Controles negativos executados</p><h2>Dois erros, duas obrigações</h2><div class="rejection-layout"><section>${rejectionFigure()}</section><figure class="terminal-figure fragment" data-step="2"><img src="assets/checker-rejection.svg" alt="Saída real de Bend: SOME PROOFS FAIL, expected bob, observed alice, Location false."/><figcaption>Controle <code>read-bob</code>: chave real <code>bob/00000001</code>;<br><code>bob/n7</code> é ilustrativo. Trecho literal; … indica linhas omitidas.<br>Capturado por <code>capture_checker_figures.py</code>.</figcaption></figure></div>`,
 bottom:`Aplicação de notas: ${pt(value('RlsNegativeFixtures'),0)} negativos causais e ${pt(value('RlsNativeResponses'),0)} respostas nativas conferidas.`,
 notes:`Os dois diagramas representam obrigações independentes: ler Bob viola a permissão; criar sem atualizar o diretório viola a consistência final. À direita há a saída real do verificador. O controle read-bob usa a chave concreta bob/00000001, que é o caso correspondente ao identificador ilustrativo bob/n7. O verificador esperava bob e encontrou alice na prova de permissão. Os controles read-bob e create-without-directory foram executados em Bend e BendTT, com falha somente em false. A figura mostra apenas o diagnóstico inicial do primeiro controle; a elipse marca o contexto omitido. Os logs completos e o comando de reprodução estão nos artefatos da apresentação.`,
 sources:[sources.rls,source('Diagnóstico real: read-bob','paper/presentation/assets/read-bob-check-only.txt')]
},
{
 id:'prova',title:'O que a prova acrescenta',seconds:45,
 html:`<p class="kicker">Garantia sobre o programa</p><h2>O que a prova acrescenta</h2><div class="split"><section><h3>Um teste</h3><p class="spaced">Executa um caso escolhido<br>e confere seu resultado.</p><p class="small muted spaced">Exemplo: Alice cria n1<br>com um estado inicial específico.</p></section><section><h3>Um certificado</h3><p class="spaced">Estabelece as leis para todos<br>os estados válidos cobertos<br>e todos os caminhos do programa.</p><p class="small muted spaced">Inclui resultados ausentes,<br>recusas e passos intermediários.</p></section></div><p class="foot-message">A terminação é uma obrigação adicional. A garantia vale sob as premissas declaradas.</p>`,
 bottom:'O certificado fala da execução real do interpretador e das leis instaladas.',
 notes:'Testes e provas respondem a perguntas diferentes e ambos aparecem na avaliação. Um teste executa uma situação concreta e confere a resposta e o estado. O certificado quantifica sobre todos os estados iniciais válidos compatíveis com seu alvo e sobre as continuações reais das operações. Se uma leitura pode retornar uma linha ou indicar ausência, a prova precisa cobrir os dois casos. Uma prova de terminação fornece um caminho final finito. Isso não significa uma garantia de prazo físico. O conjunto de propriedades também depende da definição das leis e das premissas do verificador, compilador e host, que vou explicitar adiante.',
 sources:[sources.laws,sources.proofs]
},
{
 id:'llms',title:'Onde os LLMs entram',seconds:50,
 html:`<p class="kicker">Autoria assistida por IA</p><h2>Onde os LLMs entram</h2><div class="llm-layout"><section>${llmFigure()}<ul class="llms-points"><li class="anim-fade-up" ${delay(.2)}>${icon('warning',{size:40,cls:'tone-coral'})}<span>Código gerado pode parecer correto e estar errado.</span></li><li class="fragment" data-step="1">${icon('shield-check',{size:40,cls:'tone-green'})}<span>Confia-se nas leis e no verificador, não no modelo.</span></li><li class="fragment" data-step="2">${icon('refresh',{size:40,cls:'tone-coral'})}<span>Prova rejeitada: o gerador corrige e tenta de novo.</span></li></ul></section><figure class="illustration"><img src="assets/program-proof-generator.webp" alt="Ilustração conceitual: gerador produz programa e certificado em folhas separadas diante de um portal de verificação independente."/><figcaption>O gerador produz os artefatos.<br>O banco verifica a prova.</figcaption></figure></div>`,
 bottom:`Geração de provas por LLMs: Baldur (Isabelle/HOL), Misu et al. (Dafny), AutoVerus (Verus). O JayDB2 trata do lado que recebe as provas.`,
 notes:'LLMs e agentes já escrevem código que lê e altera dados, e esse código pode parecer correto e estar errado. Revisar cada programa gerado à mão não acompanha esse volume. No JayDB2 o fluxo é outro. O usuário expressa uma intenção, e o LLM, com bibliotecas de provas, produz o programa e a prova. [→] O verificador do banco confere essa prova contra as leis instaladas. A resposta é sim ou não e não depende da explicação do modelo: o que continua confiável são as leis escritas pelo administrador e o próprio verificador, que é a camada T1. O gerador fica fora da base de confiança. [→] Se a prova não passa, o gerador recebe a rejeição, corrige e tenta de novo; nada é executado nesse meio-tempo. Há trabalhos recentes que estudam a geração em si: o Baldur gera e repara provas em Isabelle, Misu e colegas sintetizam métodos Dafny verificados, e o AutoVerus gera provas para código Rust verificado pelo Verus. Eles medem com que frequência a geração dá certo. O JayDB2 trata do lado complementar, o banco que recebe esses artefatos e só os executa se a prova passar. O uso de LLMs na construção deste trabalho aparece na declaração de IA, no fim.',
 sources:[sources.ai,sources.baldur,sources.misu,sources.autoverus]
},
{
 id:'metodo',title:'Como o trabalho foi avaliado',seconds:40,
 html:`<p class="kicker">Problema de pesquisa e método</p><h2>Como o trabalho foi avaliado</h2><div class="metodo-grid"><section class="metodo-card">${metodoPictogram(1)}<p class="metodo-n">RQ1</p><h3>Ligar a prova ao programa que executa</h3><p>Especificação e teoremas sobre as funções executáveis.</p></section><section class="metodo-card fragment" data-step="1">${metodoPictogram(2)}<p class="metodo-n">RQ2</p><h3>Combinar acesso e consistência</h3><p>Aplicações certificadas e variantes inválidas direcionadas.</p></section><section class="metodo-card fragment" data-step="2">${metodoPictogram(3)}<p class="metodo-n">RQ3</p><h3>Medir custo, reuso e CUDA</h3><p>Experimentos nativos com resultados e estados conferidos.</p></section></div>`,
 bottom:'Objetivo geral: implementar e avaliar o serviço, com ligação explícita entre certificado, execução e publicação.',
 notes:'A pesquisa organiza a construção em três perguntas. A primeira trata da conexão entre o certificado aceito e o programa que de fato executa: a prova fica selada ao código. Ela é respondida com uma especificação e com teoremas sobre as próprias funções executáveis do banco. [→] A segunda testa se as leis conseguem combinar permissão em cada acesso com consistência no momento da publicação. Para isso construí aplicações certificadas e variantes inválidas, cada uma feita para quebrar uma obrigação específica. [→] A terceira mede o custo real do protótipo, o efeito da preparação, que permite reutilizar uma prova, e o da execução opcional em CUDA. Todos os números que vou mostrar vêm dos experimentos retidos no repositório, com as respostas e os estados conferidos.',
 sources:[sources.evidence,sources.proofs]
},
{
 id:'arquitetura',title:'Da prova ao código executado',seconds:55,
 html:`<p class="kicker">Arquitetura</p><h2>Da prova ao código executado</h2>${arquiteturaFigure()}`,
 bottom:'Bend 2.0.39 / BendTT · Rust 1.98.0 · Node 24.19.0 · Clang 19.1.1',
 notes:`O diagrama tem duas faixas: a admissão, que acontece antes de qualquer execução, e a execução de cada chamada. Na admissão, o cliente entrega programa e prova. O Node, pelo stage.mjs, monta com eles o Book, o conjunto de definições Bend que será verificado. Os dois verificadores oficiais, Bend e BendTT, conferem as obrigações sobre esse mesmo Book, e os dois precisam aceitar. [→] O mesmo Book é compilado para C e depois para um executável nativo; essa compilação é confiada, faz parte de T2. O ponto central é o vínculo: um selo confere o Book antes da emissão do C, outro confere o resultado depois, e hashes ligam o executável às fontes verificadas. Nenhum artefato é liberado antes das duas aceitações e dessas conferências. É por isso que a prova fala do código exato que vai rodar; esse vínculo está em T1. O diagrama mostra dependências lógicas; na CPU, parte da compilação pode se sobrepor à segunda verificação. [→] A cada chamada roda um worker nativo cujas funções são escritas em Bend e verificadas: o Gate autentica o cliente sobre o estado atual e inicia exatamente o programa admitido, o interpretador executa cada ação, e o finalizador decide entre Commit e Keep. [→] O host Rust só executa essa decisão: em Commit, publica o estado e a resposta selecionados; em Keep, preserva o estado anterior. Essa parte física é a camada T3. A próxima chamada parte do estado publicado, e as transações seguem uma fila serial.`,
 sources:[sources.proofs,sources.evidence,sources.gpu]
},
{
 id:'garantias',title:'O alcance das garantias',theme:'dark',seconds:50,
 html:`<p class="kicker">Base de confiança explícita</p><h2>O alcance das garantias</h2>${trustFigure()}<p class="small diagram-note">Camadas de dependência. Configuração e estado inicial válidos são premissas.</p>`,
 bottom:'Durabilidade após falhas, recuperação geral e isolamento concorrente não estão provados.',
 notes:'Os resultados centrais estabelecem a identidade e o início do programa exato, as leis em cada prefixo real, a finalização com estado e resposta corretos e a existência de uma execução lógica finita. Há premissas. T1 reúne correção dos verificadores e vínculo exato dos artefatos. T2 trata do compilador e do runtime. T3 reúne as tarefas físicas do host, como fornecer o estado atual, executar o artefato admitido e publicar a decisão selecionada. A validade do estado inicial é uma premissa. Assim a banca consegue localizar o que tem prova no nível Bend e onde ainda confiamos na infraestrutura. Durabilidade geral e concorrência não fazem parte desses teoremas.',
 sources:[sources.proofs]
},
{
 id:'aplicacoes',title:'A mesma interface em quatro aplicações',seconds:50,
 html:`<p class="kicker">Aplicações certificadas</p><h2>A mesma interface em quatro aplicações</h2><div class="aplic-grid">${[
  ['Disponibilidade','table','Item livre ou ocupado, com índice por usuário','Só as próprias tabelas e índices','Índice corresponde à linha principal','ler o índice de Bob; omitir o índice'],
  ['Vouchers','refresh','Emissão com recibo: repetir o pedido é seguro','Permissão atual e protocolo de recibos','Voucher e recibo consistentes','quebrar o par voucher–recibo'],
  ['Notas','news','Tabela compartilhada e um diretório por usuário','Namespace próprio; dono preservado','Diretório lista exatamente as notas','ler nota alheia; forjar dono; omitir entrada'],
  ['Simulação','chart-line','Cálculo pesado, em CPU ou CUDA','Só o próprio cenário e o próprio resultado','Resultado válido; terminação provada','ler cenário ou gravar resultado alheio']
 ].map(aplicacaoCard).join('')}</div>`,
 bottom:'Todas usam o mesmo protocolo: programa, certificado, credencial e argumentos. Cada variante inválida é rejeitada antes da execução.',
 notes:'As quatro aplicações usam a mesma interface: programa, certificado, credencial e argumentos. Cada cartão mostra a regra que vale em cada acesso, a regra que vale na publicação e um exemplo de variante inválida. Disponibilidade: cada usuário marca seu item como livre ou ocupado e mantém uma tabela comum que funciona como índice; durante a operação só toca as próprias tabelas, e ao publicar o índice precisa corresponder à linha principal. Vouchers: um identificador de pedido fica ligado à entrada exata e ao resultado guardado, para que repetir o mesmo pedido devolva o resultado sem nova emissão; voucher e recibo precisam sair juntos e consistentes. Notas é o exemplo que acompanhamos: tabela compartilhada, diretório por usuário, dono preservado, e o diretório lista exatamente as notas. A simulação é o caso de cálculo pesado: lê o cenário do próprio usuário, escreve só o próprio resultado, tem prova de terminação e pode usar CUDA. Em todas, as variantes inválidas, como ler o índice de Bob ou omitir a entrada no diretório, são rejeitadas na obrigação que quebram, antes de executar.',
 sources:[sources.rls,sources.voucher,source('Disponibilidade e índices','applications/indexed/README.md'),sources.simulation]
},
{
 id:'evidencia',title:'Como a correção foi conferida',seconds:40,
 html:`<p class="kicker">Evidências de correção</p><h2>Como a correção foi conferida</h2><div class="evid-grid">${
  evidenciaCard(0,{iconName:'proof',tone:'green',title:'Teoremas',question:'O que vale para todos os casos',text:'Provas sobre as funções executáveis: Gate, interpretador e finalizador.',
   body:`<ul class="evid-checks">${['Admissão exata','Leis em cada passo','Finalização correta','Execução finita'].map(evidenciaCheck).join('')}</ul>`,checker:'Bend e BendTT',checkerIcon:'shield-check'})+
  evidenciaCard(1,{iconName:'x',tone:'coral',title:'Controles negativos',question:'O que precisa ser recusado',text:'Variantes inválidas devem falhar na obrigação esperada, nos dois verificadores.',
   body:`<div class="evid-stats">${evidenciaStat(value('NegativeFixtures'),'variantes<br>do núcleo')}${evidenciaStat(value('RlsNegativeFixtures'),'variantes<br>de notas')}</div>`,checker:'Bend e BendTT',checkerIcon:'shield-check'})+
  evidenciaCard(2,{iconName:'play',tone:'ink',title:'Sessões nativas',question:'O que o serviço real faz',text:'O serviço real recebe pedidos; respostas e estados completos são conferidos.',
   body:`<div class="evid-stats">${evidenciaStat(value('RlsNativeResponses'),'respostas na<br>sessão de notas')}</div><ul class="evid-checks">${evidenciaCheck('Estado inalterado após cada rejeição')}</ul>`,checker:'Serviço nativo em Rust',checkerIcon:'server'})
 }</div>`,
 bottom:'Contadores de evidências diferentes, não um total de testes. Execuções retidas com sucesso: make verify-contract, make verify e make test.',
 notes:`A correção foi conferida por três tipos de evidência, que se complementam. Primeiro, os teoremas: são provas sobre as próprias funções executáveis do banco, o Gate, o interpretador e o finalizador, e não sobre um modelo separado. Elas estabelecem admissão do programa exato, leis em cada passo, finalização correta e execução finita, para todos os estados válidos, sob as premissas T1 a T3. Bend e BendTT conferem essas provas. [→] Segundo, os controles negativos. Uma prova pode ser verdadeira e ainda assim fraca demais; por isso cada variante inválida precisa falhar exatamente na obrigação esperada, nos dois verificadores. São ${pt(value('NegativeFixtures'),0)} variantes do núcleo e ${pt(value('RlsNegativeFixtures'),0)} da aplicação de notas. Os negativos de GPU e de simulação também falham nas mesmas obrigações, antes da compilação. [→] Terceiro, as sessões nativas: o serviço real, com o host Rust, recebe pedidos e cada resposta e estado são conferidos. A sessão de notas confere ${pt(value('RlsNativeResponses'),0)} respostas, e depois de cada rejeição confere que o estado completo ficou inalterado. Esses contadores medem coisas diferentes e não somam um total de testes. Os comandos make verify-contract, make verify e make test foram executados com sucesso e seus registros estão no repositório.`,
 sources:[sources.evidence,sources.proofs,sources.rls]
},
{
 id:'reuso',title:'A prova pode ser reutilizada',seconds:45,
 html:`<p class="kicker">E1–E2 · leitura</p><h2>A prova pode ser reutilizada</h2><div class="chart-area" style="height:370px">${reuseChart()}</div><p class="small spaced">Preparar verifica e compila uma vez. Cada chamada reutiliza o programa<br>com credencial e argumentos atuais.</p><p class="small accent" style="margin-top:17px"><strong>${pt(value('BreakEvenReadCalls'),0)} chamadas</strong> para amortizar a preparação no modelo de medianas.</p>`,
 bottom:`E1: n=${pt(value('OrdinarySamples'),0)}. E2 volátil: n=${pt(value('PreparedSamples'),0)} chamadas e ${pt(value('RegistrationSamples'),0)} preparações. Perfis de compilação diferentes; escala logarítmica.`,
 notes:`A leitura ordinária custa ${pt(value('OrdinaryReadMedianSeconds'))} segundos porque repete a admissão. Um certificado universal permite preparar uma vez por ${pt(value('RegistrationReadVolatileMedianSeconds'))} segundos e reutilizar o programa com novas credenciais e argumentos. A leitura preparada volátil custa ${pt(value('PreparedReadVolatileMedianMs'))} milissegundos e autentica novamente. O gráfico é logarítmico. O modelo de medianas estima amortização em ${pt(value('BreakEvenReadCalls'),0)} chamadas. Os perfis de compilação diferem; medimos os caminhos completos, sem isolar apenas a retirada da checagem.`,
 sources:[sources.evidence,sources.prepared]
},
{
 id:'sql',title:'O protótipo ainda custa mais que SQL',seconds:45,
 html:`<p class="kicker">E3 · ${pt(value('ScalingSmallRows'),0)} linhas · operações pontuais</p><h2>O protótipo ainda custa<br>mais que SQL</h2><div class="chart-area" style="height:390px">${sqlChart()}</div><p class="small spaced">A leitura preparada custa cerca de <strong>${pt(value('JayPointReadOverPostgres'),0)} vezes</strong> a leitura no PostgreSQL.<br>O reuso remove a checagem, mas mantém custos do caminho de execução.</p>`,
 bottom:`Medianas em ms. n=${pt(value('ComparisonSamples'),0)} por operação/sistema/condição. JayDB2 preparado durável. SQLite sem propriedade.`,
 notes:`Com ${pt(value('ScalingSmallRows'),0)} linhas, a leitura PostgreSQL custa ${pt(value('PostgresPointReadMedianMs'),3)} milissegundos; JayDB2 preparado durável custa ${pt(value('JayPointReadMedianMs'),3)}, cerca de ${pt(value('JayPointReadOverPostgres'),0)} vezes mais. Atualizações também são mais lentas. Os sistemas usam configurações duráveis descritas no artigo. SQLite não impõe propriedade. As fronteiras incluem drivers e respostas diferentes. Preparação melhora o caminho JayDB2, mas o protótipo ainda tem custo elevado diante de bancos convencionais.`,
 sources:[sources.evidence]
},
{
 id:'escala',title:'O estado completo limita a escala',seconds:50,
 html:`<p class="kicker">E5 · crescimento da população</p><h2>O estado completo limita a escala</h2><div class="chart-area" style="height:440px;margin-top:25px">${scaleChart()}</div><p class="small" style="margin-top:12px">O teto configurado de <strong>${pt(value('StateLimitBytes'),0)} bytes</strong> comporta ${pt(value('StateMaximumRows'),0)} linhas deste formato.<br>A próxima linha excede o limite e o banco preserva o estado anterior.</p>`,
 bottom:`${pt(value('ScalingSessionCount'),0)} sessão, ${pt(value('ScalingSamples'),0)} amostras por ponto/operação/modo. Medianas e intervalo interquartil. Linhas conectam medidas.`,
 notes:`A leitura volátil cresce de ${pt(value('ScalingSmallVolatileReadMedianMs'))} para ${pt(value('ScalingMaximumVolatileReadMedianMs'))} milissegundos. A atualização durável chega a ${pt(value('ScalingMaximumPersistentUpdateMedianMs'))}. Ler a primeira chave tem custo semelhante a ler a última, consistente com trabalho sobre o estado completo dominando o crescimento. Isso não isola cada mecanismo. O teto de ${pt(value('StateLimitBytes'),0)} bytes admite ${pt(value('StateMaximumRows'),0)} linhas deste formato; a seguinte é recusada com estado preservado. São os limites do protótipo e da configuração medidos.`,
 sources:[sources.evidence]
},
{
 id:'gpu',title:'Execução GPU opcional',seconds:50,
 html:`<p class="kicker">Backends de execução</p><h2>Execução GPU opcional</h2><p class="small diagram-intro">A simulação usa caminhadas aleatórias inteiras. O autor marca o trecho paralelo.</p>${gpuFigure()}<p class="small diagram-note">Autenticação e controle seguem na CPU. Uma falha na GPU descarta a proposta.</p>`,
 bottom:'Resultados numéricos conferidos com oráculos Python/NumPy: evidência de teste, não prova.',
 notes:'Para avaliar um caso de cálculo pesado, a quarta aplicação simula muitas caminhadas aleatórias inteiras. O autor marca o trecho paralelo do programa e, se o administrador ativar a GPU, o Bend executa esse trecho em CUDA. Autenticação e controle da transação continuam na CPU. A admissão é a mesma: os dois verificadores aceitam o programa antes de qualquer código GPU ser gerado. As obrigações também são as mesmas, e as variantes que leem o cenário de outro usuário falham antes da compilação. Se o artefato muda ou a GPU falha, a proposta é descartada, sem recorrer silenciosamente à CPU. O preço é uma base de confiança maior: o runtime CUDA, o driver e o hardware entram em T2. A correção numérica é conferida por testes, não provada.',
 sources:[sources.gpu,sources.simulation,source('Evidência GPU','paper/evidence/gpu-programs.md')]
},
{
 id:'simulacao',title:'E6: quando a GPU compensa',seconds:55,
 html:`<p class="kicker">E6 · simulação certificada · chamadas completas</p><h2>Quando a GPU compensa</h2><div class="chart-area" style="height:430px;margin-top:22px">${simulationChart()}</div><div class="takeaways"><section><strong>CUDA: ~${pt(value('SimulationSmallCudaMs'),0)} ms já na menor</strong>Iniciar processo e GPU<br>domina as chamadas pequenas.</section><section><strong>Só na maior carga</strong>CUDA ${pt(value('SimulationLargeCudaMs'),0)} ms<br>contra CPU-16 ${pt(value('SimulationLargeCpuSixteenMs'),0)} ms.</section><section><strong>SQL na menor carga</strong>Mais rápido no início; esgota<br>o limite de 10 s nas maiores.</section></div>`,
 bottom:`Objetivo: obrigações preservadas em CUDA e onde a GPU compensa, não “JayDB2 é mais rápido”. Detalhes no apêndice.`,
 notes:`O objetivo do E6 não é mostrar que o JayDB2 é mais rápido. É mostrar que as obrigações continuam valendo no backend CUDA e onde a GPU passa a compensar. O eixo vertical é logarítmico e cada ponto é uma chamada completa. Primeiro: CUDA custa cerca de ${pt(value('SimulationSmallCudaMs'),0)} milissegundos mesmo na menor carga, porque cada pedido inicia um processo e a GPU; isso domina as chamadas pequenas. Segundo: só na maior carga a GPU vence a CPU com dezesseis workers, ${pt(value('SimulationLargeCudaMs'))} contra ${pt(value('SimulationLargeCpuSixteenMs'))} milissegundos. Terceiro: os bancos SQL são os mais rápidos na menor carga, mas PL/pgSQL e a consulta recursiva do SQLite crescem muito mais e esgotam o limite de dez segundos; isso reflete estratégias inadequadas para cálculo numérico, não o desempenho geral desses bancos. Há uma sessão e ${pt(value('SimulationRepeats'),0)} amostras por célula, com a GPU sem clock fixo; por isso só diferenças grandes têm significado. A tabela completa está no apêndice.`,
 sources:[sources.simulation,sources.compute,sources.gpu]
},
{
 id:'limites',title:'O que ainda precisa evoluir',seconds:45,
 html:`<p class="kicker">Limitações com consequência prática</p><h2>O que ainda precisa evoluir</h2><div class="method-list"><div class="n">01</div><p><strong>Estado completo e capacidade compartilhada</strong>Limitam desempenho e permitem inferências sobre tamanho agregado.</p><div class="n">02</div><p><strong>Compiladores, verificadores e host</strong>Incluem CUDA e hardware GPU quando ativados.</p><div class="n">03</div><p><strong>Persistência e mudanças de política</strong>Faltam provas gerais de falha/recuperação e recertificação.</p></div><p class="foot-message">Execução serial. Sem demonstração de isolamento concorrente ou de uso em grande escala.</p>`,
 bottom:'O limite compartilhado também permite que um usuário esgote a capacidade disponível aos demais.',
 notes:'Os limites ajudam a escolher próximos passos. Primeiro, processar o estado inteiro prejudica escala. O teto compartilhado também pode revelar tamanho agregado por meio de respostas de limite e permitir esgotamento de capacidade por outro usuário. Segundo, há confiança explícita em verificadores, compilação e host. Terceiro, testes de reabertura e repetição de pedidos não substituem uma prova geral de durabilidade após falhas. Também faltam mecanismos avaliados para mudanças de política e recertificação. CUDA amplia T2; clocks GPU não fixados e SQL sem admissão equivalente limitam E6. As transações são seriais. Esse conjunto de limites impede apresentar o protótipo como um substituto pronto para um banco de produção, mas deixa clara a contribuição que já pode ser investigada.',
 sources:[sources.proofs,sources.evidence,sources.rls]
},
{
 id:'futuro',title:'Trabalhos futuros',seconds:45,
 html:`<p class="kicker">Continuidade da pesquisa</p><h2>Trabalhos futuros</h2><div class="method-list"><div class="n">01</div><p><strong>Avaliar geração em pedidos inéditos</strong>Medir aceitação dos artefatos, correções e esforço humano.</p><div class="n">02</div><p><strong>Reduzir trabalho sobre o estado completo</strong>Avaliar outras representações e workers GPU persistentes.</p><div class="n">03</div><p><strong>Ampliar garantias formais</strong>Estudar recuperação após falhas e recertificação após mudanças de política.</p></div>`,
 bottom:`Etapas propostas; estes resultados ainda não foram estabelecidos.`,
 notes:`Os próximos passos têm critérios concretos. Um experimento com pedidos inéditos deve medir quantos programas e certificados são aceitos, quantas correções exigem e quanto esforço humano permanece. Na implementação, é preciso reduzir o trabalho sobre o estado completo e avaliar workers GPU persistentes. Na formalização, os próximos alvos são recuperação após falhas e mudanças de política com recertificação. Estas são propostas de continuidade, ainda sem resultados neste trabalho.`,
 sources:[sources.artifact,sources.evidence]
},
{
 id:'declaracao-ia',title:'Uso de inteligência artificial',seconds:35,
 html:`<p class="kicker">Declaração de autoria assistida</p><h2>Uso de inteligência artificial</h2><div class="split disclosure" style="grid-template-columns:1fr 1fr 1fr;gap:55px"><section><h3>Claude Opus 5.5</h3><p>Anthropic<br>Planejamento e coordenação,<br>parte do código e das provas,<br>revisões e texto final.</p></section><section><h3>GPT-6.1 Sol</h3><p>OpenAI<br>Código e provas,<br>scripts de medição,<br>redação do artigo,<br>slides e notas.</p></section><section><h3>Kimi K3.1 Pro</h3><p>Moonshot AI<br>Revisão do artigo<br>e dos slides.</p></section></div><p class="lead spaced-lg">Todos os testes relacionados ao JayDB2 foram escritos por LLMs,<br>sob direção do autor.</p><p class="small spaced">O autor responde pelo conteúdo. As medições vêm de experimentos executados.<br>As ilustrações dos slides foram geradas com a ferramenta de imagens da OpenAI.</p>`,
 bottom:'Regulamento TCC CC: declaração de ferramentas, finalidade e partes com contribuição de IA.',
 notes:`Usei três assistentes de IA sob minha direção. O Claude Opus 5.5, da Anthropic, ajudou no planejamento, nas revisões, em parte do código e das provas e no texto final. O GPT-6.1 Sol, da OpenAI, ajudou com código, provas, medições, artigo, slides e notas. O Kimi K3.1 Pro, da Moonshot AI, ajudou a revisar artigo e slides. Todos os testes foram escritos por IA, e as ilustrações dos slides foram geradas com a ferramenta de imagens da OpenAI. Eu respondo pelo conteúdo; as medições vêm de experimentos executados.`,
 sources:[sources.ai]
},
{
 id:'conclusao',title:'JayDB2: síntese do trabalho',theme:'dark conclusion',seconds:30,
 html:`${logo('dark','anim-fade')}<p class="kicker">Conclusão</p><h2>JayDB2: síntese do trabalho</h2><div class="closing-points"><p>Um programa pode chegar ao banco com uma prova<br>das regras que precisa respeitar.</p><p>Serviço executável que verifica certificados ligados<br>ao programa executado e à sua finalização.</p><p>Aplicações combinam leis de acesso e consistência.<br>Experimentos medem custo, reuso, escala e CUDA.</p><p>O protótipo depende de T1–T3 e tem custo elevado<br>frente a SQL nas operações pontuais avaliadas.</p></div><p class="small spaced">Obrigado.</p>`,
 bottom:'Gabriel Jota Lizardo · PUC Minas',
 notes:`A pergunta do trabalho foi se um programa pode chegar ao banco com uma prova das regras que precisa respeitar. O trabalho construiu um serviço executável que exige certificados ligados ao programa admitido, à sua execução e à sua finalização; a publicação física fica em T3. As aplicações combinam acesso e consistência, e os experimentos medem o custo desse caminho, a preparação, a escala e o offload em CUDA. Os resultados dependem da base T1 a T3; nas operações pontuais, o custo do protótipo continua elevado frente a SQL. As limitações apresentadas delimitam o que foi estabelecido. Obrigado.`,
 sources:[sources.artifact]
},
{
 id:'b-sql',title:'Por que não usar apenas PostgreSQL?',backup:true,seconds:0,
 html:`<p class="kicker">Perguntas · mecanismos existentes</p><h2>Por que não usar<br>apenas PostgreSQL?</h2><table class="data-table"><thead><tr><th>Mecanismo</th><th>O que oferece</th></tr></thead><tbody><tr><td><strong>Privilégios / RLS</strong></td><td>Restringem operações e linhas acessíveis.</td></tr><tr><td><strong>Restrições / gatilhos</strong></td><td>Verificam integridade e regras da aplicação.</td></tr><tr><td><strong>Certificado JayDB2</strong></td><td>Estabelece proposições sobre estados e caminhos<br>do programa antes de sua execução.</td></tr></tbody></table><p class="small spaced">Há alternativas convencionais para várias políticas demonstradas.<br>O experimento investiga a interface de programas certificados e seu custo.</p>`,
 bottom:'PostgreSQL RLS filtra linhas. A recusa de um certificado tem uma interface diferente.',
 notes:'Privilégios, RLS e gatilhos resolvem muitos problemas reais e não são apresentados como incapazes de proteger dados. Para tabelas separadas por dono, privilégios são uma alternativa especialmente próxima. O diferencial estudado é a entrega de uma prova de proposições sobre todos os estados e caminhos cobertos do programa, incluindo regras de publicação e protocolos mais específicos. O custo adicional é grande no protótipo. O benchmark com RLS tem outra interface: filtrar linhas e recusar a admissão não são o mesmo comportamento. Não há justificativa para dizer que o JayDB2 substitui esses mecanismos em todos os cenários.',
 sources:[sources.evidence,{label:'PostgreSQL: RLS',url:'https://www.postgresql.org/docs/16/ddl-rowsecurity.html'},{label:'PostgreSQL: privilégios',url:'https://www.postgresql.org/docs/16/ddl-priv.html'}]
},
{
 id:'b-prova',title:'Como ler o alvo de um certificado',backup:true,seconds:0,
 html:`<p class="kicker">Perguntas · prova e esforço</p><h2>Como ler o alvo de um certificado</h2><figure class="code-figure certificate-figure"><img src="assets/client-certificate.svg" alt="Trecho literal da declaração certificate: recebe contexto, argumentos, código, estado válido, identidade presente e profundidade n; produz SafetyTrace da execução real."/><figcaption>Declaração literal · applications/rls/ClientProof.bend · quebras de linha para leitura</figcaption></figure><p class="small spaced">Dado um estado válido, a prova cobre os prefixos da execução em <code>SafetyTrace</code>.<br>A terminação é uma obrigação adicional. Na preparação, contexto e argumentos também são universais.</p><p class="small spaced">Linhas locais de programa / prova: disponibilidade ${pt(value('IndexedClientLines'),0)} / ${pt(value('IndexedProofLines'),0)},<br>vouchers ${pt(value('VoucherClientLines'),0)} / ${pt(value('VoucherProofLines'),0)}, notas ${pt(value('RlsClientLines'),0)} / ${pt(value('RlsProofLines'),0)}. Bibliotecas e provas de domínio ficam fora dessas contagens.</p>`,
 bottom:`Contagem de linhas não mede produtividade nem dificuldade.`,
 notes:`O trecho vem da declaração certificate da aplicação de notas. Os parâmetros ctx, args e code identificam o pedido. O parâmetro s é um estado arbitrário, valid exige sua validade e identity exige a presença da identidade. A profundidade n também é arbitrária. O resultado SafetyTrace fala de S.execute, a execução real. Um certificado ordinário fixa contexto e argumentos; a preparação exige uma prova universal também nesses parâmetros. A terminação tem declaração separada. As contagens locais excluem bibliotecas e provas de domínio e não estimam esforço nem produtividade de LLMs.`,
 sources:[sources.laws,sources.evidence,source('Certificado de notas','applications/rls/ClientProof.bend')]
},
{
 id:'b-resposta',title:'E se a resposta se perder?',backup:true,seconds:0,
 html:`<p class="kicker">Perguntas · vouchers e repetição</p><h2>E se a resposta se perder?</h2>${retryFigure()}<p class="small diagram-note">Uma entrada conflitante é recusada. Retirar voucher e recibo encerra a proteção do ID.<br>Testes nativos cobrem perda de resposta e reabertura após publicação durável.</p>`,
 bottom:'A aplicação define o protocolo. O cliente não repete escritas silenciosamente.',
 notes:'A perda de resposta pode ocorrer depois de o banco publicar a transação. Repetir uma emissão comum poderia duplicar um efeito. A aplicação de vouchers liga o ID do pedido à entrada exata e ao resultado retido. Um pedido idêntico, ainda autorizado, retorna esse resultado sem repetir a emissão. Uma entrada diferente com o mesmo ID é recusada. O protocolo inclui retirada explícita, que remove o voucher e recibo e termina a proteção daquele ID. Os testes matam o serviço após publicação durável e verificam o comportamento na reabertura. Isso é evidência de cenário e não uma prova completa de falhas de armazenamento.',
 sources:[sources.voucher]
},
{
 id:'b-simulacao',title:'E6: tabela completa e método',backup:true,seconds:0,
 html:`<p class="kicker">Perguntas · E6 em detalhe</p><h2>E6: tabela completa e método</h2><p class="small" style="margin-top:18px">Medianas em ms de chamadas completas. CPU-1, CPU-16 e CUDA são backends do JayDB2.</p>${simulationTable()}<div class="split" style="margin-top:30px;gap:60px"><p class="micro"><strong>Amostragem.</strong> ${pt(value('SimulationSessionCount'),0)} sessão por backend, ${pt(value('SimulationWarmups'),0)} aquecimento excluído, ${pt(value('SimulationRepeats'),0)} amostras por célula. ${E.GpuDevice} sem clock fixo, também usada pelo desktop. Processo e dispositivo novos a cada pedido. Limite = cancelamento real; não executado = após limite anterior.</p><p class="micro"><strong>Comparação.</strong> Armazenamento volátil: RAM / TEMP / :memory:. PL/pgSQL interpretado e CTE recursiva não foram feitos para cálculo numérico; SQL sem admissão por prova ou autenticação equivalentes. Preparação separada (ms): ${pt(value('SimulationCpuOnePreparationMs'),0)} / ${pt(value('SimulationCpuSixteenPreparationMs'),0)} / ${pt(value('SimulationCudaPreparationMs'),0)}.</p></div>`,
 bottom:`Resultados e estados completos conferidos com oráculos Python/NumPy fora do tempo medido. Memória GPU reservada: ${pt(value('GpuCorpusMiB'),0)} MiB.`,
 notes:`A tabela completa mostra todas as medianas. Em JayDB2, o tempo inclui codificação, transporte, autenticação, conferência dos artefatos, início de processo e dispositivo, publicação e decodificação. Em SQL inclui a execução no banco e a leitura do resultado, sem função externa em Python. Todos usam armazenamento volátil. Há uma sessão, um aquecimento excluído e ${pt(value('SimulationRepeats'),0)} amostras por célula. A preparação é medida à parte, com uma observação. A GPU não tinha clock fixo e também atendia o desktop. Os tempos esgotados não são extrapolados. Um worker GPU persistente mudaria os resultados das chamadas pequenas e é trabalho futuro.`,
 sources:[sources.compute,sources.simulation]
},
{
 id:'b-reproducao',title:'Como reproduzir os resultados',backup:true,seconds:0,
 html:`<p class="kicker">Perguntas · medição e reprodução</p><h2>Como reproduzir os resultados</h2><div class="split"><section><h3>Ambiente</h3><p class="spaced">Intel i7-11700K, Linux, ext4.<br>3,6 GHz nominal, turbo desligado.<br>Um cliente; E1–E5: uma thread, GPU off.</p><p class="small muted spaced">Bend 2.0.39, Rust 1.98.0,<br>Node 24.19.0, Clang 19.1.1.</p></section><section><h3>Amostras e fronteiras</h3><p class="spaced">E1–E3: três sessões.<br>E5: ${pt(value('ScalingSessionCount'),0)} sessão, ${pt(value('ScalingSamples'),0)} amostras por ponto.<br>E6: CPU-1/CPU-16/CUDA e SQL.<br>Inicialização e conferência fora do tempo.</p><p class="small muted spaced">E1–E5 JayDB2: quadro pré-codificado até resposta completa.<br>E6 JayDB2: inclui codificação e início do worker/GPU.<br>SQL: execute(...).fetchall(), incluindo driver.</p></section></div><p class="small spaced"><a href="${repo}/blob/main/paper/README.md" target="_blank" rel="noopener">github.com/j0taaa/jaydb2 · paper/README.md</a><br>JSONs, respostas, hashes e comandos ficam em paper/evidence/.</p>`,
 bottom:'Medições retidas no repositório, com dados e respostas conferidos.',
 notes:'Os comandos e os dados brutos estão no guia do artigo. Os arquivos retêm metadados, versões e fingerprints de fonte e executável. A política de CPU foi salva, alterada e restaurada com conferência. E1 a E3 possuem três sessões independentes. E5 tem uma única sessão e populações ascendentes. As medidas incluem resultados diferentes de serialização em JayDB2 e nos drivers SQL, por isso são comparações de caminho completo. Os tempos de checagem e compilação se sobrepõem e não devem ser somados. As observações lentas foram mantidas. E6 inclui codificação e decodificação; usa uma sessão, preparação separada, armazenamento volátil e GPU sem clock fixo. NumPy 2.5.4 valida os oráculos; driver e NVRTC vêm dos artefatos registrados. Os dados são os experimentos retidos.',
 sources:[sources.evidence,sources.artifact]
}
];
window.JAYDB2_SLIDES=slides;
