'use strict';
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
const arrow='<span class="connector" aria-hidden="true"><svg viewBox="0 0 65 40"><path d="M0 20H61M49 8l12 12-12 12"/></svg></span>';
const fragment=(html,n=1)=>`<div class="fragment" data-step="${n}">${html}</div>`;
const node=(n,title,body)=>`<div class="node"><div class="node-number">${n}</div><h3>${title}</h3><p>${body}</p></div>`;
const footer=(text)=>`<span class="source">${text}</span>`;
function reuseChart(){
  const x=n=>335+Math.log10(n)*225;
  const rows=[['Chamada ordinária',value('OrdinaryReadMedianSeconds')*1000,pt(value('OrdinaryReadMedianSeconds'))+' s','#dc6e52'],['Preparação, uma vez',value('RegistrationReadVolatileMedianSeconds')*1000,pt(value('RegistrationReadVolatileMedianSeconds'))+' s','#a1b3a6'],['Chamada preparada',value('PreparedReadVolatileMedianMs'),pt(value('PreparedReadVolatileMedianMs'))+' ms','#087869']];
  return `<svg viewBox="0 0 1400 370" role="img" aria-label="Leitura ordinária: ${pt(value('OrdinaryReadMedianSeconds'))} segundos. Preparação única: ${pt(value('RegistrationReadVolatileMedianSeconds'))} segundos. Leitura preparada volátil: ${pt(value('PreparedReadVolatileMedianMs'))} milissegundos. Eixo logarítmico em milissegundos.">${[1,10,100,1000,10000].map(n=>`<line class="gridline" x1="${x(n)}" y1="20" x2="${x(n)}" y2="285"/><text class="tick" x="${x(n)}" y="320" text-anchor="middle">${pt(n,0)}</text>`).join('')}${rows.map(([label,n,labelValue,color],i)=>{const y=53+i*89;return `<text class="series-label" x="0" y="${y+25}">${label}</text><rect x="335" y="${y}" width="${x(n)-335}" height="35" fill="${color}"/><text class="value" x="${x(n)+18}" y="${y+26}">${labelValue}</text>`;}).join('')}<text class="axis-label" x="790" y="363" text-anchor="middle">Latência (ms) · escala logarítmica</text></svg>`;
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
 html:`<p class="kicker">Motivação</p><h2>Quem confere o que um programa<br>faz com os dados?</h2><div class="news-columns"><section><div class="news-date">DINAMARCA · DIVULGADO EM 5 OUT 2026</div><div class="news-number">8,8 milhões</div><div class="news-title">de pessoas com dados do registro populacional acessados</div><div class="news-caption">O invasor abusou do acesso legítimo de uma empresa: as operações eram autenticadas.</div></section><section class="fragment" data-step="1"><div class="news-date">PROGRAMAS GERADOS POR IA</div><div class="news-number">Agentes</div><div class="news-title">escrevem cada vez mais o código que lê e altera dados</div><div class="news-caption">Um programa plausível pode estar errado. Confiar no autor, humano ou modelo, não basta.</div></section></div><p class="foot-message fragment" data-step="2"><strong>O problema não é apenas quem entra: é o que cada programa tem permissão para fazer.</strong></p>`,
 bottom:'Fonte: comunicado oficial do CPR. O caso motiva a pergunta; não demonstra prevenção pelo protótipo.',
 notes:'Em outubro, o registro populacional dinamarquês informou acesso indevido a dados de aproximadamente oito milhões e oitocentas mil pessoas. O invasor usou o acesso legítimo de uma empresa: as operações eram autenticadas, mas o que elas podiam fazer não estava suficientemente limitado. Ao mesmo tempo, agentes de IA passam a escrever o código que lê e altera dados, e um programa plausível pode estar errado. As duas situações levam à mesma pergunta: quem confere o que um programa faz com os dados antes de ele executar? O problema não é apenas quem entra, mas o que cada programa tem permissão para fazer. O JayDB2 investiga uma resposta. Não afirmo que o protótipo impediria esse ataque específico.',
 sources:[sources.cpr]
},
{
 id:'o-que-e',title:'O que é o JayDB2',seconds:45,
 html:`<p class="kicker">A ideia</p><h2>O que é o JayDB2</h2><p class="lead">Um banco que exige uma prova de que o programa<br>respeita as regras instaladas pelo administrador.</p><div class="diagram">${node('01','O cliente propõe','Programa, argumentos,<br>credencial e prova.')}${arrow}${node('02','O banco verifica','A prova precisa corresponder<br>ao programa que vai executar.')}${arrow}${node('03','O programa executa','Mudanças ficam privadas<br>até a conclusão aceita.')}</div><p class="admin-rule">O administrador define esquema e leis; o cliente demonstra que as respeita.</p>`,
 bottom:'Programa e certificado entram juntos na admissão',
 notes:'Há três papéis. O administrador decide como os dados são organizados e quais regras a aplicação exige. O cliente escreve um programa para realizar sua operação e entrega uma prova. O JayDB2 confere se a prova tem o tipo exigido e se está ligada ao programa exato. Se a admissão aceita, o banco executa o programa em um estado de trabalho privado. Uma conclusão bem-sucedida pode publicar o resultado completo. Outros resultados preservam o estado anterior. A prova é uma estrutura formal que um verificador consegue checar. Ela não é uma explicação em linguagem natural nem uma aprovação feita pelo próprio modelo que escreveu o programa.',
 sources:[sources.laws,sources.artifact]
},
{
 id:'pedido',title:'Um pedido comum',seconds:30,
 html:`<p class="kicker">Exemplo: notas compartilhadas</p><h2>Um pedido comum</h2><div class="request">Salve uma nota para mim e inclua<br>essa nota na minha lista.</div><div class="split"><section><div class="owner">Alice</div><div class="ledger"><div class="ledger-line"><span>Nota</span><code>alice/n1</code></div><div class="ledger-line"><span>Dona</span><span>Alice</span></div><div class="ledger-line"><span>Diretório de Alice</span><span>inclui n1</span></div></div></section><section><div class="owner bob">Bob</div><div class="ledger"><div class="ledger-line"><span>Nota</span><code>bob/n7</code></div><div class="ledger-line"><span>Dono</span><span>Bob</span></div><div class="ledger-line"><span>Dados de Bob</span><span>fora do pedido</span></div></div></section></div>`,
 bottom:'Pedido e resultado pretendido são ilustrativos. A interface recebe programa e certificado em Bend.',
 notes:`Alice quer salvar uma nota e encontrá-la em seu diretório. Bob também possui notas nessa tabela compartilhada. O pedido envolve duas obrigações: Alice não deve acessar a nota de Bob e, ao concluir, seu diretório deve listar exatamente as notas que pertencem a ela. A tela ilustra o resultado pretendido; o próximo exemplo parte do estado vazio. A interface implementada recebe o programa e sua prova em Bend.`,
 sources:[sources.rls]
},
{
 id:'leis',title:'As regras da aplicação',seconds:30,
 html:`<p class="kicker">O que o administrador exige</p><h2>As regras da aplicação</h2><table class="data-table"><thead><tr><th>Regra</th><th>Significado neste exemplo</th></tr></thead><tbody><tr><td><strong>Propriedade</strong></td><td>Alice acessa apenas seu namespace.</td></tr><tr><td><strong>Dono da nota</strong></td><td>A criação usa a identidade autenticada.<br>Uma atualização preserva o dono.</td></tr><tr><td><strong>Diretório exato</strong></td><td>O diretório lista todas as notas do dono<br>e nenhuma nota de outra pessoa.</td></tr></tbody></table>`,
 bottom:'A aplicação também define um administrador com leitura ampliada e sem exceção de escrita.',
 notes:`Estas são as regras da aplicação. Cada chave está ligada à identidade atual. Na criação, o dono gravado deve ser o usuário autenticado. Uma atualização preserva esse dono. O diretório deve listar todas as notas dele e nenhuma de outra pessoa. O administrador pode fazer leituras ampliadas, mas não recebe exceção de escrita. Essas obrigações foram formalizadas e entram no certificado. Os controles negativos tentam quebrar cada uma delas para conferir a rejeição.`,
 sources:[sources.rls]
},
{
 id:'transacao',title:'Uma mudança privada, um resultado completo',seconds:55,
 html:`<p class="kicker">Como a transação funciona</p><h2>Uma mudança privada,<br>um resultado completo</h2><div class="state-grid"><section class="state-step"><div class="state-label">ANTES</div><h3>Estado publicado</h3><div class="entry">Notas de Alice: nenhuma</div><div class="entry">Diretório: vazio</div><div class="state-result">Os dados concordam.</div></section><section class="state-step warning fragment" data-step="1"><div class="state-label">DURANTE</div><h3>Proposta privada</h3><div class="entry">Nota n1 criada</div><div class="entry">Diretório ainda vazio</div><div class="state-result">Inconsistência temporária.<br>Outros clientes não a observam.</div></section><section class="state-step fragment" data-step="2"><div class="state-label">AO CONCLUIR</div><h3>Publicação aceita</h3><div class="entry">Nota n1 criada</div><div class="entry">Diretório inclui n1</div><div class="state-result">O resultado completo<br>pode ficar visível.</div></section></div><p class="foot-message">Cada acesso deve ser permitido. A consistência entre tabelas precisa valer na publicação.</p>`,
 bottom:'A regra de diretório exato vale nos estados publicados; a proposta pode ficar incompleta durante a operação.',
 notes:'A ordem das escritas importa para a explicação. Antes do pedido, não há nota e o diretório está vazio. O programa cria a nota em sua proposta privada. Nesse instante, o diretório ainda não foi atualizado. Isso é permitido como situação intermediária. O programa então acrescenta a entrada correta e conclui. A lei exige que a correspondência seja exata quando o novo estado é publicado. O certificado estabelece essa propriedade sobre o caminho real do programa. Se o programa recusa, a proposta não substitui o estado publicado. E a regra de acesso continua valendo durante todo o processo: uma operação privada não ganha permissão para ler Bob.',
 sources:[sources.rls,sources.laws]
},
{
 id:'rejeicoes',title:'Dois erros, duas obrigações diferentes',seconds:45,
 html:`<p class="kicker">Controles negativos executados</p><h2>Dois erros, duas<br>obrigações diferentes</h2><div class="demo-comparison"><section><h3>Ler uma nota de Bob</h3><p class="fail-line">Alice tenta observar<br>um dado que não lhe pertence.</p><div class="status-word coral-text">Acesso inválido</div><p class="fail-reason">A prova falha na permissão.</p></section><section class="fragment" data-step="1"><h3>Esquecer o diretório</h3><p class="fail-line">O programa cria a nota de Alice,<br>mas deixa sua lista incompleta.</p><div class="status-word coral-text">Resultado inválido</div><p class="fail-reason">A prova falha na consistência final.</p></section></div><p class="foot-message">O host rejeita a admissão e as verificações posteriores confirmam o estado preservado.</p>`,
 bottom:`Aplicação de notas: ${pt(value('RlsNegativeFixtures'),0)} negativos causais e ${pt(value('RlsNativeResponses'),0)} respostas nativas conferidas.`,
 notes:`Ler Bob falha na permissão, mesmo que o programa recuse depois. Esquecer o diretório falha na consistência final, apesar de respeitar o acesso. A aplicação tem ${pt(value('RlsNegativeFixtures'),0)} controles negativos causais e ${pt(value('RlsNativeResponses'),0)} respostas nativas conferidas, incluindo o estado completo preservado após rejeições. Cada controle isola uma obrigação. São evidências complementares às provas.`,
 sources:[sources.rls]
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
 html:`<p class="kicker">Autoria assistida por IA</p><h2>Onde os LLMs entram</h2><div class="diagram">${node('INTENÇÃO','Pedido do usuário','A pessoa descreve<br>a operação desejada.')}${arrow}${node('AUTORIA','LLM + bibliotecas','Constrói o programa<br>e a sua prova.')}${arrow}${node('ADMISSÃO','Verificador do banco','Aceita só o que cumpre<br>as regras do administrador.')}</div><div class="split" style="margin-top:58px;gap:60px"><section><h3>Trabalhos relacionados</h3><p class="small spaced">LLMs já geram provas e código verificado:<br>Isabelle (Baldur), Dafny e Verus (AutoVerus).<br>Eles medem a taxa de sucesso da geração.</p></section><section><h3>Neste projeto</h3><p class="small spaced">LLMs ajudaram a escrever código e provas.<br><strong>Todos os testes do JayDB2 foram escritos por LLMs</strong>, sob direção do autor.</p></section></div>`,
 bottom:'O JayDB2 é o lado consumidor: o gerador não precisa ser confiável, porque a prova é verificada.',
 notes:'A escrita manual de provas torna uma operação pequena cara de produzir. LLMs e bibliotecas de provas permitem outro fluxo: partir da intenção, construir programa e certificado, submeter ao verificador e corrigir quando não passa. Há trabalhos recentes nessa direção: o Baldur gera e repara provas em Isabelle, Misu e colegas sintetizam métodos Dafny verificados, e o AutoVerus gera provas para código Rust verificado pelo Verus. Esses trabalhos medem com que frequência a geração dá certo. O JayDB2 trata do lado complementar: um banco que só executa o artefato gerado se a prova passar, então o gerador não precisa ser confiável. Neste projeto, LLMs ajudaram no código e nas provas, e todos os testes do JayDB2 foram escritos por LLMs sob minha direção.',
 sources:[sources.ai,sources.baldur,sources.misu,sources.autoverus]
},
{
 id:'metodo',title:'Como o trabalho foi avaliado',seconds:40,
 html:`<p class="kicker">Problema de pesquisa e método</p><h2>Como o trabalho foi avaliado</h2><div class="method-list"><div class="n">RQ1</div><p><strong>Ligar a prova ao programa que executa</strong>Especificação e teoremas sobre as funções executáveis.</p><div class="n">RQ2</div><p><strong>Combinar acesso e consistência</strong>Aplicações certificadas e variantes inválidas direcionadas.</p><div class="n">RQ3</div><p><strong>Medir custo, reuso e CUDA</strong>Experimentos nativos com resultados e estados conferidos.</p></div>`,
 bottom:'Objetivo geral: implementar e avaliar o serviço, com ligação explícita entre certificado, execução e publicação.',
 notes:'A pesquisa organiza a construção em três perguntas. A primeira trata da conexão entre o certificado aceito e a execução. A segunda testa se leis conseguem combinar permissão em cada acesso e consistência ao final. A terceira mede o custo real do protótipo e o efeito da preparação e de CUDA opcional. O método começa pela especificação das ações, implementa as funções do banco, estabelece teoremas e constrói aplicações e controles inválidos. Depois mede o serviço nativo. Todos os números que vou mostrar vêm dos experimentos retidos no repositório, com verificação das respostas.',
 sources:[sources.evidence,sources.proofs]
},
{
 id:'arquitetura',title:'A prova precisa acompanhar o código exato',seconds:55,
 html:`<p class="kicker">A conexão com a implementação</p><h2>A prova precisa acompanhar<br>o código exato</h2><div class="diagram">${node('ADMISSÃO','Verificar e compilar','Programa e prova compõem<br>o mesmo Book em Bend.')}${arrow}${node('EXECUÇÃO','Interpretar e finalizar','Bend decide as ações<br>e o resultado completo.')}${arrow}${node('PUBLICAÇÃO','Commit ou Keep','Rust instala o estado<br>selecionado ou mantém o anterior.')}</div><p class="admin-rule">Selos, hashes e provas geradas ligam o admitido ao executado.</p><p class="small muted spaced">Node coordena a preparação das fontes. Rust coordena processos e estado.<br>As transações do serviço seguem uma fila serial.</p>`,
 bottom:'Bend 2.0.39 / BendTT · Rust 1.98.0 · Node 24.19.0 · Clang 19.1.1',
 notes:'O problema de sistemas aparece aqui. Seria insuficiente verificar um programa e depois executar um artefato diferente. A admissão monta um Book com as definições relevantes e alimenta a compilação com esse mesmo conteúdo. Provas geradas e conferências de identidade ligam o programa certificado ao que o worker inicia. As funções em Bend interpretam ações e finalizam a resposta. Uma decisão tipada, Commit ou Keep, informa ao host qual estado e resposta foram selecionados. Rust precisa instalar exatamente esse resultado e encaminhar seus bytes. Node coordena as ferramentas de admissão. O serviço processa transações em série, o que delimita a composição estudada.',
 sources:[sources.proofs,sources.evidence]
},
{
 id:'garantias',title:'O alcance das garantias',theme:'dark',seconds:50,
 html:`<p class="kicker">Base de confiança explícita</p><h2>O alcance das garantias</h2><p class="lead">Admissão exata, leis em cada passo,<br>conclusão válida e terminação lógica.</p><div class="trust-lines"><div class="trust-id">T1</div><section><h3>Verificação e vínculo</h3><p>Correção dos verificadores e correspondência entre fonte, prova e artefato.</p></section><div class="trust-id">T2</div><section><h3>Compilação e execução nativa</h3><p>Preservação do comportamento pelo compilador e runtime.</p></section><div class="trust-id">T3</div><section><h3>Trabalho físico do host</h3><p>Estado atual, processos, registro e publicação exata de Commit / Keep.</p></section></div>`,
 bottom:'Durabilidade após falhas, recuperação geral e isolamento concorrente não estão provados.',
 notes:'Os resultados centrais estabelecem a identidade e o início do programa exato, as leis em cada prefixo real, a finalização com estado e resposta corretos e a existência de uma execução lógica finita. Há premissas. T1 reúne correção dos verificadores e vínculo exato dos artefatos. T2 trata do compilador e do runtime. T3 reúne as tarefas físicas do host, como fornecer o estado atual, executar o artefato admitido e publicar a decisão selecionada. A validade do estado inicial é uma premissa. Assim a banca consegue localizar o que tem prova no nível Bend e onde ainda confiamos na infraestrutura. Durabilidade geral e concorrência não fazem parte desses teoremas.',
 sources:[sources.proofs]
},
{
 id:'aplicacoes',title:'A mesma interface em quatro aplicações',seconds:50,
 html:`<p class="kicker">Aplicações certificadas</p><h2>A mesma interface<br>em quatro aplicações</h2><table class="data-table apps-table"><thead><tr><th>Aplicação</th><th>Durante a operação</th><th>Ao publicar</th></tr></thead><tbody><tr><td><strong>Disponibilidade</strong></td><td>Só as tabelas do próprio usuário</td><td>Índice corresponde à linha principal</td></tr><tr><td><strong>Vouchers</strong></td><td>Permissão atual e protocolo de recibos</td><td>Voucher e recibo consistentes</td></tr><tr><td><strong>Notas</strong></td><td>Namespace próprio, dono preservado</td><td>Diretório lista exatamente as notas</td></tr><tr><td><strong>Simulação</strong></td><td>Lê só o próprio cenário</td><td>Escreve só o próprio resultado; termina</td></tr></tbody></table>`,
 bottom:'Cada aplicação tem variantes inválidas que quebram uma obrigação específica e são rejeitadas.',
 notes:'As quatro aplicações usam a mesma interface. Disponibilidade mantém uma linha principal e tabelas comuns que funcionam como índices. Vouchers ligam um identificador de pedido à entrada exata e ao resultado guardado, para permitir repetir um pedido com segurança. Notas é o exemplo inicial, com tabela compartilhada e diretórios por usuário. A simulação é um caso de cálculo pesado: lê o cenário do próprio usuário, calcula e escreve só o próprio resultado, com prova de terminação. Todas combinam regras que valem em cada acesso com regras que valem na publicação, e cada uma tem variantes inválidas que localizam a obrigação que falha.',
 sources:[sources.rls,sources.voucher,source('Disponibilidade e índices','applications/indexed/README.md'),sources.simulation]
},
{
 id:'evidencia',title:'Artefatos gerados, verificação executada',theme:'dark',seconds:40,
 html:`<p class="kicker">Evidências de construção e correção</p><h2>Artefatos gerados,<br>verificação executada</h2><div class="metric-line"><section><div class="metric-value">${pt(value('NegativeFixtures'),0)}</div><div class="metric-label">controles negativos<br>do núcleo</div></section><section><div class="metric-value">${pt(value('RlsNegativeFixtures'),0)}</div><div class="metric-label">negativos adicionais<br>da aplicação de notas</div></section><section><div class="metric-value">${pt(value('RlsNativeResponses'),0)}</div><div class="metric-label">respostas nativas conferidas<br>na sessão de notas</div></section></div><div class="success-log">✓ make verify-contract<br>✓ make verify<br>✓ make test</div>`,
 bottom:'Execuções retidas com sucesso. Os contadores representam evidências diferentes, não o total de testes do projeto.',
 notes:`Os teoremas estabelecem propriedades das funções sob premissas. Os controles negativos mostram que variantes inválidas falham no alvo esperado. As sessões nativas conferem respostas e estados reais. A evidência atual retém ${pt(value('NegativeFixtures'),0)} negativos do núcleo, ${pt(value('RlsNegativeFixtures'),0)} adicionais de notas e ${pt(value('RlsNativeResponses'),0)} respostas na sessão de notas. Os três comandos terminaram com sucesso. Esses contadores não são uma quantidade única de testes. Os negativos GPU e simulação também falham nas mesmas obrigações, em ambos os verificadores, antes da compilação.`,
 sources:[sources.evidence,sources.rls]
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
 html:`<p class="kicker">Mesmo programa, mesma prova</p><h2>Execução GPU opcional</h2><p class="lead">A simulação calcula milhares de caminhadas aleatórias inteiras.<br>O autor marca o trecho paralelo; o Bend pode executá-lo em CUDA.</p><div class="diagram">${node('ADMISSÃO','A mesma','Os dois verificadores aceitam<br>antes de gerar código GPU.')}${arrow}${node('OBRIGAÇÕES','As mesmas','Acesso, terminação, publicação.<br>Negativos falham igual.')}${arrow}${node('EXECUÇÃO','Sem atalho','Artefato alterado ou falha<br>descarta a proposta.')}</div><p class="admin-rule">O programa e o certificado não mudam; a base de confiança, sim: runtime CUDA, driver e GPU entram em T2.</p>`,
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
 html:`<p class="kicker">Limitações com consequência prática</p><h2>O que ainda precisa evoluir</h2><div class="method-list"><div class="n">01</div><p><strong>Estado completo e capacidade compartilhada</strong>Limitam desempenho e permitem inferências sobre tamanho agregado.</p><div class="n">02</div><p><strong>Compiladores, verificadores e host</strong>Incluem CUDA e hardware GPU quando ativados.</p><div class="n">03</div><p><strong>Persistência e mudanças de política</strong>Faltam provas gerais de falha/recuperação e re-certificação.</p></div><p class="foot-message">Execução serial. Sem demonstração de isolamento concorrente ou de uso em grande escala.</p>`,
 bottom:'O limite compartilhado também permite que um usuário esgote a capacidade disponível aos demais.',
 notes:'Os limites ajudam a escolher próximos passos. Primeiro, processar o estado inteiro prejudica escala. O teto compartilhado também pode revelar tamanho agregado por meio de respostas de limite e permitir esgotamento de capacidade por outro usuário. Segundo, há confiança explícita em verificadores, compilação e host. Terceiro, testes de reabertura e repetição de pedidos não substituem uma prova geral de durabilidade após falhas. Também faltam mecanismos avaliados para mudanças de política e re-certificação. CUDA amplia T2; clocks GPU não fixados e SQL sem admissão equivalente limitam E6. As transações são seriais. Esse conjunto de limites impede apresentar o protótipo como um substituto pronto para um banco de produção, mas deixa clara a contribuição que já pode ser investigada.',
 sources:[sources.proofs,sources.evidence,sources.rls]
},
{
 id:'futuro',title:'Uma arquitetura para programas gerados por IA',theme:'mint',seconds:45,
 html:`<p class="kicker">Próxima etapa de pesquisa</p><h2>Uma arquitetura para programas<br>gerados por IA</h2><p class="statement" style="margin-top:45px;font-size:55px">O gerador constrói o programa e sua prova.<br>O banco verifica as regras que deve cumprir.</p><div class="progress-line"><section class="progress-item"><h3>Já construído</h3><p>Serviço executável,<br>aplicações certificadas<br>e testes escritos por LLMs.</p></section><section class="progress-item"><h3>Próximo experimento</h3><p>Pedidos inéditos,<br>sucesso de geração<br>e esforço de correção.</p></section><section class="progress-item"><h3>Próxima engenharia</h3><p>Menos trabalho sobre<br>o estado completo<br>e melhores garantias do host.<br>Workers GPU persistentes.</p></section></div>`,
 bottom:'Direção proposta: programas de banco de dados verificados de forma independente em aplicações assistidas por IA.',
 notes:'O projeto permite formular uma direção de pesquisa mais ampla. A interface entre geração e banco pode exigir evidência verificável do comportamento permitido. A experiência atual já inclui serviço executável, programas e certificados construídos com ajuda de IA e testes escritos por LLMs. O próximo experimento deve receber pedidos inéditos e registrar quantos artefatos passam, quantas correções exigem e quanto trabalho humano permanece. Em paralelo, o sistema precisa reduzir o custo sobre o estado completo e fortalecer a fronteira do host e avaliar workers GPU persistentes. Assim o futuro aparece como um caminho apoiado no que foi construído, com critérios concretos para avaliar a próxima etapa.',
 sources:[sources.artifact,sources.evidence]
},
{
 id:'declaracao-ia',title:'Uso de inteligência artificial',seconds:35,
 html:`<p class="kicker">Declaração de autoria assistida</p><h2>Uso de inteligência artificial</h2><div class="split disclosure" style="grid-template-columns:1fr 1fr 1fr;gap:55px"><section><h3>Claude Opus 5.5</h3><p>Anthropic<br>Planejamento e coordenação,<br>parte do código e das provas,<br>revisões, revisão do texto.</p></section><section><h3>GPT-6.1 Sol</h3><p>OpenAI<br>Código e provas,<br>scripts de medição,<br>redação do artigo,<br>slides e notas.</p></section><section><h3>Kimi K3.1 Pro</h3><p>Moonshot AI<br>Revisão do artigo<br>e dos slides.</p></section></div><p class="lead spaced-lg">Todos os testes relacionados ao JayDB2 foram escritos por LLMs,<br>sob direção do autor.</p><p class="small spaced">O autor responde pelo conteúdo. As medições vêm de experimentos executados.<br>A imagem da capa foi gerada com a ferramenta de imagens da OpenAI.</p>`,
 bottom:'Regulamento TCC CC: declaração de ferramentas, finalidade e partes com contribuição de IA.',
 notes:`Usei três assistentes de IA sob minha direção. O Claude Opus 5.5, da Anthropic, ajudou no planejamento, na coordenação, nas revisões técnicas, em parte do código e das provas e na revisão final do texto. O GPT-6.1 Sol, da OpenAI, ajudou a escrever código, provas, scripts de medição, o texto do artigo, os slides e as notas. O Kimi K3.1 Pro, da Moonshot AI, ajudou a revisar o artigo e os slides. Todos os testes do JayDB2 foram escritos por IA sob minha direção, e a imagem da capa foi gerada com a ferramenta de imagens da OpenAI. Eu respondo pelo conteúdo, e todas as medições vêm de experimentos executados.`,
 sources:[sources.ai]
},
{
 id:'conclusao',title:'JayDB2: o que fica demonstrado',theme:'dark conclusion',seconds:30,
 html:`<p class="kicker">Conclusão</p><h2>JayDB2</h2><p class="statement">Um programa pode chegar ao banco<br>com uma prova das regras<br>que precisa respeitar.</p><p class="bottom-line">A conexão com a execução foi construída e avaliada.<br>Reuso, escala e autoria assistida definem os próximos passos.</p>`,
 bottom:'Gabriel Jota Lizardo · PUC Minas',
 notes:'A contribuição do JayDB2 é tornar concreta essa interface: um programa chega acompanhado de uma prova das regras definidas pelo administrador, e essa prova está ligada às funções que executam e publicam seu resultado. As aplicações mostram acesso e consistência. A avaliação mede custo, reuso e escala. CUDA só supera CPU-16 na maior carga E6, sob T2 ampliada. A autoria assistida por LLMs torna especialmente interessante investigar a produção de novos programas e certificados sobre essa base. Obrigado.',
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
 html:`<p class="kicker">Perguntas · prova e esforço</p><h2>Como ler o alvo<br>de um certificado</h2><div class="code-block">Para todo estado inicial válido s,<br>para todo contexto e argumento cobertos,<br>para cada prefixo real da execução:<br><br>    as leis aplicáveis precisam valer.<br><br>Uma obrigação adicional estabelece terminação.</div><p class="small spaced">Linhas locais de programa / prova: disponibilidade ${pt(value('IndexedClientLines'),0)} / ${pt(value('IndexedProofLines'),0)},<br>vouchers ${pt(value('VoucherClientLines'),0)} / ${pt(value('VoucherProofLines'),0)}, notas ${pt(value('RlsClientLines'),0)} / ${pt(value('RlsProofLines'),0)}. Bibliotecas e provas de domínio ficam fora dessas contagens.</p>`,
 bottom:'Representação explicativa do alvo formal. Contagem de linhas não mede produtividade nem dificuldade.',
 notes:'A forma explicativa resume o quantificador do certificado. Um certificado ordinário fixa contexto e argumentos do pedido e quantifica sobre estados e profundidades. A preparação exige uma prova universal também em contextos e argumentos. As leis podem falar do estado estável, do prefixo em execução e do encerramento. O programa precisa fornecer uma continuação válida para cada resultado de uma ação. As contagens locais ajudam a visualizar tamanho, mas excluem partes compartilhadas e não estimam quanto esforço foi necessário. Não há medida controlada de produtividade de LLMs neste trabalho.',
 sources:[sources.laws,sources.evidence]
},
{
 id:'b-resposta',title:'E se a resposta se perder?',backup:true,seconds:0,
 html:`<p class="kicker">Perguntas · vouchers e repetição</p><h2>E se a resposta se perder?</h2><div class="diagram">${node('PRIMEIRO PEDIDO','Voucher + recibo','A transação publica<br>o efeito e seu resultado.')}${arrow}${node('REPETIÇÃO IDÊNTICA','Permissão atual','Confere identidade,<br>operação e entrada exata.')}${arrow}${node('RESULTADO RETIDO','Sem nova emissão','Devolve o resultado<br>associado ao pedido.')}</div><p class="admin-rule">Entrada conflitante recusa. Retirar voucher e recibo encerra a proteção desse identificador.</p><p class="small muted spaced">Há testes nativos com perda de resposta e reabertura após publicação durável.<br>Uma prova geral de recuperação continua como trabalho futuro.</p>`,
 bottom:'A aplicação define o protocolo. O cliente não repete escritas silenciosamente.',
 notes:'A perda de resposta pode ocorrer depois de o banco publicar a transação. Repetir uma emissão comum poderia duplicar um efeito. A aplicação de vouchers liga o ID do pedido à entrada exata e ao resultado retido. Um pedido idêntico, ainda autorizado, retorna esse resultado sem repetir a emissão. Uma entrada diferente com o mesmo ID recusa. O protocolo inclui retirada explícita, que remove o voucher e recibo e termina a proteção daquele ID. Os testes matam o serviço após publicação durável e verificam o comportamento na reabertura. Isso é evidência de cenário e não uma prova completa de falhas de armazenamento.',
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
 html:`<p class="kicker">Perguntas · medição e reprodução</p><h2>Como reproduzir os resultados</h2><div class="split"><section><h3>Ambiente</h3><p class="spaced">Intel i7-11700K, Linux, ext4.<br>3,6 GHz nominal, turbo desligado.<br>Um cliente; E1–E5: uma thread, GPU off.</p><p class="small muted spaced">Bend 2.0.39, Rust 1.98.0,<br>Node 24.19.0, Clang 19.1.1.</p></section><section><h3>Amostras e fronteiras</h3><p class="spaced">E1–E3: três sessões.<br>E5: ${pt(value('ScalingSessionCount'),0)} sessão, ${pt(value('ScalingSamples'),0)} amostras por ponto.<br>E6: CPU-1/CPU-16/CUDA e SQL.<br>Inicialização e conferência fora do tempo.</p><p class="small muted spaced">JayDB2: quadro pré-codificado até resposta completa.<br>SQL: execute(...).fetchall(), incluindo driver.</p></section></div><p class="small spaced"><a href="${repo}/blob/main/paper/README.md" target="_blank" rel="noopener">github.com/j0taaa/jaydb2 · paper/README.md</a><br>JSONs, respostas, hashes e comandos ficam em paper/evidence/.</p>`,
 bottom:'Medições retidas no repositório, com dados e respostas conferidos.',
 notes:'Os comandos e os dados brutos estão no guia do artigo. Os arquivos retêm metadados, versões e fingerprints de fonte e executável. A política de CPU foi salva, alterada e restaurada com conferência. E1 a E3 possuem três sessões independentes. E5 tem uma única sessão e populações ascendentes. As medidas incluem resultados diferentes de serialização em JayDB2 e nos drivers SQL, por isso são comparações de caminho completo. Os tempos de checagem e compilação se sobrepõem e não devem ser somados. As observações lentas foram mantidas. E6 inclui codificação e decodificação; usa uma sessão, preparação separada, armazenamento volátil e GPU sem clock fixo. NumPy 2.5.4 valida os oráculos; driver e NVRTC vêm dos artefatos registrados. Os dados são os experimentos retidos.',
 sources:[sources.evidence,sources.artifact]
}
];
window.JAYDB2_SLIDES=slides;
