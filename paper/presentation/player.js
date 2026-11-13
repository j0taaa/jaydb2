'use strict';
(() => {
  const $=id=>document.getElementById(id);
  const slides=window.JAYDB2_SLIDES;
  const mainCount=slides.filter(s=>!s.backup).length;
  let current=0,revealed=0;
  const sections=slides.map((s,i)=>{
    const el=document.createElement('section');
    el.className='slide '+(s.theme||'');el.id='slide-'+s.id;
    el.setAttribute('aria-label',(s.backup?'Apêndice: ':'Slide '+(i+1)+': ')+s.title);
    el.hidden=true;
    if(s.theme?.includes('cover'))el.style.backgroundImage='url("assets/verification-gate.webp")';
    el.innerHTML=s.html+`<div class="bottom"><span class="source">${s.bottom||''}</span><span class="slide-number">${s.backup?'A'+(i-mainCount+1):String(i+1).padStart(2,'0')+' / '+mainCount}</span></div>`;
    $('canvas').append(el);return el;
  });
  const maxStep=()=>Math.max(0,...[...sections[current].querySelectorAll('[data-step]')].map(el=>Number(el.dataset.step)));
  const resize=()=>{$('canvas').style.setProperty('--deck-scale',$('viewport').getBoundingClientRect().width/1600);};
  new ResizeObserver(resize).observe($('viewport'));
  window.addEventListener('resize',resize);
  const optionGroups=[document.createElement('optgroup'),document.createElement('optgroup')];
  optionGroups[0].label='Defesa';optionGroups[1].label='Perguntas';
  slides.forEach((s,i)=>{
    optionGroups[s.backup?1:0].append(new Option((s.backup?'A'+(i-mainCount+1):String(i+1).padStart(2,'0'))+' · '+s.title,String(i)));
    const b=document.createElement('button');b.type='button';
    const n=document.createElement('span');n.textContent=s.backup?'A'+(i-mainCount+1):String(i+1).padStart(2,'0');
    b.append(n,document.createTextNode(s.title));
    b.onclick=()=>{$('overview').close();show(i,0);};$('overview-list').append(b);
  });
  $('slide-select').append(...optionGroups);
  function update(){
    const s=slides[current];
    sections[current].querySelectorAll('[data-step]').forEach(el=>{
      const visible=Number(el.dataset.step)<=revealed;el.classList.toggle('shown',visible);el.setAttribute('aria-hidden',String(!visible));
    });
    $('slide-select').value=current;
    $('counter').textContent=s.backup?'A'+(current-mainCount+1)+' / '+(slides.length-mainCount):(current+1)+' / '+mainCount;
    $('previous').disabled=current===0&&revealed===0;
    $('next').disabled=(current===mainCount-1||current===slides.length-1)&&revealed===maxStep();
    $('step-indicator').textContent=maxStep()&&revealed<maxStep()?'Avançar revela a próxima etapa':'';
    $('progress').setAttribute('aria-valuemax',String(mainCount));
    $('progress').setAttribute('aria-valuenow',String(Math.min(current+1,mainCount)));
    $('progress-fill').style.width=(Math.min(current+1,mainCount)/mainCount*100)+'%';
    $('notes-title').textContent=(s.backup?'Apêndice':'Slide '+(current+1))+' · '+s.title;
    const elapsed=slides.slice(0,current).reduce((a,t)=>a+(t.backup?0:t.seconds),0);
    $('note-meta').textContent=s.backup?'Material para perguntas. Fora do tempo planejado da defesa.':'Tempo sugerido: '+s.seconds+' s · início previsto em '+Math.floor(elapsed/60)+':'+String(elapsed%60).padStart(2,'0');
    $('notes-text').textContent=s.notes;
    $('notes-sources').replaceChildren(...s.sources.map(source=>{const a=document.createElement('a');a.href=source.url;a.textContent=source.label;a.target='_blank';a.rel='noopener';return a;}));
    $('announcement').textContent=(s.backup?'Apêndice. ':'Slide '+(current+1)+' de '+mainCount+'. ')+s.title;
    try{history.replaceState(null,'','#'+s.id);}catch{}
    resize();
    if(window.parent!==window) window.parent.postMessage({type:'jaydb2:slide',index:current},location.origin==='null'?'*':location.origin);
  }
  function show(index,step=0){
    sections[current].hidden=true;current=Math.max(0,Math.min(slides.length-1,index));revealed=step;
    sections[current].hidden=false;update();
  }
  function next(){if(revealed<maxStep()){revealed++;update();}else if(current!==mainCount-1&&current<slides.length-1)show(current+1);}
  function previous(){if(revealed>0){revealed--;update();}else if(current>0){show(current-1);revealed=maxStep();update();}}
  function notes(){const visible=$('notes').hidden;$('notes').hidden=!visible;$('notes-toggle').setAttribute('aria-expanded',String(visible));}
  function overview(){if($('overview').open)$('overview').close();else $('overview').showModal();}
  async function fullscreen(){try{if(document.fullscreenElement)await document.exitFullscreen();else if($('player').requestFullscreen)await $('player').requestFullscreen();else $('announcement').textContent='O navegador não oferece tela cheia.';}catch{$('announcement').textContent='Não foi possível ativar a tela cheia neste navegador.';}}
  $('next').onclick=next;$('previous').onclick=previous;
  $('slide-select').onchange=e=>show(Number(e.target.value));
  $('notes-toggle').onclick=notes;$('overview-open').onclick=overview;
  $('overview-close').onclick=()=>$('overview').close();
  $('fullscreen').onclick=fullscreen;$('print').onclick=()=>window.print();
  document.addEventListener('fullscreenchange',()=>{$('fullscreen').textContent=document.fullscreenElement?'Sair da tela cheia':'Tela cheia';resize();});
  document.addEventListener('keydown',e=>{
    if(e.altKey||e.ctrlKey||e.metaKey||/INPUT|SELECT|TEXTAREA/.test(e.target.tagName))return;
    if($('overview').open)return;
    const key=e.key.toLowerCase();
    if(['arrowright','pagedown',' '].includes(key)){if(e.target.tagName==='BUTTON'&&key===' ')return;e.preventDefault();next();}
    else if(['arrowleft','pageup'].includes(key)){e.preventDefault();previous();}
    else if(key==='home'){e.preventDefault();show(0);}
    else if(key==='end'){e.preventDefault();show(mainCount-1);}
    else if(key==='n')notes();else if(key==='f')fullscreen();else if(key==='o')overview();
  });
  window.addEventListener('hashchange',()=>{const i=slides.findIndex(s=>s.id===location.hash.slice(1));if(i>=0)show(i);});
  const hash=location.hash.slice(1),initial=slides.findIndex(s=>s.id===hash);show(initial<0?0:initial);
  window.JAYDB2_PLAYER={show,next,previous,get state(){return{current,revealed,mainCount,total:slides.length};}};
})();
