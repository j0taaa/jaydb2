// BendTT output syntax. Every binder gets a fresh level; J reserves
// its endpoint and evidence levels together. No changes to the kernel.
export class Syntax {
  constructor(start = 20000) { this.next = start; }
  fresh() { const n = this.next; this.next += 2; return n; }
}
export const V = l => ({ $: 'Var', l });
export const R = k => ({ $: 'Ref', k });
export const lab = k => ({ $: 'Lab', k });
export const K = q => ({ $: 'Typ', q: typeof q === 'number' ? lab('Q' + q) : q });
export const UT = { $: 'Enu', ks: ['()'] }, UV = lab('()');
export const all = (q,l,A,B) => ({ $: 'All', q,l,A,B });
export const sig = (q,l,A,B) => ({ $: 'Sig', q,l,A,B });
export const lam = (q,l,f) => ({ $: 'Lam', q,l,f });
export const app = (f,x,q=1) => ({ $: 'App', q,f,x });
export const apps = (f,xs) => xs.reduce((f,[q,x])=>app(f,x,q),f);
export const tup = (q,a,b) => ({ $: 'Tup', q,a,b });
export const tuple = xs => xs.reduceRight((b,[q,a])=>tup(q,a,b),UV);
export const bind = (tag,bs,b) => bs.reduceRight((b,[q,l,A])=>tag === 'Lam' ? lam(q,l,b) : ({ $:tag,q,l,A,B:b }),b);
export const prj = h => ({ $: 'Prj', h });
export const mats = xs => xs.reduceRight((m,[k,h])=>({ $:'Mat',k,h,m }), { $:'Efq' });
export const unit = x => mats([['()',x]]);
export const ann = (x,T) => ({ $:'Ann',x,T });
export const eq = (a,b,T) => ({ $:'Eql',a,b,T });
export const rfl = { $:'Rfl' };
export const let1 = (l,v,f) => ({ $:'Let',q:1,l,v,f });
export const rwt = (e,l,P,f) => ({ $:'Rwt',e,l,P,f });
export function split(bs,body) {
  return bs.reduceRight((h,[q,l])=>prj(lam(q,l,h)),unit(body));
}
export function show(o) {
  const v = l => 'r'+l, q = n => n===0?'-':n===2?'+':'';
  switch (o.$) {
    case 'Ref': return o.k;
    case 'Var': return v(o.l);
    case 'Enu': return '<'+o.ks.join(', ')+'>';
    case 'Lab': return o.k==='()'?'()':'.'+o.k;
    case 'Typ': return '*('+show(o.q)+')';
    case 'Min': return '('+show(o.a)+' <&> '+show(o.b)+')';
    case 'All': case 'Sig': return (o.$==='All'?'∀':'Σ')+q(o.q)+v(o.l)+' : '+show(o.A)+' -> '+show(o.B);
    case 'Lam': return 'λ'+q(o.q)+v(o.l)+' => '+show(o.f);
    case 'App': return '('+show(o.f)+' '+q(o.q)+show(o.x)+')';
    case 'Tup': return '('+q(o.q)+show(o.a)+', '+show(o.b)+')';
    case 'Prj': return 'λ{(,): '+show(o.h)+'}';
    case 'Mat': return 'λ{'+(o.k==='()'?'()':'.'+o.k)+': '+show(o.h)+'; '+show(o.m)+'}';
    case 'Efq': return 'λ{}';
    case 'Eql': return '{'+show(o.a)+' == '+show(o.b)+' : '+show(o.T)+'}';
    case 'Rfl': return '{==}';
    case 'Ann': return '{'+show(o.x)+' : '+show(o.T)+'}';
    case 'Let': return '!'+q(o.q)+v(o.l)+' = '+show(o.v)+'; '+show(o.f);
    case 'Rwt': return '%'+show(o.e)+' : '+v(o.l)+', '+v(o.l+1)+' => '+show(o.P)+'; '+show(o.f);
    default: throw new Error('Unsupported structural O node: '+o.$);
  }
}
export const declarationsText = ds => ds.map(([k,T,b])=>k+' : '+show(T)+' =\n  '+show(b)).join('\n\n')+'\n';
