#!/usr/bin/env python3
"""Derive combined tables and figures from the three validated benchmark runs."""
import argparse
import hashlib
from html import escape
import json
import math
from pathlib import Path
import statistics
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'experiments/database-comparison'))
from compare import load_manifest, compare

WORKLOADS = ['point_read','point_update','two_row_transaction','scan_sum','relationship_join']
LABELS = ['Point read','Point update','Two-row transaction','SUM','JOIN']

def derive(paths):
    ms = [load_manifest(p)[0] for p in paths]
    for m in ms:
        assert m['status']=='passed' and len(m['results'])==30
    assert [m['settings'].get('profile','legacy') for m in ms] == ['legacy','legacy','single-call-queries-v1'], 'Expected baseline, unchanged-workload engine run and labelled query profile'
    compare(paths[0],paths[1],engines=['jaydb2'])
    compare(paths[0],paths[2],engines=['jaydb2'],allow_workload_change=True)
    indexes=[{(r['scenario'],r['engine']):r for r in m['results']} for m in ms]
    hashes={}
    for s in ms[0]['scenario_sha256']:
        hs={i[s,e]['final_data_sha256'] for i in indexes for e in ['jaydb2','postgresql','sqlite']}
        assert len(hs)==1,(s,hs)
        hashes[s]=next(iter(hs))
    aggregate=[]
    for label,m in zip(['baseline','engine','query'],ms):
        for e in ['jaydb2','postgresql','sqlite']:
            records=[r for r in m['results'] if r['engine']==e]
            for w in WORKLOADS:
                xs=[r['summary'][w]['median_ns']/1e6 for r in records if w in r['summary']]
                aggregate.append(dict(run=label,engine=e,workload=w,scenarios=len(xs),median_ms=statistics.median(xs),min_ms=min(xs),max_ms=max(xs)))
    speeds=[]
    for name,index in zip(['engine','query'],indexes[1:]):
        for w in WORKLOADS:
            pairs=[(indexes[0][s,'jaydb2']['summary'][w]['median_ns'],index[s,'jaydb2']['summary'][w]['median_ns']) for s in ms[0]['scenario_sha256'] if w in index[s,'jaydb2']['summary']]
            ratios=[b/c for b,c in pairs]
            speeds.append(dict(run=name,workload=w,scenarios=len(pairs),median_paired_speedup=statistics.median(ratios),min_paired_speedup=min(ratios),max_paired_speedup=max(ratios),slower_count=sum(c>b for b,c in pairs)))
    rivals=[]
    for name,index in zip(['engine','query'],indexes[1:]):
        for rival in ['postgresql','sqlite']:
            for w in WORKLOADS:
                pairs=[(s,index[s,'jaydb2']['summary'][w]['median_ns'],index[s,rival]['summary'][w]['median_ns']) for s in ms[0]['scenario_sha256'] if w in index[s,'jaydb2']['summary']]
                ratios=[j/r for _,j,r in pairs]
                rivals.append(dict(run=name,rival=rival,workload=w,scenarios=len(pairs),jay_wins=sum(j<r for _,j,r in pairs),median_paired_jay_over_rival=statistics.median(ratios),min_paired_jay_over_rival=min(ratios),max_paired_jay_over_rival=max(ratios)))
    setup=[]
    resources=[]
    for name,m in zip(['baseline','engine','query'],ms):
        for e in ['jaydb2','postgresql','sqlite']:
            records=[r for r in m['results'] if r['engine']==e]
            rss=[r['memory']['observed_peak_tree_rss_bytes']/2**20 for r in records]
            resources.append(dict(run=name,engine=e,median_observed_peak_tree_rss_mib=statistics.median(rss),min_observed_peak_tree_rss_mib=min(rss),max_observed_peak_tree_rss_mib=max(rss),median_live_storage_kib=statistics.median(r['storage_bytes_live']/1024 for r in records),median_closed_storage_kib=statistics.median(r['storage_bytes_closed']/1024 for r in records),memory_scope=records[0]['memory_scope']))
            for key in ['create_schema_and_client_ns','populate_ns','reopen_and_client_prepare_ns']:
                xs=[r[key]/1e6 for r in m['results'] if r['engine']==e]
                setup.append(dict(run=name,engine=e,metric=key,median_ms=statistics.median(xs),min_ms=min(xs),max_ms=max(xs)))
    return dict(aggregation='Unweighted median of per-scenario sample medians. Speedups are medians of paired scenario ratios; no composite score.',sources=[dict(path=str(p),sha256=hashlib.sha256(Path(p).read_bytes()).hexdigest(),git_head=m['git_head'],profile=m['settings'].get('profile','legacy'),hardware=m['hardware']) for p,m in zip(paths,ms)],matching_final_data_sha256=hashes,aggregate=aggregate,speedups=speeds,rivals=rivals,setup=setup,resources=resources)

def charts(output,d):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.ticker import FuncFormatter
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'svg.hashsalt':'jaydb2-performance-followup'})
    indexed={(x['run'],x['engine'],x['workload']):x['median_ms'] for x in d['aggregate']}
    fig,axs=plt.subplots(2,1,figsize=(11.8,8.0),layout='constrained')
    series=[('baseline','jaydb2','JayDB2 baseline','#888888'),('engine','jaydb2','JayDB2 engine change','#475bd6'),('query','jaydb2','JayDB2 + single-call profile','#7f44b5')]
    for j,(run,e,label,color) in enumerate(series):
        axs[0].bar([x+(j-1)*.24 for x in range(5)],[indexed[run,e,w] for w in WORKLOADS],width=.22,label=label,color=color)
    for j,(run,e,label,color) in enumerate([('query','jaydb2','JayDB2 + single-call profile','#7f44b5'),('query','postgresql','PostgreSQL','#087f8c'),('query','sqlite','SQLite','#c4780c')]):
        axs[1].bar([x+(j-1)*.24 for x in range(5)],[indexed[run,e,w] for w in WORKLOADS],width=.22,label=label,color=color)
    for ax,title in zip(axs,['Same JayDB2 engine workload; application profile shown separately','Single-call application profile compared with real SQL engines']):
        ax.set_yscale('log');ax.set_ylabel('Median of scenario medians (ms, log scale)');ax.set_title(title,loc='left',fontweight='bold');ax.grid(axis='y',alpha=.25);ax.set_axisbelow(True);ax.spines[['top','right']].set_visible(False);ax.yaxis.set_major_formatter(FuncFormatter(lambda x,_:f'{x:g}'));ax.set_xticks(range(5),LABELS);ax.legend(frameon=False,fontsize=9)
    fig.suptitle('Measured performance without changing durability or logical limits',fontsize=14)
    fig.text(.5,.002,'7 checked samples + 1 warmup; 10 scenarios (9 JOINs); 8 rows/table; one client. Setup excluded and reported separately.',ha='center',fontsize=9)
    for suffix in ['svg','png']:
        fig.savefig(output/f'comparison.{suffix}',dpi=180,metadata={'Date':None} if suffix=='svg' else None)
    plt.close(fig)

def html_chart(output,d):
    ix={(x['run'],x['engine'],x['workload']):x['median_ms'] for x in d['aggregate']}
    series=[('baseline','jaydb2','JayDB2 baseline'),('engine','jaydb2','JayDB2 engine change'),
            ('query','jaydb2','JayDB2 single-call profile'),('query','postgresql','PostgreSQL'),('query','sqlite','SQLite')]
    values=[ix[r,e,w] for r,e,_ in series for w in WORKLOADS]
    lo,hi=math.floor(math.log10(min(values))),math.ceil(math.log10(max(values)))
    y=lambda v: 30+(hi-math.log10(v))*260/(hi-lo)
    parts=['<svg viewBox="0 0 1000 350" role="img" aria-label="Median latency across five workflows; lower is faster">']
    for n in range(lo,hi+1):
        py=y(10**n)
        parts.append(f'<path class="grid" d="M76,{py:.2f}H985"/><text x="65" y="{py+4:.2f}" text-anchor="end">{10**n:g}</text>')
    parts.append('<text x="76" y="15">Milliseconds · logarithmic scale · lower is faster</text>')
    for wi,(w,label) in enumerate(zip(WORKLOADS,LABELS)):
        cx=76+(wi+.5)*909/5
        parts.append(f'<text x="{cx:.2f}" y="320" text-anchor="middle">{escape(label)}</text>')
        for si,(r,e,name) in enumerate(series):
            v=ix[r,e,w];px=cx+(si-2)*22;py=y(v)
            parts.append(f'<rect class="s{si}" x="{px-9:.2f}" y="{py:.2f}" width="18" height="{290-py:.2f}"><title>{escape(name)} · {escape(label)}: {v:.6g} ms</title></rect>')
    parts.append('</svg>')
    styles=''.join(f'.s{i}{{fill:var(--chart-{i+1});background:var(--chart-{i+1})}}' for i in range(5))
    legend=''.join(f'<span><i class="s{i}"></i>{escape(label)}</span>' for i,(_,_,label) in enumerate(series))
    html='''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>JayDB2 performance follow-up</title><style>
    *{box-sizing:border-box}body{margin:0;padding:0;color:var(--foreground);font:14px/1.5 var(--font-sans),sans-serif}main{margin:0}figure{margin:0}figcaption{font-size:18px;font-weight:650;margin-bottom:12px}.legend{display:flex;flex-wrap:wrap;gap:7px 18px;font-size:12px}.legend span{display:flex;align-items:center;gap:6px}.legend i{display:inline-block;width:9px;height:9px;border-radius:50%}svg{display:block;width:100%;height:350px}svg text{fill:var(--muted-foreground);font:13px var(--font-sans),sans-serif}.grid{stroke:var(--border);stroke-dasharray:3 4;fill:none}.note{color:var(--muted-foreground);font-size:12px;margin:8px 0 0}
    '''+styles+'</style><main><figure><figcaption>Measured latency across the ten databases</figcaption><div class="legend">'+legend+'</div>'+''.join(parts)+'''</figure><p class="note">Unweighted median of each scenario’s seven checked sample medians; one warmup, one client, durable storage, eight rows/table. JOIN covers nine scenarios; other workloads cover ten. Program preparation is excluded here and reported separately.</p><p class="note">The engine comparison keeps the original access strategy. The single-call profile changes the application: generic SUM/JOIN each run in one transaction, and certified point reads reuse a durable root. SQL values are from the same profile run. Bar titles show exact values.</p></main></html>'''
    (output/'charts.html').write_text(html)

def main():
    p=argparse.ArgumentParser();p.add_argument('baseline',type=Path);p.add_argument('engine',type=Path);p.add_argument('query',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    d=derive([a.baseline,a.engine,a.query]);a.output.mkdir(parents=True,exist_ok=False);(a.output/'combined-analysis.json').write_text(json.dumps(d,indent=2,sort_keys=True)+'\n');charts(a.output,d);html_chart(a.output,d)
    ix={(r['run'],r['engine'],r['workload']):r for r in d['aggregate']};sx={(r['run'],r['workload']):r for r in d['speedups']}
    lines=['| Workload | Jay baseline ms | Jay engine ms | Paired speedup | Jay single-call ms | Paired speedup | PostgreSQL ms | SQLite ms |','| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |']
    for w,l in zip(WORKLOADS,LABELS):
        lines.append(f"| {l} | {ix['baseline','jaydb2',w]['median_ms']:.3f} | {ix['engine','jaydb2',w]['median_ms']:.3f} | {sx['engine',w]['median_paired_speedup']:.2f}× | {ix['query','jaydb2',w]['median_ms']:.3f} | {sx['query',w]['median_paired_speedup']:.2f}× | {ix['query','postgresql',w]['median_ms']:.4f} | {ix['query','sqlite',w]['median_ms']:.4f} |")
    (a.output/'latency-table.md').write_text('\n'.join(lines)+'\n');print('\n'.join(lines))
if __name__=='__main__': main()
