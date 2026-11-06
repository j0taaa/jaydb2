#!/usr/bin/env python3
"""Derive retained evidence and charts from a complete 30-database experiment.

Usage: build/database-comparison-analysis-venv/bin/python \
  build/database-comparison-analysis/generate.py build/database-comparison-final/result.json

Incomplete, fatal, duplicate, unchecked, or statistically inconsistent runs are
rejected before writing evidence. Completed engine failures are retained as
feasibility findings and receive no timing summaries. No service is started here.
"""
from __future__ import annotations

import argparse
import csv
from datetime import datetime
import hashlib
from html import escape
import json
import math
from pathlib import Path
import re
import statistics

ROOT = Path(__file__).resolve().parents[2]
ENGINES = ('jaydb2', 'postgresql', 'sqlite')
LABELS = {'jaydb2': 'JayDB2', 'postgresql': 'PostgreSQL', 'sqlite': 'SQLite'}
COLORS = {'jaydb2': '#475bd6', 'postgresql': '#087f8c', 'sqlite': '#c4780c'}
WORKLOADS = ('point_read', 'point_update', 'two_row_transaction', 'scan_sum', 'relationship_join')
WORKLOAD_LABELS = {'point_read': 'Point read', 'point_update': 'Point update',
                   'two_row_transaction': 'Two-row transaction', 'scan_sum': 'Whole-table SUM',
                   'relationship_join': 'Relationship JOIN'}
TABLE_COUNTS = [1, 3, 5, 8, 10, 12, 15, 18, 22, 26]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def save(path, data):
    path.write_text(json.dumps(data, indent=2, sort_keys=True, ensure_ascii=False) + '\n')


def public_manifest(value):
    """Retain full records, hashes and samples; omit any embedded patch bodies.

    Current runner stores patches in separate files, not in result.json. Reject
    unexpected secrets instead of publishing redacted data as if it were raw.
    Local trust-authenticated PostgreSQL socket DSNs contain no password.
    """
    if isinstance(value, dict):
        result = {}
        for key, child in value.items():
            lowered = key.lower()
            require(not (lowered in {'password', 'api_key', 'access_token', 'secret', 'secret_key'} and child),
                    f'Refusing to publish secret-bearing key {key!r}')
            if 'patch' in lowered and isinstance(child, str) and len(child) > 50000 and 'sha' not in lowered:
                continue
            result[key] = public_manifest(child)
        return result
    if isinstance(value, list):
        return [public_manifest(v) for v in value]
    if isinstance(value, str):
        require(not re.search(r'\bpassword\s*=', value, re.I), 'Refusing a password-bearing connection string')
    return value


def spread(values, unit):
    xs = list(values)
    return {'n_scenarios': len(xs), 'aggregation': 'Median, minimum and maximum of one value per scenario',
            'unit': unit, 'median': statistics.median(xs) if xs else None,
            'min': min(xs) if xs else None, 'max': max(xs) if xs else None}


def load_checked(path, scenario_dir=None):
    raw = path.read_bytes()
    manifest = json.loads(raw)
    require(manifest.get('status') in ('passed', 'failed'), 'Only a completed manifest can generate report evidence')
    require(bool(manifest.get('finished_utc')), 'Run must have a recorded finish time')
    require(not manifest.get('error'), 'Top-level fatal errors must be resolved before generating evidence')
    records = manifest.get('results', [])
    require(len(records) == 30, 'Expected exactly 30 engine/scenario records')
    require(all(r.get('status') in ('passed', 'failed') for r in records), 'Every engine/scenario record must be complete')
    require(manifest['status'] != 'passed' or all(r['status'] == 'passed' for r in records),
            'Passed manifest contains failed engine records')
    settings = manifest['settings']
    n, warmups = settings['samples'], settings['warmups']
    require(type(n) is int and n >= 2, 'Need at least two real samples per workload')
    require(type(warmups) is int and warmups >= 0, 'Invalid warmup count')
    require(set(settings['engines']) == set(ENGINES), 'Expected all three real engines')
    scenarios = sorted({r['scenario'] for r in records})
    require(len(scenarios) == 10, 'Expected exactly ten scenarios')
    by_pair = {(r['scenario'], r['engine']): r for r in records}
    require(set(by_pair) == {(s, e) for s in scenarios for e in ENGINES}, 'Missing or duplicate engine/scenario record')
    specs_dir = scenario_dir or path.parent / 'suite' / 'scenarios'
    specs = {}
    rows = []
    for index, scenario in enumerate(scenarios):
        spec_bytes = (specs_dir / f'{scenario}.json').read_bytes()
        require(sha(spec_bytes) == manifest['scenario_sha256'][scenario], f'Scenario source hash differs: {scenario}')
        spec = json.loads(spec_bytes)
        require(spec['id'] == scenario, f'Scenario identity mismatch: {scenario}')
        require(len(spec['tables']) == TABLE_COUNTS[index], f'Unexpected table count for {scenario}')
        require(all(len(t['rows']) == 8 for t in spec['tables']), f'Unexpected fixture size for {scenario}')
        specs[scenario] = spec
        expected_workloads = set(WORKLOADS if spec['join'] else WORKLOADS[:-1])
        for engine in ENGINES:
            record = by_pair[scenario, engine]
            if record['status'] == 'failed':
                continue
            require(set(record['summary']) == expected_workloads, f'Missing or extra workload: {scenario}/{engine}')
            require(all(sample.get('checked') is True and sample['actual'] == sample['expected']
                        for sample in record['samples']), f'Unchecked or incorrect sample: {scenario}/{engine}')
            for workload in WORKLOADS:
                if workload not in expected_workloads:
                    continue
                samples = [s for s in record['samples'] if s['workload'] == workload and s['phase'] == 'sample']
                warm = [s for s in record['samples'] if s['workload'] == workload and s['phase'] == 'warmup']
                require(len(samples) == n and len(warm) == warmups, f'Sample count differs: {scenario}/{engine}/{workload}')
                require(all(type(s['elapsed_ns']) is int and s['elapsed_ns'] > 0 for s in samples), 'Invalid elapsed time')
                xs = [s['elapsed_ns'] for s in samples]
                median = statistics.median(xs)
                p95 = sorted(xs)[max(0, math.ceil(.95 * len(xs)) - 1)]
                mad = statistics.median(abs(x - median) for x in xs)
                summary = record['summary'][workload]
                for key, value in [('n', n), ('median_ns', median), ('p95_ns', p95), ('min_ns', min(xs)), ('max_ns', max(xs)), ('mad_ns', mad)]:
                    require(summary[key] == value, f'Stored summary does not match raw samples: {scenario}/{engine}/{workload}/{key}')
                rows.append({'scenario': scenario, 'title': spec['title'], 'tables': len(spec['tables']),
                             'rows_per_table': 8, 'engine': engine, 'workload': workload, 'samples': n,
                             'median_ms': median / 1e6, 'p95_sample_nearest_rank_ms': p95 / 1e6,
                             'min_ms': min(xs) / 1e6, 'max_ms': max(xs) / 1e6, 'mad_ms': mad / 1e6,
                             'create_schema_and_client_ms': record['create_schema_and_client_ns'] / 1e6,
                             'populate_ms': record['populate_ns'] / 1e6,
                             'reopen_and_client_prepare_ms': record['reopen_and_client_prepare_ns'] / 1e6,
                             'storage_bytes_live': record['storage_bytes_live'],
                             'storage_bytes_closed': record.get('storage_bytes_closed', ''),
                             'observed_peak_tree_rss_bytes': record['memory']['observed_peak_tree_rss_bytes'],
                             'memory_scope': record['memory_scope']})
    return manifest, raw, scenarios, specs, by_pair, rows


def analyze(manifest, raw, scenarios, specs, by_pair, rows):
    analysis = {
        'source_result_sha256': sha(raw), 'source_result_path': manifest['output'] + '/result.json',
        'aggregation': 'One median per engine/scenario/workload, then an unweighted median across scenarios; never pooled requests',
        'scenario_count': 10, 'database_count': 30, 'attempted_tables_per_engine': sum(TABLE_COUNTS),
        'passed_database_count': sum(r['status'] == 'passed' for r in by_pair.values()),
        'failed_database_count': sum(r['status'] == 'failed' for r in by_pair.values()),
        'failures': [{'scenario': r['scenario'], 'engine': r['engine'], 'error': r.get('error', r.get('close_error', 'Unspecified engine failure'))}
                     for r in by_pair.values() if r['status'] == 'failed'],
        'attempted_seed_rows_per_engine': 8 * sum(TABLE_COUNTS), 'samples_per_workload_per_database': manifest['settings']['samples'],
        'warmups_per_workload_per_database': manifest['settings']['warmups'],
        'workload_note': 'SQL SUM/JOIN are one native query; JayDB2 uses 9/17 prepared service requests for these eight-row client workflows. Point operations and two-row transactions each use one service request.',
        'scope_notes': [
            'Feasibility-sized synthetic fixtures: eight rows per table, with schema complexity varied; not a row-count scaling study.',
            'One client, durable writes, warmed caches and prepared JayDB2 programs; setup/preparation excluded from workload samples.',
            'Successful scenario medians are equally weighted. Relationship JOIN has up to nine scenarios; the single-table project has no join. Completed failures are retained but have no timing values.',
            'Sample p95 is nearest-rank over the small measured sample set, not a reliable population tail estimate.',
            'RSS scopes differ; summed RSS double-counts shared pages and 10 ms sampling may miss peaks. SQLite includes the Python harness.',
            'Storage scopes differ: PostgreSQL catalogs, live SQLite WAL/SHM, and JayDB2 snapshot storage exclude/include different overheads.',
            'Schema/client setup excludes initial PostgreSQL cluster startup but includes JayDB2 startup and certified-program compilation.',
        ], 'engines': {}, 'relative_workflow_latency_ratios': {},
        'scenarios': [{'id': s, 'title': specs[s]['title'], 'tables': len(specs[s]['tables']),
                       'seed_rows': 8 * len(specs[s]['tables'])} for s in scenarios],
    }
    if manifest.get('finished_utc') and manifest.get('started_utc'):
        analysis['run_wall_seconds'] = (datetime.fromisoformat(manifest['finished_utc']) - datetime.fromisoformat(manifest['started_utc'])).total_seconds()
    for engine in ENGINES:
        engine_rows = [r for r in rows if r['engine'] == engine]
        records = [by_pair[s, engine] for s in scenarios if by_pair[s, engine]['status'] == 'passed']
        entry = {'workloads': {}, 'n_passed_scenarios': len(records), 'n_failed_scenarios': len(scenarios)-len(records),
                 'successful_seed_rows': sum(8*len(specs[r['scenario']]['tables']) for r in records),
                 'successful_tables': sum(len(specs[r['scenario']]['tables']) for r in records)}
        for workload in WORKLOADS:
            values = [r['median_ms'] for r in engine_rows if r['workload'] == workload]
            entry['workloads'][workload] = {
                'n_scenarios': len(values), 'aggregation': 'Median of per-scenario workload medians', 'unit': 'ms',
                'median_of_scenario_medians_ms': statistics.median(values) if values else None,
                'min_scenario_median_ms': min(values) if values else None, 'max_scenario_median_ms': max(values) if values else None,
            }
        for key in ['create_schema_and_client_ns', 'populate_ns', 'reopen_and_client_prepare_ns']:
            entry[key.removesuffix('_ns') + '_ms'] = spread((r[key] / 1e6 for r in records), 'ms')
        entry['storage_bytes_live'] = spread((r['storage_bytes_live'] for r in records), 'bytes')
        if records and all('storage_bytes_closed' in r for r in records):
            entry['storage_bytes_closed'] = spread((r['storage_bytes_closed'] for r in records), 'bytes')
        entry['observed_peak_tree_rss_bytes'] = spread((r['memory']['observed_peak_tree_rss_bytes'] for r in records), 'bytes')
        entry['memory_scope'] = records[0]['memory_scope'] if records else None
        entry['duplicate_id_behavior'] = sorted({r['checks']['duplicate_id']['behavior'] for r in records})
        entry['foreign_key_behavior'] = sorted({r['checks']['foreign_key']['behavior'] for r in records if 'foreign_key' in r['checks']})
        if engine == 'jaydb2' and records:
            entry['initial_preparation_ms'] = {key: spread((r['jay_setup'][key] / 1e6 for r in records), 'ms')
                                               for key in records[0]['jay_setup']}
        analysis['engines'][engine] = entry
    indexed = {(r['scenario'], r['engine'], r['workload']): r['median_ms'] for r in rows}
    for denominator in ('postgresql', 'sqlite'):
        comparison = {}
        for workload in WORKLOADS:
            ratios = [indexed[s, 'jaydb2', workload] / indexed[s, denominator, workload]
                      for s in scenarios if (s, 'jaydb2', workload) in indexed and (s, denominator, workload) in indexed]
            comparison[workload] = spread(ratios, 'dimensionless ratio of paired scenario medians')
        analysis['relative_workflow_latency_ratios']['jaydb2_over_' + denominator] = comparison
    return analysis


def matplotlib_charts(output, manifest, scenarios, specs, rows, analysis):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.ticker import FuncFormatter
    plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10, 'svg.hashsalt': 'jaydb2-database-comparison'})
    indexed = {(r['scenario'], r['engine'], r['workload']): r['median_ms'] for r in rows}
    fig, axes = plt.subplots(2, 1, figsize=(11.8, 7.4), sharex=True, layout='constrained')
    for axis, workload in zip(axes, WORKLOADS[:2], strict=True):
        for engine in ENGINES:
            axis.plot(range(10), [indexed.get((s, engine, workload), float('nan')) for s in scenarios], marker='o',
                      linewidth=1.8, markersize=4.5, label=LABELS[engine], color=COLORS[engine])
        axis.set_yscale('log')
        axis.set_ylabel('Median latency (ms, log scale)')
        axis.set_title(WORKLOAD_LABELS[workload], loc='left', fontweight='bold')
        axis.grid(axis='y', which='major', alpha=.25)
        axis.spines[['top', 'right']].set_visible(False)
        axis.yaxis.set_major_formatter(FuncFormatter(lambda x, pos: f'{x:g}'))
    if not rows:
        for axis in axes:
            axis.set_axis_off()
            axis.text(.5, .5, 'No successful timing records', transform=axis.transAxes, ha='center')
    axes[0].legend(ncol=3, loc='upper left', bbox_to_anchor=(.58, 1.18), frameon=False)
    axes[-1].set_xticks(range(10), [f'{i+1:02}\n{len(specs[s]["tables"])} tables' for i, s in enumerate(scenarios)])
    axes[-1].set_xlabel('Scenario number and schema size — eight rows per table')
    fig.suptitle(f'Point-operation medians across ten application databases\n{manifest["settings"]["samples"]} measured samples per point, {manifest["settings"]["warmups"]} warmup; {analysis["failed_database_count"]} failed databases omitted', fontsize=13)
    fig.savefig(output / 'latency.svg', metadata={'Date': None})
    fig.savefig(output / 'latency.png', dpi=180)
    plt.close(fig)

    fig, axis = plt.subplots(figsize=(11.8, 5.1), layout='constrained')
    for i, engine in enumerate(ENGINES):
        axis.bar([x + (i-1)*.24 for x in range(5)],
                 [analysis['engines'][engine]['workloads'][w]['median_of_scenario_medians_ms'] if analysis['engines'][engine]['workloads'][w]['median_of_scenario_medians_ms'] is not None else float('nan') for w in WORKLOADS],
                 width=.22, color=COLORS[engine], label=LABELS[engine])
    if not rows:
        axis.set_axis_off()
        axis.text(.5, .5, 'No successful timing records', transform=axis.transAxes, ha='center')
    axis.set_yscale('log')
    axis.set_ylabel('Median of scenario medians (ms, log scale)')
    axis.set_xticks(range(5), ['Point read\nup to 10 scenarios', 'Point update\nup to 10 scenarios', 'Two-row transaction\nup to 10 scenarios', 'Whole-table SUM\nup to 10 scenarios', 'Relationship JOIN\nup to 9 scenarios'])
    axis.grid(axis='y', which='major', alpha=.25)
    axis.set_axisbelow(True)
    axis.spines[['top', 'right']].set_visible(False)
    axis.yaxis.set_major_formatter(FuncFormatter(lambda x, pos: f'{x:g}'))
    axis.legend(ncol=3, frameon=False, loc='upper left')
    fig.suptitle('Five application workflows — unweighted median of per-scenario medians', fontsize=13)
    fig.text(.5, .005, 'Native SQL SUM/JOIN versus 9/17 prepared JayDB2 service calls; these are client workflow measurements.', ha='center', fontsize=9)
    fig.savefig(output / 'workloads.svg', metadata={'Date': None})
    fig.savefig(output / 'workloads.png', dpi=180)
    plt.close(fig)


def svg_chart(series, labels, title, grouped=False):
    """Theme-aware inline SVG with responsive width and a fixed 300 px height."""
    width, height = 1000, 300
    left, right, top, bottom = 78, 24, 23, 62
    plot_w, plot_h = width-left-right, height-top-bottom
    values = [v for xs in series.values() for v in xs if v is not None]
    if not values:
        return f'<svg viewBox="0 0 {width} {height}" role="img" aria-label="{escape(title)}"><text x="50" y="150">No successful timing records</text></svg>'
    low, high = math.floor(math.log10(min(values))), math.ceil(math.log10(max(values)))
    if high == low:
        high += 1
    y = lambda value: top + (high - math.log10(value)) / (high-low) * plot_h
    x = lambda i: left + (i+.5) * plot_w / len(labels)
    items = [f'<svg viewBox="0 0 {width} {height}" role="img" aria-label="{escape(title)}" xmlns="http://www.w3.org/2000/svg">',
             f'<text class="axis-label" x="{left}" y="13">Latency in milliseconds · logarithmic axis</text>']
    for exponent in range(low, high+1):
        value, py = 10**exponent, y(10**exponent)
        items.append(f'<path class="grid" d="M{left},{py:.2f}H{width-right}"/>')
        items.append(f'<text class="tick" x="{left-10}" y="{py+4:.2f}" text-anchor="end">{value:g}</text>')
    for i, label in enumerate(labels):
        items.append(f'<text class="tick" x="{x(i):.2f}" y="{height-bottom+23}" text-anchor="middle">{escape(label)}</text>')
    for j, engine in enumerate(ENGINES):
        points = [(x(i), y(v)) if v is not None else None for i, v in enumerate(series[engine])]
        if grouped:
            for i, value in enumerate(series[engine]):
                if value is None:
                    continue
                px, py = x(i)+(j-1)*25, y(value)
                items.append(f'<rect class="{engine}" x="{px-10:.2f}" y="{py:.2f}" width="20" height="{top+plot_h-py:.2f}" opacity=".92"><title>{escape(LABELS[engine])}: {escape(labels[i])}, {value:.6g} ms</title></rect>')
        else:
            segments = [[]]
            for point in points:
                if point is None:
                    segments.append([])
                else:
                    segments[-1].append(point)
            for segment in segments:
                points_attr = ' '.join(f'{px:.2f},{py:.2f}' for px,py in segment)
                if points_attr:
                    items.append(f'<polyline class="{engine} line" points="{points_attr}"/>')
            for i, point in enumerate(points):
                if point is None:
                    continue
                px, py = point
                items.append(f'<circle class="{engine}" cx="{px:.2f}" cy="{py:.2f}" r="4"><title>{escape(LABELS[engine])}: {escape(labels[i])}, {series[engine][i]:.6g} ms</title></circle>')
    items.append('</svg>')
    return ''.join(items)


def html_charts(output, manifest, scenarios, specs, rows, analysis):
    indexed = {(r['scenario'], r['engine'], r['workload']): r['median_ms'] for r in rows}
    figures = []
    labels = [f'{i+1:02} · {len(specs[s]["tables"])} tables' for i,s in enumerate(scenarios)]
    for workload in WORKLOADS[:2]:
        title = WORKLOAD_LABELS[workload] + ' by application schema'
        chart = svg_chart({e: [indexed.get((s,e,workload)) for s in scenarios] for e in ENGINES}, labels, title)
        figures.append(f'<figure><figcaption>{escape(title)}</figcaption>{chart}</figure>')
    title = 'Five workflows: median of scenario medians'
    chart = svg_chart({e: [analysis['engines'][e]['workloads'][w]['median_of_scenario_medians_ms'] for w in WORKLOADS] for e in ENGINES},
                      ['Point read', 'Point update', 'Two-row transaction', 'SUM · up to 10', 'JOIN · up to 9'], title, grouped=True)
    figures.append(f'<figure><figcaption>{title}</figcaption>{chart}</figure>')
    legend = ''.join(f'<span><i class="{e}"></i>{LABELS[e]}</span>' for e in ENGINES)
    markup = '''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>JayDB2 database comparison charts</title>
<style>
:root {color-scheme:light dark; --chart-text:var(--foreground); --chart-muted:var(--muted-foreground); --chart-grid:var(--border); --jaydb2:var(--chart-1); --postgresql:var(--chart-2); --sqlite:var(--chart-3);}
* {box-sizing:border-box} body {background:transparent;color:var(--chart-text);font:14px/1.5 var(--font-sans),sans-serif;margin:0;padding:0;} main {max-width:1120px;margin:auto;} .legend {display:flex;flex-wrap:wrap;gap:24px;margin:0 0 12px;} .legend span {display:flex;align-items:center;gap:7px;} .legend i {width:10px;height:10px;border-radius:50%;display:inline-block;} .legend .jaydb2 {background:var(--jaydb2)} .legend .postgresql {background:var(--postgresql)} .legend .sqlite {background:var(--sqlite)} figure {margin:18px 0 22px;} figcaption {font-size:17px;font-weight:650;margin:0 0 6px;} svg {display:block;width:100%;height:300px;overflow:visible;} svg text {fill:var(--chart-muted);font:12px system-ui,sans-serif;} svg .axis-label {font-size:11px;} svg .grid {fill:none;stroke:var(--chart-grid);stroke-width:1;stroke-dasharray:3 4;} svg .jaydb2 {fill:var(--jaydb2);stroke:var(--jaydb2);} svg .postgresql {fill:var(--postgresql);stroke:var(--postgresql);} svg .sqlite {fill:var(--sqlite);stroke:var(--sqlite);} svg .line {fill:none;stroke-width:2;} .note {max-width:1000px;color:var(--chart-muted);font-size:13px;margin:9px 0;} @media(max-width:640px){body{padding:0}svg .tick{font-size:11px}.legend{gap:14px}}
</style><main>'''
    markup += f'<div class="legend">{legend}</div><p class="note">{analysis["passed_database_count"]}/30 databases passed; {analysis["failed_database_count"]} failed databases have no timing plotted. {manifest["settings"]["samples"]} checked samples per workload/database after {manifest["settings"]["warmups"]} warmup. One client, durable storage, eight rows per table. Lower latency is faster; each grid step is a tenfold change.</p>'
    markup += ''.join(figures)
    markup += '<p class="note">Point charts show each scenario’s sample median. The workflow chart gives equal weight to each scenario median: up to ten successful scenarios for reads, updates, transactions and SUM; up to nine for JOIN. Exact successful counts are retained per engine in analysis.json. SQL uses native SUM/JOIN; JayDB2 composes 9/17 prepared service calls. These are client workflow timings, with setup and compilation excluded. The multi-request JayDB2 queries do not provide a transaction snapshot under concurrent writes.</p>'
    markup += '<p class="note">Scenario numbers follow the report: tasks, budget, blog, ecommerce, clinic, learning, hotel, logistics, manufacturing and municipal services. These small fixtures compare schema feasibility and measured access paths, not production-scale capacity.</p></main></html>'
    (output / 'charts.html').write_text(markup)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('result', type=Path)
    parser.add_argument('--output', type=Path, default=ROOT / 'experiments/database-comparison/evidence')
    parser.add_argument('--scenario-dir', type=Path, help='Defaults to the recorded run snapshot suite/scenarios')
    args = parser.parse_args()
    manifest, raw, scenarios, specs, records, rows = load_checked(args.result.resolve(), args.scenario_dir)
    public = public_manifest(manifest)
    analysis = analyze(manifest, raw, scenarios, specs, records, rows)
    # All evidence validation precedes any output creation.
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    save(output / 'results.json', public)
    save(output / 'analysis.json', analysis)
    with (output / 'summary.csv').open('w', newline='') as file:
        writer = csv.DictWriter(file, fieldnames=list(rows[0]) if rows else ['scenario', 'engine', 'workload', 'samples', 'median_ms'])
        writer.writeheader()
        writer.writerows(rows)
    matplotlib_charts(output, manifest, scenarios, specs, rows, analysis)
    html_charts(output, manifest, scenarios, specs, rows, analysis)
    print(json.dumps({'status': 'generated', 'source_result_sha256': sha(raw), 'output': str(output),
                      'databases': len(records), 'workload_summaries': len(rows),
                      'files': ['results.json', 'analysis.json', 'summary.csv', 'latency.svg', 'latency.png', 'workloads.svg', 'workloads.png', 'charts.html']}, indent=2))


if __name__ == '__main__':
    main()
