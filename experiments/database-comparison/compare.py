#!/usr/bin/env python3
"""Compare matched benchmark runs without changing fixtures or hiding regressions.

No services start here. Exit 0 means the configured sampled gate passed, 1 means
observed regressions or functional failures exceeded it, and 2 means inputs are
invalid/incompatible. Passing a finite sampled gate never proves no regressions.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
import hashlib
import json
import math
from pathlib import Path
import statistics
import sys

from model import equal

WORKLOADS = {'point_read', 'point_update', 'two_row_transaction', 'scan_sum', 'relationship_join'}
REQUIRED = WORKLOADS - {'relationship_join'}
SETUP = ('create_schema_and_client_ns', 'populate_ns', 'reopen_and_client_prepare_ns')
MEASURED_FILES = {'run.py', 'jay.py', 'sql_engines.py', 'model.py', 'memory.py'}
LEGACY_PROGRAMS = {'Access.bend', 'Batch.bend', 'ReadRow.bend'}
PROFILE_SETTINGS = {'profile', 'profile_metadata'}
REQUIRED_CHECKS = ('full_initial_data_equivalence', 'all_timed_outputs_and_written_cells',
                   'missing_row_returns_none', 'insert_delete_roundtrip', 'full_final_data_after_reopen')


def require(value, message):
    if not value:
        raise ValueError(message)


def positive_number(value):
    return type(value) in (int, float) and math.isfinite(value) and value > 0


def load_manifest(path):
    raw = Path(path).read_bytes()
    m = json.loads(raw)
    require(m.get('status') in ('passed', 'failed') and m.get('finished_utc'), 'Run is incomplete')
    require(not m.get('error'), 'Run has a fatal top-level error; preserve and resolve it before comparison')
    settings = m.get('settings', {})
    n, warmups = settings.get('samples'), settings.get('warmups')
    require(type(n) is int and n >= 2 and type(warmups) is int and warmups >= 0, 'Invalid sample counts')
    engines = settings.get('engines', [])
    require(engines and len(set(engines)) == len(engines), 'Missing/duplicate configured engines')
    scenarios = m.get('scenario_sha256', {})
    require(scenarios and all(isinstance(v, str) and len(v) == 64 for v in scenarios.values()), 'Missing scenario identities')
    records = m.get('results', [])
    pairs = {(r['scenario'], r['engine']): r for r in records}
    require(len(pairs) == len(records), 'Duplicate engine/scenario record')
    require(set(pairs) == {(s, e) for s in scenarios for e in engines}, 'Missing/extra engine/scenario record')
    require(all(r.get('status') in ('passed', 'failed') for r in records), 'Incomplete engine record')
    require(m['status'] != 'passed' or all(r['status'] == 'passed' for r in records), 'Passing manifest hides a failed engine')
    checked = {}
    for pair, record in pairs.items():
        if record['status'] == 'failed':
            continue
        checks = record.get('checks', {})
        require(all(checks.get(k) is True for k in REQUIRED_CHECKS), f'Missing correctness checks: {pair}')
        require(checks.get('wrong_type_rejected') and checks.get('failed_second_write_rolled_back'), f'Missing negative checks: {pair}')
        require(checks.get('duplicate_id', {}).get('behavior'), f'Missing duplicate-key probe: {pair}')
        summary = record.get('summary', {})
        require(REQUIRED <= set(summary) <= WORKLOADS, f'Unexpected workload coverage: {pair}')
        if 'relationship_join' in summary:
            require(checks.get('foreign_key', {}).get('behavior'), f'Missing foreign-key probe: {pair}')
        if pair[1] == 'postgresql':
            require(checks.get('full_final_data_after_server_restart') is True, f'Missing PostgreSQL server restart: {pair}')
        samples = record.get('samples', [])
        require(all(s.get('workload') in summary and s.get('phase') in ('sample', 'warmup') for s in samples), f'Unexpected sample category: {pair}')
        require(all(s.get('checked') is True and 'actual' in s and 'expected' in s and equal(s['actual'], s['expected']) for s in samples), f'Incorrect or unchecked output: {pair}')
        values = {}
        for workload in sorted(summary):
            measured = [s for s in samples if s['workload'] == workload and s['phase'] == 'sample']
            warm = [s for s in samples if s['workload'] == workload and s['phase'] == 'warmup']
            require(len(measured) == n and len(warm) == warmups, f'Sample count mismatch: {pair}/{workload}')
            require(all(type(s.get('iteration')) is int for s in measured+warm), f'Invalid iteration type: {pair}/{workload}')
            require({s.get('iteration') for s in measured} == set(range(warmups, n+warmups)), f'Sample iterations differ: {pair}/{workload}')
            require({s.get('iteration') for s in warm} == set(range(warmups)), f'Warmup iterations differ: {pair}/{workload}')
            xs = [s.get('elapsed_ns') for s in measured]
            require(all(type(x) is int and x > 0 for x in xs), f'Invalid latency: {pair}/{workload}')
            med = statistics.median(xs)
            calculated = {'n': n, 'median_ns': med, 'min_ns': min(xs), 'max_ns': max(xs),
                          'p95_ns': sorted(xs)[math.ceil(.95*n)-1],
                          'mad_ns': statistics.median(abs(x-med) for x in xs)}
            require(all(type(summary[workload].get(k)) in (int, float) and summary[workload][k] == v for k, v in calculated.items()), f'Summary disagrees with raw samples: {pair}/{workload}')
            values[workload] = calculated
        require(all(positive_number(record.get(k)) for k in SETUP), f'Invalid/missing setup measurement: {pair}')
        checked[pair] = values
    require(m.get('suite_sha256') and m.get('source_sha256'), 'Missing benchmark/engine source provenance')
    return m, pairs, checked, hashlib.sha256(raw).hexdigest()


def workload_identity(m):
    # The runner reads these root programs, not generated project copies. The
    # optional query implementation is not a measured input of the legacy path.
    # Reporting tools and unused profiles may evolve without relabelling it.
    query_profile = profile(m)['profile'] != 'legacy'
    return {name: digest for name, digest in m['suite_sha256'].items()
            if name in MEASURED_FILES or name in LEGACY_PROGRAMS
            or (name.startswith('scenarios/') and name.endswith('.json'))
            or (query_profile and name.startswith('query/') and name.endswith(('.py', '.bend')))}


def profile(m):
    settings = m['settings']
    label, metadata = settings.get('profile', 'legacy'), settings.get('profile_metadata', {})
    require(isinstance(label, str) and label, 'Profile must be a nonempty string')
    require(isinstance(metadata, dict), 'Profile metadata must be a record')
    return {'profile': label, 'metadata': metadata}


def provenance(m, digest):
    return {'manifest_sha256': digest, 'git_head': m.get('git_head'), 'git_branch': m.get('git_branch'),
            'git_status': m.get('git_status'), 'controller_sha256': m.get('jay_binary_sha256'),
            'versions': m.get('versions'), 'toolchain_lock': m.get('toolchain_lock'),
            'verified_tools': m.get('verified_tools'), 'hardware': m.get('hardware'),
            'settings': m['settings'], 'original_inventory_guard_status': m.get('original_inventory_guard_status'),
            'has_post_run_provenance_audit': m.get('provenance_audit', {}).get('status') == 'passed'}


def change(baseline, candidate, noise, failure):
    pct = (candidate/baseline - 1)*100
    label = 'within_tolerance'
    if pct < -noise:
        label = 'improvement'
    elif pct > failure:
        label = 'regression_exceeds_threshold'
    elif pct > noise:
        label = 'possible_regression'
    return {'baseline_ns': baseline, 'candidate_ns': candidate, 'delta_percent': pct,
            'speedup': baseline/candidate, 'classification': label}


def compare(baseline_path, candidate_path, *, engines=None, noise_percent=5.0,
            fail_regression_percent=15.0, gate_metrics=('latency',),
            allow_workload_change=False, allow_environment_change=False):
    require(math.isfinite(noise_percent) and 0 <= noise_percent <= fail_regression_percent < float('inf'), 'Need 0 <= noise <= regression threshold, both finite')
    require(set(gate_metrics) <= {'latency', 'setup'} and gate_metrics, 'Gate metrics must be latency and/or setup')
    bm, bp, bx, bh = load_manifest(baseline_path)
    cm, cp, cx, ch = load_manifest(candidate_path)
    require(bm['scenario_sha256'] == cm['scenario_sha256'], 'Scenario schemas or seed rows differ')
    bs = {k: v for k, v in bm['settings'].items() if k not in {'engines', 'lock'} | PROFILE_SETTINGS}
    cs = {k: v for k, v in cm['settings'].items() if k not in {'engines', 'lock'} | PROFILE_SETTINGS}
    require(equal(bs, cs), 'Measured settings differ, including samples/warmups/durability/clients/threads/equality policy')
    selected = list(engines or bm['settings']['engines'])
    require(selected and len(set(selected)) == len(selected), 'Empty/duplicate selected engines')
    require(set(selected) <= set(bm['settings']['engines']) & set(cm['settings']['engines']), 'Selected engine missing from a run')
    warnings = []
    before_profile, after_profile = profile(bm), profile(cm)
    if not equal(before_profile, after_profile):
        require(allow_workload_change, 'Application profile metadata differs; use --allow-workload-change for a separately labelled comparison')
        warnings.append('Application profiles differ: ' + json.dumps(before_profile, sort_keys=True) + ' -> '
                        + json.dumps(after_profile, sort_keys=True)
                        + '. This does not isolate an engine optimization.')
    if workload_identity(bm) != workload_identity(cm):
        require(allow_workload_change, 'Measured workload/adapter sources differ; use --allow-workload-change only for a separately labelled application-profile comparison')
        warnings.append('Measured workload/adapter code differs; this is an application-profile comparison, not an isolated engine optimization.')
    environment_fields = ('versions', 'verified_tools', 'toolchain_lock')
    environment_changes = [k for k in environment_fields if bm.get(k) != cm.get(k)]
    for k in ('platform', 'cpu', 'logical_cpus', 'affinity', 'mem_total'):
        if bm.get('hardware', {}).get(k) != cm.get('hardware', {}).get(k):
            environment_changes.append('hardware.'+k)
    if environment_changes:
        require(allow_environment_change, 'Benchmark environment differs: '+', '.join(environment_changes))
        warnings.append('Environment differs: '+', '.join(environment_changes)+'. Gains cannot be attributed solely to engine changes.')
    rows, failures, behavior_changes = [], [], []
    for scenario in sorted(bm['scenario_sha256']):
        for engine in selected:
            pair = scenario, engine
            b, c = bp[pair], cp[pair]
            if b['status'] != 'passed' or c['status'] != 'passed':
                failures.append({'scenario': scenario, 'engine': engine, 'baseline_status': b['status'], 'candidate_status': c['status'],
                                 'baseline_error': b.get('error', b.get('close_error')), 'candidate_error': c.get('error', c.get('close_error'))})
                continue
            require(bx[pair].keys() == cx[pair].keys(), f'Workload coverage differs: {pair}')
            for key in ('duplicate_id', 'foreign_key'):
                before, after = b['checks'].get(key), c['checks'].get(key)
                if (before or {}).get('behavior') != (after or {}).get('behavior'):
                    behavior_changes.append({'scenario': scenario, 'engine': engine, 'check': key,
                                             'baseline': before, 'candidate': after})
            for workload in sorted(bx[pair]):
                row = {'scenario': scenario, 'engine': engine, 'metric': 'latency', 'workload': workload,
                       'samples_each': bm['settings']['samples'],
                       'baseline_mad_ns': bx[pair][workload]['mad_ns'], 'candidate_mad_ns': cx[pair][workload]['mad_ns']}
                row.update(change(bx[pair][workload]['median_ns'], cx[pair][workload]['median_ns'], noise_percent, fail_regression_percent))
                rows.append(row)
            for metric in SETUP:
                row = {'scenario': scenario, 'engine': engine, 'metric': 'setup', 'workload': metric, 'samples_each': 1}
                row.update(change(b[metric], c[metric], noise_percent, fail_regression_percent))
                rows.append(row)
    regressions = [r for r in rows if r['classification'] == 'regression_exceeds_threshold' and r['metric'] in gate_metrics]
    groups = defaultdict(list)
    for row in rows:
        if row['metric'] == 'latency':
            groups[row['engine'], row['workload']].append(row['speedup'])
    aggregate = [{'engine': e, 'workload': w, 'paired_scenarios': len(xs),
                  'median_paired_speedup': statistics.median(xs), 'min_paired_speedup': min(xs), 'max_paired_speedup': max(xs)}
                 for (e, w), xs in sorted(groups.items())]
    engine_changes = sorted(n for n in bm['source_sha256'].keys() | cm['source_sha256'].keys()
                            if bm['source_sha256'].get(n) != cm['source_sha256'].get(n))
    return {'format': 'jaydb-benchmark-comparison-v1', 'status': 'gate_failed' if regressions or failures or behavior_changes else 'gate_passed',
            'baseline': provenance(bm, bh), 'candidate': provenance(cm, ch), 'engines': selected,
            'noise_percent': noise_percent, 'fail_regression_percent': fail_regression_percent,
            'gated_metrics': list(gate_metrics), 'warnings': warnings, 'engine_source_changes': engine_changes,
            'profiles': {'baseline': before_profile, 'candidate': after_profile},
            'failures': failures, 'behavior_changes': behavior_changes, 'threshold_regressions': regressions,
            'rows': rows, 'workload_speedups': aggregate,
            'scope': 'All paired observations retained. Medians are recomputed from raw samples. No composite score or workload weighting. Setup has one observation per scenario. Tolerances classify observed changes, not statistical significance; passing cannot establish absence of regressions.'}


def markdown(report):
    lines = ['# Paired benchmark comparison', '', f'Configured sampled gate: **{report["status"]}**.', '', report['scope'], '',
             f'Baseline controller: `{report["baseline"]["controller_sha256"]}`',
             f'Candidate controller: `{report["candidate"]["controller_sha256"]}`', '',
             'Application profiles: `' + json.dumps(report['profiles'], sort_keys=True) + '`', '',
             f'Noise tolerance: {report["noise_percent"]:g}%; regression threshold: {report["fail_regression_percent"]:g}%; gated metrics: {", ".join(report["gated_metrics"])}.', '']
    lines += [warning+'\n' for warning in report['warnings']]
    if report['failures'] or report['behavior_changes']:
        lines += ['Functional failures or changed integrity behavior:', '', '```json',
                  json.dumps({'failures': report['failures'], 'behavior_changes': report['behavior_changes']}, indent=2), '```', '']
    lines += ['Every paired measurement (negative change is faster):', '',
              '| Scenario | Engine | Metric | Baseline ms | Candidate ms | Change | Classification |',
              '| --- | --- | --- | ---: | ---: | ---: | --- |']
    for row in report['rows']:
        lines.append(f'| {row["scenario"]} | {row["engine"]} | {row["workload"]} | {row["baseline_ns"]/1e6:.6g} | {row["candidate_ns"]/1e6:.6g} | {row["delta_percent"]:+.2f}% | {row["classification"]} |')
    return '\n'.join(lines)+'\n'


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('baseline', type=Path)
    p.add_argument('candidate', type=Path)
    p.add_argument('--output', type=Path, required=True, help='New directory for comparison.json and comparison.md')
    p.add_argument('--engines', nargs='+')
    p.add_argument('--noise-percent', type=float, default=5)
    p.add_argument('--fail-regression-percent', type=float, default=15)
    p.add_argument('--gate-metrics', choices=['latency', 'setup'], nargs='+', default=['latency'])
    p.add_argument('--allow-workload-change', action='store_true')
    p.add_argument('--allow-environment-change', action='store_true')
    a = p.parse_args(argv)
    try:
        report = compare(a.baseline, a.candidate, engines=a.engines, noise_percent=a.noise_percent,
                         fail_regression_percent=a.fail_regression_percent, gate_metrics=a.gate_metrics,
                         allow_workload_change=a.allow_workload_change, allow_environment_change=a.allow_environment_change)
        a.output.mkdir(parents=True, exist_ok=False)
        (a.output/'comparison.json').write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
        (a.output/'comparison.md').write_text(markdown(report))
    except (ValueError, KeyError, TypeError, OSError) as exc:
        print(f'Invalid comparison: {exc}', file=sys.stderr)
        return 2
    print(f'{report["status"]}: {a.output}/comparison.json')
    return 0 if report['status'] == 'gate_passed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
