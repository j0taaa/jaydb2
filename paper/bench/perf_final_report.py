#!/usr/bin/env python3
"""Validate new repeated-program evidence and reproduce its tables/figure.

Does not write any of the thesis baseline inputs or their derived artifacts.
Run with the task's pytest/matplotlib venv after all benchmark invocations.
"""
import copy
import hashlib
import json
from pathlib import Path
import statistics as st

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'paper/evidence'
BASE = '3f28eb7c69d5da06b2bfe89ce3d720ed6d581acc'
AFTER = '1ea6ddc'


def load(name):
    return json.loads((OUT / name).read_text())


def checked(rows):
    for row in rows:
        assert row['checked'] is True
        assert json.dumps(row['actual'], sort_keys=True) == json.dumps(row['expected'], sort_keys=True)
        if 'elapsed_ns' in row:
            assert isinstance(row['elapsed_ns'], int) and row['elapsed_ns'] > 0


def frequency(obs):
    assert len(obs['scaling_cur_freq_khz']) == 16
    assert obs['affinity_cpus']
    assert all(v == ('1' if k.endswith('/no_turbo') else 'performance')
               for k, v in obs['settings'].items())


def stats(rows, workload=None):
    values = [r['elapsed_ns'] / 1e6 for r in rows
              if workload is None or r.get('workload') == workload]
    q = st.quantiles(values, n=4, method='inclusive')
    return dict(median_ms=st.median(values), q1_ms=q[0], q3_ms=q[2], n=len(values))


def summarize(record, workload=None):
    result = stats(record['samples'], workload)
    sm = [stats(s['samples'], workload)['median_ms'] for s in record['sessions']]
    return dict(result, session_medians_ms=sm, session_min_ms=min(sm), session_max_ms=max(sm))


def cell(result):
    return (f"{result['median_ms']:.4f} [{result['q1_ms']:.4f}, {result['q3_ms']:.4f}]; "
            f"{result['session_min_ms']:.4f}–{result['session_max_ms']:.4f}")


def validate(data, experiment, baseline):
    meta = data['metadata']
    assert (meta['commit'] == BASE if baseline else meta['commit'].startswith(AFTER))
    frequency(meta['frequency'])
    assert data['runner']['completed_utc']
    expected_groups = 6 if experiment == 'prepared' else 12
    assert len(data['records']) == expected_groups
    assert meta['session_count'] == 3
    if experiment == 'prepared':
        assert {(r['program'], r['persistent']) for r in data['records']} == {
            (p, m) for p in ('read', 'indexed', 'voucher') for m in (False, True)}
    for r in data['records']:
        assert len(r['sessions']) == 3
        checked(r['samples'])
        assert len(r['samples']) == (900 if experiment == 'prepared' else 1800)
        reconstructed = []
        counters = {}
        for sid, s in enumerate(r['sessions'], 1):
            assert s['session'] == sid
            frequency(s['frequency'])
            checked(s['samples']); checked(s['warmup'])
            for workload in ([None] if experiment == 'prepared' else ['read', 'update']):
                samples = [x for x in s['samples'] if workload is None or x['workload'] == workload]
                assert [x['iteration'] for x in samples] == list(range(1, 301))
                warm = [x for x in s['warmup'] if workload is None or x['workload'] == workload]
                assert len(warm) == 1 and warm[0]['iteration'] == 0
            for row in copy.deepcopy(s['samples']):
                w = row.get('workload', 'call'); counters[w] = counters.get(w, 0) + 1
                row.update(session=sid, session_iteration=row['iteration'], iteration=counters[w])
                reconstructed.append(row)
            if experiment == 'prepared':
                assert len(s['registrations']) == 3
                checked(s['registrations'])
                if r['program'] == 'voucher':
                    assert all(x['untimed_retirement_checked'] for x in s['samples'])
                if not baseline:
                    assert all('prepared_worker' in x['phases_ns'] and
                               'packet_authentication' not in x['phases_ns'] for x in s['samples'])
            elif r['engine'] == 'jaydb2':
                assert s['total_rows_checked']
                assert all(x['stored_value_checked'] and x['stored_value'] == x['iteration']
                           for x in s['samples'] if x['workload'] == 'update')
            if experiment == 'comparison':
                assert r['persistent'] and s['total_rows_checked']
                if r['engine'] == 'postgresql':
                    settings = s['settings']
                    assert all(settings[k] == 'on' for k in ('fsync', 'synchronous_commit', 'full_page_writes'))
                    assert settings['role'][1:] == [False, False]
                    if r['policy'] == 'owner':
                        assert settings['rls'] == [True, True]
                elif r['engine'] == 'sqlite':
                    assert s['settings']['journal_mode'] == 'wal' and s['settings']['synchronous'] == 2
        assert reconstructed == r['samples'], 'pooled observations differ from independent sessions'
    if experiment == 'comparison':
        assert data['large_rows'] == 1104
        assert {(r['engine'], r['policy'], r['rows']) for r in data['records']} == {
            (e, p, n) for e in ('jaydb2', 'postgresql', 'sqlite')
            for p in ('point', 'owner') for n in (10, 1104)}
        assert len(data['policy_checks']) == 36 and len(data['policy_postchecks']) == 18
        checked(data['policy_checks']); checked(data['policy_postchecks'])
        for probe in data['policy_checks']:
            assert probe['refused'] == (probe['engine'] != 'sqlite')
        pg = data['settings']['postgresql']; sq = data['settings']['sqlite']
        assert all(pg[k] == 'on' for k in ('fsync', 'synchronous_commit', 'full_page_writes'))
        assert pg['role'][1:] == [False, False] and pg['rls'] == [True, True]
        assert sq['journal_mode'] == 'wal' and sq['synchronous'] == 2


def scaling(baseline):
    prefix = 'perf-final-baseline-' if baseline else 'perf-final-'
    datasets = [load(f'{prefix}scaling-session{i}.json') for i in (1, 2, 3)]
    result = dict(metadata=copy.deepcopy(datasets[0]['metadata']), session_count=3,
                  experiment='E5 three independent repetitions of unchanged one-session protocol',
                  raw_files=[f'{prefix}scaling-session{i}.json' for i in (1, 2, 3)], records=[])
    result['metadata']['session_count'] = 3
    groups = {}
    for sid, data in enumerate(datasets, 1):
        for key in ('source_sha256', 'binary_sha256', 'toolchain'):
            assert data['metadata'][key] == datasets[0]['metadata'][key]
        assert data['runner']['completed_utc']
        assert data['max_rows'] == 1105 and data['session_count'] == 1
        assert (data['metadata']['commit'] == BASE if baseline else data['metadata']['commit'].startswith(AFTER))
        frequency(data['metadata']['frequency'])
        assert data['populations'] == [10, 30, 100, 300, 600, 1000, 1105]
        assert len(data['records']) == 14 and len(data['boundary_checks']) == 2
        checked(data['boundary_checks'])
        for b in data['boundary_checks']:
            assert b['actual'] == dict(status='limit', value=None)
            checked([b['rollback_check']])
            assert b['rollback_check']['actual'] == dict(status='refusal', value=None)
        for persistent in (False, True):
            records = [r for r in data['records'] if r['persistent'] == persistent]
            assert len({r['service_pid'] for r in records}) == 1
            assert [r['rows'] for r in records] == data['populations']
        for r in data['records']:
            checked(r['samples']); checked(r['warmup']); checked(r['first_key_samples'])
            frequency(r['frequency'])
            for op in ('read', 'update'):
                assert [x['iteration'] for x in r['samples'] if x['workload'] == op] == list(range(1, 51))
                assert all(x.get('stored_value_checked') for x in r['samples'] if x['workload'] == 'update')
            assert len(r['first_key_samples']) == (50 if r['rows'] in (10, 1105) else 0)
            item = copy.deepcopy(r); item['session'] = sid
            key = r['persistent'], r['rows']
            g = groups.setdefault(key, dict(rows=r['rows'], persistent=r['persistent'], state_bytes=r['state_bytes'],
                                             sessions=[], samples=[], first_key_samples=[]))
            g['sessions'].append(item)
            for field in ('samples', 'first_key_samples'):
                g[field].extend(dict(x, session=sid) for x in r[field])
    result['records'] = list(groups.values())
    (OUT / f'{prefix}scaling.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def find(data, **filters):
    return next(r for r in data['records'] if all(r[k] == v for k, v in filters.items()))


def main():
    data = {side: {exp: load(f'perf-final-{"baseline-" if side == "before" else ""}{exp}.json')
                   for exp in ('prepared', 'comparison')} for side in ('before', 'after')}
    for side, experiments in data.items():
        for exp, d in experiments.items():
            validate(d, exp, side == 'before')
        experiments['scaling'] = scaling(side == 'before')
        assert len({d['metadata']['source_sha256'] for d in experiments.values()}) == 1
        assert len({d['metadata']['binary_sha256'] for d in experiments.values()}) == 1
        assert all(d['metadata']['toolchain'] == experiments['prepared']['metadata']['toolchain']
                   for d in experiments.values())
    for exp in ('prepared', 'comparison'):
        assert data['before'][exp]['runner']['harness_sha256'] == data['after'][exp]['runner']['harness_sha256']
    lines = [
        '# Final fixed-clock repeated-program benchmark', '',
        f'Before: `{BASE}`. After: `{data["after"]["prepared"]["metadata"]["commit"]}` '
        '(the integrated `perf/repeated-programs` source). The evidence branch adds only benchmark drivers, '
        'raw observations and this report. No engine, host, proof, compiler, emitted C or runtime was edited.', '',
        '## Protocol and provenance', '',
        'All headline before values below are fresh same-day reruns of the detached baseline, '
        '**not** copied from `final-report.md`. The initial estimate was comfortably below three hours: '
        'historical E2 measured calls plus registrations took about 576 s; E3 timed calls plus ordinary '
        'context took about 1,336 s, before untimed initialization/population/readback. '
        'Baseline and after use byte-identical `run.py`, `workloads.py` and `fixtures.py`. '
        '`perf_final.py` imports the chosen checkout’s unchanged experiment function and redirects its '
        'save destination; it changes no workload, timing interval, warmup, sample count, storage flag or phase marker.', '',
        'Revision identity comes from `metadata.commit` and the source/binary fingerprints. '
        'The unchanged harness also emits a hard-coded historical `metadata.base_commit` '
        '(95027be…); that field is not the before engine for this report.', '',
        'Each benchmark invocation holds `flock /tmp/jaydb2-experiments-heavy.lock` and runs inside '
        '`paper/bench/fixed-clock.sh` with unlimited stack, performance governor/EPP and turbo disabled '
        '(nominal 3.6 GHz, i7-11700K, 16 logical CPUs). Locks are released after each experiment invocation. '
        'The unchanged harness uses one native thread, warm page cache, no inspector and no core pinning. '
        'Each raw file records source/binary/toolchain hashes, CPU settings, affinity, endpoint sampled '
        'frequencies, UTC and the exact runner command. Endpoint frequencies do not establish an integrated clock rate.', '',
        'E2 and E3 retain exactly three fresh service/database sessions per condition, 300 timed calls '
        'per operation/session after one discarded warmup (n=900). E2 retains three registrations per '
        'session and checked, untimed voucher retirement. E3 retains small-state ordinary context, '
        'untimed initialization/population and checked readback after every update. PostgreSQL 16.15 '
        'and SQLite are remeasured in **both** comparison invocations, with fresh cluster/database '
        'per condition/session and the original rotated engine/condition order.', '',
        'E5 repeats the original ascending-size session three times per revision: one service per '
        'storage mode is reused across 10, 30, 100, 300, 600, 1,000 and 1,105 rows **within each repetition**. '
        'Each point retains 50 reads and 50 updates after one warmup (n=150 pooled); first-key endpoint '
        'reads and the actual excess-row/rollback probes remain. The original published E5 had one '
        'session/n=50; it is preserved and is not pooled here. E5 revision order is before/after, '
        'after/before, before/after. E2 runs after then before; E3 runs before then after. These '
        'are same-day condition-matched reruns, not randomized session-by-session pairs for E2/E3.', '',
        'JayDB2 latency starts at sending the pre-encoded frame and ends at reading the complete '
        'framed response. SQL times `execute(...).fetchall()`, including driver conversion. '
        'Result checks are outside the interval. JayDB2 updates return an acknowledgement, SQL returns '
        'the changed integer. PostgreSQL uses fsync/synchronous_commit/full_page_writes=on; SQLite '
        'uses WAL/FULL. Point and owner conditions have the same **total** row count; owner divides '
        '10 as 5+5 and 1,104 as 552+552. PostgreSQL enforces RLS for owner; SQLite is unconstrained '
        'and its cross-owner probes succeed. JayDB2 probes reject the supplied unchanged ownership '
        'certificate for an altered program; this is not an exhaustive proof about all certificates.', '',
        'All table values are milliseconds: **pooled median [inclusive Q1, Q3]; min–max of session '
        'medians**. No outlier removal. Session spread is descriptive, not a confidence interval. '
        'Ratios divide pooled medians, not medians of paired per-call ratios. Before and after each '
        'use their own contemporaneous PostgreSQL denominator; SQL variation can change those ratios '
        'independently of the JayDB2 speedup.', '',
        '## E2 prepared programs', '',
        'The read fixture starts with ten two-column rows; Indexed and Voucher retain their original '
        'application fixtures rather than being relabeled as ten-row point updates.', '',
        '| Program / storage | Before: median [Q1, Q3]; session spread | After: median [Q1, Q3]; session spread | Before/after | n each |',
        '|---|---:|---:|---:|---:|']
    summary = dict(before_commit=BASE, after_commit=data['after']['prepared']['metadata']['commit'],
                   statistics='inclusive quartiles; pooled median; min/max independent-session medians', prepared=[], comparison=[], scaling=[])
    for persistent in (False, True):
        for program in ('read', 'indexed', 'voucher'):
            b, a = [summarize(find(data[side]['prepared'], program=program, persistent=persistent)) for side in ('before', 'after')]
            label = f'{program.title()} / {"durable" if persistent else "volatile"}'
            lines.append(f'| {label} | {cell(b)} | {cell(a)} | {b["median_ms"]/a["median_ms"]:.2f}× | 900 |')
            summary['prepared'].append(dict(program=program, persistent=persistent, before=b, after=a))
    noisy = find(data['before']['prepared'], program='indexed', persistent=True)
    rt = [st.median(x['elapsed_ns']/1e6 for x in s['samples']) for s in noisy['sessions']]
    pub = [st.median(x['phases_ns']['publication']/1e6 for x in s['samples']) for s in noisy['sessions']]
    worker = [st.median(x['phases_ns']['prepared_worker']/1e6 for x in s['samples']) for s in noisy['sessions']]
    lines += ['', 'The baseline durable Indexed session medians were '
              + ', '.join(f'{x:.3f}' for x in rt) + ' ms. Publication medians in the same order were '
              + ', '.join(f'{x:.3f}' for x in pub) + ' ms, while worker medians were '
              + ', '.join(f'{x:.3f}' for x in worker) + ' ms. The long session coincides with '
              'publication time; its underlying cause was not isolated. All samples are retained. '
              'This variation limits precise causal attribution of the durable speedup.', '']
    lines += ['', '### Cold registration cost', '',
              'Nine registrations per program/storage/revision (three per fresh service); no registration '
              'warmup is removed. These are seconds, **min / median / max; min–max of session registration '
              'medians**. Repeated-call speedups do not imply a faster first registration.', '',
              '| Program / storage | Before (s) | After (s) | n each |', '|---|---:|---:|---:|']
    for persistent in (False, True):
        for program in ('read', 'indexed', 'voucher'):
            cells = []
            for side in ('before', 'after'):
                r = find(data[side]['prepared'], program=program, persistent=persistent)
                values = [x['elapsed_ns']/1e9 for x in r['registrations']]
                medians = [st.median(x['elapsed_ns']/1e9 for x in s['registrations']) for s in r['sessions']]
                cells.append(f'{min(values):.3f} / {st.median(values):.3f} / {max(values):.3f}; {min(medians):.3f}–{max(medians):.3f}')
            lines.append(f'| {program.title()} / {"durable" if persistent else "volatile"} | {cells[0]} | {cells[1]} | 9 |')
    lines += ['', '## E3 durable local comparisons', '',
              'Lower JayDB2/PostgreSQL is better. Read success emits Commit even with an equal root; '
              'durable equal-root reuse avoids a new disk sync. Changing updates persist a complete '
              'JayDB2 image; PostgreSQL and SQLite use their native SQL durability mechanisms.', '']
    for count in (10, 1104):
        for policy in ('point', 'owner'):
            lines += [f'### {count:,} total rows / {policy}', '',
                      '| Operation / engine | Before: median [Q1, Q3]; session spread | After: median [Q1, Q3]; session spread | n each |',
                      '|---|---:|---:|---:|']
            for op in ('read', 'update'):
                entries = {}
                for engine in ('jaydb2', 'postgresql', 'sqlite'):
                    b, a = [summarize(find(data[side]['comparison'], rows=count, policy=policy, engine=engine), op) for side in ('before', 'after')]
                    entries[engine] = (b, a)
                    lines.append(f'| {op} / {engine} | {cell(b)} | {cell(a)} | 900 |')
                    summary['comparison'].append(dict(rows=count, policy=policy, operation=op, engine=engine, before=b, after=a))
                ratios = [entries['jaydb2'][i]['median_ms'] / entries['postgresql'][i]['median_ms'] for i in (0, 1)]
                summary['comparison'][-3]['jaydb2_over_postgresql'] = dict(before=ratios[0], after=ratios[1])
            lines += ['', 'JayDB2/PostgreSQL: ' + '; '.join(
                f'{op} **{next(x for x in summary["comparison"] if x["rows"] == count and x["policy"] == policy and x["operation"] == op and x["engine"] == "jaydb2")["jaydb2_over_postgresql"]["before"]:.2f}× → '
                f'{next(x for x in summary["comparison"] if x["rows"] == count and x["policy"] == policy and x["operation"] == op and x["engine"] == "jaydb2")["jaydb2_over_postgresql"]["after"]:.2f}×**'
                for op in ('read', 'update')) + '.', '']
    lines += ['## E5 scaling', '',
              'The fixture has one two-column cells table (text id, int64 value), canonical seven-byte '
              'keys such as `k000000`, and two users. The 1,105-row maximum applies to this fixture '
              'under its configured byte ceiling, not to arbitrary schemas or configurations.', '',
              '![Fixed-clock scaling medians and inclusive interquartile bands](perf-repeated-scaling.svg)', '']
    for persistent in (False, True):
        for op in ('read', 'update'):
            lines += [f'### {"Durable" if persistent else "Volatile"} / last-key {op}', '',
                      '| Rows / canonical bytes | Before: median [Q1, Q3]; session spread | After: median [Q1, Q3]; session spread | Before/after | n each |',
                      '|---|---:|---:|---:|---:|']
            for count in (10, 30, 100, 300, 600, 1000, 1105):
                records = [find(data[side]['scaling'], persistent=persistent, rows=count) for side in ('before', 'after')]
                b, a = [summarize(r, op) for r in records]
                lines.append(f'| {count:,} / {records[0]["state_bytes"]:,} | {cell(b)} | {cell(a)} | {b["median_ms"]/a["median_ms"]:.2f}× | 150 |')
                summary['scaling'].append(dict(rows=count, persistent=persistent, operation=op, before=b, after=a))
    lines += ['', 'First-key endpoint controls (n=150 each):', '',
              '| Rows / storage | Before: median [Q1, Q3]; session spread | After: median [Q1, Q3]; session spread |', '|---|---:|---:|']
    for persistent in (False, True):
        for count in (10, 1105):
            results = []
            for side in ('before', 'after'):
                r = copy.deepcopy(find(data[side]['scaling'], rows=count, persistent=persistent))
                r['samples'] = r['first_key_samples']
                for s in r['sessions']: s['samples'] = s['first_key_samples']
                results.append(summarize(r))
            lines.append(f'| {count:,} / {"durable" if persistent else "volatile"} | {cell(results[0])} | {cell(results[1])} |')
    lines += phases()
    lines += ['', '### Durable publication observed in E2', '',
              'These are the actual E2 application fixtures (n=900 per cell), not a separate point-update '
              'microbenchmark. The publication marker includes durable storage and RAM publication; '
              'it is not an isolated fdatasync timer. Read equal-root reuse and changing Indexed/Voucher '
              'states have different storage work.', '',
              '| Durable fixture | Before publication median [Q1, Q3] ms | After publication median [Q1, Q3] ms |',
              '|---|---:|---:|']
    for program in ('read', 'indexed', 'voucher'):
        cells = []
        for side in ('before', 'after'):
            rows = find(data[side]['prepared'], program=program, persistent=True)['samples']
            s = stats([dict(elapsed_ns=x['phases_ns']['publication']) for x in rows])
            cells.append(f'{s["median_ms"]:.4f} [{s["q1_ms"]:.4f}, {s["q3_ms"]:.4f}]')
        lines.append(f'| {program.title()} | {cells[0]} | {cells[1]} |')
    lines += ['', 'The earlier [durable diagnosis](perf-durable.md) traced the old two-sync '
              'replacement path and the new one-fdatasync routine commit. Its syscall probes are '
              'separate instrumented experiments, not additive components of the present E2 medians. '
              'Creation and slot growth still use file sync/replacement/directory sync; their untimed '
              'setup cost is not credited as routine-call throughput.', '']
    narrative = ROOT / 'paper/bench/perf_final_discussion.md'
    lines += ['', narrative.read_text().strip(), '']
    point = [r for r in summary['comparison'] if r['engine'] == 'jaydb2' and r['policy'] == 'point']
    outcomes = ['## Measured outcome', '']
    for op in ('read', 'update'):
        cells = [next(r for r in point if r['rows'] == n and r['operation'] == op) for n in (10, 1104)]
        outcomes.append('Durable point ' + op + ': ' + '; '.join(
            f"{r['rows']:,} rows **{r['before']['median_ms']:.4f} → {r['after']['median_ms']:.4f} ms**, "
            f"JayDB2/PostgreSQL **{r['jaydb2_over_postgresql']['before']:.2f}× → {r['jaydb2_over_postgresql']['after']:.2f}×**"
            for r in cells) + ' (n=900 per engine/revision/cell).')
        outcomes.append('')
    outcomes += ['These medians describe this protocol on this machine; the tables retain quartiles '
                 'and session spread, including SQL durability variation. They do not establish '
                 'parity across workloads or an architecture-independent latency floor.', '']
    lines[4:4] = outcomes
    if (OUT / 'perf-final-validation.json').exists():
        audit = load('perf-final-validation.json')
        lines += ['## Completed validation', '', '| Command / audit | Outcome |', '|---|---|']
        for row in audit['commands']:
            lines.append(f'| `{row["command"]}` | {row["result"]} (exit {row["returncode"]}) |')
        lines += [f'| Original evidence | {len(audit["original_evidence_sha256"])} files byte-identical to {AFTER} |',
                  '| Engine/proof/host/original harness and paper sources | Unchanged |',
                  f'| Fixed-clock restoration | {len(audit["clock_restorations"])} verified receipts |',
                  f'| Final CPU readback | All governors powersave; no_turbo=0 at {audit["cpu_final"]["utc"]} |',
                  '| Full make release/proof/application suite | Not rerun under benchmark-only override |', '']
    (OUT / 'perf-repeated.md').write_text('\n'.join(lines))
    (OUT / 'perf-final-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    plot(summary)
    print('PASS: new E2/E3/E5 protocol, output, readback, policy, frequency, fingerprint and pooled/session checks')


def phases():
    datasets = [load(f'perf-final-phases-session{i}.json') for i in (1, 2, 3)]
    lines = ['', '## Where the remaining time goes', '',
             'Fresh current-source phase captures use the existing `repeated_diagnose.capture(100)` '
             'with markers enabled: three fresh volatile service sessions, last-key read and alternating '
             '0/1 update at 10 and 1,105 rows, n=300 per cell after one warmup/session. '
             'This separate diagnostic is not pooled into E2/E3/E5. Values are pooled median '
             '[inclusive Q1, Q3] milliseconds; phase medians need not add to round-trip median.', '',
             '| Inclusive phase / residual | Read / 10 | Update / 10 | Read / 1,105 | Update / 1,105 |',
             '|---|---:|---:|---:|---:|']
    for d in datasets:
        assert d['metadata']['commit'].startswith(AFTER)
        reference = load('perf-final-prepared.json')['metadata']
        for key in ('source_sha256', 'binary_sha256', 'toolchain'):
            assert d['metadata'][key] == reference[key]
        frequency(d['metadata']['frequency'])
        assert len(d['records']) == 4
        assert {(r['rows'], r['operation']) for r in d['records']} == {
            (n, op) for n in (10, 1105) for op in ('read', 'update')}
        for r in d['records']:
            checked(r['samples']); assert len(r['samples']) == 100
            checked(r['warmup']); assert len(r['warmup']) == 1
            assert all('packet_authentication' not in x['phases_ns'] for x in r['samples'])
    for phase, label in [('prepared_integrity', 'Snapshot packet + candidate routing (`prepared_integrity`)'),
                         ('prepared_worker', 'Prepared worker + packet/transport/capture'),
                         ('publication', 'Publication'), ('residual', 'Round trip minus those non-overlapping host markers'),
                         ('roundtrip', '**Complete client round trip**')]:
        cells = []
        for count, op in ((10, 'read'), (10, 'update'), (1105, 'read'), (1105, 'update')):
            rows = [x for d in datasets for r in d['records'] if r['rows'] == count and r['operation'] == op for x in r['samples']]
            assert len(rows) == 300
            values = [x['elapsed_ns'] if phase == 'roundtrip' else
                      x['elapsed_ns'] - sum(x['phases_ns'].get(p, 0) for p in ('prepared_integrity', 'prepared_worker', 'publication'))
                      if phase == 'residual' else x['phases_ns'][phase] for x in rows]
            s = stats([dict(elapsed_ns=x) for x in values])
            cells.append(f'{s["median_ms"]:.4f} [{s["q1_ms"]:.4f}, {s["q3_ms"]:.4f}]')
        lines.append('| ' + label + ' | ' + ' | '.join(cells) + ' |')
    lines += ['', 'The residual is computed per call before summarizing. It includes unmarked host work, '
              'client pipe scheduling and complete response delivery; it is not a pure CPU estimate. '
              'Worker timing includes checked full-root decoding/validation, current authentication/selection, '
              'actual access, one canonical state encoding, result framing and child collection. '
              'Pre-selection image verification/startup is outside the interval; asynchronous pool refill '
              'still consumes real CPU and may overlap. Removing a separate authenticator and file scan '
              'does not remove whole-state work.', '',
              'The earlier [diagnosis](perf-repeated-diagnosis.md) profiled the original engine with '
              'BPF (n=30): at 10/1,105 rows, read access was 0.0068/0.3102 ms and update access '
              '0.0119/0.7626 ms, versus 0.8339/8.6420 ms inclusive checked read entry and '
              '0.1908/14.2970 ms finalization/output. These are **historical instrumented baseline '
              'regions**, not the present worker’s cost decomposition. Finalization formerly encoded '
              'state twice; [task C](perf-finalization-c.md) removes one encoding. '
              '[Task D](perf-checked-entry.md) separately measured framing-after entry at '
              '0.889/8.527 ms for read and 0.935/8.501 ms for update, with root decode/validation '
              'inside it at 0.267/5.019 and 0.296/5.053 ms. Its source base lacked the final combined '
              'refinements; it did not deliver a direct typed decoder. Those overlapping, separately '
              'instrumented regions cannot be added to current host phases or subtracted to claim an '
              'exact current encode budget. No new BPF breakdown of the final integrated worker is claimed.', '']
    return lines


def plot(summary):
    import matplotlib
    matplotlib.use('Agg')
    matplotlib.rcParams['svg.hashsalt'] = 'jaydb2-perf-repeated'
    import matplotlib.pyplot as plt
    fig, axes = plt.subplots(2, 2, figsize=(10, 7), sharex=True)
    for i, persistent in enumerate((False, True)):
        for j, op in enumerate(('read', 'update')):
            ax = axes[i, j]
            records = [r for r in summary['scaling'] if r['persistent'] == persistent and r['operation'] == op]
            xs = [r['rows'] for r in records]
            for side, label, color in [('before', 'Before (3f28eb7)', '#8a5266'), ('after', 'After (1ea6ddc)', '#167f91')]:
                ax.plot(xs, [r[side]['median_ms'] for r in records], marker='o', markersize=3, label=label, color=color)
                ax.fill_between(xs, [r[side]['q1_ms'] for r in records], [r[side]['q3_ms'] for r in records], color=color, alpha=.18)
            ax.set_title(f'{"Durable" if persistent else "Volatile"} {op}')
            ax.set_ylabel('Round-trip latency (ms)'); ax.grid(alpha=.2)
            if i == 1: ax.set_xlabel('Total rows')
    axes[0, 0].legend(frameon=False)
    fig.suptitle('Repeated prepared point calls · fixed clock · 3 sessions per revision\nMedians and inclusive interquartile bands; n=150 per point')
    fig.tight_layout()
    svg = OUT / 'perf-repeated-scaling.svg'
    fig.savefig(svg, metadata={'Date': None})
    # Matplotlib emits spaces before SVG path-data newlines; normalize text only.
    svg.write_text('\n'.join(line.rstrip() for line in svg.read_text().splitlines()) + '\n')
    plt.close(fig)


if __name__ == '__main__':
    main()
