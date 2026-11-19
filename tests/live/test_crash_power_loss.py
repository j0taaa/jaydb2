"""Simulated power loss over a concurrent durable workload.

python3 -m tests.live.test_crash_power_loss --fault-binary FAULT --normal-binary NORMAL

Build both release binaries, with and without storage-fault-injection, from one
frozen source tree: the storage descriptor binds the executable and the staged
sources, so the copies only reopen under the same snapshot.

Each run starts the fault build with JAYDB_POWER_LOSS_CUT=kind:n and drives
concurrent transfers; every third run also performs online migrations, whose
2.6 MB epoch frames rotate the 8 MiB segment. At the n-th hook of that kind the server writes
manifest.json (every WAL batch it wrote, by LSN) and `--trials` copies of its
storage directory. In each copy, every 4 KiB block written since its file's
last sync is kept, reverted or torn, and every directory change since the last
directory sync is applied or not. The server then exits with status 86. Each
copy must open with the normal build and hold a batch-boundary prefix of the
commit order that contains every acknowledged transfer, with no partial one.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import os
from pathlib import Path
from random import Random
import resource
import shutil
import socket
import subprocess
import tempfile
from threading import Barrier
from time import monotonic
import traceback

from tests.live.test_concurrency import APP, INITIAL_LEFT, Listener, TOKEN, exchange, execute
from tests.service.test_end_to_end import ROOT, Server
from tools.client import prepared_frame

CLIENTS = 9
PAIRS = 3
DISCONNECT = (EOFError, BrokenPipeError, ConnectionResetError, socket.timeout)
# Hook kinds in server/wal.rs, with occurrence ranges for runs without and
# with migrations. The second segment-name hook is the size-based rotation.
KINDS = {
    'wal': ((1, 700), (1, 400)),           # before a WAL frame's fdatasync
    'epoch': (None, (1, 4)),               # the same, for a frame with an epoch record
    'segment-name': ((1, 1), (2, 2)),      # before the directory sync for a new segment
    'checkpoint': ((1, 4), (1, 2)),        # before a checkpoint file's fsync
    'checkpoint-name': ((1, 4), (1, 2)),   # after the checkpoint rename, before the directory sync
    'reclaim': ((1, 4), (1, 2)),           # after reclaiming files, before the directory sync
}
MIGRATION = """import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Old/Configuration.bend as Old

def migrate(s: D.State) -> D.State:
  s

def preserves(s: D.State, valid: R.Valid(Old.config(), s)) -> Unit:
  Unit{}
"""


def event(name, **fields):
    print(json.dumps({"event": name, **fields}), flush=True)


class Host(Listener):
    def __init__(self, app, binary, database, root, mode, env=None):
        self.endpoint = root / 'live.sock'
        self.admin = root / 'admin.sock'
        self.app = app
        Server.__init__(self, app, binary=binary, seed=mode == 'create', threads=1,
                        env=dict(os.environ, TMPDIR=str(root), **(env or {})),
                        arguments=['--listen', str(self.endpoint), '--concurrency', str(CLIENTS),
                                   '--admin-socket', str(self.admin),
                                   '--storage', str(database), '--storage-mode', mode])

    def prepare(self, stream):
        reply = exchange(stream, prepared_frame(
            0, (self.app / 'Client.bend').read_text(), TOKEN,
            proof=(self.app / 'PreparedProof.bend').read_text()))
        assert reply['status'] == 'prepared', (reply, self.diagnostics())
        return reply['value']


def fixture(root):
    """Transfers between pairs return the receiving balance, a per-pair ordinal."""
    app = root / 'app'
    shutil.copytree(APP, app)
    seed = (app / 'Seed.bend').read_text()
    pairs = []
    for index in range(PAIRS):
        pair = [f'lane-{chr(ord("a") + 2 * index + side)}' for side in (0, 1)]
        old = f'row("{pair[0]}", 0)'
        assert old in seed
        seed = seed.replace(old, f'row("{pair[0]}", {INITIAL_LEFT})')
        pairs.append(pair)
    (app / 'Seed.bend').write_text(seed)
    client = app / 'Client.bend'
    code = client.read_text()
    for old, new in [('def moved(from: String, to: String, left: U32, right: U32,',
                      'def moved(from: String, to: String, left: U32, +right: U32,'),
                     ('write(to, (right + 1 : U32), S.Finish{D.VAbsent{}})',
                      'write(to, (right + 1 : U32), show((right + 1 : U32)))')]:
        assert old in code
        code = code.replace(old, new)
    client.write_text(code)
    return app, pairs


def migrated_app(app, root, number):
    """The same application under a distinct environment (message limit)."""
    new = root / f'app-{number}'
    shutil.copytree(app, new)
    configuration = new / 'Configuration.bend'
    text = configuration.read_text()
    assert 'S.Limits{65536n, ' in text
    configuration.write_text(text.replace('S.Limits{65536n, ', f'S.Limits{{{65536 - number}n, '))
    return new


def migrate(host, app, root):
    """Online identity migration. Returns its epoch LSN, or None if the host died."""
    module = root / 'Identity.bend'
    module.write_text(MIGRATION)
    with socket.socket(socket.AF_UNIX) as stream, stream.makefile('rb') as reply:
        stream.settimeout(600)
        stream.connect(str(host.admin))
        stream.sendall(json.dumps({'command': 'migrate', 'configuration': str(app / 'Configuration.bend'),
                                   'migration': str(module)}).encode() + b'\n')
        line = reply.readline()
    if not line and host.process.wait(timeout=60) == 86:
        return None
    result = json.loads(line)
    assert result['status'] == 'success', (result, host.diagnostics())
    host.app = app
    return result['lsn']


def write_until_cut(host, pairs, handle, limit):
    """Each session repeats one pair's transfer until the deadline or the cut."""
    barrier = Barrier(CLIENTS, timeout=120)
    deadline = monotonic() + limit

    def writer(index):
        pair = index % len(pairs)
        request = execute(handle, pairs[pair])
        seen = set()
        try:
            with host.session() as stream:
                stream.settimeout(120)
                barrier.wait()
                while monotonic() < deadline:
                    response = exchange(stream, request)
                    assert response['status'] == 'success', (pair, response, host.diagnostics())
                    ordinal = response['value']
                    assert type(ordinal) is int and ordinal not in seen, response
                    seen.add(ordinal)
        except DISCONNECT:
            pass
        except AssertionError:
            if host.process.poll() is None:
                raise
        return pair, seen

    acknowledged = [set() for _ in pairs]
    with ThreadPoolExecutor(CLIENTS) as pool:
        for pair, seen in pool.map(writer, range(CLIENTS)):
            assert not acknowledged[pair] & seen, 'a transfer was acknowledged twice'
            acknowledged[pair].update(seen)
    return acknowledged


def oracle(pairs, acknowledged, manifest, epochs):
    """Pair positions after every whole WAL batch, in LSN order."""
    by_keys = {frozenset(pair): index for index, pair in enumerate(pairs)}
    position = [0] * len(pairs)
    prefixes = {tuple(position): {0}}
    groups = 0
    lsn = 0
    written_epochs = []
    for batch in manifest['batches']:
        groups += len(batch) > 1
        for record in batch:
            lsn += 1
            assert record['lsn'] == lsn, ('manifest is not a consecutive history', record, lsn)
            if record.get('epoch'):
                written_epochs.append(lsn)
            else:
                position[by_keys[frozenset(record['keys'])]] += 1
        prefixes.setdefault(tuple(position), set()).add(lsn)
    # Acknowledged migrations, and perhaps one more cut while in progress.
    assert written_epochs[:len(epochs)] == epochs and len(written_epochs) - len(epochs) <= 1, (
        written_epochs, epochs)
    for index, values in enumerate(acknowledged):
        assert all(0 < value <= position[index] for value in values), ('ack beyond history', index)
    return prefixes, groups, lsn, written_epochs


def open_copy(candidates, database, root, normal):
    """Open with the newest configuration whose descriptor matches."""
    for index, app in reversed(list(enumerate(candidates))):
        host = Host(app, normal, database, root, 'open')
        try:
            with host.session() as stream:
                return host, index, host.prepare(stream)
        except AssertionError as error:
            host.close()
            if index and 'incompatible WAL environment descriptor' in str(error):
                continue
            raise
    raise AssertionError('no configuration opened the copy')


def check_copy(candidates, database, root, normal, pairs, acknowledged, prefixes, epochs, acked_epochs):
    root.mkdir()
    host, configuration, handle = open_copy(candidates, database, root, normal)
    try:
        with host.session() as stream:
            observed = []
            for index, (left, right) in enumerate(pairs):
                replies = [exchange(stream, execute(handle, key)) for key in (left, right)]
                assert all(reply['status'] == 'success' for reply in replies), replies
                left_value, right_value = (reply['value'] for reply in replies)
                assert left_value + right_value == INITIAL_LEFT, ('partial transfer', index, replies)
                assert right_value >= max(acknowledged[index], default=0), (
                    'acknowledged transfer lost', index, right_value, max(acknowledged[index]))
                observed.append(right_value)
            assert configuration >= acked_epochs, ('acknowledged migration lost', configuration)
            # The descriptor must match exactly the epochs in the recovered prefix.
            lsns = [lsn for lsn in prefixes.get(tuple(observed), ())
                    if sum(epoch <= lsn for epoch in epochs) == configuration]
            assert lsns, ('not a batch prefix of the commit order', observed, configuration)
            # The recovered log accepts new durable writes.
            assert exchange(stream, execute(handle, pairs[0])) == {
                'status': 'success', 'value': observed[0] + 1}
            return min(lsns), configuration
    finally:
        host.close()
        shutil.rmtree(root, ignore_errors=True)


def run_once(root, number, args, random):
    root.mkdir()
    migrations = args.migrations if number % args.migration_every == args.migration_every - 1 else 0
    kinds = sorted(kind for kind in KINDS if KINDS[kind][bool(migrations)])
    kind = args.kind if args.kind in kinds else random.choice(kinds)
    low, high = KINDS[kind][bool(migrations)]
    occurrence = random.randint(low, min(high, migrations) if kind == 'epoch' else high)
    seed = args.seed + number * args.trials
    app, pairs = fixture(root)
    images = root / 'images'
    source = root / 'source'
    source.mkdir()
    host = Host(app, args.fault_binary, source / 'db', source, 'create', env={
        'JAYDB_POWER_LOSS_CUT': f'{kind}:{occurrence}',
        'JAYDB_POWER_LOSS_DIR': str(images),
        'JAYDB_POWER_LOSS_CONTROLLER': str(args.normal_binary),
        'JAYDB_POWER_LOSS_SEED': str(seed),
        'JAYDB_POWER_LOSS_TRIALS': str(args.trials),
    })
    candidates, epochs = [app], []
    acknowledged = [set() for _ in pairs]
    try:
        with host.session() as stream:
            handle = host.prepare(stream)
        for phase in range(migrations + 1):
            last = phase == migrations
            for pair, seen in enumerate(write_until_cut(host, pairs, handle,
                                                        args.run_limit if last else args.burst)):
                assert not acknowledged[pair] & seen, 'a transfer was acknowledged twice'
                acknowledged[pair] |= seen
            if last or host.process.poll() is not None:
                break
            candidates.append(migrated_app(candidates[0], root, phase + 1))
            lsn = migrate(host, candidates[-1], root)
            if lsn is None:
                break
            epochs.append(lsn)
            try:
                with host.session() as stream:
                    handle = host.prepare(stream)
            except (AssertionError, *DISCONNECT):
                if host.process.poll() is None:
                    raise
                break
        try:
            status = host.process.wait(timeout=60)
        except subprocess.TimeoutExpired:
            status = None
        if status != 86:
            event('no-cut', run=number, kind=kind, occurrence=occurrence, status=status)
            return None
        segments = sorted(path.name for path in (source / 'db').glob('segment-*'))
    finally:
        host.close()
    manifest = json.loads((images / 'manifest.json').read_text())
    prefixes, groups, written, written_epochs = oracle(pairs, acknowledged, manifest, epochs)
    candidates = candidates[:len(written_epochs) + 1]
    event('cut', run=number, kind=kind, occurrence=occurrence, written=written,
          acknowledged=sum(map(len, acknowledged)), group_commits=groups,
          epochs=written_epochs, acknowledged_epochs=epochs, segments=segments)

    results, errors = [], []
    with ThreadPoolExecutor(args.parallel) as pool:
        futures = {
            pool.submit(check_copy, candidates, images / f'trial-{trial}', root / f'open-{trial}',
                        args.normal_binary, pairs, acknowledged, prefixes, written_epochs,
                        len(epochs)): trial
            for trial in range(seed, seed + args.trials)
        }
        for future in as_completed(futures):
            try:
                results.append(future.result())
            except Exception as error:
                errors.append(futures[future])
                event('fail', run=number, kind=kind, seed=futures[future], error=str(error)[:4000])
    lost = sum(lsn < written for lsn, _ in results)
    event('run', run=number, kind=kind, passed=len(results), failed=len(errors),
          recovered=sorted(set(results)), lost_unacknowledged_tail=lost)
    if not args.keep and not errors:
        shutil.rmtree(images, ignore_errors=True)
    return {'kind': kind, 'passed': len(results), 'failed': len(errors), 'groups': groups,
            'lost': lost, 'epochs': len(written_epochs), 'rotated': len(segments) > 1}


def run(root, args):
    random = Random(args.seed)
    totals = {'runs': 0, 'no_cut': 0, 'aborted': 0, 'trials': 0, 'failed': 0,
              'group_commits': 0, 'trials_with_lost_unacknowledged_tail': 0,
              'epochs_written': 0, 'rotated_runs': 0, 'by_kind': {}}
    for number in range(args.runs):
        try:
            result = run_once(root / f'run-{number}', number, args, random)
        except Exception:
            totals['aborted'] += 1
            event('aborted', run=number, error=traceback.format_exc()[-4000:])
            continue
        if result is None:
            totals['no_cut'] += 1
            continue
        totals['runs'] += 1
        totals['trials'] += result['passed'] + result['failed']
        totals['failed'] += result['failed']
        totals['group_commits'] += result['groups']
        totals['trials_with_lost_unacknowledged_tail'] += result['lost']
        totals['epochs_written'] += result['epochs']
        totals['rotated_runs'] += result['rotated']
        kind = totals['by_kind'].setdefault(result['kind'], {'runs': 0, 'trials': 0})
        kind['runs'] += 1
        kind['trials'] += result['passed'] + result['failed']
        if not args.keep:
            shutil.rmtree(root / f'run-{number}', ignore_errors=True)
    event('summary', **totals)
    return int(bool(totals['failed'] or totals['aborted'] or totals['no_cut']))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--fault-binary', type=Path, required=True)
    parser.add_argument('--normal-binary', type=Path, default=ROOT / 'target/release/jaydb2')
    parser.add_argument('--runs', type=int, default=20, help='Workloads, each cut once')
    parser.add_argument('--trials', type=int, default=8, help='Randomized copies per cut')
    parser.add_argument('--kind', choices=sorted(KINDS), help='Prefer this hook kind where it applies')
    parser.add_argument('--migrations', type=int, default=4,
                        help='Online migrations per migration run; their epoch frames rotate a segment')
    parser.add_argument('--migration-every', type=int, default=3, help='Every n-th run migrates')
    parser.add_argument('--burst', type=float, default=2, help='Seconds of transfers between migrations')
    parser.add_argument('--parallel', type=int, default=3, help='Concurrent reopens')
    parser.add_argument('--run-limit', type=float, default=300, help='Seconds before a run without a cut stops')
    parser.add_argument('--seed', type=int, default=93821)
    parser.add_argument('--keep', action='store_true', help='Keep the copies and fixtures')
    args = parser.parse_args()
    args.fault_binary = args.fault_binary.resolve()
    args.normal_binary = args.normal_binary.resolve()
    if min(args.runs, args.trials, args.parallel, args.migration_every) < 1:
        parser.error('runs, trials and parallel must be positive')
    if args.fault_binary == args.normal_binary:
        parser.error('provide separate fault-injection and normal binaries')
    _, hard_limit = resource.getrlimit(resource.RLIMIT_STACK)
    resource.setrlimit(resource.RLIMIT_STACK, (hard_limit, hard_limit))
    workspace = Path(tempfile.mkdtemp(prefix='jaydb-power-', dir=os.environ.get('TMPDIR', '/tmp')))
    event('workspace', path=str(workspace))
    try:
        return run(workspace, args)
    finally:
        if not args.keep:
            shutil.rmtree(workspace, ignore_errors=True)


if __name__ == '__main__':
    raise SystemExit(main())
