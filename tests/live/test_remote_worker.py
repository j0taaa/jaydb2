"""Exercise the checked native live ABI against the fresh-process task service."""

from contextlib import contextmanager
import json
import os
from pathlib import Path
import select
from statistics import median
import subprocess
import tempfile
from time import perf_counter
import unittest

from applications.tasks.app import prepare
from tests.service.test_end_to_end import ROOT, Server
from tools.client import decode, encode, frame, prepared_frame, unframe


RTS = ['+RTS', '--threads', '1', '--gpu', 'off', '-RTS']
USERS = {
    'alice-token': {'id': 'alice', 'kind': 'user', 'credential': 'alice-token'},
    'bob-token': {'id': 'bob', 'kind': 'user', 'credential': 'bob-token'},
}
OP_FIELDS = {
    'authenticate': ('credential',),
    'read_cell': ('collection', 'key', 'column'),
    'keys': ('collection',),
    'define_row': ('collection', 'key', 'fields'),
    'remove_row': ('collection', 'key'),
}


def block(payload):
    return len(payload).to_bytes(8, 'big') + payload


def split(packet):
    size = int.from_bytes(packet[:8], 'big')
    assert len(packet) >= 8 + size
    return packet[8:8 + size], packet[8 + size:]


def answer(result, **fields):
    return b'\x06' + (1 + len(fields)).to_bytes(8, 'big') + b''.join(
        encode(name) + encode(value) for name, value in [('result', result), *fields.items()])


class FakeHost:
    def __init__(self):
        self.rows = {'alice': {}, 'bob': {}}

    def transaction(self):
        # A refusal must discard even the valid write issued before it.
        return {table: rows.copy() for table, rows in self.rows.items()}

    def reply(self, payload, working):
        assert payload[0] == 6
        # The fixed-order private record carries canonical values. Read its
        # alternating names and values as a list to retain the wire order.
        field_count = int.from_bytes(payload[1:9], 'big')
        values = decode(b'\x05' + (2 * field_count).to_bytes(8, 'big') + payload[9:])
        assert values[0] == 'op'
        op = values[1]
        assert tuple(values[2::2]) == OP_FIELDS[op], values
        fields = dict(zip(values[2::2], values[3::2], strict=True))
        if op == 'authenticate':
            user = USERS.get(fields['credential'])
            return answer('no_user') if user is None else answer('user', **user)
        rows = working[fields['collection']]
        if op == 'keys':
            return answer('keys', keys=sorted(rows))
        key = fields['key']
        if op == 'read_cell':
            return answer('row_absent') if key not in rows else answer('cell', value=rows[key][fields['column']])
        if op == 'define_row':
            rows[key] = fields['fields']
        elif op == 'remove_row':
            rows.pop(key, None)
        return answer('changed')


@contextmanager
def worker(program):
    with tempfile.TemporaryFile() as errors, subprocess.Popen([str(program), *RTS],
            cwd=ROOT, env=dict(os.environ, BENDRTS=''), stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=errors, bufsize=0) as child:
        try:
            yield child, errors
        finally:
            if child.poll() is None:
                child.kill()
                child.wait(timeout=10)


def diagnostics(errors):
    return os.pread(errors.fileno(), os.fstat(errors.fileno()).st_size, 0)


def write(child, payload):
    data = memoryview(block(payload))
    while data:
        data = data[child.stdin.write(data):]


def read(child):
    def exact(size):
        data = bytearray()
        deadline = perf_counter() + 10
        while len(data) < size:
            ready, _, _ = select.select([child.stdout], [], [], max(0, deadline - perf_counter()))
            assert ready, 'live worker timed out'
            part = os.read(child.stdout.fileno(), size - len(data))
            assert part, 'live worker closed before the final frame'
            data.extend(part)
        return bytes(data)

    return exact(int.from_bytes(exact(8), 'big'))


def exchange(child, request, host):
    working = host.transaction()
    write(child, request)
    while (packet := read(child))[0] == 2:
        write(child, host.reply(packet[1:], working))
    response = packet[1:]
    assert packet[0] == int(unframe(response)['status'] == 'success')
    if packet[0]:
        host.rows = working
    return response


def baseline(server, request):
    server.process.stdin.write(request)
    server.process.stdin.flush()
    header = server.read(8)
    return header + server.read(int.from_bytes(header, 'big'))


def rss_kib(pid):
    status = Path(f'/proc/{pid}/status').read_text()
    return int(next(line.split()[1] for line in status.splitlines() if line.startswith('VmRSS:')))


def build(work, output, metadata, purpose):
    locked = json.loads((ROOT/'tools/admission/toolchain.lock.json').read_text())
    toolchain = ROOT/'.tools'
    result = subprocess.run(['node', '--stack_size=65536', str(work/'runtime/tools/service/stage.mjs'),
        purpose, str(work), str(output), str(metadata), str(toolchain/('bend-source-' + locked['version'])),
        str(toolchain/('bendtt-' + locked['kernelSha256']))],
        cwd=ROOT, capture_output=True, text=True, timeout=180)
    assert result.returncode == 0, result.stdout + result.stderr
    report = json.loads((output/'checked.c.json').read_text())['admission']
    assert report['primary'] and report['bendtt']
    return Path(json.loads(result.stdout)['program'])


def direct_metadata(work, destination, message):
    root = encode({'tables': [{'name': 'alice', 'rows': []}, {'name': 'bob', 'rows': []}],
                   'users': list(USERS.values())})
    # Use the frozen executable to generate exactly the same concrete
    # bindings and Instance the service would use.
    authenticator, = (work/'authenticate').glob('*.program')
    result = subprocess.run([str(authenticator), *RTS], input=block(root) + message,
                            capture_output=True, timeout=10, cwd=ROOT)
    assert result.returncode == 0 and result.stdout[:1] == b'\x01', result.stderr
    _, packet = split(result.stdout[1:])
    code, packet = split(packet)
    proof, packet = split(packet)
    instance, bindings = split(packet)
    destination.mkdir()
    for name, value in zip(('Client', 'ClientProof', 'Instance', 'Bindings'),
                           (code, proof, instance, bindings), strict=True):
        (destination/f'{name}.bend').write_bytes(value)


class LiveWorkerTest(unittest.TestCase):
    def test_task_worker(self):
        with tempfile.TemporaryDirectory(prefix='jaydb-live-') as tmp:
            tmp = Path(tmp)
            app = tmp/'app'
            app.mkdir()
            prepare(app)
            code = (app/'Client.bend').read_text()
            proof = (app/'ClientProof.bend').read_text()
            universal = proof.replace('def B.certificate(s, valid, identity, n):',
                'def B.certificate(ctx, args, s, valid, identity, n):'
                ).replace('I.context()', 'ctx').replace('I.arguments()', 'args')
            server = Server(app, env=dict(os.environ, TMPDIR=str(tmp)), threads=1)
            try:
                self.exercise(server, tmp, code, proof, universal)
                server.finish()
            finally:
                server.close()

    def exercise(self, server, tmp, code, proof, universal):
        receipt = server.prepared(0, code, 'alice-token', proof=universal)
        self.assertEqual(receipt['status'], 'prepared', server.diagnostics())
        handle = receipt['value']
        work, = tmp.glob(f'jaydb2-{server.process.pid}-*')
        metadata, = work.glob('request-*/metadata')
        live = build(work, tmp/'live', metadata, 'live-prepare')
        environment = json.loads((work/'environment.json').read_text())['identity']
        registry = block(encode([[[environment, handle, code, universal, False, '']], [handle]]))
        host = FakeHost()
        cases = [
            ('alice-token', ['save', 't1', 'Buy bread', False], 'success'),
            ('alice-token', ['view', 't1'], 'success'),
            ('bob-token', ['view', 't1'], 'success'),
            ('wrong-token', ['view', 't1'], 'authentication'),
            ('alice-token', ['cancel', 't1', 'Discard this', True], 'refusal'),
            ('alice-token', ['view', 't1'], 'success'),
            ('alice-token', ['list'], 'success'),
        ]
        with worker(live) as (child, errors):
            comparisons = []
            for credential, args, status in cases:
                request = prepared_frame(1, handle, credential, args)
                expected = baseline(server, request)
                live_request = registry + request[8:]
                actual = exchange(child, live_request, host)
                self.assertEqual(actual, expected)
                comparisons.append((live_request, expected))
                self.assertEqual(unframe(actual)['status'], status)
                if credential == 'bob-token':
                    self.assertIsNone(unframe(actual)['value'])

            # A syntactically valid row for a different credential cannot
            # authenticate, even if the handle and its proof check would fail.
            invalid = prepared_frame(1, 'unknown', 'wrong-token', proof='invalid')
            write(child, registry + invalid[8:])
            self.assertEqual(read(child)[0], 2)
            write(child, answer('user', **USERS['alice-token']))
            self.assertEqual(read(child), b'\0' + baseline(server, invalid))

            # FailureData short circuits a continuation that otherwise
            # returns a value; no provisional rows are committed.
            point = prepared_frame(1, handle, 'alice-token', ['view', 't1'])
            write(child, registry + point[8:])
            self.assertEqual(read(child)[0], 2)
            write(child, answer('user', **USERS['alice-token']))
            self.assertEqual(read(child)[0], 2)
            write(child, answer('data_error'))
            self.assertEqual(read(child), b'\0' + frame({'status': 'data', 'value': None}))

            # Compare wall time with the public prepared path, which starts
            # fresh authentication and execution subprocesses for every call.
            expected = baseline(server, point)
            warmup, count, benchmark = 500, 3500, 40
            samples, live_ms, fresh_ms = [], [], []
            for i in range(count):
                if i % 25 == 0:
                    for request, response in comparisons:
                        self.assertEqual(exchange(child, request, host), response)
                start = perf_counter()
                actual = exchange(child, registry + point[8:], host)
                ms = (perf_counter() - start) * 1000
                self.assertEqual(actual, expected)
                if i >= warmup and (i + 1) % 250 == 0:
                    samples.append(rss_kib(child.pid))
                if warmup <= i < warmup + benchmark:
                    live_ms.append(ms)
                    start = perf_counter()
                    self.assertEqual(baseline(server, point), expected)
                    fresh_ms.append((perf_counter() - start) * 1000)
            print(f'point read median over {benchmark} requests: '
                  f'persistent {median(live_ms):.3f} ms, fresh service {median(fresh_ms):.3f} ms')
            print(f'RSS after warmup, KiB, over {count} reads and recurring mixed requests: {samples}')
            self.assertLessEqual(max(samples) - min(samples), 2048)
            child.stdin.close()
            self.assertEqual(child.wait(timeout=10), 0, diagnostics(errors))
            self.assertEqual(child.stdout.read(), b'')

        # The direct entry uses concrete bindings and exits while stdin
        # remains open, after it has answered exactly one request.
        args = ['view', 't1']
        direct_message = frame(dict(code=code, proof=proof, credential='alice-token', arguments=args))
        direct_metadata(work, tmp/'metadata', direct_message[8:])
        direct = build(work, tmp/'direct', tmp/'metadata', 'live-execute')
        with worker(direct) as (child, errors):
            self.assertEqual(exchange(child, direct_message[8:], host), expected)
            self.assertEqual(child.wait(timeout=10), 0, diagnostics(errors))
            self.assertEqual(child.stdout.read(), b'')

        # Malformed, wrong-shape, or truncated answers fail-stop with no
        # final packet. The canonical sorted order would also be wrong here.
        for bad in (answer('cell', value=True), encode(USERS['alice-token'] | {'result': 'user'})):
            with worker(live) as (child, errors):
                write(child, registry + point[8:])
                self.assertEqual(read(child)[0], 2)
                write(child, bad)
                self.assertEqual(child.wait(timeout=10), 1, diagnostics(errors))
                self.assertEqual(child.stdout.read(), b'')
                self.assertIn(b'inconsistent', diagnostics(errors))

        with worker(live) as (child, errors):
            write(child, registry + point[8:])
            self.assertEqual(read(child)[0], 2)
            child.stdin.write(b'\x00')
            child.stdin.close()
            self.assertEqual(child.wait(timeout=10), 1, diagnostics(errors))
            self.assertEqual(child.stdout.read(), b'')
            self.assertIn(b'truncated live frame header', diagnostics(errors))


if __name__ == '__main__':
    unittest.main()
