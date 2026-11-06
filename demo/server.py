#!/usr/bin/env python3
"""HTTP workbench for JayDB2, with opt-in administrator inspection."""
from __future__ import annotations

import argparse
from collections import deque
import hashlib
from http.cookies import SimpleCookie
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import os
from pathlib import Path
import re
import secrets
import select
import signal
import socket
import subprocess
import sys
import tempfile
import threading
import time
from urllib.parse import urlsplit

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.client import decode, frame, unframe

EXAMPLE = ROOT / 'examples/access'
CODE = (EXAMPLE / 'Client.bend').read_text()
PROOF = (EXAMPLE / 'ClientProof.bend').read_text()
FORBIDDEN = CODE.replace('D.ReadCell{D.Users{}, id, "credential"}',
                         'D.ReadCell{D.Users{}, "bob", "credential"}')
COOKIE = 'jaydb2_demo'
TTL = 30 * 60
MAX_SESSIONS = 8
CALL_TIMEOUT = 180  # Web adapter watchdog; outside the database's contract.
COMPILERS = threading.BoundedSemaphore(2)


def schema_from_sources(sources):
    """Display declarations from this fixed example, never infer state."""
    data = sources.get('Data.bend', '')
    declaration = re.search(r'def schema_users\(\).*?\n  (SchemaTable[^\n]+)', data)
    if not declaration:
        return {'error': 'Schema declaration unavailable; inspect Data.bend.'}
    text = declaration[1]
    table = re.search(r'SchemaTable\{"([^"]+)", "([^"]+)"', text)
    columns = [{'name': name, 'type': kind, 'optional': optional == 'True'}
               for name, kind, optional in re.findall(r'Column\{"([^"]+)", (\w+)\{\}, (True|False)\{\}\}', text)]
    return {'source': 'Data.schema_users / Configuration.schema',
            'users': {'name': table[1], 'primary_key': table[2], 'columns': columns},
            'application_declaration': sources.get('Configuration.bend', '').split('def schema()', 1)[-1].split('\ndef ', 1)[0].strip(),
            'users_declaration': text}


class Unavailable(Exception):
    pass


class Session:
    def __init__(self):
        self.lock = threading.RLock()
        self.view = threading.Condition()
        self.last_used = time.monotonic()
        self.created_at = time.time()
        self.receipts = deque(maxlen=40)
        self.sequence = 0
        self.native_sequence = -1
        self.call_sequence = 0
        self.version = 0
        self.state = None
        self.state_bytes = 0
        self.state_hash = None
        self.observed_at = None
        self.sources = {}
        self.seed_source = None
        self.environment = None
        self.limits = None
        self.diagnostic = None
        self.generated_sources = {}
        self.inspection_error = None
        self.running = False
        self.failed = False
        self.errors = deque(maxlen=30)
        self.inspection = None
        self.directory = tempfile.TemporaryDirectory(prefix='jaydb2-inspect-')
        self.listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self.listener.settimeout(CALL_TIMEOUT)
        endpoint = str(Path(self.directory.name) / 'observer.sock')
        self.listener.bind(endpoint)
        self.listener.listen(1)
        try:
            self.process = subprocess.Popen([
                str(ROOT / 'jaydb2'), '--configuration', str(EXAMPLE / 'Configuration.bend'),
                '--seed', str(EXAMPLE / 'Seed.bend'), '--inspect-socket', endpoint], cwd=ROOT,
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                start_new_session=True)
        except Exception:
            self.listener.close()
            self.directory.cleanup()
            raise
        self.error_thread = threading.Thread(target=self._drain_errors, daemon=True)
        self.inspection_thread = threading.Thread(target=self._inspect, daemon=True)
        self.error_thread.start()
        self.inspection_thread.start()

    def _drain_errors(self):
        try:
            for line in self.process.stderr:
                self.errors.append(line.decode('utf-8', 'replace').rstrip()[:2000])
        finally:
            self.process.stderr.close()

    def _inspect(self):
        def read(size):
            result = bytearray()
            while len(result) < size:
                chunk = self.inspection.recv(size - len(result))
                if not chunk:
                    raise EOFError('Inspector disconnected')
                result.extend(chunk)
            return bytes(result)

        def packet(limit):
            size = int.from_bytes(read(8), 'big')
            if size > limit:
                raise ValueError('Inspector frame exceeds its limit')
            return read(size)

        try:
            self.inspection, _ = self.listener.accept()
            self.listener.close()
            while True:
                metadata = json.loads(packet(2 * 1024 * 1024))
                raw_state = packet(65536)
                state = decode(raw_state)
                with self.view:
                    if metadata['event'] == 'initialized':
                        self.sources = metadata['sources']
                        self.seed_source = metadata['seed']
                        self.environment = metadata['environment']
                        self.limits = metadata['limits']
                    elif metadata['event'] == 'authenticated':
                        self.generated_sources = metadata['generated_sources']
                    self.native_sequence = metadata['sequence']
                    self.state = state
                    self.state_bytes = len(raw_state)
                    self.state_hash = hashlib.sha256(raw_state).hexdigest()
                    self.observed_at = time.time()
                    self.diagnostic = metadata.get('diagnostic')
                    self.version += 1
                    self.view.notify_all()
        except (OSError, EOFError, ValueError, KeyError) as error:
            with self.view:
                self.inspection_error = str(error)
                self.version += 1
                self.view.notify_all()
        finally:
            if self.inspection:
                self.inspection.close()

    def _read(self, size, deadline):
        result = bytearray()
        while len(result) < size:
            remaining = deadline - time.monotonic()
            if remaining <= 0 or not select.select([self.process.stdout], [], [], remaining)[0]:
                raise Unavailable('Incomplete response or timeout. Outcome unknown; no automatic retry.')
            chunk = os.read(self.process.stdout.fileno(), size - len(result))
            if not chunk:
                if self.state is None:
                    # Initialization failures have no transaction outcome to
                    # preserve. Report the actual host/compiler error so a
                    # missing configuration or stale deployment is actionable.
                    self.error_thread.join(timeout=1)
                    diagnostic = '\n'.join(self.errors)[-6000:]
                    raise Unavailable('Database startup failed: ' + (diagnostic or 'process ended before initialization completed.'))
                raise Unavailable('Database process ended. Reset the instance to reload the seed.')
            result.extend(chunk)
        return bytes(result)

    def _write(self, data, deadline):
        # A pipe can fill before startup finishes or after a stalled reader.
        # Polling a blocking fd alone would still let a large write hang.
        fd = self.process.stdin.fileno()
        os.set_blocking(fd, False)
        pending = memoryview(data)
        while pending:
            remaining = deadline - time.monotonic()
            if remaining <= 0 or not select.select([], [fd], [], remaining)[1]:
                raise Unavailable('Incomplete request or timeout. Outcome unknown; no automatic retry.')
            try:
                count = os.write(fd, pending)
            except BlockingIOError:
                continue
            pending = pending[count:]

    def _call(self, code, proof, credential, arguments):
        if self.failed or self.process.poll() is not None:
            raise Unavailable('Database unavailable. Reset the instance to reload the seed.')
        request = {'code': code, 'proof': proof, 'credential': credential, 'arguments': arguments}
        encoded = frame(request)
        if len(encoded) - 8 > 32768:
            raise ValueError('Canonical request exceeds the 32,768-byte message limit.')
        self.call_sequence += 1
        try:
            deadline = time.monotonic() + CALL_TIMEOUT
            self._write(encoded, deadline)
            header = self._read(8, deadline)
            size = int.from_bytes(header, 'big')
            if size > 32768:
                raise Unavailable('Invalid database response frame.')
            response_bytes = header + self._read(size, deadline)
            response = unframe(response_bytes)
            if not isinstance(response, dict) or set(response) != {'status', 'value'}:
                raise Unavailable('Invalid database response.')
            with self.view:
                self.view.wait_for(lambda: self.native_sequence >= self.call_sequence or self.inspection_error,
                                   timeout=max(0, deadline - time.monotonic()))
                if self.native_sequence < self.call_sequence:
                    self.inspection_error = self.inspection_error or 'Published state inspection timed out'
            return response, request, len(encoded), len(response_bytes)
        except (OSError, ValueError, Unavailable) as error:
            self.close()
            raise Unavailable(str(error)) from error

    def ready(self):
        with self.lock, COMPILERS:
            response, _, _, _ = self._call(CODE, PROOF, '', None)
            if response != {'status': 'authentication', 'value': None} or self.state is None:
                self.close()
                raise Unavailable('Database initialization or inspector probe failed.')

    def execute(self, action, credential, value=None, code=None, proof=None, arguments=None):
        with self.lock, COMPILERS:
            self.last_used = time.monotonic()
            started = time.monotonic()
            if action != 'custom':
                code = FORBIDDEN if action == 'forbidden' else CODE
                proof = PROOF
                arguments = None if action in ('rollback', 'forbidden') else (credential if action == 'verify' else value)
            with self.view:
                state_before_json = json.dumps(self.state, ensure_ascii=False, indent=2)
                self.generated_sources = {}
                self.diagnostic = None
                self.running = True
                self.version += 1
                self.view.notify_all()
            try:
                response, request, sent, received = self._call(code, proof, credential, arguments)
                with self.view:
                    self.sequence += 1
                    receipt = {'sequence': self.sequence, 'action': action, 'request': request,
                               'request_json': json.dumps(request, ensure_ascii=False, indent=2),
                               'response': response, 'response_json': json.dumps(response, ensure_ascii=False, indent=2),
                               'diagnostic': self.diagnostic, 'state_sha256': self.state_hash,
                               'generated_sources': self.generated_sources,
                               'inspection_sequence': self.native_sequence,
                               'state_before_json': state_before_json,
                               'state_after_json': json.dumps(self.state, ensure_ascii=False, indent=2),
                               'duration_ms': round((time.monotonic() - started) * 1000),
                               'request_bytes': sent, 'response_bytes': received,
                               'timestamp': time.time(), 'database_pid': self.process.pid}
                    self.receipts.append(receipt)
                    return receipt
            finally:
                with self.view:
                    self.running = False
                    self.version += 1
                    self.view.notify_all()
                self.last_used = time.monotonic()

    def snapshot(self, touch=True):
        # Independent from the execution lock: readers see the last published
        # snapshot while the real compiler/worker is busy.
        if touch:
            self.last_used = time.monotonic()
        with self.view:
            return {'database_pid': self.process.pid, 'created_at': self.created_at,
                    'alive': not self.failed and self.process.poll() is None,
                    'expires_after_idle_seconds': TTL, 'receipts': list(self.receipts),
                    'running': self.running, 'version': self.version,
                    'inspection': {'sequence': self.native_sequence, 'observed_at': self.observed_at,
                                   'state': self.state, 'state_json': json.dumps(self.state, ensure_ascii=False, indent=2),
                                   'canonical_bytes': self.state_bytes, 'sha256': self.state_hash,
                                   'error': self.inspection_error},
                    'limits': self.limits, 'environment_identity': (self.environment or {}).get('identity')}

    def source_info(self):
        with self.view:
            return {'program': CODE, 'proof': PROOF, 'forbidden_program': FORBIDDEN,
                    'configuration': self.sources.get('Configuration.bend'),
                    'seed': self.seed_source,
                    'files': self.sources, 'environment': self.environment,
                    'schema': schema_from_sources(self.sources), 'limits': self.limits}

    def close(self):
        with self.lock:
            self.failed = True
            try:
                self.process.stdin.close()
            except BrokenPipeError:
                pass
            if self.process.poll() is None:
                try:
                    self.process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    try:
                        os.killpg(self.process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    self.process.wait()
            self.process.stdout.close()
            try:
                # A failed startup may never connect to the inspector. Wake
                # the reader's accept() before joining its thread.
                self.listener.shutdown(socket.SHUT_RDWR)
            except OSError:
                pass
            self.listener.close()
            if self.inspection:
                try:
                    self.inspection.shutdown(socket.SHUT_RDWR)
                except OSError:
                    pass
            self.error_thread.join(timeout=2)
            self.inspection_thread.join(timeout=2)
            self.directory.cleanup()
            with self.view:
                self.version += 1
                self.view.notify_all()


class DemoServer(ThreadingHTTPServer):
    daemon_threads = True

    def __init__(self, address):
        self.sessions = {}
        self.sessions_lock = threading.Lock()
        self.stopping = threading.Event()
        super().__init__(address, Handler)
        threading.Thread(target=self._reap, daemon=True).start()

    def _reap(self):
        while not self.stopping.wait(30):
            with self.sessions_lock:
                for token, session in list(self.sessions.items()):
                    if session.lock.acquire(blocking=False):
                        try:
                            if time.monotonic() - session.last_used > TTL:
                                session.close()
                                del self.sessions[token]
                        finally:
                            session.lock.release()

    def session(self, token):
        with self.sessions_lock:
            return self.sessions.get(token)

    def create_session(self):
        with self.sessions_lock:
            if len(self.sessions) >= MAX_SESSIONS:
                raise Unavailable('All eight demo instances are in use. Try again after a session expires.')
            token = secrets.token_urlsafe(32)
            session = Session()
            self.sessions[token] = session
        try:
            session.ready()
        except Exception:
            session.close()
            with self.sessions_lock:
                self.sessions.pop(token, None)
            raise
        return token, session

    def remove_session(self, token):
        with self.sessions_lock:
            session = self.sessions.pop(token, None)
        if session:
            session.close()

    def server_close(self):
        self.stopping.set()
        with self.sessions_lock:
            for session in self.sessions.values():
                session.close()
            self.sessions.clear()
        super().server_close()


class Handler(BaseHTTPRequestHandler):
    server_version = 'JayDB2Demo/2.0'

    def log_message(self, format, *args):
        sys.stderr.write(f'demo: {self.command} {self.path.split("?")[0]} {args[1] if len(args) > 1 else ""}\n')

    def send_data(self, status, data, content_type='application/json; charset=utf-8', cookie=None):
        if isinstance(data, (dict, list)):
            data = json.dumps(data, ensure_ascii=False).encode()
        self.send_response(status)
        self.send_header('Content-Type', content_type)
        self.send_header('Content-Length', str(len(data)))
        self.send_header('Cache-Control', 'no-store')
        self.send_header('X-Content-Type-Options', 'nosniff')
        self.send_header('Referrer-Policy', 'same-origin')
        self.send_header('Content-Security-Policy', "default-src 'self'; script-src 'self'; style-src 'self'; img-src 'self' data:; connect-src 'self'; frame-ancestors 'none'; base-uri 'none'; form-action 'self'")
        if cookie is not None:
            secure = '; Secure' if self.headers.get('X-Forwarded-Proto') == 'https' else ''
            self.send_header('Set-Cookie', f'{COOKIE}={cookie}; HttpOnly; SameSite=Strict; Path=/{secure}')
        self.end_headers()
        try:
            self.wfile.write(data)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def token(self):
        cookie = SimpleCookie()
        try:
            cookie.load(self.headers.get('Cookie', ''))
        except Exception:
            return None
        return cookie[COOKIE].value if COOKIE in cookie else None

    def events(self, session):
        self.send_response(200)
        self.send_header('Content-Type', 'text/event-stream')
        self.send_header('Cache-Control', 'no-store')
        self.send_header('X-Accel-Buffering', 'no')
        self.end_headers()
        version = -1
        try:
            while not self.server.stopping.is_set():
                with session.view:
                    session.view.wait_for(lambda: session.version != version or session.failed, timeout=15)
                    data = session.snapshot(touch=False)
                if data['version'] != version:
                    payload = json.dumps(data, ensure_ascii=False)
                    self.wfile.write(f'id: {data["version"]}\ndata: {payload}\n\n'.encode())
                    version = data['version']
                else:
                    self.wfile.write(b': keepalive\n\n')
                self.wfile.flush()
                if not data['alive']:
                    return
        except (BrokenPipeError, ConnectionResetError, OSError):
            return

    def do_GET(self):
        path = urlsplit(self.path).path
        if path == '/api/health':
            return self.send_data(200, {'service': 'jaydb2-demo', 'transport': 'real-cli', 'ok': True})
        if path in ('/api/session', '/api/sources', '/api/events'):
            session = self.server.session(self.token())
            if session is None:
                return self.send_data(409 if path != '/api/session' else 200, {'session': None, 'error': 'No active instance'} if path != '/api/session' else {'session': None})
            if path == '/api/events':
                return self.events(session)
            return self.send_data(200, session.snapshot() if path == '/api/session' else session.source_info())
        files = {'/': ('index.html', 'text/html; charset=utf-8'),
                 '/app.js': ('app.js', 'text/javascript; charset=utf-8'),
                 '/styles.css': ('styles.css', 'text/css; charset=utf-8'),
                 '/favicon.svg': ('favicon.svg', 'image/svg+xml')}
        if path not in files:
            return self.send_data(404, {'error': 'Not found'})
        name, mime = files[path]
        self.send_data(200, (Path(__file__).parent / 'static' / name).read_bytes(), mime)

    def do_POST(self):
        origin = self.headers.get('Origin')
        if origin and urlsplit(origin).netloc != self.headers.get('Host'):
            return self.send_data(403, {'error': 'Same-origin requests only'})
        if self.headers.get('Content-Type', '').split(';')[0] != 'application/json':
            return self.send_data(415, {'error': 'Send application/json'})
        try:
            size = int(self.headers.get('Content-Length', '0'))
            if not 0 < size <= 262144:
                return self.send_data(413, {'error': 'HTTP body must be 1–262144 bytes; canonical DB message limit is 32768 bytes'})
            body = json.loads(self.rfile.read(size))
            if not isinstance(body, dict):
                raise ValueError('Expected a JSON object')
            path = urlsplit(self.path).path
            token = self.token()
            if path == '/api/session':
                session = self.server.session(token)
                if session:
                    return self.send_data(200, session.snapshot())
                token, session = self.server.create_session()
                return self.send_data(201, session.snapshot(), cookie=token)
            if path == '/api/reset':
                self.server.remove_session(token)
                return self.send_data(200, {'session': None}, cookie='')
            if path != '/api/execute':
                return self.send_data(404, {'error': 'Not found'})
            action, credential, value = (body.get(key) for key in ('action', 'credential', 'value'))
            if action not in ('rotate', 'verify', 'rollback', 'forbidden', 'custom'):
                raise ValueError('Unknown operation')
            if not isinstance(credential, str) or not 1 <= len(credential.encode('utf-8')) <= 256:
                raise ValueError('Credential must contain 1–256 UTF-8 bytes')
            if action == 'rotate' and (not isinstance(value, str) or not 1 <= len(value.encode('utf-8')) <= 256):
                raise ValueError('New credential must contain 1–256 UTF-8 bytes')
            code, proof, arguments = None, None, None
            if action == 'custom':
                code, proof = body.get('code'), body.get('proof')
                if not isinstance(code, str) or not isinstance(proof, str):
                    raise ValueError('Custom requests require code and proof strings')
                arguments = json.loads(body['arguments_json']) if isinstance(body.get('arguments_json'), str) else body.get('arguments')
            session = self.server.session(token)
            if session is None:
                return self.send_data(409, {'error': 'Session expired. Reset the instance to reload the seed.'})
            self.send_data(200, session.execute(action, credential, value, code, proof, arguments))
        except (ValueError, UnicodeError, RecursionError) as error:
            self.send_data(400, {'error': str(error)})
        except (Unavailable, OSError) as error:
            self.send_data(503, {'error': str(error)})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--host', default='127.0.0.1')
    parser.add_argument('--port', default=8094, type=int)
    args = parser.parse_args()
    if not (ROOT / 'target/release/jaydb2').is_file():
        parser.error('Build the real database first: make build')
    with DemoServer((args.host, args.port)) as server:
        print(f'JayDB2 workbench: http://{args.host}:{server.server_port}', flush=True)
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            pass


if __name__ == '__main__':
    main()
