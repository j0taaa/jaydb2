"""HTTP -> canonical frames -> real Rust/Bend database, with no mocks."""
from concurrent.futures import ThreadPoolExecutor
from http.cookiejar import CookieJar
import json
import threading
import unittest
from urllib.error import HTTPError
from urllib.request import build_opener, HTTPCookieProcessor, Request

from demo.server import CODE, PROOF, DemoServer


class DemoHTTPTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.server = DemoServer(('127.0.0.1', 0))
        cls.base = f'http://127.0.0.1:{cls.server.server_port}'
        cls.thread = threading.Thread(target=cls.server.serve_forever, daemon=True)
        cls.thread.start()

    @classmethod
    def tearDownClass(cls):
        cls.server.shutdown()
        cls.thread.join()
        cls.server.server_close()

    def browser(self):
        return build_opener(HTTPCookieProcessor(CookieJar()))

    def call(self, browser, path, body=None):
        request = Request(self.base + path, data=json.dumps(body).encode() if body is not None else None,
                          headers={'Content-Type': 'application/json'})
        with browser.open(request, timeout=180) as response:
            return json.load(response)

    def execute(self, browser, action, credential, value=None):
        return self.call(browser, '/api/execute', {'action': action, 'credential': credential, 'value': value})

    def test_real_database_publication_rollback_proof_and_session_isolation(self):
        browser = self.browser()
        initial = self.call(browser, '/api/session', {})
        pid = initial['database_pid']
        self.assertTrue(initial['alive'])
        self.assertEqual(initial['receipts'], [])
        self.assertEqual(initial['inspection']['state'], {'tables': [], 'users': [
            {'credential': 'alice-token', 'id': 'alice', 'kind': 'user'},
            {'credential': 'bob-token', 'id': 'bob', 'kind': 'user'}]})
        self.assertIsNone(initial['inspection']['error'])
        sources = self.call(browser, '/api/sources')
        self.assertEqual(sources['schema']['users']['primary_key'], 'id')
        self.assertEqual([column['name'] for column in sources['schema']['users']['columns']],
                         ['credential', 'id', 'kind'])
        self.assertIn('AllAllowed', sources['configuration'])
        self.assertIn('Requirements.bend', sources['files'])
        self.assertEqual(sources['environment']['identity'], initial['environment_identity'])

        # Unicode crosses JSON, the canonical wire codec, and native Bend.
        changed = self.execute(browser, 'rotate', 'alice-token', 'alice-new-é-🔑')
        self.assertEqual(changed['response'], {'status': 'success', 'value': 'alice-new-é-🔑'})
        self.assertEqual(changed['database_pid'], pid)
        self.assertGreater(changed['request_bytes'], 8)
        self.assertGreater(changed['response_bytes'], 8)
        self.assertGreater(changed['duration_ms'], 0)
        self.assertEqual(changed['request']['code'], CODE)
        self.assertEqual(changed['request']['proof'], PROOF)
        self.assertEqual(json.loads(changed['state_before_json'])['users'][0]['credential'], 'alice-token')
        self.assertEqual(json.loads(changed['state_after_json'])['users'][0]['credential'], 'alice-new-é-🔑')
        self.assertEqual(self.execute(browser, 'verify', 'alice-token')['response'],
                         {'status': 'authentication', 'value': None})

        rolled_back = self.execute(browser, 'rollback', 'alice-new-é-🔑')
        self.assertEqual(rolled_back['response'],
                         {'status': 'refusal', 'value': 'cancelled'})
        self.assertEqual(rolled_back['state_before_json'], rolled_back['state_after_json'])
        self.assertEqual(self.execute(browser, 'verify', 'discarded')['response'],
                         {'status': 'authentication', 'value': None})
        self.assertEqual(self.execute(browser, 'verify', 'alice-new-é-🔑')['response'],
                         {'status': 'success', 'value': 'alice-new-é-🔑'})
        rejected = self.execute(browser, 'forbidden', 'alice-new-é-🔑')
        self.assertEqual(rejected['response'],
                         {'status': 'certificate', 'value': None})
        self.assertIsNotNone(rejected['diagnostic'])
        self.assertEqual(rejected['state_before_json'], rejected['state_after_json'])
        self.assertEqual(self.execute(browser, 'verify', 'alice-new-é-🔑')['response'],
                         {'status': 'success', 'value': 'alice-new-é-🔑'})

        # The database also owns uniqueness, not a JavaScript or HTTP check.
        self.assertEqual(self.execute(browser, 'rotate', 'alice-new-é-🔑', 'bob-token')['response'],
                         {'status': 'data', 'value': None})
        self.assertEqual(self.execute(browser, 'verify', 'bob-token')['response'],
                         {'status': 'success', 'value': 'bob-token'})
        self.assertEqual(self.execute(browser, 'verify', 'alice-new-é-🔑')['response'],
                         {'status': 'success', 'value': 'alice-new-é-🔑'})

        # Concurrent HTTP requests share one serial pipe without mixing frames.
        with ThreadPoolExecutor(max_workers=2) as pool:
            responses = list(pool.map(lambda value: self.execute(browser, 'rotate', 'bob-token', value),
                                      ['bob-one', 'bob-two']))
        self.assertEqual(sorted(result['response']['status'] for result in responses),
                         ['authentication', 'success'])
        state = self.call(browser, '/api/session')
        self.assertEqual(state['database_pid'], pid)
        self.assertEqual(len(state['receipts']), 12)
        self.assertEqual([item['sequence'] for item in state['receipts']], list(range(1, 13)))

        other = self.browser()
        fresh = self.call(other, '/api/session', {})
        self.assertNotEqual(fresh['database_pid'], pid)
        self.assertEqual(self.execute(other, 'verify', 'alice-token')['response'],
                         {'status': 'success', 'value': 'alice-token'})
        self.call(other, '/api/reset', {})

        self.call(browser, '/api/reset', {})
        self.assertEqual(self.call(browser, '/api/session'), {'session': None})
        restarted = self.call(browser, '/api/session', {})
        self.assertNotEqual(restarted['database_pid'], pid)
        self.assertEqual(self.execute(browser, 'verify', 'alice-token')['response'],
                         {'status': 'success', 'value': 'alice-token'})
        self.call(browser, '/api/reset', {})

    def test_custom_program_proof_and_live_published_state(self):
        browser = self.browser()
        self.call(browser, '/api/session', {})
        try:
            code = CODE.replace('S.Finish{value}', 'S.Finish{D.VText{"custom-proof-ok"}}')
            proof = PROOF + '\n# Custom proof submitted verbatim through HTTP.\n'
            body = {'action': 'custom', 'credential': 'alice-token', 'code': code,
                    'proof': proof, 'arguments_json': '"alice-custom"'}
            with browser.open(self.base + '/api/events', timeout=180) as stream:
                self.assertEqual(stream.headers['Content-Type'], 'text/event-stream')

                def event():
                    while True:
                        line = stream.readline()
                        if not line:
                            self.fail('Event stream closed')
                        if line.startswith(b'data: '):
                            return json.loads(line[6:])

                initial = event()
                self.assertEqual(initial['inspection']['state']['users'][0]['credential'], 'alice-token')
                with ThreadPoolExecutor(max_workers=1) as pool:
                    pending = pool.submit(self.call, browser, '/api/execute', body)
                    while True:
                        running = event()
                        if running['running']:
                            break
                    # Inspection remains responsive during the actual compiler.
                    during = self.call(browser, '/api/session')
                    self.assertTrue(during['running'])
                    self.assertEqual(during['inspection']['sha256'], initial['inspection']['sha256'])
                    result = pending.result(timeout=180)
                    while True:
                        published = event()
                        if published['inspection']['state']['users'][0]['credential'] == 'alice-custom':
                            break
                self.assertEqual(result['response'], {'status': 'success', 'value': 'custom-proof-ok'})
                self.assertEqual(result['request']['code'], code)
                self.assertEqual(result['request']['proof'], proof)
                self.assertIn('def context()', result['generated_sources']['Instance.bend'])
                self.assertIn('def code()', result['generated_sources']['Bindings.bend'])
                self.assertEqual(result['state_sha256'], published['inspection']['sha256'])

            rejected = self.call(browser, '/api/execute', {**body, 'credential': 'alice-custom',
                'proof': proof + '\nthis is not a Bend definition\n'})
            self.assertEqual(rejected['response']['status'], 'certificate')
            self.assertTrue(rejected['diagnostic']['message'])
            self.assertEqual(rejected['state_before_json'], rejected['state_after_json'])
            with self.assertRaises(HTTPError) as raised:
                self.call(browser, '/api/execute', {**body, 'code': code + '#' * 32768})
            self.assertEqual(raised.exception.code, 400)
            raised.exception.close()
            state = self.call(browser, '/api/session')
            self.assertTrue(state['alive'])
            self.assertEqual(state['inspection']['state']['users'][0]['credential'], 'alice-custom')
            self.assertEqual(state['receipts'][-1]['sequence'], 2)
        finally:
            self.call(browser, '/api/reset', {})

    def test_http_boundaries_and_no_implicit_instance_or_replay(self):
        browser = self.browser()
        self.assertEqual(self.call(browser, '/api/health')['transport'], 'real-cli')
        self.assertEqual(self.call(browser, '/api/session'), {'session': None})
        for body, status in [({'action': 'rotate', 'credential': 'alice-token', 'value': 'new'}, 409),
                             ({'action': 'shell', 'credential': 'x'}, 400),
                             ({'action': 'rotate', 'credential': 'x', 'value': 123}, 400),
                             ({'action': 'verify', 'credential': 'x' * 257}, 400)]:
            with self.assertRaises(HTTPError) as raised:
                self.call(browser, '/api/execute', body)
            self.assertEqual(raised.exception.code, status)
            raised.exception.close()
        with self.assertRaises(HTTPError) as raised:
            browser.open(Request(self.base + '/api/session', data=b'{}', headers={
                'Content-Type': 'application/json', 'Origin': 'https://another.example'}))
        self.assertEqual(raised.exception.code, 403)
        raised.exception.close()
        with self.assertRaises(HTTPError) as raised:
            browser.open(self.base + '/../../examples/access/Seed.bend')
        self.assertEqual(raised.exception.code, 404)
        raised.exception.close()
        with browser.open(self.base + '/') as response:
            self.assertIn("script-src 'self'", response.headers['Content-Security-Policy'])
            self.assertIn(b'JayDB2', response.read())
        self.assertEqual(self.call(browser, '/api/session'), {'session': None})


if __name__ == '__main__':
    unittest.main(verbosity=2)
