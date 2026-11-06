import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { encode, decode, frame, unframe, preparedFrame } from '../src/index.ts';
import type { Value } from '../src/index.ts';

const root = fileURLToPath(new URL('../../../', import.meta.url));
const text = (value: string) => Buffer.concat([Buffer.from([4]), u64(Buffer.byteLength(value)), Buffer.from(value)]);
function u64(n: number | bigint): Buffer { const b = Buffer.alloc(8); b.writeBigUInt64BE(BigInt(n)); return b; }

test('wire matches independent Python codec and keeps all int64 bits', () => {
  const cases: Value[] = [null, false, true, 0n, -1n, -(1n << 63n), (1n << 63n) - 1n,
    '', '\ufeffBOM', 'é e\u0301 🫖 \u0000 \u{10ffff}', [], {}, [1n, 'x', false, null],
    { z: [2n, { a: 'y' }], a: -42n }, { __proto__: null, constructor: 'safe', prototype: 'field' }];
  const python = spawnSync('python3', ['-B', '-c', `
from tools.client import encode,frame,prepared_frame
cases=[None,False,True,0,-1,-(1<<63),(1<<63)-1,'','\\ufeffBOM','é e\\u0301 🫖 \\x00 \\U0010ffff',[],{},[1,'x',False,None],{'z':[2,{'a':'y'}],'a':-42},{'constructor':'safe','prototype':'field'}]
for value in cases: print(encode(value).hex())
print(frame({'arguments':[1],'code':'src','credential':'token','proof':'proof'}).hex())
for op in range(4): print(prepared_frame(op,'src','token',[1],'proof').hex())
`], { cwd: root, encoding: 'utf8' });
  assert.equal(python.status, 0, python.stderr);
  const lines = python.stdout.trim().split('\n');
  for (const [i, value] of cases.entries()) {
    assert.equal(encode(value).toString('hex'), lines[i], `case ${i}`);
    assert.equal(encode(decode(encode(value))).toString('hex'), lines[i]);
  }
  const request = { arguments: [1n], code: 'src', credential: 'token', proof: 'proof' };
  assert.equal(frame(request).toString('hex'), lines[cases.length]);
  for (const op of [0, 1, 2, 3] as const) assert.equal(preparedFrame(op, 'src', 'token', [1n], 'proof').toString('hex'), lines[cases.length + 1 + op]);
  assert.deepEqual(unframe(frame(request)), request);
  assert.equal(decode(encode(123)), 123n);
});

test('prototype-sensitive names are ordinary record fields', () => {
  const value = Object.create(null) as { [key: string]: Value };
  value.__proto__ = { x: 1n }; Object.defineProperty(value, 'constructor', { value: 'not a constructor', enumerable: true });
  const result = decode(encode(value)) as { [key: string]: Value };
  assert.equal(Object.getPrototypeOf(result), Object.prototype);
  assert.equal(Object.hasOwn(result, '__proto__'), true);
  assert.deepEqual(result.__proto__, { x: 1n });
  assert.equal(result.constructor, 'not a constructor');
});

test('dense and deeply nested values need no recursive JS codec stack', () => {
  let value: Value = 7n;
  for (let i = 0; i < 15_000; i++) value = [value];
  const bytes = encode(value);
  assert.deepEqual(encode(decode(bytes)), bytes);
  const shared = { a: true };
  assert.deepEqual(decode(encode([shared, shared])), [shared, shared]);
});

test('unrepresentable JS values fail before transmission', () => {
  const cyclic: Value[] = []; cyclic.push(cyclic);
  let getterCalled = false;
  const getter = { get a() { getterCalled = true; return 1; } };
  const values: unknown[] = [undefined, NaN, Infinity, 0.1, Number.MAX_SAFE_INTEGER + 1,
    1n << 63n, -(1n << 63n) - 1n, '\ud800', '\udfff', new Date(), new Map(), /x/,
    cyclic, [1, , 3], Object.assign([1], { extra: true }), { 'bad-name': 1 }, { 'a\n': 1 },
    { 'a\r': 1 }, { 'a\u2028': 1 }, { 'a\u2029': 1 }, { ['a'.repeat(65)]: 1 },
    getter, { [Symbol('hidden')]: 1 }, Object.defineProperty({}, 'hidden', { value: 1 })];
  for (const value of values) assert.throws(() => encode(value as Value));
  assert.equal(getterCalled, false);
});

test('invalid, noncanonical and truncated wire values are rejected', () => {
  const record = (...fields: string[]) => Buffer.concat([Buffer.from([6]), u64(fields.length / 2), ...fields.map(text)]);
  const invalid = [Buffer.alloc(0), Buffer.from([7]), Buffer.from([3, 0]), Buffer.from([0, 0]),
    Buffer.concat([Buffer.from([4]), u64(2), Buffer.from([0xc0, 0xaf])]),
    Buffer.concat([Buffer.from([4]), u64(3), Buffer.from([0xed, 0xa0, 0x80])]),
    Buffer.concat([Buffer.from([5]), u64((1n << 64n) - 1n)]),
    Buffer.concat([Buffer.from([6]), u64(1), Buffer.from([0, 0])]),
    record('b', 'v', 'a', 'v'), record('a', 'v', 'a', 'v'), record('bad\n', 'v'),
    record('bad-name', 'v'), record('', 'v')];
  for (const bytes of invalid) assert.throws(() => decode(bytes), bytes.toString('hex'));
  const encoded = encode({ key: [null, 42n, 'text'] });
  for (let size = 0; size < encoded.length; size++) assert.throws(() => decode(encoded.subarray(0, size)));
  for (const bytes of [Buffer.alloc(0), u64(0), frame(null).subarray(1), Buffer.concat([frame(null), Buffer.from([0])])]) assert.throws(() => unframe(bytes));
  assert.throws(() => preparedFrame(4 as 0, '', ''));
});
