/** The existing canonical JayDB value format; int64 always decodes to bigint. */
export type Value = null | boolean | bigint | number | string | readonly Value[] | { readonly [key: string]: Value };

// Unlike `$`, this end assertion cannot match before a final line terminator.
const NAME = /^[A-Za-z_][A-Za-z0-9_]{0,63}(?![\s\S])/;
const MIN_INT = -(1n << 63n);
const MAX_INT = (1n << 63n) - 1n;
const utf8 = new TextDecoder('utf-8', { fatal: true, ignoreBOM: true });

function textBytes(value: string): Buffer {
  // Buffer.from replaces isolated UTF-16 surrogates; canonical strings must not.
  for (let i = 0; i < value.length; i++) {
    const unit = value.charCodeAt(i);
    if (unit >= 0xd800 && unit <= 0xdbff) {
      const next = value.charCodeAt(++i);
      if (!(next >= 0xdc00 && next <= 0xdfff)) throw new TypeError('Isolated UTF-16 surrogate');
    } else if (unit >= 0xdc00 && unit <= 0xdfff) {
      throw new TypeError('Isolated UTF-16 surrogate');
    }
  }
  return Buffer.from(value, 'utf8');
}

function length(value: number): Buffer {
  const bytes = Buffer.allocUnsafe(8);
  bytes.writeBigUInt64BE(BigInt(value));
  return bytes;
}

export function encode(value: Value): Buffer {
  const chunks: Buffer[] = [];
  const ancestors = new Set<object>();
  const pending: ({ value: unknown } | { leave: object })[] = [{ value }];
  while (pending.length) {
    const item = pending.pop()!;
    if ('leave' in item) { ancestors.delete(item.leave); continue; }
    const current = item.value;
    if (current === null) { chunks.push(Buffer.from([0])); continue; }
    if (typeof current === 'boolean') { chunks.push(Buffer.from([current ? 2 : 1])); continue; }
    if (typeof current === 'bigint' || typeof current === 'number') {
      if (typeof current === 'number' && !Number.isSafeInteger(current)) {
        throw new TypeError('Use bigint for integers outside the JavaScript safe integer range');
      }
      const integer = BigInt(current);
      if (integer < MIN_INT || integer > MAX_INT) throw new RangeError('Integer outside int64');
      const bytes = Buffer.allocUnsafe(9);
      bytes[0] = 3; bytes.writeBigInt64BE(integer, 1); chunks.push(bytes); continue;
    }
    if (typeof current === 'string') {
      const bytes = textBytes(current);
      chunks.push(Buffer.from([4]), length(bytes.length), bytes); continue;
    }
    if (typeof current !== 'object' || current === undefined) throw new TypeError('Value is not representable by JayDB');
    if (ancestors.has(current)) throw new TypeError('Cyclic value');
    const descriptors = Object.getOwnPropertyDescriptors(current);
    if (Object.getOwnPropertySymbols(current).length) throw new TypeError('Symbol properties are not wire fields');
    ancestors.add(current); pending.push({ leave: current });
    if (Array.isArray(current)) {
      if (Object.keys(descriptors).length !== current.length + 1) throw new TypeError('Use a dense array without extra properties');
      chunks.push(Buffer.from([5]), length(current.length));
      for (let i = current.length - 1; i >= 0; i--) {
        const descriptor = descriptors[String(i)];
        if (!descriptor || !('value' in descriptor) || !descriptor.enumerable) throw new TypeError('Use a dense data array');
        pending.push({ value: descriptor.value });
      }
    } else {
      const prototype = Object.getPrototypeOf(current);
      if (prototype !== Object.prototype && prototype !== null) throw new TypeError('Use a plain data record');
      const names = Object.keys(descriptors).sort();
      chunks.push(Buffer.from([6]), length(names.length));
      for (let i = names.length - 1; i >= 0; i--) {
        const name = names[i]!;
        const descriptor = descriptors[name]!;
        if (!NAME.test(name) || !('value' in descriptor) || !descriptor.enumerable) throw new TypeError('Invalid record field');
        pending.push({ value: descriptor.value }, { value: name });
      }
    }
  }
  return Buffer.concat(chunks);
}

export function decode(bytes: Uint8Array): Value {
  const data = Buffer.from(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let position = 0;
  const stack: { tag: 5 | 6; count: number; values: Value[] }[] = [];
  function take(size: number): Buffer {
    if (size > data.length - position) throw new RangeError('Truncated value');
    const result = data.subarray(position, position + size); position += size; return result;
  }
  function size(): number {
    const value = take(8).readBigUInt64BE();
    if (value > BigInt(data.length - position)) throw new RangeError('Length exceeds remaining value bytes');
    return Number(value);
  }
  function record(values: Value[]): Value {
    const result: { [key: string]: Value } = {};
    let previous = '';
    for (let i = 0; i < values.length; i += 2) {
      const name = values[i];
      if (typeof name !== 'string' || !NAME.test(name) || name <= previous) throw new TypeError('Noncanonical record');
      previous = name;
      Object.defineProperty(result, name, { value: values[i + 1]!, enumerable: true, writable: true, configurable: true });
    }
    return result;
  }
  outer: while (true) {
    const tag = take(1)[0]!;
    let value: Value;
    switch (tag) {
      case 0: value = null; break;
      case 1: case 2: value = tag === 2; break;
      case 3: value = take(8).readBigInt64BE(); break;
      case 4: value = utf8.decode(take(size())); break;
      case 5: case 6: {
        const count = size();
        if (count) { stack.push({ tag, count, values: [] }); continue; }
        value = tag === 5 ? [] : {}; break;
      }
      default: throw new TypeError('Invalid value tag');
    }
    while (stack.length) {
      const container = stack[stack.length - 1]!;
      container.values.push(value);
      if (container.values.length !== container.count * (container.tag === 6 ? 2 : 1)) continue outer;
      stack.pop(); value = container.tag === 5 ? container.values : record(container.values);
    }
    if (position !== data.length) throw new TypeError('Bytes after value');
    return value;
  }
}

export function frame(value: Value): Buffer {
  const body = encode(value);
  return Buffer.concat([length(body.length), body]);
}

export function preparedFrame(operation: 0 | 1 | 2 | 3, code: string, credential: string,
  arguments_: Value = null, proof = ''): Buffer {
  if (![0, 1, 2, 3].includes(operation)) throw new TypeError('Invalid prepared operation');
  const body = Buffer.concat([Buffer.from([7, operation]), encode({ arguments: arguments_, code, credential, proof })]);
  return Buffer.concat([length(body.length), body]);
}

export function unframe(bytes: Uint8Array): Value {
  const data = Buffer.from(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  if (data.length < 8 || data.readBigUInt64BE() !== BigInt(data.length - 8)) throw new RangeError('Invalid frame');
  return decode(data.subarray(8));
}
