import { createHash } from 'node:crypto';

// Internal fixed-point check over the frontend's typed data. The public
// admission handle never exposes this graph; JS prototypes and host objects
// are not part of the submitted Bend language.
export function bookFingerprint(B, book) {
  const term = t => t == null ? t : B.term_lower(t);
  const ctor = c => ({ ...c, T: term(c.T) });
  const graph = {
    order: book.order, hols: book.hols,
    tlds: Object.entries(book.tlds).map(([name, d]) => [name, {
      ...d, T: term(d.T),
      ...(d.$ === 'ADT' ? { c: d.c.map(ctor) } : {
        v: term(d.v), e: d.e === undefined ? undefined : term(B.term_higher(d.e)),
      }),
    }]),
    ctrs: Object.entries(book.ctrs).map(([name, c]) => [name, ctor(c)]),
    tmps: Object.entries(book.tmps).map(([name, variants]) => [name, [...variants]]),
  };
  return createHash('sha256').update(JSON.stringify(graph,
    (key, value) => key === 's' ? undefined : value)).digest('hex');
}
