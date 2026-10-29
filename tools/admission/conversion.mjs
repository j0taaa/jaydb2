// Upstream tries rigid conversion at the root, then unfolds all descendants.
// After a wrapper unfolds, identical large arithmetic subterms can occur below
// that root. Try the SAME rigid judgment at each recursive comparison before
// unfolding. This adds no equation or accepted primitive; BendTT still checks
// the entire resulting derivation independently.
export function preserveRigidSubterms(source) {
  const anchor = 'function compare_go(mode: "EQ" | "LE", book: Book, lhs: HTerm, rhs: HTerm, dep: number): boolean {\n';
  if (source.split(anchor).length !== 2) throw new Error('Conversion adapter: pinned anchor diverged');
  return source.replace(anchor, anchor + '  if (book !== RIGID && compare_go(mode, RIGID, lhs, rhs, dep)) return true;\n');
}
