// Reuse an already checked physical instance only after the original closed
// argument checks and the original definitional equality judgment. Textual
// keys remain representatives, and an existing exact key keeps its own Def.
export function internEquivalentInstances(source) {
  const anchor = '  let o = is.get(key);';
  if (source.split(anchor).length !== 2) throw new Error('Pinned instance lookup anchor changed');
  return source.replace(anchor, '  let o = admission_instance(book, tm.k, xs);') + `

export function admission_instance(book: Book, name: Name, xs: HTerm[]): Name | undefined {
  const variants = book.tmps[name];
  if (variants === undefined) return undefined;
  const key = xs.map(a => term_key(term_lower(a))).join("\\n");
  const exact = variants.get(key);
  if (exact !== undefined) return exact;
  for (const [encoded, physical] of variants) {
    const def = book.tlds[physical];
    if (def?.$ !== "Def" || def.x !== 0) continue;
    const prior = encoded.split("\\n").map(a => term_higher(JSON.parse(a) as LTerm));
    if (prior.length === xs.length && xs.every((x, i) => term_compare("EQ", book, x, prior[i]))) {
      return physical;
    }
  }
  return undefined;
}
`;
}
