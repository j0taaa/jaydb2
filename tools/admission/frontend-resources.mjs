/** Remove only compiler resource sentinels, preserving all checking rules. */
export function uncapTemplates(source) {
  const guards = [
    `  if (key.length > 32768) {
    throw Err(book, ctx, "a ~ argument that stops growing", tm, tm.s, lhs.def);
  }`,
    `    if (z > 64) {
      throw Err(book, ctx, "a template that stops instantiating itself (64 levels at most)", tm, tm.s, lhs.def);
    }`,
  ];
  for (const guard of guards) {
    if (source.split(guard).length !== 2) throw new Error('Pinned template resource guard changed');
    source = source.replace(guard, '');
  }
  return source;
}
