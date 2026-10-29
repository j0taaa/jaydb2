// Upstream already expresses large Nat literals as q * NAT_MAX + r. A unary
// block of 4096 overflows Node's stack in term -> ctr_term -> arg_term -> term.
// Change only the block size in this exact, pinned translation rule. BendTT
// still checks every resulting definition/proof, with the original kernel.
export function adaptSafeNumerals(source) {
  const anchor = 'const NAT_MAX = 4096;';
  if (source.split(anchor).length !== 2) throw new Error('Safe numerals: upstream anchor diverged');
  return source.replace(anchor, 'const NAT_MAX = 128;');
}
