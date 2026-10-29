// The official parser beta-reduces in term_higher and flattens match rows.
// A post-parse Book alone therefore cannot certify source-level purity. These
// *observation-only* insertions retain raw trees, including discarded syntax.
// Anchors are exact and checked against the pinned upstream source. Neither
// parsing decisions nor reduction/checker/compiler semantics are replaced.
export function instrumentFrontend(source) {
  function replace(from, to, count = 1) {
    if (source.split(from).length - 1 !== count) throw new Error('Frontend observer: upstream anchor diverged');
    source = source.replaceAll(from, to);
  }
  source += `
let admission_observer: ((owner: string | null, term: unknown) => void) | null = null;
let admission_owner: string | null = null;
export function admission_observe(f: typeof admission_observer): void {
  admission_observer = f;
  admission_owner = null;
}
function admission_raw<T>(term: T): T {
  admission_observer?.(admission_owner, term);
  return term;
}
`;
  replace('export function term_higher(tm: LTerm, env: Env = null): HTerm {',
    'export function term_higher(tm: LTerm, env: Env = null): HTerm {\n  if (env === null) admission_raw(tm);');
  replace('export function parse_body(p: Parse, col: number = 0): Body {',
    `export function parse_body(p: Parse, col: number = 0): Body {
  return admission_raw(admission_parse_body(p, col));
}
function admission_parse_body(p: Parse, col: number = 0): Body {`);
  replace('const k   = law ? q : parse_fresh(p, nm);',
    'const k   = law ? q : parse_fresh(p, nm);\n  admission_owner = k;');
  replace('const k = parse_fresh(p, parse_name(p));',
    'const k = parse_fresh(p, parse_name(p));\n      admission_owner = k;', 2);
  return source;
}
