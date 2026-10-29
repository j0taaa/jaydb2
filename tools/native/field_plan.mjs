/** Trusted decoder lowering inventory, never an event log or certificate.
 * The ordinary emitter and installed frontend stay pinned. A plan with an
 * unresolved origin MUST NOT authorize an accounted module or publication.
 */
import crypto from 'node:crypto';
const hash = text => crypto.createHash('sha256').update(text).digest('hex');

export function planFields(metadata, { codec = 'Codec', data = 'Dados' } = {}) {
  if (!metadata.emittedCUnchanged || !metadata.noRuntimeEventsClaimed)
    throw new Error('FIELD_PLAN: expected unchanged-C inspection, not a runtime witness');
  const prefix = codec + ':';
  const guards = metadata.sites.filter(s => s.kind === 'decoder-guard-entry'
    && s.origin.startsWith(prefix)).map(s => ({ ...s,
      role: s.origin.endsWith(':percorrer') ? 'wire-cursor-source' : 'effective-guard-arguments',
      positionFormula: s.origin.endsWith(':percorrer')
        ? 'wire_size - corpo_at_entry (tag); last length byte is tag+8' : null,
      runtimeBranchWitness: false,
    }));
  const names = new Set(['VAusente','VBool','VInt','VTexto','VListaVazia',
    'VLista','VRegistroVazio','VRegistro','Campo'].map(s => data + ':' + s));
  const sites = metadata.sites.filter(s => s.kind === 'value-expression'
    && s.origin.startsWith(prefix) && (names.has(s.constructor)
      || ['SCon','Chr','Con'].includes(s.constructor))).map((s,index) => ({
        siteId: index, origin: s.origin, segment: s.segment,
        constructor: s.constructor, startLine: s.startLine, endLine: s.endLine,
        representation: s.layout, words: s.words,
        classification: names.has(s.constructor) ? 'decoded-value'
          : s.constructor === 'Con' ? 'partial-sequence-candidate' : 'partial-text',
        storage: s.words.length === 1 && /term_ctr\(/.test(s.words[0]) ? 'arena' : 'inline-or-flattened',
        quantityOrigin: 'original wire header or fixed primitive payload width',
        runtimeOriginBound: false, storesLoweredThroughFieldBoundary: false,
      }));
  for (const name of ['concluir_palavra','abrir_conferido','abrir_variavel','ler_tag','percorrer'])
    if (!guards.some(s => s.origin === prefix + name))
      throw new Error('FIELD_PLAN: missing effective decoder guard/cursor ' + name);
  const required = { concluir_palavra: ['f','alto','baixo','pilha','corpo','teto'],
    abrir_conferido: ['c','f','n','pilha'], abrir_variavel: ['vazio','f','n','pilha'],
    ler_tag: ['tag','pilha'], percorrer: ['bs','corpo','teto','m'] };
  for (const entry of guards) {
    const actual = entry.arguments.map(x => x.name);
    const expected = required[entry.origin.slice(prefix.length)];
    if (actual.join('|') !== expected.join('|'))
      throw new Error('FIELD_PLAN: changed trusted guard parameters: ' + entry.origin);
  }
  return { abi: 2, unchangedC: true, noRuntimeEventsClaimed: true,
    inspectionCompilerSha256: metadata.inspectionCompilerSha256,
    emittedCSha256: metadata.cSha256 ?? metadata.emittedCSha256,
    sites, guards, runtimeCoverageComplete: false,
    proofReference: 'proof/AlocacoesComprimentos.bend::abertura_variavel_real_respeita_corpo_e_teto',
    pending: ['executed Cabe branch and exact wire cursor binding',
      'origin retention through partial text, list, record and ancestor completion',
      'all real constructors, including helper/flattened/immediate stores, lowered under hold',
      'real counter completeness and environment/runtime correspondence'],
    inventorySha256: hash(JSON.stringify({sites,guards})),
  };
}

export function requirePublishableFieldPlan(plan) {
  // This inventory never authorizes publication. The separate staged native
  // lowering and a complete real observer cannot be replaced by edited JSON.
  void plan;
  throw new Error('FIELD_COVERAGE_INCOMPLETE: native field lowering/origin binding is not complete; publication refused');
}
