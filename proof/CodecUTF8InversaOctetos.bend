# O precheck de octetos aceita o UTF-8 de todo texto valido do contrato.
import Base
import ../contrato/Bytes.bend as B
import ./CodecUTF8Bits.bend as X
import ./CodecUTF8InversaBits.bend as I
import ./CodecUTF8Inversa.bend as E
import ./CodecPalavrasWord.bend as W
import ./CodecUnicode.bend as U
import ./Fundamentos.bend as F

law ascii_e_octeto:
  for +cp: U32
  for ascii: {U32.is_lt(cp, 128) == True{} : Bool}
  {U32.is_le(cp, 255) == True{} : Bool}
def ascii_e_octeto(cp, ascii):
  Equal.trans(Bool, U32.is_le(cp, 255), U32.is_lt(cp, 256), True{},
    U.limite_u32_sucessor(cp, 255, {==}), U.u32_lt_transitivo(cp, 128, 256, ascii, {==}))

law prefixo2_e_octeto:
  for +lo: Word(5n)
  {U32.is_le(I.prefixo2(lo), 255) == True{} : Bool}
def prefixo2_e_octeto(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c), U32.cmp(I.prefixo2(lo), 255), LT{},
    X.comparar_blocos(5n, 27n, lo, W.ajustar(5n, 32n, X.bits(31)),
      W.ajustar(27n, 32n, X.bits(6)), W.ajustar(27n, 32n, X.bits(7))))

law prefixo3_e_octeto:
  for +lo: Word(4n)
  {U32.is_le(I.prefixo3(lo), 255) == True{} : Bool}
def prefixo3_e_octeto(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c), U32.cmp(I.prefixo3(lo), 255), LT{},
    X.comparar_blocos(4n, 28n, lo, W.ajustar(4n, 32n, X.bits(15)),
      W.ajustar(28n, 32n, X.bits(14)), W.ajustar(28n, 32n, X.bits(15))))

law prefixo4_e_octeto:
  for +lo: Word(3n)
  {U32.is_le(I.prefixo4(lo), 255) == True{} : Bool}
def prefixo4_e_octeto(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c), U32.cmp(I.prefixo4(lo), 255), LT{},
    X.comparar_blocos(3n, 29n, lo, W.ajustar(3n, 32n, X.bits(7)),
      W.ajustar(29n, 32n, X.bits(30)), W.ajustar(29n, 32n, X.bits(31))))

law continuacao_e_octeto:
  for +lo: Word(6n)
  {U32.is_le(X.continuacao(lo), 255) == True{} : Bool}
def continuacao_e_octeto(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c), U32.cmp(X.continuacao(lo), 255), LT{},
    X.comparar_blocos(6n, 26n, lo, W.ajustar(6n, 32n, X.bits(63)),
      W.ajustar(26n, 32n, X.bits(2)), W.ajustar(26n, 32n, X.bits(3))))

law forma2_emite_octetos:
  for +hi: Word(5n)
  for +b0: Word(6n)
  {B.octetos_validos(B.utf8_codigo_emitir(X.escalar2(hi, b0), False{}, True{}, False{})) == True{} : Bool}
def forma2_emite_octetos(hi, b0):
  %Equal.sym(List<&2, U32>, B.utf8_codigo_emitir(X.escalar2(hi, b0), False{}, True{}, False{}), [I.prefixo2(hi), X.continuacao(b0)], X.utf8_forma_2_bytes(hi, b0)) :
    {B.octetos_validos(_) == True{} : Bool}
  F.e_booleano_intro(U32.is_le(I.prefixo2(hi), 255), B.octetos_validos([X.continuacao(b0)]), prefixo2_e_octeto(hi), F.e_booleano_intro(U32.is_le(X.continuacao(b0), 255), B.octetos_validos([]), continuacao_e_octeto(b0), {==}))

law forma3_emite_octetos:
  for +hi: Word(4n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  {B.octetos_validos(B.utf8_codigo_emitir(X.escalar3(hi, b0, b1), False{}, False{}, True{})) == True{} : Bool}
def forma3_emite_octetos(hi, b0, b1):
  %Equal.sym(List<&2, U32>, B.utf8_codigo_emitir(X.escalar3(hi, b0, b1), False{}, False{}, True{}), [I.prefixo3(hi), X.continuacao(b0), X.continuacao(b1)], X.utf8_forma_3_bytes(hi, b0, b1)) :
    {B.octetos_validos(_) == True{} : Bool}
  F.e_booleano_intro(U32.is_le(I.prefixo3(hi), 255), B.octetos_validos([X.continuacao(b0), X.continuacao(b1)]), prefixo3_e_octeto(hi), F.e_booleano_intro(U32.is_le(X.continuacao(b0), 255), B.octetos_validos([X.continuacao(b1)]), continuacao_e_octeto(b0), F.e_booleano_intro(U32.is_le(X.continuacao(b1), 255), B.octetos_validos([]), continuacao_e_octeto(b1), {==})))

law forma4_emite_octetos:
  for +hi: Word(3n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  for +b2: Word(6n)
  {B.octetos_validos(B.utf8_codigo_emitir(X.escalar4(hi, b0, b1, b2), False{}, False{}, False{})) == True{} : Bool}
def forma4_emite_octetos(hi, b0, b1, b2):
  %Equal.sym(List<&2, U32>, B.utf8_codigo_emitir(X.escalar4(hi, b0, b1, b2), False{}, False{}, False{}), [I.prefixo4(hi), X.continuacao(b0), X.continuacao(b1), X.continuacao(b2)], X.utf8_forma_4_bytes(hi, b0, b1, b2)) :
    {B.octetos_validos(_) == True{} : Bool}
  F.e_booleano_intro(U32.is_le(I.prefixo4(hi), 255), B.octetos_validos([X.continuacao(b0), X.continuacao(b1), X.continuacao(b2)]), prefixo4_e_octeto(hi), F.e_booleano_intro(U32.is_le(X.continuacao(b0), 255), B.octetos_validos([X.continuacao(b1), X.continuacao(b2)]), continuacao_e_octeto(b0), F.e_booleano_intro(U32.is_le(X.continuacao(b1), 255), B.octetos_validos([X.continuacao(b2)]), continuacao_e_octeto(b1), F.e_booleano_intro(U32.is_le(X.continuacao(b2), 255), B.octetos_validos([]), continuacao_e_octeto(b2), {==}))))

law codigo2_emite_octetos:
  for +cp: U32
  for limite: {U32.is_lt(cp, 2048) == True{} : Bool}
  {B.octetos_validos(B.utf8_codigo_emitir(cp, False{}, True{}, False{})) == True{} : Bool}
def codigo2_emite_octetos(cp, limite):
  %Equal.sym(U32, cp, X.escalar2(E.hi2(cp), E.lo6(cp)), E.codigo_forma2(cp, limite)) :
    {B.octetos_validos(B.utf8_codigo_emitir(_, False{}, True{}, False{})) == True{} : Bool}
  forma2_emite_octetos(E.hi2(cp), E.lo6(cp))

law codigo3_emite_octetos:
  for +cp: U32
  for limite: {U32.is_lt(cp, 65536) == True{} : Bool}
  {B.octetos_validos(B.utf8_codigo_emitir(cp, False{}, False{}, True{})) == True{} : Bool}
def codigo3_emite_octetos(cp, limite):
  %Equal.sym(U32, cp, X.escalar3(E.hi3(cp), E.lo6(U32.shrn(cp, 6n)), E.lo6(cp)), E.codigo_forma3(cp, limite)) :
    {B.octetos_validos(B.utf8_codigo_emitir(_, False{}, False{}, True{})) == True{} : Bool}
  forma3_emite_octetos(E.hi3(cp), E.lo6(U32.shrn(cp, 6n)), E.lo6(cp))

law codigo4_emite_octetos:
  for +cp: U32
  for limite: {U32.is_lt(cp, 2097152) == True{} : Bool}
  {B.octetos_validos(B.utf8_codigo_emitir(cp, False{}, False{}, False{})) == True{} : Bool}
def codigo4_emite_octetos(cp, limite):
  %Equal.sym(U32, cp, X.escalar4(E.hi4(cp), E.lo6(U32.shrn(cp, 12n)), E.lo6(U32.shrn(cp, 6n)), E.lo6(cp)), E.codigo_forma4(cp, limite)) :
    {B.octetos_validos(B.utf8_codigo_emitir(_, False{}, False{}, False{})) == True{} : Bool}
  forma4_emite_octetos(E.hi4(cp), E.lo6(U32.shrn(cp, 12n)), E.lo6(U32.shrn(cp, 6n)), E.lo6(cp))

law codigo_emite_octetos_casos:
  for +cp: U32
  for ascii: Bool
  for dois: Bool
  for tres: Bool
  for a: {U32.is_lt(cp, 128) == ascii : Bool}
  for d: {U32.is_lt(cp, 2048) == dois : Bool}
  for t: {U32.is_lt(cp, 65536) == tres : Bool}
  for valido: {B.codigo_valido(cp) == True{} : Bool}
  {B.octetos_validos(B.utf8_codigo_emitir(cp, ascii, dois, tres)) == True{} : Bool}
def codigo_emite_octetos_casos(cp, ascii, dois, tres, a, d, t, valido):
  match ascii dois tres:
    case True{} _ _:
      F.e_booleano_intro(U32.is_le(cp, 255), True{}, ascii_e_octeto(cp, a), {==})
    case False{} True{} _:
      codigo2_emite_octetos(cp, d)
    case False{} False{} True{}:
      codigo3_emite_octetos(cp, t)
    case False{} False{} False{}:
      codigo4_emite_octetos(cp, E.codigo_valido_cabe_21_bits(cp, valido))

law utf8_codigo_valido_emite_octetos:
  for +cp: U32
  for valido: {B.codigo_valido(cp) == True{} : Bool}
  {B.octetos_validos(B.utf8_codigo(cp)) == True{} : Bool}
def utf8_codigo_valido_emite_octetos(cp, valido):
  codigo_emite_octetos_casos(cp, U32.is_lt(cp, 128), U32.is_lt(cp, 2048), U32.is_lt(cp, 65536), {==}, {==}, {==}, valido)

law concatenar_preserva_octetos:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +va: {B.octetos_validos(a) == True{} : Bool}
  for vb: {B.octetos_validos(b) == True{} : Bool}
  {B.octetos_validos(B.concatenar(a, b)) == True{} : Bool}
def concatenar_preserva_octetos(a, b, va, vb):
  match a:
    case Nil{}:
      vb
    case Con{+h, +tail}:
      F.e_booleano_intro(U32.is_le(h, 255), B.octetos_validos(B.concatenar(tail, b)),
        F.e_booleano_esquerda(U32.is_le(h, 255), B.octetos_validos(tail), va),
        concatenar_preserva_octetos(tail, b, F.e_booleano_direita(U32.is_le(h, 255), B.octetos_validos(tail), va), vb))

law utf8_texto_valido_emite_octetos:
  for +s: String
  for +valido: {B.texto_valido(s) == True{} : Bool}
  {B.octetos_validos(B.utf8(s)) == True{} : Bool}
def utf8_texto_valido_emite_octetos(s, valido):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+cp}, +tail}:
      concatenar_preserva_octetos(B.utf8_codigo(cp), B.utf8(tail),
        utf8_codigo_valido_emite_octetos(cp, F.e_booleano_esquerda(B.codigo_valido(cp), B.texto_valido(tail), valido)),
        utf8_texto_valido_emite_octetos(tail, F.e_booleano_direita(B.codigo_valido(cp), B.texto_valido(tail), valido)))
