# Canonicalidade dos trechos aceitos: conserva os octetos, incluindo zeros.
import Base
import ../contrato/Bytes.bend as B
import ../src/Codec.bend as C
import ./CodecPalavrasWord.bend as W
import ./CodecUTF8Bits.bend as X
import ./CodecUTF8InversaBits.bend as I
import ./CodecUTF8Inversa.bend as E
import ./CodecUnicode.bend as U
import ./Fundamentos.bend as F
import ./Ordens.bend as O

law ge_verdadeiro_lt_falso:
  for c: Cmp
  for e: {Cmp.is_ge(c) == True{} : Bool}
  {Cmp.is_lt(c) == False{} : Bool}
def ge_verdadeiro_lt_falso(c, e):
  match c:
    case EQ{}:
      {==}
    case GT{}:
      {==}
    case LT{}:
      F.absurdo_booleano({True{} == False{} : Bool}, e)

def ge_compor(ab: Cmp, bc: Cmp, ac: Cmp, h: O.Coerente(ab, bc, ac),
  a: {Cmp.is_ge(ab) == True{} : Bool}, b: {Cmp.is_ge(bc) == True{} : Bool}) ->
  {Cmp.is_ge(ac) == True{} : Bool}:
  match ab bc:
    case LT{} _:
      F.absurdo_booleano({Cmp.is_ge(ac) == True{} : Bool}, a)
    case _ LT{}:
      F.absurdo_booleano({Cmp.is_ge(ac) == True{} : Bool}, b)
    case EQ{} EQ{}:
      %Equal.sym(Cmp, ac, EQ{}, h) : {Cmp.is_ge(_) == True{} : Bool}
      {==}
    case EQ{} GT{}:
      %Equal.sym(Cmp, ac, GT{}, h) : {Cmp.is_ge(_) == True{} : Bool}
      {==}
    case GT{} EQ{}:
      %Equal.sym(Cmp, ac, GT{}, h) : {Cmp.is_ge(_) == True{} : Bool}
      {==}
    case GT{} GT{}:
      %Equal.sym(Cmp, ac, GT{}, h) : {Cmp.is_ge(_) == True{} : Bool}
      {==}

law ge_transitivo:
  for +a: U32
  for +b: U32
  for +c: U32
  for ab: {U32.is_ge(a, b) == True{} : Bool}
  for bc: {U32.is_ge(b, c) == True{} : Bool}
  {U32.is_ge(a, c) == True{} : Bool}
def ge_transitivo(a, b, c, ab, bc):
  ge_compor(U32.cmp(a, b), U32.cmp(b, c), U32.cmp(a, c), O.u32_coerente(a, b, c), ab, bc)

law cauda_ge:
  for a: Bool
  for b: Bool
  for c: Cmp
  for e: {Cmp.is_ge(Word.cmp.fin(a, b, c)) == True{} : Bool}
  {Cmp.is_ge(c) == True{} : Bool}
def cauda_ge(a, b, c, e):
  match c:
    case EQ{}:
      {==}
    case GT{}:
      {==}
    case LT{}:
      e

law le_ge_igual:
  for c: Cmp
  for le: {Cmp.is_le(c) == True{} : Bool}
  for ge: {Cmp.is_ge(c) == True{} : Bool}
  {c == EQ{} : Cmp}
def le_ge_igual(c, le, ge):
  match c:
    case EQ{}:
      {==}
    case LT{}:
      F.absurdo_booleano({LT{} == EQ{} : Cmp}, ge)
    case GT{}:
      F.absurdo_booleano({GT{} == EQ{} : Cmp}, le)

law palavra_entre_blocos:
  for +k: Nat
  for +n: Nat
  for +w: Word(Nat.add(k, n))
  for +prefixo: Word(n)
  for ge: {Cmp.is_ge(Word.cmp(Nat.add(k, n), w, W.juntar(k, n, Word.zero(k), prefixo))) == True{} : Bool}
  for le: {Cmp.is_le(Word.cmp(Nat.add(k, n), w, W.juntar(k, n, W.uns(k), prefixo))) == True{} : Bool}
  {w == W.juntar(k, n, W.ajustar(k, Nat.add(k, n), w), prefixo) : Word(Nat.add(k, n))}
def palavra_entre_blocos(k, n, w, prefixo, ge, le):
  match k:
    case 0n:
      O.word_igual(n, w, prefixo, le_ge_igual(Word.cmp(n, w, prefixo), le, ge))
    case 1n+p:
      match w:
        case WCon{b, t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{b, r},
            t, W.juntar(p, n, W.ajustar(p, Nat.add(p, n), t), prefixo),
            palavra_entre_blocos(p, n, t, prefixo,
              cauda_ge(b, False{}, Word.cmp(Nat.add(p, n), t, W.juntar(p, n, Word.zero(p), prefixo)), ge),
              W.limite_da_cauda(b, True{}, Word.cmp(Nat.add(p, n), t, W.juntar(p, n, W.uns(p), prefixo)), le)))

law continuacao_reconstituida:
  for +b: U32
  for ge: {U32.is_ge(b, 128) == True{} : Bool}
  for le: {U32.is_le(b, 191) == True{} : Bool}
  {b == X.continuacao(E.lo6(b)) : U32}
def continuacao_reconstituida(b, ge, le):
  match b:
    case U32{w}:
      Equal.cong(Word(32n), U32, z => U32{z}, w,
        W.juntar(6n, 26n, E.lo6(b), W.ajustar(26n, 32n, X.bits(2))),
        palavra_entre_blocos(6n, 26n, w, W.ajustar(26n, 32n, X.bits(2)), ge, le))

law prefixo2_reconstituido:
  for +b: U32
  for ge: {U32.is_ge(b, 194) == True{} : Bool}
  for le: {U32.is_le(b, 223) == True{} : Bool}
  {b == I.prefixo2(W.ajustar(5n, 32n, X.bits(b))) : U32}
def prefixo2_reconstituido(b, ge, le):
  match b:
    case U32{w}:
      Equal.cong(Word(32n), U32, z => U32{z}, w,
        W.juntar(5n, 27n, W.ajustar(5n, 32n, w), W.ajustar(27n, 32n, X.bits(6))),
        palavra_entre_blocos(5n, 27n, w, W.ajustar(27n, 32n, X.bits(6)), ge_transitivo(b, 194, 192, ge, {==}), le))

law prefixo3_reconstituido:
  for +b: U32
  for ge: {U32.is_ge(b, 224) == True{} : Bool}
  for le: {U32.is_le(b, 239) == True{} : Bool}
  {b == I.prefixo3(W.ajustar(4n, 32n, X.bits(b))) : U32}
def prefixo3_reconstituido(b, ge, le):
  match b:
    case U32{w}:
      Equal.cong(Word(32n), U32, z => U32{z}, w,
        W.juntar(4n, 28n, W.ajustar(4n, 32n, w), W.ajustar(28n, 32n, X.bits(14))),
        palavra_entre_blocos(4n, 28n, w, W.ajustar(28n, 32n, X.bits(14)), ge, le))

law prefixo4_reconstituido:
  for +b: U32
  for ge: {U32.is_ge(b, 240) == True{} : Bool}
  for le: {U32.is_le(b, 244) == True{} : Bool}
  {b == I.prefixo4(W.ajustar(3n, 32n, X.bits(b))) : U32}
def prefixo4_reconstituido(b, ge, le):
  match b:
    case U32{w}:
      lt = Equal.trans(Bool, U32.is_lt(b, 245), U32.is_le(b, 244), True{},
        Equal.sym(Bool, U32.is_le(b, 244), U32.is_lt(b, 245), U.limite_u32_sucessor(b, 244, {==})), le)
      teto = Equal.trans(Bool, U32.is_le(b, 247), U32.is_lt(b, 248), True{},
        U.limite_u32_sucessor(b, 247, {==}), U.u32_lt_transitivo(b, 245, 248, lt, {==}))
      Equal.cong(Word(32n), U32, z => U32{z}, w,
        W.juntar(3n, 29n, W.ajustar(3n, 32n, w), W.ajustar(29n, 32n, X.bits(30))),
        palavra_entre_blocos(3n, 29n, w, W.ajustar(29n, 32n, X.bits(30)), ge, teto))

law forma2_limite_superior:
  for +hi: Word(5n)
  for +b0: Word(6n)
  {U32.is_lt(X.escalar2(hi, b0), 2048) == True{} : Bool}
def forma2_limite_superior(hi, b0):
  match hi b0:
    case WCon{+hi0, WCon{+hi1, WCon{+hi2, WCon{+hi3, WCon{+hi4, WNil{}}}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}}:
      Equal.trans(Bool, U32.is_lt(X.escalar2(hi, b0), 2048), U32.is_le(X.escalar2(hi, b0), 2047), True{},
        Equal.sym(Bool, U32.is_le(X.escalar2(hi, b0), 2047), U32.is_lt(X.escalar2(hi, b0), 2048), U.limite_u32_sucessor(X.escalar2(hi, b0), 2047, {==})),
        I.blocos_limite_superior(11n, 21n, W.juntar(6n, 5n, b0, hi), Word.zero(21n), Word.zero(21n)))

law forma3_limite_superior:
  for +hi: Word(4n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  {U32.is_lt(X.escalar3(hi, b0, b1), 65536) == True{} : Bool}
def forma3_limite_superior(hi, b0, b1):
  match hi b0 b1:
    case WCon{+hi0, WCon{+hi1, WCon{+hi2, WCon{+hi3, WNil{}}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}} WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WNil{}}}}}}}:
      Equal.trans(Bool, U32.is_lt(X.escalar3(hi, b0, b1), 65536), U32.is_le(X.escalar3(hi, b0, b1), 65535), True{},
        Equal.sym(Bool, U32.is_le(X.escalar3(hi, b0, b1), 65535), U32.is_lt(X.escalar3(hi, b0, b1), 65536), U.limite_u32_sucessor(X.escalar3(hi, b0, b1), 65535, {==})),
        I.blocos_limite_superior(16n, 16n, W.juntar(6n, 10n, b1, W.juntar(6n, 4n, b0, hi)), Word.zero(16n), Word.zero(16n)))

law forma2_recodifica:
  for +hi: Word(5n)
  for +b0: Word(6n)
  for +minimo: {U32.is_ge(X.escalar2(hi, b0), 128) == True{} : Bool}
  {B.utf8_codigo(X.escalar2(hi, b0)) == [I.prefixo2(hi), X.continuacao(b0)] : List<&2, U32>}
def forma2_recodifica(hi, b0, minimo):
  %Equal.sym(Bool, U32.is_lt(X.escalar2(hi, b0), 128), False{}, ge_verdadeiro_lt_falso(U32.cmp(X.escalar2(hi, b0), 128), minimo)) :
    {B.utf8_codigo_emitir(X.escalar2(hi, b0), _, U32.is_lt(X.escalar2(hi, b0), 2048), U32.is_lt(X.escalar2(hi, b0), 65536)) == [I.prefixo2(hi), X.continuacao(b0)] : List<&2, U32>}
  %Equal.sym(Bool, U32.is_lt(X.escalar2(hi, b0), 2048), True{}, forma2_limite_superior(hi, b0)) :
    {B.utf8_codigo_emitir(X.escalar2(hi, b0), False{}, _, U32.is_lt(X.escalar2(hi, b0), 65536)) == [I.prefixo2(hi), X.continuacao(b0)] : List<&2, U32>}
  X.utf8_forma_2_bytes(hi, b0)

law forma3_recodifica:
  for +hi: Word(4n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  for +minimo: {U32.is_ge(X.escalar3(hi, b0, b1), 2048) == True{} : Bool}
  {B.utf8_codigo(X.escalar3(hi, b0, b1)) == [I.prefixo3(hi), X.continuacao(b0), X.continuacao(b1)] : List<&2, U32>}
def forma3_recodifica(hi, b0, b1, minimo):
  %Equal.sym(Bool, U32.is_lt(X.escalar3(hi, b0, b1), 128), False{}, ge_verdadeiro_lt_falso(U32.cmp(X.escalar3(hi, b0, b1), 128), ge_transitivo(X.escalar3(hi, b0, b1), 2048, 128, minimo, {==}))) :
    {B.utf8_codigo_emitir(X.escalar3(hi, b0, b1), _, U32.is_lt(X.escalar3(hi, b0, b1), 2048), U32.is_lt(X.escalar3(hi, b0, b1), 65536)) == [I.prefixo3(hi), X.continuacao(b0), X.continuacao(b1)] : List<&2, U32>}
  %Equal.sym(Bool, U32.is_lt(X.escalar3(hi, b0, b1), 2048), False{}, ge_verdadeiro_lt_falso(U32.cmp(X.escalar3(hi, b0, b1), 2048), minimo)) :
    {B.utf8_codigo_emitir(X.escalar3(hi, b0, b1), False{}, _, U32.is_lt(X.escalar3(hi, b0, b1), 65536)) == [I.prefixo3(hi), X.continuacao(b0), X.continuacao(b1)] : List<&2, U32>}
  %Equal.sym(Bool, U32.is_lt(X.escalar3(hi, b0, b1), 65536), True{}, forma3_limite_superior(hi, b0, b1)) :
    {B.utf8_codigo_emitir(X.escalar3(hi, b0, b1), False{}, False{}, _) == [I.prefixo3(hi), X.continuacao(b0), X.continuacao(b1)] : List<&2, U32>}
  X.utf8_forma_3_bytes(hi, b0, b1)

law forma4_recodifica:
  for +hi: Word(3n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  for +b2: Word(6n)
  for +minimo: {U32.is_ge(X.escalar4(hi, b0, b1, b2), 65536) == True{} : Bool}
  {B.utf8_codigo(X.escalar4(hi, b0, b1, b2)) == [I.prefixo4(hi), X.continuacao(b0), X.continuacao(b1), X.continuacao(b2)] : List<&2, U32>}
def forma4_recodifica(hi, b0, b1, b2, minimo):
  %Equal.sym(Bool, U32.is_lt(X.escalar4(hi, b0, b1, b2), 128), False{}, ge_verdadeiro_lt_falso(U32.cmp(X.escalar4(hi, b0, b1, b2), 128), ge_transitivo(X.escalar4(hi, b0, b1, b2), 65536, 128, minimo, {==}))) :
    {B.utf8_codigo_emitir(X.escalar4(hi, b0, b1, b2), _, U32.is_lt(X.escalar4(hi, b0, b1, b2), 2048), U32.is_lt(X.escalar4(hi, b0, b1, b2), 65536)) == [I.prefixo4(hi), X.continuacao(b0), X.continuacao(b1), X.continuacao(b2)] : List<&2, U32>}
  %Equal.sym(Bool, U32.is_lt(X.escalar4(hi, b0, b1, b2), 2048), False{}, ge_verdadeiro_lt_falso(U32.cmp(X.escalar4(hi, b0, b1, b2), 2048), ge_transitivo(X.escalar4(hi, b0, b1, b2), 65536, 2048, minimo, {==}))) :
    {B.utf8_codigo_emitir(X.escalar4(hi, b0, b1, b2), False{}, _, U32.is_lt(X.escalar4(hi, b0, b1, b2), 65536)) == [I.prefixo4(hi), X.continuacao(b0), X.continuacao(b1), X.continuacao(b2)] : List<&2, U32>}
  %Equal.sym(Bool, U32.is_lt(X.escalar4(hi, b0, b1, b2), 65536), False{}, ge_verdadeiro_lt_falso(U32.cmp(X.escalar4(hi, b0, b1, b2), 65536), minimo)) :
    {B.utf8_codigo_emitir(X.escalar4(hi, b0, b1, b2), False{}, False{}, _) == [I.prefixo4(hi), X.continuacao(b0), X.continuacao(b1), X.continuacao(b2)] : List<&2, U32>}
  X.utf8_forma_4_bytes(hi, b0, b1, b2)

law ascii_recodifica:
  for +cp: U32
  for ascii: {U32.is_lt(cp, 128) == True{} : Bool}
  {B.utf8_codigo(cp) == [cp] : List<&2, U32>}
def ascii_recodifica(cp, ascii):
  %Equal.sym(Bool, U32.is_lt(cp, 128), True{}, ascii) :
    {B.utf8_codigo_emitir(cp, _, U32.is_lt(cp, 2048), U32.is_lt(cp, 65536)) == [cp] : List<&2, U32>}
  {==}
