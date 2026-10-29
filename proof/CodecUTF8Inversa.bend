# Inversao escalar do encoder original pela transducao real do parser.
import Base
import ../contrato/Bytes.bend as B
import ../src/Codec.bend as C
import ./CodecUTF8.bend as T
import ./CodecUTF8Bits.bend as X
import ./CodecUTF8InversaBits.bend as I
import ./CodecPalavrasWord.bend as W
import ./CodecUnicode.bend as U
import ./Fundamentos.bend as F

def acumular(cp: U32, lo: Word(6n)) -> U32:
  U32{W.juntar(6n, 26n, lo, W.ajustar(26n, 32n, X.bits(cp)))}

law percorrer_ascii:
  for +cp: U32
  for +acc: String
  for ascii: {U32.is_lt(cp, 128) == True{} : Bool}
  {T.percorrer_texto([cp], T.Lendo{C.Inicio{}, acc}) == T.Lendo{C.Inicio{}, SCon{Chr{cp}, acc}} : T.Texto}
def percorrer_ascii(cp, acc, ascii):
  %Equal.sym(Bool, U32.is_lt(cp, 128), True{}, ascii) :
    {T.juntar(C.iniciar_utf8(_, U32.is_ge(cp, 194) && U32.is_le(cp, 223), U32.is_ge(cp, 224) && U32.is_le(cp, 239), U32.is_ge(cp, 240) && U32.is_le(cp, 244), cp), acc) == T.Lendo{C.Inicio{}, SCon{Chr{cp}, acc}} : T.Texto}
  {==}

law percorrer_forma2:
  for +hi: Word(5n)
  for +b0: Word(6n)
  for +acc: String
  for +minimo: {U32.is_ge(X.escalar2(hi, b0), 128) == True{} : Bool}
  for +valido: {B.codigo_valido(X.escalar2(hi, b0)) == True{} : Bool}
  {T.percorrer_texto([I.prefixo2(hi), X.continuacao(b0)], T.Lendo{C.Inicio{}, acc}) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar2(hi, b0)}, acc}} : T.Texto}
def percorrer_forma2(hi, b0, acc, minimo, valido):
  match hi b0:
    case WCon{+hi0, WCon{+hi1, WCon{+hi2, WCon{+hi3, WCon{+hi4, WNil{}}}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}}:
      %Equal.sym(C.Escalar, C.passo_utf8(C.Inicio{}, I.prefixo2(hi)), C.Parcial{C.Continua{1n, U32{W.juntar(5n, 27n, hi, Word.zero(27n))}, 128}}, I.iniciar_dois(hi, b0, minimo)) :
        {T.percorrer_texto([X.continuacao(b0)], T.juntar(_, acc)) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar2(hi, b0)}, acc}} : T.Texto}
      %Equal.sym(C.Escalar, C.passo_utf8(C.Continua{1n, U32{W.juntar(5n, 27n, hi, Word.zero(27n))}, 128}, X.continuacao(b0)), C.completar_utf8(0n, acumular(U32{W.juntar(5n, 27n, hi, Word.zero(27n))}, b0), 128), I.passo_continuacao(0n, U32{W.juntar(5n, 27n, hi, Word.zero(27n))}, 128, b0)) :
        {T.percorrer_texto([], T.juntar(_, acc)) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar2(hi, b0)}, acc}} : T.Texto}
      %Equal.sym(Bool, U32.is_ge(X.escalar2(hi, b0), 128) && B.codigo_valido(X.escalar2(hi, b0)), True{}, F.e_booleano_intro(U32.is_ge(X.escalar2(hi, b0), 128), B.codigo_valido(X.escalar2(hi, b0)), minimo, valido)) :
        {T.juntar(C.escalar_conferido(_, X.escalar2(hi, b0)), acc) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar2(hi, b0)}, acc}} : T.Texto}
      {==}

law percorrer_forma3:
  for +hi: Word(4n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  for +acc: String
  for +minimo: {U32.is_ge(X.escalar3(hi, b0, b1), 2048) == True{} : Bool}
  for +valido: {B.codigo_valido(X.escalar3(hi, b0, b1)) == True{} : Bool}
  {T.percorrer_texto([I.prefixo3(hi), X.continuacao(b0), X.continuacao(b1)], T.Lendo{C.Inicio{}, acc}) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar3(hi, b0, b1)}, acc}} : T.Texto}
def percorrer_forma3(hi, b0, b1, acc, minimo, valido):
  match hi b0 b1:
    case WCon{+hi0, WCon{+hi1, WCon{+hi2, WCon{+hi3, WNil{}}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}} WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WNil{}}}}}}}:
      %Equal.sym(C.Escalar, C.passo_utf8(C.Inicio{}, I.prefixo3(hi)), C.Parcial{C.Continua{2n, U32{W.juntar(4n, 28n, hi, Word.zero(28n))}, 2048}}, I.iniciar_tres(hi)) :
        {T.percorrer_texto([X.continuacao(b0), X.continuacao(b1)], T.juntar(_, acc)) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar3(hi, b0, b1)}, acc}} : T.Texto}
      %Equal.sym(C.Escalar, C.passo_utf8(C.Continua{2n, U32{W.juntar(4n, 28n, hi, Word.zero(28n))}, 2048}, X.continuacao(b0)), C.completar_utf8(1n, acumular(U32{W.juntar(4n, 28n, hi, Word.zero(28n))}, b0), 2048), I.passo_continuacao(1n, U32{W.juntar(4n, 28n, hi, Word.zero(28n))}, 2048, b0)) :
        {T.percorrer_texto([X.continuacao(b1)], T.juntar(_, acc)) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar3(hi, b0, b1)}, acc}} : T.Texto}
      %Equal.sym(C.Escalar, C.passo_utf8(C.Continua{1n, acumular(U32{W.juntar(4n, 28n, hi, Word.zero(28n))}, b0), 2048}, X.continuacao(b1)), C.completar_utf8(0n, acumular(acumular(U32{W.juntar(4n, 28n, hi, Word.zero(28n))}, b0), b1), 2048), I.passo_continuacao(0n, acumular(U32{W.juntar(4n, 28n, hi, Word.zero(28n))}, b0), 2048, b1)) :
        {T.percorrer_texto([], T.juntar(_, acc)) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar3(hi, b0, b1)}, acc}} : T.Texto}
      %Equal.sym(Bool, U32.is_ge(X.escalar3(hi, b0, b1), 2048) && B.codigo_valido(X.escalar3(hi, b0, b1)), True{}, F.e_booleano_intro(U32.is_ge(X.escalar3(hi, b0, b1), 2048), B.codigo_valido(X.escalar3(hi, b0, b1)), minimo, valido)) :
        {T.juntar(C.escalar_conferido(_, X.escalar3(hi, b0, b1)), acc) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar3(hi, b0, b1)}, acc}} : T.Texto}
      {==}

law percorrer_forma4:
  for +hi: Word(3n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  for +b2: Word(6n)
  for +acc: String
  for +minimo: {U32.is_ge(X.escalar4(hi, b0, b1, b2), 65536) == True{} : Bool}
  for +valido: {B.codigo_valido(X.escalar4(hi, b0, b1, b2)) == True{} : Bool}
  {T.percorrer_texto([I.prefixo4(hi), X.continuacao(b0), X.continuacao(b1), X.continuacao(b2)], T.Lendo{C.Inicio{}, acc}) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar4(hi, b0, b1, b2)}, acc}} : T.Texto}
def percorrer_forma4(hi, b0, b1, b2, acc, minimo, valido):
  match hi b0 b1 b2:
    case WCon{+hi0, WCon{+hi1, WCon{+hi2, WNil{}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}} WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WNil{}}}}}}} WCon{+b20, WCon{+b21, WCon{+b22, WCon{+b23, WCon{+b24, WCon{+b25, WNil{}}}}}}}:
      %Equal.sym(C.Escalar, C.passo_utf8(C.Inicio{}, I.prefixo4(hi)), C.Parcial{C.Continua{3n, U32{W.juntar(3n, 29n, hi, Word.zero(29n))}, 65536}}, I.iniciar_quatro(hi, I.escalar4_prefixo_limitado(hi, b0, b1, b2, valido))) :
        {T.percorrer_texto([X.continuacao(b0), X.continuacao(b1), X.continuacao(b2)], T.juntar(_, acc)) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar4(hi, b0, b1, b2)}, acc}} : T.Texto}
      %Equal.sym(C.Escalar, C.passo_utf8(C.Continua{3n, U32{W.juntar(3n, 29n, hi, Word.zero(29n))}, 65536}, X.continuacao(b0)), C.completar_utf8(2n, acumular(U32{W.juntar(3n, 29n, hi, Word.zero(29n))}, b0), 65536), I.passo_continuacao(2n, U32{W.juntar(3n, 29n, hi, Word.zero(29n))}, 65536, b0)) :
        {T.percorrer_texto([X.continuacao(b1), X.continuacao(b2)], T.juntar(_, acc)) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar4(hi, b0, b1, b2)}, acc}} : T.Texto}
      %Equal.sym(C.Escalar, C.passo_utf8(C.Continua{2n, acumular(U32{W.juntar(3n, 29n, hi, Word.zero(29n))}, b0), 65536}, X.continuacao(b1)), C.completar_utf8(1n, acumular(acumular(U32{W.juntar(3n, 29n, hi, Word.zero(29n))}, b0), b1), 65536), I.passo_continuacao(1n, acumular(U32{W.juntar(3n, 29n, hi, Word.zero(29n))}, b0), 65536, b1)) :
        {T.percorrer_texto([X.continuacao(b2)], T.juntar(_, acc)) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar4(hi, b0, b1, b2)}, acc}} : T.Texto}
      %Equal.sym(C.Escalar, C.passo_utf8(C.Continua{1n, acumular(acumular(U32{W.juntar(3n, 29n, hi, Word.zero(29n))}, b0), b1), 65536}, X.continuacao(b2)), C.completar_utf8(0n, acumular(acumular(acumular(U32{W.juntar(3n, 29n, hi, Word.zero(29n))}, b0), b1), b2), 65536), I.passo_continuacao(0n, acumular(acumular(U32{W.juntar(3n, 29n, hi, Word.zero(29n))}, b0), b1), 65536, b2)) :
        {T.percorrer_texto([], T.juntar(_, acc)) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar4(hi, b0, b1, b2)}, acc}} : T.Texto}
      %Equal.sym(Bool, U32.is_ge(X.escalar4(hi, b0, b1, b2), 65536) && B.codigo_valido(X.escalar4(hi, b0, b1, b2)), True{}, F.e_booleano_intro(U32.is_ge(X.escalar4(hi, b0, b1, b2), 65536), B.codigo_valido(X.escalar4(hi, b0, b1, b2)), minimo, valido)) :
        {T.juntar(C.escalar_conferido(_, X.escalar4(hi, b0, b1, b2)), acc) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar4(hi, b0, b1, b2)}, acc}} : T.Texto}
      {==}

# Transporta apenas um fato booleano, nunca a conclusao da inversao.
def fato_transferido(-P: U32 -> Bool, -a: U32, -b: U32,
  e: {a == b : U32}, fato: {P(a) == True{} : Bool}) -> {P(b) == True{} : Bool}:
  %e : {P(_) == True{} : Bool}
  fato

def lo6(cp: U32) -> Word(6n):
  W.ajustar(6n, 32n, X.bits(cp))

def hi2(cp: U32) -> Word(5n):
  W.ajustar(5n, 32n, X.bits(U32.shrn(cp, 6n)))

def hi3(cp: U32) -> Word(4n):
  W.ajustar(4n, 32n, X.bits(U32.shrn(cp, 12n)))

def hi4(cp: U32) -> Word(3n):
  W.ajustar(3n, 32n, X.bits(U32.shrn(cp, 18n)))

law codigo_forma2:
  for +cp: U32
  for limite: {U32.is_lt(cp, 2048) == True{} : Bool}
  {cp == X.escalar2(hi2(cp), lo6(cp)) : U32}
def codigo_forma2(cp, limite):
  match cp:
    case U32{+w}:
      match w:
        case WCon{+w0, WCon{+w1, WCon{+w2, WCon{+w3, WCon{+w4, WCon{+w5, WCon{+w6, WCon{+w7, WCon{+w8, WCon{+w9, WCon{+w10, +resto}}}}}}}}}}}:
          le = Equal.trans(Bool, U32.is_le(cp, 2047), U32.is_lt(cp, 2048), True{}, U.limite_u32_sucessor(cp, 2047, {==}), limite)
          Equal.cong(Word(32n), U32, z => U32{z}, w, W.juntar(11n, 21n, W.ajustar(11n, 32n, w), Word.zero(21n)), W.limite_bits_baixos(11n, 21n, w, le))

law codigo_forma3:
  for +cp: U32
  for limite: {U32.is_lt(cp, 65536) == True{} : Bool}
  {cp == X.escalar3(hi3(cp), lo6(U32.shrn(cp, 6n)), lo6(cp)) : U32}
def codigo_forma3(cp, limite):
  match cp:
    case U32{+w}:
      match w:
        case WCon{+w0, WCon{+w1, WCon{+w2, WCon{+w3, WCon{+w4, WCon{+w5, WCon{+w6, WCon{+w7, WCon{+w8, WCon{+w9, WCon{+w10, WCon{+w11, WCon{+w12, WCon{+w13, WCon{+w14, WCon{+w15, +resto}}}}}}}}}}}}}}}}:
          le = Equal.trans(Bool, U32.is_le(cp, 65535), U32.is_lt(cp, 65536), True{}, U.limite_u32_sucessor(cp, 65535, {==}), limite)
          Equal.cong(Word(32n), U32, z => U32{z}, w, W.juntar(16n, 16n, W.ajustar(16n, 32n, w), Word.zero(16n)), W.limite_bits_baixos(16n, 16n, w, le))

law codigo_forma4:
  for +cp: U32
  for limite: {U32.is_lt(cp, 2097152) == True{} : Bool}
  {cp == X.escalar4(hi4(cp), lo6(U32.shrn(cp, 12n)), lo6(U32.shrn(cp, 6n)), lo6(cp)) : U32}
def codigo_forma4(cp, limite):
  match cp:
    case U32{+w}:
      match w:
        case WCon{+w0, WCon{+w1, WCon{+w2, WCon{+w3, WCon{+w4, WCon{+w5, WCon{+w6, WCon{+w7, WCon{+w8, WCon{+w9, WCon{+w10, WCon{+w11, WCon{+w12, WCon{+w13, WCon{+w14, WCon{+w15, WCon{+w16, WCon{+w17, WCon{+w18, WCon{+w19, WCon{+w20, +resto}}}}}}}}}}}}}}}}}}}}}:
          le = Equal.trans(Bool, U32.is_le(cp, 2097151), U32.is_lt(cp, 2097152), True{}, U.limite_u32_sucessor(cp, 2097151, {==}), limite)
          Equal.cong(Word(32n), U32, z => U32{z}, w, W.juntar(21n, 11n, W.ajustar(21n, 32n, w), Word.zero(11n)), W.limite_bits_baixos(21n, 11n, w, le))

law percorrer_emitir_forma2:
  for +hi: Word(5n)
  for +b0: Word(6n)
  for +acc: String
  for minimo: {U32.is_ge(X.escalar2(hi, b0), 128) == True{} : Bool}
  for valido: {B.codigo_valido(X.escalar2(hi, b0)) == True{} : Bool}
  {T.percorrer_texto(B.utf8_codigo_emitir(X.escalar2(hi, b0), False{}, True{}, False{}), T.Lendo{C.Inicio{}, acc}) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar2(hi, b0)}, acc}} : T.Texto}
def percorrer_emitir_forma2(hi, b0, acc, minimo, valido):
  %Equal.sym(List<&2, U32>, B.utf8_codigo_emitir(X.escalar2(hi, b0), False{}, True{}, False{}), [I.prefixo2(hi), X.continuacao(b0)], X.utf8_forma_2_bytes(hi, b0)) :
    {T.percorrer_texto(_, T.Lendo{C.Inicio{}, acc}) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar2(hi, b0)}, acc}} : T.Texto}
  percorrer_forma2(hi, b0, acc, minimo, valido)

law percorrer_emitir_forma3:
  for +hi: Word(4n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  for +acc: String
  for minimo: {U32.is_ge(X.escalar3(hi, b0, b1), 2048) == True{} : Bool}
  for valido: {B.codigo_valido(X.escalar3(hi, b0, b1)) == True{} : Bool}
  {T.percorrer_texto(B.utf8_codigo_emitir(X.escalar3(hi, b0, b1), False{}, False{}, True{}), T.Lendo{C.Inicio{}, acc}) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar3(hi, b0, b1)}, acc}} : T.Texto}
def percorrer_emitir_forma3(hi, b0, b1, acc, minimo, valido):
  %Equal.sym(List<&2, U32>, B.utf8_codigo_emitir(X.escalar3(hi, b0, b1), False{}, False{}, True{}), [I.prefixo3(hi), X.continuacao(b0), X.continuacao(b1)], X.utf8_forma_3_bytes(hi, b0, b1)) :
    {T.percorrer_texto(_, T.Lendo{C.Inicio{}, acc}) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar3(hi, b0, b1)}, acc}} : T.Texto}
  percorrer_forma3(hi, b0, b1, acc, minimo, valido)

law percorrer_emitir_forma4:
  for +hi: Word(3n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  for +b2: Word(6n)
  for +acc: String
  for minimo: {U32.is_ge(X.escalar4(hi, b0, b1, b2), 65536) == True{} : Bool}
  for valido: {B.codigo_valido(X.escalar4(hi, b0, b1, b2)) == True{} : Bool}
  {T.percorrer_texto(B.utf8_codigo_emitir(X.escalar4(hi, b0, b1, b2), False{}, False{}, False{}), T.Lendo{C.Inicio{}, acc}) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar4(hi, b0, b1, b2)}, acc}} : T.Texto}
def percorrer_emitir_forma4(hi, b0, b1, b2, acc, minimo, valido):
  %Equal.sym(List<&2, U32>, B.utf8_codigo_emitir(X.escalar4(hi, b0, b1, b2), False{}, False{}, False{}), [I.prefixo4(hi), X.continuacao(b0), X.continuacao(b1), X.continuacao(b2)], X.utf8_forma_4_bytes(hi, b0, b1, b2)) :
    {T.percorrer_texto(_, T.Lendo{C.Inicio{}, acc}) == T.Lendo{C.Inicio{}, SCon{Chr{X.escalar4(hi, b0, b1, b2)}, acc}} : T.Texto}
  percorrer_forma4(hi, b0, b1, b2, acc, minimo, valido)

law percorrer_codigo2:
  for +cp: U32
  for +acc: String
  for limite: {U32.is_lt(cp, 2048) == True{} : Bool}
  for minimo: {U32.is_ge(cp, 128) == True{} : Bool}
  for valido: {B.codigo_valido(cp) == True{} : Bool}
  {T.percorrer_texto(B.utf8_codigo_emitir(cp, False{}, True{}, False{}), T.Lendo{C.Inicio{}, acc}) == T.Lendo{C.Inicio{}, SCon{Chr{cp}, acc}} : T.Texto}
def percorrer_codigo2(cp, acc, limite, minimo, valido):
  +forma = codigo_forma2(cp, limite)
  m = fato_transferido(z => U32.is_ge(z, 128), cp, X.escalar2(hi2(cp), lo6(cp)), forma, minimo)
  v = fato_transferido(z => B.codigo_valido(z), cp, X.escalar2(hi2(cp), lo6(cp)), forma, valido)
  %Equal.sym(U32, cp, X.escalar2(hi2(cp), lo6(cp)), forma) :
    {T.percorrer_texto(B.utf8_codigo_emitir(_, False{}, True{}, False{}), T.Lendo{C.Inicio{}, acc}) == T.Lendo{C.Inicio{}, SCon{Chr{_}, acc}} : T.Texto}
  percorrer_emitir_forma2(hi2(cp), lo6(cp), acc, m, v)

law percorrer_codigo3:
  for +cp: U32
  for +acc: String
  for limite: {U32.is_lt(cp, 65536) == True{} : Bool}
  for minimo: {U32.is_ge(cp, 2048) == True{} : Bool}
  for valido: {B.codigo_valido(cp) == True{} : Bool}
  {T.percorrer_texto(B.utf8_codigo_emitir(cp, False{}, False{}, True{}), T.Lendo{C.Inicio{}, acc}) == T.Lendo{C.Inicio{}, SCon{Chr{cp}, acc}} : T.Texto}
def percorrer_codigo3(cp, acc, limite, minimo, valido):
  +forma = codigo_forma3(cp, limite)
  m = fato_transferido(z => U32.is_ge(z, 2048), cp, X.escalar3(hi3(cp), lo6(U32.shrn(cp, 6n)), lo6(cp)), forma, minimo)
  v = fato_transferido(z => B.codigo_valido(z), cp, X.escalar3(hi3(cp), lo6(U32.shrn(cp, 6n)), lo6(cp)), forma, valido)
  %Equal.sym(U32, cp, X.escalar3(hi3(cp), lo6(U32.shrn(cp, 6n)), lo6(cp)), forma) :
    {T.percorrer_texto(B.utf8_codigo_emitir(_, False{}, False{}, True{}), T.Lendo{C.Inicio{}, acc}) == T.Lendo{C.Inicio{}, SCon{Chr{_}, acc}} : T.Texto}
  percorrer_emitir_forma3(hi3(cp), lo6(U32.shrn(cp, 6n)), lo6(cp), acc, m, v)

law percorrer_codigo4:
  for +cp: U32
  for +acc: String
  for limite: {U32.is_lt(cp, 2097152) == True{} : Bool}
  for minimo: {U32.is_ge(cp, 65536) == True{} : Bool}
  for valido: {B.codigo_valido(cp) == True{} : Bool}
  {T.percorrer_texto(B.utf8_codigo_emitir(cp, False{}, False{}, False{}), T.Lendo{C.Inicio{}, acc}) == T.Lendo{C.Inicio{}, SCon{Chr{cp}, acc}} : T.Texto}
def percorrer_codigo4(cp, acc, limite, minimo, valido):
  +forma = codigo_forma4(cp, limite)
  m = fato_transferido(z => U32.is_ge(z, 65536), cp, X.escalar4(hi4(cp), lo6(U32.shrn(cp, 12n)), lo6(U32.shrn(cp, 6n)), lo6(cp)), forma, minimo)
  v = fato_transferido(z => B.codigo_valido(z), cp, X.escalar4(hi4(cp), lo6(U32.shrn(cp, 12n)), lo6(U32.shrn(cp, 6n)), lo6(cp)), forma, valido)
  %Equal.sym(U32, cp, X.escalar4(hi4(cp), lo6(U32.shrn(cp, 12n)), lo6(U32.shrn(cp, 6n)), lo6(cp)), forma) :
    {T.percorrer_texto(B.utf8_codigo_emitir(_, False{}, False{}, False{}), T.Lendo{C.Inicio{}, acc}) == T.Lendo{C.Inicio{}, SCon{Chr{_}, acc}} : T.Texto}
  percorrer_emitir_forma4(hi4(cp), lo6(U32.shrn(cp, 12n)), lo6(U32.shrn(cp, 6n)), lo6(cp), acc, m, v)

law codigo_valido_cabe_21_bits:
  for +cp: U32
  for valido: {B.codigo_valido(cp) == True{} : Bool}
  {U32.is_lt(cp, 2097152) == True{} : Bool}
def codigo_valido_cabe_21_bits(cp, valido):
  le = F.e_booleano_esquerda(U32.is_le(cp, 1114111), U32.is_lt(cp, 55296) || U32.is_gt(cp, 57343), valido)
  lt = Equal.trans(Bool, U32.is_lt(cp, 1114112), U32.is_le(cp, 1114111), True{},
    Equal.sym(Bool, U32.is_le(cp, 1114111), U32.is_lt(cp, 1114112), U.limite_u32_sucessor(cp, 1114111, {==})), le)
  U.u32_lt_transitivo(cp, 1114112, 2097152, lt, {==})

law percorrer_codigo_casos:
  for +cp: U32
  for ascii: Bool
  for dois: Bool
  for tres: Bool
  for +acc: String
  for a: {U32.is_lt(cp, 128) == ascii : Bool}
  for d: {U32.is_lt(cp, 2048) == dois : Bool}
  for t: {U32.is_lt(cp, 65536) == tres : Bool}
  for +valido: {B.codigo_valido(cp) == True{} : Bool}
  {T.percorrer_texto(B.utf8_codigo_emitir(cp, ascii, dois, tres), T.Lendo{C.Inicio{}, acc}) ==
    T.Lendo{C.Inicio{}, SCon{Chr{cp}, acc}} : T.Texto}
def percorrer_codigo_casos(cp, ascii, dois, tres, acc, a, d, t, valido):
  match ascii dois tres:
    case True{} _ _:
      percorrer_ascii(cp, acc, a)
    case False{} True{} _:
      percorrer_codigo2(cp, acc, d, I.lt_falso_e_ge(U32.cmp(cp, 128), a), valido)
    case False{} False{} True{}:
      percorrer_codigo3(cp, acc, t, I.lt_falso_e_ge(U32.cmp(cp, 2048), d), valido)
    case False{} False{} False{}:
      percorrer_codigo4(cp, acc, codigo_valido_cabe_21_bits(cp, valido), I.lt_falso_e_ge(U32.cmp(cp, 65536), t), valido)

# Completude escalar universal, com a selecao de faixa ORIGINAL do contrato.
law utf8_codigo_emite_exatamente_o_escalar:
  for +cp: U32
  for +acc: String
  for valido: {B.codigo_valido(cp) == True{} : Bool}
  {T.percorrer_texto(B.utf8_codigo(cp), T.Lendo{C.Inicio{}, acc}) ==
    T.Lendo{C.Inicio{}, SCon{Chr{cp}, acc}} : T.Texto}
def utf8_codigo_emite_exatamente_o_escalar(cp, acc, valido):
  percorrer_codigo_casos(cp, U32.is_lt(cp, 128), U32.is_lt(cp, 2048), U32.is_lt(cp, 65536), acc, {==}, {==}, {==}, valido)

law percorrer_concatenacao:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +t: T.Texto
  {T.percorrer_texto(B.concatenar(a, b), t) == T.percorrer_texto(b, T.percorrer_texto(a, t)) : T.Texto}
def percorrer_concatenacao(a, b, t):
  match a:
    case Nil{}:
      {==}
    case Con{h, resto}:
      percorrer_concatenacao(resto, b, T.passo_texto(t, h))

# Inducao no texto, conservando um acumulador arbitrario do parser.
law utf8_texto_emite_exatamente_o_texto_invertido:
  for +s: String
  for +acc: String
  for +valido: {B.texto_valido(s) == True{} : Bool}
  {T.percorrer_texto(B.utf8(s), T.Lendo{C.Inicio{}, acc}) ==
    T.Lendo{C.Inicio{}, String.reverse.go(s, acc)} : T.Texto}
def utf8_texto_emite_exatamente_o_texto_invertido(s, acc, valido):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+cp}, +tail}:
      %Equal.sym(T.Texto,
        T.percorrer_texto(B.concatenar(B.utf8_codigo(cp), B.utf8(tail)), T.Lendo{C.Inicio{}, acc}),
        T.percorrer_texto(B.utf8(tail), T.percorrer_texto(B.utf8_codigo(cp), T.Lendo{C.Inicio{}, acc})),
        percorrer_concatenacao(B.utf8_codigo(cp), B.utf8(tail), T.Lendo{C.Inicio{}, acc})) :
        {_ == T.Lendo{C.Inicio{}, String.reverse.go(tail, SCon{Chr{cp}, acc})} : T.Texto}
      %Equal.sym(T.Texto,
        T.percorrer_texto(B.utf8_codigo(cp), T.Lendo{C.Inicio{}, acc}), T.Lendo{C.Inicio{}, SCon{Chr{cp}, acc}},
        utf8_codigo_emite_exatamente_o_escalar(cp, acc, F.e_booleano_esquerda(B.codigo_valido(cp), B.texto_valido(tail), valido))) :
        {T.percorrer_texto(B.utf8(tail), _) == T.Lendo{C.Inicio{}, String.reverse.go(tail, SCon{Chr{cp}, acc})} : T.Texto}
      utf8_texto_emite_exatamente_o_texto_invertido(tail, SCon{Chr{cp}, acc}, F.e_booleano_direita(B.codigo_valido(cp), B.texto_valido(tail), valido))

law reverse_acumulador_duplo:
  for +s: String
  for +a: String
  for +b: String
  {String.reverse.go(String.reverse.go(s, a), b) == String.reverse.go(a, String.append(s, b)) : String}
def reverse_acumulador_duplo(s, a, b):
  match s:
    case SNil{}:
      {==}
    case SCon{h, tail}:
      reverse_acumulador_duplo(tail, SCon{h, a}, b)

law append_vazio_direita:
  for +s: String
  {String.append(s, "") == s : String}
def append_vazio_direita(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, tail}:
      Equal.cong(String, String, r => SCon{h, r}, String.append(tail, ""), tail, append_vazio_direita(tail))

law reverse_duplo:
  for +s: String
  {String.reverse(String.reverse(s)) == s : String}
def reverse_duplo(s):
  Equal.trans(String, String.reverse(String.reverse(s)), String.append(s, ""), s,
    reverse_acumulador_duplo(s, "", ""), append_vazio_direita(s))

# Ida e volta completa de qualquer String valida; nenhum limite de tamanho.
law utf8_texto_valido_decodifica_exatamente:
  for +s: String
  for valido: {B.texto_valido(s) == True{} : Bool}
  {T.finalizar_texto(T.percorrer_texto(B.utf8(s), T.Lendo{C.Inicio{}, ""})) == Some{s} : Maybe<&2, String>}
def utf8_texto_valido_decodifica_exatamente(s, valido):
  %Equal.sym(T.Texto, T.percorrer_texto(B.utf8(s), T.Lendo{C.Inicio{}, ""}), T.Lendo{C.Inicio{}, String.reverse(s)}, utf8_texto_emite_exatamente_o_texto_invertido(s, "", valido)) :
    {T.finalizar_texto(_) == Some{s} : Maybe<&2, String>}
  Equal.cong(String, Maybe<&2, String>, r => Some{r}, String.reverse(String.reverse(s)), s, reverse_duplo(s))
