# Aritmetica geral de reconstrução dos payloads UTF-8, bit a bit.
import Base
import ../contrato/Bytes.bend as B
import ../src/Codec.bend as C
import ./CodecPalavrasWord.bend as W
import ./Ordens.bend as O

# A subtracao usa o complemento do carry inicial da adicao.
law adc_sbb_cancelam:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +carry: Bool
  {Word.adc(n, Word.adc(n, a, b, False{}, carry), b, True{}, Bool.not(carry)) == a : Word(n)}
def adc_sbb_cancelam(n, a, b, carry):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b carry:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r},
            Word.adc(p, Word.adc(p, at, bt, False{}, False{}), bt, True{}, True{}), at,
            adc_sbb_cancelam(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r},
            Word.adc(p, Word.adc(p, at, bt, False{}, False{}), bt, True{}, True{}), at,
            adc_sbb_cancelam(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r},
            Word.adc(p, Word.adc(p, at, bt, False{}, False{}), bt, True{}, True{}), at,
            adc_sbb_cancelam(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r},
            Word.adc(p, Word.adc(p, at, bt, False{}, True{}), bt, True{}, False{}), at,
            adc_sbb_cancelam(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r},
            Word.adc(p, Word.adc(p, at, bt, False{}, False{}), bt, True{}, True{}), at,
            adc_sbb_cancelam(p, at, bt, False{}))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r},
            Word.adc(p, Word.adc(p, at, bt, False{}, True{}), bt, True{}, False{}), at,
            adc_sbb_cancelam(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r},
            Word.adc(p, Word.adc(p, at, bt, False{}, True{}), bt, True{}, False{}), at,
            adc_sbb_cancelam(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r},
            Word.adc(p, Word.adc(p, at, bt, False{}, True{}), bt, True{}, False{}), at,
            adc_sbb_cancelam(p, at, bt, True{}))

law somar_subtrair_cancela:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.sub(n, Word.add(n, a, b), b) == a : Word(n)}
def somar_subtrair_cancela(n, a, b):
  adc_sbb_cancelam(n, a, b, False{})

law somar_blocos:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  for +outro: Word(n)
  {Word.add(Nat.add(k, n), W.zeros_baixos(k, n, hi), W.juntar(k, n, lo, outro)) ==
    W.juntar(k, n, lo, Word.add(n, hi, outro)) : Word(Nat.add(k, n))}
def somar_blocos(k, n, lo, hi, outro):
  match k:
    case 0n:
      {==}
    case 1n+p:
      match lo:
        case WCon{False{}, +t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{False{}, r},
            Word.add(Nat.add(p, n), W.zeros_baixos(p, n, hi), W.juntar(p, n, t, outro)), W.juntar(p, n, t, Word.add(n, hi, outro)),
            somar_blocos(p, n, t, hi, outro))
        case WCon{True{}, +t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{True{}, r},
            Word.add(Nat.add(p, n), W.zeros_baixos(p, n, hi), W.juntar(p, n, t, outro)), W.juntar(p, n, t, Word.add(n, hi, outro)),
            somar_blocos(p, n, t, hi, outro))

law subtrair_blocos:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  for +outro: Word(n)
  {Word.sub(Nat.add(k, n), W.juntar(k, n, lo, hi), W.zeros_baixos(k, n, outro)) ==
    W.juntar(k, n, lo, Word.sub(n, hi, outro)) : Word(Nat.add(k, n))}
def subtrair_blocos(k, n, lo, hi, outro):
  match k:
    case 0n:
      {==}
    case 1n+p:
      match lo:
        case WCon{False{}, +t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{False{}, r},
            Word.sub(Nat.add(p, n), W.juntar(p, n, t, hi), W.zeros_baixos(p, n, outro)), W.juntar(p, n, t, Word.sub(n, hi, outro)),
            subtrair_blocos(p, n, t, hi, outro))
        case WCon{True{}, +t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{True{}, r},
            Word.sub(Nat.add(p, n), W.juntar(p, n, t, hi), W.zeros_baixos(p, n, outro)), W.juntar(p, n, t, Word.sub(n, hi, outro)),
            subtrair_blocos(p, n, t, hi, outro))

def bits(x: U32) -> Word(32n):
  U32{w} = x
  w

def continuacao(lo: Word(6n)) -> U32:
  U32{W.juntar(6n, 26n, lo, W.ajustar(26n, 32n, bits(2)))}

law continuar_reconstroi_seis_bits_exatos:
  for +cp: U32
  for +lo: Word(6n)
  {(cp * 64 + continuacao(lo) - 128 : U32) ==
    U32{W.juntar(6n, 26n, lo, W.ajustar(26n, 32n, bits(cp)))} : U32}
def continuar_reconstroi_seis_bits_exatos(cp, lo):
  match cp:
    case U32{+w}:
      %Equal.sym(Word(32n), Word.mul(32n, w, bits(64)),
        W.zeros_baixos(6n, 26n, W.ajustar(26n, 32n, w)), W.multiplicar_potencia_dois(6n, 26n, 32n, w)) :
        {U32{Word.sub(32n, Word.add(32n, _, bits(continuacao(lo))), bits(128))} == U32{W.juntar(6n, 26n, lo, W.ajustar(26n, 32n, w))} : U32}
      %Equal.sym(Word(32n), Word.add(32n, W.zeros_baixos(6n, 26n, W.ajustar(26n, 32n, w)), bits(continuacao(lo))),
        W.juntar(6n, 26n, lo, Word.add(26n, W.ajustar(26n, 32n, w), W.ajustar(26n, 32n, bits(2)))),
        somar_blocos(6n, 26n, lo, W.ajustar(26n, 32n, w), W.ajustar(26n, 32n, bits(2)))) :
        {U32{Word.sub(32n, _, bits(128))} == U32{W.juntar(6n, 26n, lo, W.ajustar(26n, 32n, w))} : U32}
      %Equal.sym(Word(32n), Word.sub(32n, W.juntar(6n, 26n, lo, Word.add(26n, W.ajustar(26n, 32n, w), W.ajustar(26n, 32n, bits(2)))), bits(128)),
        W.juntar(6n, 26n, lo, Word.sub(26n, Word.add(26n, W.ajustar(26n, 32n, w), W.ajustar(26n, 32n, bits(2))), W.ajustar(26n, 32n, bits(2)))),
        subtrair_blocos(6n, 26n, lo, Word.add(26n, W.ajustar(26n, 32n, w), W.ajustar(26n, 32n, bits(2))), W.ajustar(26n, 32n, bits(2)))) :
        {U32{_} == U32{W.juntar(6n, 26n, lo, W.ajustar(26n, 32n, w))} : U32}
      Equal.cong(Word(26n), U32, z => U32{W.juntar(6n, 26n, lo, z)},
        Word.sub(26n, Word.add(26n, W.ajustar(26n, 32n, w), W.ajustar(26n, 32n, bits(2))), W.ajustar(26n, 32n, bits(2))),
        W.ajustar(26n, 32n, w), somar_subtrair_cancela(26n, W.ajustar(26n, 32n, w), W.ajustar(26n, 32n, bits(2))))

law mascara_seis_bits:
  for +cp: U32
  {U32.and(cp, 63) == U32{W.juntar(6n, 26n, W.ajustar(6n, 32n, bits(cp)), Word.zero(26n))} : U32}
def mascara_seis_bits(cp):
  match cp:
    case U32{w}:
      Equal.cong(Word(32n), U32, z => U32{z}, Word.and(32n, w, W.juntar(6n, 26n, W.uns(6n), Word.zero(26n))),
        W.juntar(6n, 26n, W.ajustar(6n, 32n, w), Word.zero(26n)), W.mascara_baixa(6n, 26n, w))

def escalar2(hi: Word(5n), b0: Word(6n)) -> U32:
  U32{W.juntar(6n, 26n, b0, W.juntar(5n, 21n, hi, Word.zero(21n)))}

law utf8_forma_2_bytes:
  for +hi: Word(5n)
  for +b0: Word(6n)
  {B.utf8_codigo_emitir(escalar2(hi, b0), False{}, True{}, False{}) == [U32{W.juntar(5n, 27n, hi, W.ajustar(27n, 32n, bits(6)))}, continuacao(b0)] : List<&2, U32>}
def utf8_forma_2_bytes(hi, b0):
  match hi b0:
    case WCon{+hi0, WCon{+hi1, WCon{+hi2, WCon{+hi3, WCon{+hi4, WNil{}}}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}}:
      %Equal.sym(U32, U32.and(escalar2(hi, b0), 63), U32{W.juntar(6n, 26n, W.ajustar(6n, 32n, bits(escalar2(hi, b0))), Word.zero(26n))}, mascara_seis_bits(escalar2(hi, b0))) :
        {[U32.or(192, U32.shrn(escalar2(hi, b0), 6n)), U32.or(128, _)] == [U32{W.juntar(5n, 27n, hi, W.ajustar(27n, 32n, bits(6)))}, continuacao(b0)] : List<&2, U32>}
      {==}

def escalar3(hi: Word(4n), b0: Word(6n), b1: Word(6n)) -> U32:
  U32{W.juntar(6n, 26n, b1, W.juntar(6n, 20n, b0, W.juntar(4n, 16n, hi, Word.zero(16n))))}

law utf8_forma_3_bytes:
  for +hi: Word(4n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  {B.utf8_codigo_emitir(escalar3(hi, b0, b1), False{}, False{}, True{}) == [U32{W.juntar(4n, 28n, hi, W.ajustar(28n, 32n, bits(14)))}, continuacao(b0), continuacao(b1)] : List<&2, U32>}
def utf8_forma_3_bytes(hi, b0, b1):
  match hi b0 b1:
    case WCon{+hi0, WCon{+hi1, WCon{+hi2, WCon{+hi3, WNil{}}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}} WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WNil{}}}}}}}:
      %Equal.sym(U32, U32.and(U32.shrn(escalar3(hi, b0, b1), 6n), 63), U32{W.juntar(6n, 26n, W.ajustar(6n, 32n, bits(U32.shrn(escalar3(hi, b0, b1), 6n))), Word.zero(26n))}, mascara_seis_bits(U32.shrn(escalar3(hi, b0, b1), 6n))) :
        {[U32.or(224, U32.shrn(escalar3(hi, b0, b1), 12n)), U32.or(128, _), U32.or(128, U32.and(escalar3(hi, b0, b1), 63))] == [U32{W.juntar(4n, 28n, hi, W.ajustar(28n, 32n, bits(14)))}, continuacao(b0), continuacao(b1)] : List<&2, U32>}
      %Equal.sym(U32, U32.and(escalar3(hi, b0, b1), 63), U32{W.juntar(6n, 26n, W.ajustar(6n, 32n, bits(escalar3(hi, b0, b1))), Word.zero(26n))}, mascara_seis_bits(escalar3(hi, b0, b1))) :
        {[U32.or(224, U32.shrn(escalar3(hi, b0, b1), 12n)), U32.or(128, U32{W.juntar(6n, 26n, W.ajustar(6n, 32n, bits(U32.shrn(escalar3(hi, b0, b1), 6n))), Word.zero(26n))}), U32.or(128, _)] == [U32{W.juntar(4n, 28n, hi, W.ajustar(28n, 32n, bits(14)))}, continuacao(b0), continuacao(b1)] : List<&2, U32>}
      {==}

def escalar4(hi: Word(3n), b0: Word(6n), b1: Word(6n), b2: Word(6n)) -> U32:
  U32{W.juntar(6n, 26n, b2, W.juntar(6n, 20n, b1, W.juntar(6n, 14n, b0, W.juntar(3n, 11n, hi, Word.zero(11n)))))}

law utf8_forma_4_bytes:
  for +hi: Word(3n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  for +b2: Word(6n)
  {B.utf8_codigo_emitir(escalar4(hi, b0, b1, b2), False{}, False{}, False{}) == [U32{W.juntar(3n, 29n, hi, W.ajustar(29n, 32n, bits(30)))}, continuacao(b0), continuacao(b1), continuacao(b2)] : List<&2, U32>}
def utf8_forma_4_bytes(hi, b0, b1, b2):
  match hi b0 b1 b2:
    case WCon{+hi0, WCon{+hi1, WCon{+hi2, WNil{}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}} WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WNil{}}}}}}} WCon{+b20, WCon{+b21, WCon{+b22, WCon{+b23, WCon{+b24, WCon{+b25, WNil{}}}}}}}:
      %Equal.sym(U32, U32.and(U32.shrn(escalar4(hi, b0, b1, b2), 12n), 63), U32{W.juntar(6n, 26n, W.ajustar(6n, 32n, bits(U32.shrn(escalar4(hi, b0, b1, b2), 12n))), Word.zero(26n))}, mascara_seis_bits(U32.shrn(escalar4(hi, b0, b1, b2), 12n))) :
        {[U32.or(240, U32.shrn(escalar4(hi, b0, b1, b2), 18n)), U32.or(128, _), U32.or(128, U32.and(U32.shrn(escalar4(hi, b0, b1, b2), 6n), 63)), U32.or(128, U32.and(escalar4(hi, b0, b1, b2), 63))] == [U32{W.juntar(3n, 29n, hi, W.ajustar(29n, 32n, bits(30)))}, continuacao(b0), continuacao(b1), continuacao(b2)] : List<&2, U32>}
      %Equal.sym(U32, U32.and(U32.shrn(escalar4(hi, b0, b1, b2), 6n), 63), U32{W.juntar(6n, 26n, W.ajustar(6n, 32n, bits(U32.shrn(escalar4(hi, b0, b1, b2), 6n))), Word.zero(26n))}, mascara_seis_bits(U32.shrn(escalar4(hi, b0, b1, b2), 6n))) :
        {[U32.or(240, U32.shrn(escalar4(hi, b0, b1, b2), 18n)), U32.or(128, U32{W.juntar(6n, 26n, W.ajustar(6n, 32n, bits(U32.shrn(escalar4(hi, b0, b1, b2), 12n))), Word.zero(26n))}), U32.or(128, _), U32.or(128, U32.and(escalar4(hi, b0, b1, b2), 63))] == [U32{W.juntar(3n, 29n, hi, W.ajustar(29n, 32n, bits(30)))}, continuacao(b0), continuacao(b1), continuacao(b2)] : List<&2, U32>}
      %Equal.sym(U32, U32.and(escalar4(hi, b0, b1, b2), 63), U32{W.juntar(6n, 26n, W.ajustar(6n, 32n, bits(escalar4(hi, b0, b1, b2))), Word.zero(26n))}, mascara_seis_bits(escalar4(hi, b0, b1, b2))) :
        {[U32.or(240, U32.shrn(escalar4(hi, b0, b1, b2), 18n)), U32.or(128, U32{W.juntar(6n, 26n, W.ajustar(6n, 32n, bits(U32.shrn(escalar4(hi, b0, b1, b2), 12n))), Word.zero(26n))}), U32.or(128, U32{W.juntar(6n, 26n, W.ajustar(6n, 32n, bits(U32.shrn(escalar4(hi, b0, b1, b2), 6n))), Word.zero(26n))}), U32.or(128, _)] == [U32{W.juntar(3n, 29n, hi, W.ajustar(29n, 32n, bits(30)))}, continuacao(b0), continuacao(b1), continuacao(b2)] : List<&2, U32>}
      {==}

law prioridade_associativa:
  for a: Cmp
  for b: Cmp
  for c: Cmp
  {O.prioridade(O.prioridade(a, b), c) == O.prioridade(a, O.prioridade(b, c)) : Cmp}
def prioridade_associativa(a, b, c):
  match a:
    case EQ{}:
      {==}
    case LT{}:
      {==}
    case GT{}:
      {==}

law prioridade_igual_direita:
  for c: Cmp
  {O.prioridade(c, EQ{}) == c : Cmp}
def prioridade_igual_direita(c):
  match c:
    case EQ{}:
      {==}
    case LT{}:
      {==}
    case GT{}:
      {==}

law comparar_blocos:
  for +k: Nat
  for +n: Nat
  for +a: Word(k)
  for +b: Word(k)
  for +x: Word(n)
  for +y: Word(n)
  {Word.cmp(Nat.add(k, n), W.juntar(k, n, a, x), W.juntar(k, n, b, y)) ==
    O.prioridade(Word.cmp(n, x, y), Word.cmp(k, a, b)) : Cmp}
def comparar_blocos(k, n, a, b, x, y):
  match k:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          Equal.sym(Cmp, O.prioridade(Word.cmp(n, x, y), EQ{}), Word.cmp(n, x, y), prioridade_igual_direita(Word.cmp(n, x, y)))
    case 1n+p:
      match a b:
        case WCon{+ah, +at} WCon{+bh, +bt}:
          %Equal.sym(Cmp,
            Word.cmp(Nat.add(p, n), W.juntar(p, n, at, x), W.juntar(p, n, bt, y)),
            O.prioridade(Word.cmp(n, x, y), Word.cmp(p, at, bt)), comparar_blocos(p, n, at, bt, x, y)) :
            {Word.cmp.fin(ah, bh, _) == O.prioridade(Word.cmp(n, x, y), Word.cmp(1n+p, a, b)) : Cmp}
          Equal.trans(Cmp,
            Word.cmp.fin(ah, bh, O.prioridade(Word.cmp(n, x, y), Word.cmp(p, at, bt))),
            O.prioridade(O.prioridade(Word.cmp(n, x, y), Word.cmp(p, at, bt)), Bool.cmp(ah, bh)),
            O.prioridade(Word.cmp(n, x, y), Word.cmp(1n+p, a, b)),
            O.word_fin_prioridade(ah, bh, O.prioridade(Word.cmp(n, x, y), Word.cmp(p, at, bt))),
            Equal.trans(Cmp,
              O.prioridade(O.prioridade(Word.cmp(n, x, y), Word.cmp(p, at, bt)), Bool.cmp(ah, bh)),
              O.prioridade(Word.cmp(n, x, y), O.prioridade(Word.cmp(p, at, bt), Bool.cmp(ah, bh))),
              O.prioridade(Word.cmp(n, x, y), Word.cmp(1n+p, a, b)),
              prioridade_associativa(Word.cmp(n, x, y), Word.cmp(p, at, bt), Bool.cmp(ah, bh)),
              Equal.cong(Cmp, Cmp, c => O.prioridade(Word.cmp(n, x, y), c),
                O.prioridade(Word.cmp(p, at, bt), Bool.cmp(ah, bh)), Word.cmp(1n+p, a, b),
                Equal.sym(Cmp, Word.cmp(1n+p, a, b), O.prioridade(Word.cmp(p, at, bt), Bool.cmp(ah, bh)), O.word_fin_prioridade(ah, bh, Word.cmp(p, at, bt))))))
