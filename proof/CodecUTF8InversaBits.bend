# Comparacoes de blocos usadas na inversao UTF-8. Todos os payloads sao
# palavras arbitrarias; os prefixos sao os bits fixados pelo formato UTF-8.
import Base
import ../contrato/Bytes.bend as B
import ../src/Codec.bend as C
import ./CodecPalavrasWord.bend as W
import ./CodecUTF8Bits.bend as X
import ./Fundamentos.bend as F
import ./Ordens.bend as O

def prefixo2(hi: Word(5n)) -> U32:
  U32{W.juntar(5n, 27n, hi, W.ajustar(27n, 32n, X.bits(6)))}

def prefixo3(hi: Word(4n)) -> U32:
  U32{W.juntar(4n, 28n, hi, W.ajustar(28n, 32n, X.bits(14)))}

def prefixo4(hi: Word(3n)) -> U32:
  U32{W.juntar(3n, 29n, hi, W.ajustar(29n, 32n, X.bits(30)))}

def bit_ge_zero(b: Bool, c: Cmp, e: {Cmp.is_ge(c) == True{} : Bool}) ->
  {Cmp.is_ge(Word.cmp.fin(b, False{}, c)) == True{} : Bool}:
  match b c:
    case False{} EQ{}:
      {==}
    case True{} EQ{}:
      {==}
    case _ GT{}:
      {==}
    case _ LT{}:
      e

def bit_le_um(b: Bool, c: Cmp, e: {Cmp.is_le(c) == True{} : Bool}) ->
  {Cmp.is_le(Word.cmp.fin(b, True{}, c)) == True{} : Bool}:
  match b c:
    case False{} EQ{}:
      {==}
    case True{} EQ{}:
      {==}
    case _ LT{}:
      {==}
    case _ GT{}:
      e

law palavra_maior_igual_zero:
  for +n: Nat
  for +w: Word(n)
  {Cmp.is_ge(Word.cmp(n, w, Word.zero(n))) == True{} : Bool}
def palavra_maior_igual_zero(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          bit_ge_zero(b, Word.cmp(p, t, Word.zero(p)), palavra_maior_igual_zero(p, t))

law palavra_menor_igual_uns:
  for +n: Nat
  for +w: Word(n)
  {Cmp.is_le(Word.cmp(n, w, W.uns(n))) == True{} : Bool}
def palavra_menor_igual_uns(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          bit_le_um(b, Word.cmp(p, t, W.uns(p)), palavra_menor_igual_uns(p, t))

law prioridade_ge_sem_negativo:
  for h: Cmp
  for l: Cmp
  for positivo: {Cmp.is_ge(l) == True{} : Bool}
  {Cmp.is_ge(O.prioridade(h, l)) == Cmp.is_ge(h) : Bool}
def prioridade_ge_sem_negativo(h, l, positivo):
  match h:
    case LT{}:
      {==}
    case GT{}:
      {==}
    case EQ{}:
      positivo

law prioridade_le_sem_excesso:
  for h: Cmp
  for l: Cmp
  for cabe: {Cmp.is_le(l) == True{} : Bool}
  {Cmp.is_le(O.prioridade(h, l)) == Cmp.is_le(h) : Bool}
def prioridade_le_sem_excesso(h, l, cabe):
  match h:
    case LT{}:
      {==}
    case GT{}:
      {==}
    case EQ{}:
      cabe

law blocos_limite_inferior:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  for +limite: Word(n)
  {Cmp.is_ge(Word.cmp(Nat.add(k, n), W.juntar(k, n, lo, hi), W.juntar(k, n, Word.zero(k), limite))) ==
    Cmp.is_ge(Word.cmp(n, hi, limite)) : Bool}
def blocos_limite_inferior(k, n, lo, hi, limite):
  %Equal.sym(Cmp,
    Word.cmp(Nat.add(k, n), W.juntar(k, n, lo, hi), W.juntar(k, n, Word.zero(k), limite)),
    O.prioridade(Word.cmp(n, hi, limite), Word.cmp(k, lo, Word.zero(k))),
    X.comparar_blocos(k, n, lo, Word.zero(k), hi, limite)) :
    {Cmp.is_ge(_) == Cmp.is_ge(Word.cmp(n, hi, limite)) : Bool}
  prioridade_ge_sem_negativo(Word.cmp(n, hi, limite), Word.cmp(k, lo, Word.zero(k)), palavra_maior_igual_zero(k, lo))

law blocos_limite_superior:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  for +limite: Word(n)
  {Cmp.is_le(Word.cmp(Nat.add(k, n), W.juntar(k, n, lo, hi), W.juntar(k, n, W.uns(k), limite))) ==
    Cmp.is_le(Word.cmp(n, hi, limite)) : Bool}
def blocos_limite_superior(k, n, lo, hi, limite):
  %Equal.sym(Cmp,
    Word.cmp(Nat.add(k, n), W.juntar(k, n, lo, hi), W.juntar(k, n, W.uns(k), limite)),
    O.prioridade(Word.cmp(n, hi, limite), Word.cmp(k, lo, W.uns(k))),
    X.comparar_blocos(k, n, lo, W.uns(k), hi, limite)) :
    {Cmp.is_le(_) == Cmp.is_le(Word.cmp(n, hi, limite)) : Bool}
  prioridade_le_sem_excesso(Word.cmp(n, hi, limite), Word.cmp(k, lo, W.uns(k)), palavra_menor_igual_uns(k, lo))

law prioridade_le_implica_hi:
  for h: Cmp
  for l: Cmp
  for cabe: {Cmp.is_le(O.prioridade(h, l)) == True{} : Bool}
  {Cmp.is_le(h) == True{} : Bool}
def prioridade_le_implica_hi(h, l, cabe):
  match h:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      cabe

law blocos_limite_hi:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  for +limlo: Word(k)
  for +limhi: Word(n)
  for cabe: {Cmp.is_le(Word.cmp(Nat.add(k, n), W.juntar(k, n, lo, hi), W.juntar(k, n, limlo, limhi))) == True{} : Bool}
  {Cmp.is_le(Word.cmp(n, hi, limhi)) == True{} : Bool}
def blocos_limite_hi(k, n, lo, hi, limlo, limhi, cabe):
  prioridade_le_implica_hi(Word.cmp(n, hi, limhi), Word.cmp(k, lo, limlo),
    (%X.comparar_blocos(k, n, lo, limlo, hi, limhi) :
      {Cmp.is_le(_) == True{} : Bool} cabe))

law lt_falso_e_ge:
  for c: Cmp
  for e: {Cmp.is_lt(c) == False{} : Bool}
  {Cmp.is_ge(c) == True{} : Bool}
def lt_falso_e_ge(c, e):
  match c:
    case EQ{}:
      {==}
    case GT{}:
      {==}
    case LT{}:
      F.absurdo_booleano({False{} == True{} : Bool}, Equal.sym(Bool, True{}, False{}, e))

law prefixo2_lt_128:
  for +lo: Word(5n)
  {U32.is_lt(prefixo2(lo), 128) == False{} : Bool}
def prefixo2_lt_128(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_lt(c),
    U32.cmp(prefixo2(lo), 128), GT{},
    X.comparar_blocos(5n, 27n, lo, W.ajustar(5n, 32n, X.bits(0)),
      W.ajustar(27n, 32n, X.bits(6)), W.ajustar(27n, 32n, X.bits(4))))

law prefixo2_ge_194:
  for +lo: Word(5n)
  {U32.is_ge(prefixo2(lo), 194) == Cmp.is_ge(Word.cmp(5n, lo, W.ajustar(5n, 32n, X.bits(2)))) : Bool}
def prefixo2_ge_194(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_ge(c),
    U32.cmp(prefixo2(lo), 194), Word.cmp(5n, lo, W.ajustar(5n, 32n, X.bits(2))),
    X.comparar_blocos(5n, 27n, lo, W.ajustar(5n, 32n, X.bits(2)),
      W.ajustar(27n, 32n, X.bits(6)), W.ajustar(27n, 32n, X.bits(6))))

law prefixo2_le_223:
  for +lo: Word(5n)
  {U32.is_le(prefixo2(lo), 223) == True{} : Bool}
def prefixo2_le_223(lo):
  blocos_limite_superior(5n, 27n, lo, W.ajustar(27n, 32n, X.bits(6)), W.ajustar(27n, 32n, X.bits(6)))

law prefixo2_subtrair:
  for +lo: Word(5n)
  {(prefixo2(lo) - 192 : U32) == U32{W.juntar(5n, 27n, lo, Word.zero(27n))} : U32}
def prefixo2_subtrair(lo):
  Equal.cong(Word(32n), U32, w => U32{w},
    X.bits((prefixo2(lo) - 192 : U32)), W.juntar(5n, 27n, lo, Word.zero(27n)),
    X.subtrair_blocos(5n, 27n, lo, W.ajustar(27n, 32n, X.bits(6)), W.ajustar(27n, 32n, X.bits(6))))

law prefixo3_lt_128:
  for +lo: Word(4n)
  {U32.is_lt(prefixo3(lo), 128) == False{} : Bool}
def prefixo3_lt_128(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_lt(c),
    U32.cmp(prefixo3(lo), 128), GT{},
    X.comparar_blocos(4n, 28n, lo, W.ajustar(4n, 32n, X.bits(0)),
      W.ajustar(28n, 32n, X.bits(14)), W.ajustar(28n, 32n, X.bits(8))))

law prefixo3_ge_194:
  for +lo: Word(4n)
  {U32.is_ge(prefixo3(lo), 194) == True{} : Bool}
def prefixo3_ge_194(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_ge(c),
    U32.cmp(prefixo3(lo), 194), GT{},
    X.comparar_blocos(4n, 28n, lo, W.ajustar(4n, 32n, X.bits(2)),
      W.ajustar(28n, 32n, X.bits(14)), W.ajustar(28n, 32n, X.bits(12))))

law prefixo3_le_223:
  for +lo: Word(4n)
  {U32.is_le(prefixo3(lo), 223) == False{} : Bool}
def prefixo3_le_223(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c),
    U32.cmp(prefixo3(lo), 223), GT{},
    X.comparar_blocos(4n, 28n, lo, W.ajustar(4n, 32n, X.bits(15)),
      W.ajustar(28n, 32n, X.bits(14)), W.ajustar(28n, 32n, X.bits(13))))

law prefixo3_ge_224:
  for +lo: Word(4n)
  {U32.is_ge(prefixo3(lo), 224) == True{} : Bool}
def prefixo3_ge_224(lo):
  blocos_limite_inferior(4n, 28n, lo, W.ajustar(28n, 32n, X.bits(14)), W.ajustar(28n, 32n, X.bits(14)))

law prefixo3_le_239:
  for +lo: Word(4n)
  {U32.is_le(prefixo3(lo), 239) == True{} : Bool}
def prefixo3_le_239(lo):
  blocos_limite_superior(4n, 28n, lo, W.ajustar(28n, 32n, X.bits(14)), W.ajustar(28n, 32n, X.bits(14)))

law prefixo3_subtrair:
  for +lo: Word(4n)
  {(prefixo3(lo) - 224 : U32) == U32{W.juntar(4n, 28n, lo, Word.zero(28n))} : U32}
def prefixo3_subtrair(lo):
  Equal.cong(Word(32n), U32, w => U32{w},
    X.bits((prefixo3(lo) - 224 : U32)), W.juntar(4n, 28n, lo, Word.zero(28n)),
    X.subtrair_blocos(4n, 28n, lo, W.ajustar(28n, 32n, X.bits(14)), W.ajustar(28n, 32n, X.bits(14))))

law prefixo4_lt_128:
  for +lo: Word(3n)
  {U32.is_lt(prefixo4(lo), 128) == False{} : Bool}
def prefixo4_lt_128(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_lt(c),
    U32.cmp(prefixo4(lo), 128), GT{},
    X.comparar_blocos(3n, 29n, lo, W.ajustar(3n, 32n, X.bits(0)),
      W.ajustar(29n, 32n, X.bits(30)), W.ajustar(29n, 32n, X.bits(16))))

law prefixo4_ge_194:
  for +lo: Word(3n)
  {U32.is_ge(prefixo4(lo), 194) == True{} : Bool}
def prefixo4_ge_194(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_ge(c),
    U32.cmp(prefixo4(lo), 194), GT{},
    X.comparar_blocos(3n, 29n, lo, W.ajustar(3n, 32n, X.bits(2)),
      W.ajustar(29n, 32n, X.bits(30)), W.ajustar(29n, 32n, X.bits(24))))

law prefixo4_le_223:
  for +lo: Word(3n)
  {U32.is_le(prefixo4(lo), 223) == False{} : Bool}
def prefixo4_le_223(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c),
    U32.cmp(prefixo4(lo), 223), GT{},
    X.comparar_blocos(3n, 29n, lo, W.ajustar(3n, 32n, X.bits(7)),
      W.ajustar(29n, 32n, X.bits(30)), W.ajustar(29n, 32n, X.bits(27))))

law prefixo4_ge_224:
  for +lo: Word(3n)
  {U32.is_ge(prefixo4(lo), 224) == True{} : Bool}
def prefixo4_ge_224(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_ge(c),
    U32.cmp(prefixo4(lo), 224), GT{},
    X.comparar_blocos(3n, 29n, lo, W.ajustar(3n, 32n, X.bits(0)),
      W.ajustar(29n, 32n, X.bits(30)), W.ajustar(29n, 32n, X.bits(28))))

law prefixo4_le_239:
  for +lo: Word(3n)
  {U32.is_le(prefixo4(lo), 239) == False{} : Bool}
def prefixo4_le_239(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c),
    U32.cmp(prefixo4(lo), 239), GT{},
    X.comparar_blocos(3n, 29n, lo, W.ajustar(3n, 32n, X.bits(7)),
      W.ajustar(29n, 32n, X.bits(30)), W.ajustar(29n, 32n, X.bits(29))))

law prefixo4_ge_240:
  for +lo: Word(3n)
  {U32.is_ge(prefixo4(lo), 240) == True{} : Bool}
def prefixo4_ge_240(lo):
  blocos_limite_inferior(3n, 29n, lo, W.ajustar(29n, 32n, X.bits(30)), W.ajustar(29n, 32n, X.bits(30)))

law prefixo4_le_244:
  for +lo: Word(3n)
  {U32.is_le(prefixo4(lo), 244) == Cmp.is_le(Word.cmp(3n, lo, W.ajustar(3n, 32n, X.bits(4)))) : Bool}
def prefixo4_le_244(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c),
    U32.cmp(prefixo4(lo), 244), Word.cmp(3n, lo, W.ajustar(3n, 32n, X.bits(4))),
    X.comparar_blocos(3n, 29n, lo, W.ajustar(3n, 32n, X.bits(4)),
      W.ajustar(29n, 32n, X.bits(30)), W.ajustar(29n, 32n, X.bits(30))))

law prefixo4_subtrair:
  for +lo: Word(3n)
  {(prefixo4(lo) - 240 : U32) == U32{W.juntar(3n, 29n, lo, Word.zero(29n))} : U32}
def prefixo4_subtrair(lo):
  Equal.cong(Word(32n), U32, w => U32{w},
    X.bits((prefixo4(lo) - 240 : U32)), W.juntar(3n, 29n, lo, Word.zero(29n)),
    X.subtrair_blocos(3n, 29n, lo, W.ajustar(29n, 32n, X.bits(30)), W.ajustar(29n, 32n, X.bits(30))))

law continuacao_ge_128:
  for +lo: Word(6n)
  {U32.is_ge(X.continuacao(lo), 128) == True{} : Bool}
def continuacao_ge_128(lo):
  blocos_limite_inferior(6n, 26n, lo, W.ajustar(26n, 32n, X.bits(2)), W.ajustar(26n, 32n, X.bits(2)))

law continuacao_le_191:
  for +lo: Word(6n)
  {U32.is_le(X.continuacao(lo), 191) == True{} : Bool}
def continuacao_le_191(lo):
  blocos_limite_superior(6n, 26n, lo, W.ajustar(26n, 32n, X.bits(2)), W.ajustar(26n, 32n, X.bits(2)))

law escalar2_minimo:
  for +hi: Word(5n)
  for +lo: Word(6n)
  {U32.is_ge(X.escalar2(hi, lo), 128) == U32.is_ge(prefixo2(hi), 194) : Bool}
def escalar2_minimo(hi, lo):
  Equal.trans(Bool, U32.is_ge(X.escalar2(hi, lo), 128),
    Cmp.is_ge(Word.cmp(26n, W.juntar(5n, 21n, hi, Word.zero(21n)), W.ajustar(26n, 32n, X.bits(2)))),
    U32.is_ge(prefixo2(hi), 194),
    blocos_limite_inferior(6n, 26n, lo, W.juntar(5n, 21n, hi, Word.zero(21n)), W.ajustar(26n, 32n, X.bits(2))),
    Equal.trans(Bool,
      Cmp.is_ge(Word.cmp(26n, W.juntar(5n, 21n, hi, Word.zero(21n)), W.ajustar(26n, 32n, X.bits(2)))),
      Cmp.is_ge(Word.cmp(5n, hi, W.ajustar(5n, 32n, X.bits(2)))), U32.is_ge(prefixo2(hi), 194),
      Equal.cong(Cmp, Bool, c => Cmp.is_ge(c),
        Word.cmp(26n, W.juntar(5n, 21n, hi, Word.zero(21n)), W.ajustar(26n, 32n, X.bits(2))),
        Word.cmp(5n, hi, W.ajustar(5n, 32n, X.bits(2))),
        X.comparar_blocos(5n, 21n, hi, W.ajustar(5n, 32n, X.bits(2)), Word.zero(21n), Word.zero(21n))),
      Equal.sym(Bool, U32.is_ge(prefixo2(hi), 194), Cmp.is_ge(Word.cmp(5n, hi, W.ajustar(5n, 32n, X.bits(2)))), prefixo2_ge_194(hi))))

law iniciar_dois:
  for +hi: Word(5n)
  for +lo: Word(6n)
  for minimo: {U32.is_ge(X.escalar2(hi, lo), 128) == True{} : Bool}
  {C.passo_utf8(C.Inicio{}, prefixo2(hi)) ==
    C.Parcial{C.Continua{1n, U32{W.juntar(5n, 27n, hi, Word.zero(27n))}, 128}} : C.Escalar}
def iniciar_dois(hi, lo, minimo):
  %Equal.sym(Bool, U32.is_lt(prefixo2(hi), 128), False{}, prefixo2_lt_128(hi)) :
    {C.iniciar_utf8(_, U32.is_ge(prefixo2(hi), 194) && U32.is_le(prefixo2(hi), 223), U32.is_ge(prefixo2(hi), 224) && U32.is_le(prefixo2(hi), 239), U32.is_ge(prefixo2(hi), 240) && U32.is_le(prefixo2(hi), 244), prefixo2(hi)) == C.Parcial{C.Continua{1n, U32{W.juntar(5n, 27n, hi, Word.zero(27n))}, 128}} : C.Escalar}
  %Equal.sym(Bool, U32.is_ge(prefixo2(hi), 194), True{},
    Equal.trans(Bool, U32.is_ge(prefixo2(hi), 194), U32.is_ge(X.escalar2(hi, lo), 128), True{},
      Equal.sym(Bool, U32.is_ge(X.escalar2(hi, lo), 128), U32.is_ge(prefixo2(hi), 194), escalar2_minimo(hi, lo)), minimo)) :
    {C.iniciar_utf8(False{}, _ && U32.is_le(prefixo2(hi), 223), U32.is_ge(prefixo2(hi), 224) && U32.is_le(prefixo2(hi), 239), U32.is_ge(prefixo2(hi), 240) && U32.is_le(prefixo2(hi), 244), prefixo2(hi)) == C.Parcial{C.Continua{1n, U32{W.juntar(5n, 27n, hi, Word.zero(27n))}, 128}} : C.Escalar}
  %Equal.sym(Bool, U32.is_le(prefixo2(hi), 223), True{}, prefixo2_le_223(hi)) :
    {C.iniciar_utf8(False{}, True{} && _, U32.is_ge(prefixo2(hi), 224) && U32.is_le(prefixo2(hi), 239), U32.is_ge(prefixo2(hi), 240) && U32.is_le(prefixo2(hi), 244), prefixo2(hi)) == C.Parcial{C.Continua{1n, U32{W.juntar(5n, 27n, hi, Word.zero(27n))}, 128}} : C.Escalar}
  Equal.cong(U32, C.Escalar, cp => C.Parcial{C.Continua{1n, cp, 128}},
    (prefixo2(hi) - 192 : U32), U32{W.juntar(5n, 27n, hi, Word.zero(27n))}, prefixo2_subtrair(hi))

law iniciar_tres:
  for +hi: Word(4n)
  {C.passo_utf8(C.Inicio{}, prefixo3(hi)) == C.Parcial{C.Continua{2n, U32{W.juntar(4n, 28n, hi, Word.zero(28n))}, 2048}} : C.Escalar}
def iniciar_tres(hi):
  %Equal.sym(Bool, U32.is_lt(prefixo3(hi), 128), False{}, prefixo3_lt_128(hi)) :
    {C.iniciar_utf8(_, U32.is_ge(prefixo3(hi), 194) && U32.is_le(prefixo3(hi), 223), U32.is_ge(prefixo3(hi), 224) && U32.is_le(prefixo3(hi), 239), U32.is_ge(prefixo3(hi), 240) && U32.is_le(prefixo3(hi), 244), prefixo3(hi)) == C.Parcial{C.Continua{2n, U32{W.juntar(4n, 28n, hi, Word.zero(28n))}, 2048}} : C.Escalar}
  %Equal.sym(Bool, U32.is_ge(prefixo3(hi), 194), True{}, prefixo3_ge_194(hi)) :
    {C.iniciar_utf8(False{}, _ && U32.is_le(prefixo3(hi), 223), U32.is_ge(prefixo3(hi), 224) && U32.is_le(prefixo3(hi), 239), U32.is_ge(prefixo3(hi), 240) && U32.is_le(prefixo3(hi), 244), prefixo3(hi)) == C.Parcial{C.Continua{2n, U32{W.juntar(4n, 28n, hi, Word.zero(28n))}, 2048}} : C.Escalar}
  %Equal.sym(Bool, U32.is_le(prefixo3(hi), 223), False{}, prefixo3_le_223(hi)) :
    {C.iniciar_utf8(False{}, True{} && _, U32.is_ge(prefixo3(hi), 224) && U32.is_le(prefixo3(hi), 239), U32.is_ge(prefixo3(hi), 240) && U32.is_le(prefixo3(hi), 244), prefixo3(hi)) == C.Parcial{C.Continua{2n, U32{W.juntar(4n, 28n, hi, Word.zero(28n))}, 2048}} : C.Escalar}
  %Equal.sym(Bool, U32.is_ge(prefixo3(hi), 224), True{}, prefixo3_ge_224(hi)) :
    {C.iniciar_utf8(False{}, True{} && False{}, _ && U32.is_le(prefixo3(hi), 239), U32.is_ge(prefixo3(hi), 240) && U32.is_le(prefixo3(hi), 244), prefixo3(hi)) == C.Parcial{C.Continua{2n, U32{W.juntar(4n, 28n, hi, Word.zero(28n))}, 2048}} : C.Escalar}
  %Equal.sym(Bool, U32.is_le(prefixo3(hi), 239), True{}, prefixo3_le_239(hi)) :
    {C.iniciar_utf8(False{}, True{} && False{}, True{} && _, U32.is_ge(prefixo3(hi), 240) && U32.is_le(prefixo3(hi), 244), prefixo3(hi)) == C.Parcial{C.Continua{2n, U32{W.juntar(4n, 28n, hi, Word.zero(28n))}, 2048}} : C.Escalar}
  Equal.cong(U32, C.Escalar, cp => C.Parcial{C.Continua{2n, cp, 2048}},
    (prefixo3(hi) - 224 : U32), U32{W.juntar(4n, 28n, hi, Word.zero(28n))}, prefixo3_subtrair(hi))

law iniciar_quatro:
  for +hi: Word(3n)
  for cabe: {U32.is_le(prefixo4(hi), 244) == True{} : Bool}
  {C.passo_utf8(C.Inicio{}, prefixo4(hi)) == C.Parcial{C.Continua{3n, U32{W.juntar(3n, 29n, hi, Word.zero(29n))}, 65536}} : C.Escalar}
def iniciar_quatro(hi, cabe):
  %Equal.sym(Bool, U32.is_lt(prefixo4(hi), 128), False{}, prefixo4_lt_128(hi)) :
    {C.iniciar_utf8(_, U32.is_ge(prefixo4(hi), 194) && U32.is_le(prefixo4(hi), 223), U32.is_ge(prefixo4(hi), 224) && U32.is_le(prefixo4(hi), 239), U32.is_ge(prefixo4(hi), 240) && U32.is_le(prefixo4(hi), 244), prefixo4(hi)) == C.Parcial{C.Continua{3n, U32{W.juntar(3n, 29n, hi, Word.zero(29n))}, 65536}} : C.Escalar}
  %Equal.sym(Bool, U32.is_ge(prefixo4(hi), 194), True{}, prefixo4_ge_194(hi)) :
    {C.iniciar_utf8(False{}, _ && U32.is_le(prefixo4(hi), 223), U32.is_ge(prefixo4(hi), 224) && U32.is_le(prefixo4(hi), 239), U32.is_ge(prefixo4(hi), 240) && U32.is_le(prefixo4(hi), 244), prefixo4(hi)) == C.Parcial{C.Continua{3n, U32{W.juntar(3n, 29n, hi, Word.zero(29n))}, 65536}} : C.Escalar}
  %Equal.sym(Bool, U32.is_le(prefixo4(hi), 223), False{}, prefixo4_le_223(hi)) :
    {C.iniciar_utf8(False{}, True{} && _, U32.is_ge(prefixo4(hi), 224) && U32.is_le(prefixo4(hi), 239), U32.is_ge(prefixo4(hi), 240) && U32.is_le(prefixo4(hi), 244), prefixo4(hi)) == C.Parcial{C.Continua{3n, U32{W.juntar(3n, 29n, hi, Word.zero(29n))}, 65536}} : C.Escalar}
  %Equal.sym(Bool, U32.is_ge(prefixo4(hi), 224), True{}, prefixo4_ge_224(hi)) :
    {C.iniciar_utf8(False{}, True{} && False{}, _ && U32.is_le(prefixo4(hi), 239), U32.is_ge(prefixo4(hi), 240) && U32.is_le(prefixo4(hi), 244), prefixo4(hi)) == C.Parcial{C.Continua{3n, U32{W.juntar(3n, 29n, hi, Word.zero(29n))}, 65536}} : C.Escalar}
  %Equal.sym(Bool, U32.is_le(prefixo4(hi), 239), False{}, prefixo4_le_239(hi)) :
    {C.iniciar_utf8(False{}, True{} && False{}, True{} && _, U32.is_ge(prefixo4(hi), 240) && U32.is_le(prefixo4(hi), 244), prefixo4(hi)) == C.Parcial{C.Continua{3n, U32{W.juntar(3n, 29n, hi, Word.zero(29n))}, 65536}} : C.Escalar}
  %Equal.sym(Bool, U32.is_ge(prefixo4(hi), 240), True{}, prefixo4_ge_240(hi)) :
    {C.iniciar_utf8(False{}, True{} && False{}, True{} && False{}, _ && U32.is_le(prefixo4(hi), 244), prefixo4(hi)) == C.Parcial{C.Continua{3n, U32{W.juntar(3n, 29n, hi, Word.zero(29n))}, 65536}} : C.Escalar}
  %Equal.sym(Bool, U32.is_le(prefixo4(hi), 244), True{}, cabe) :
    {C.iniciar_utf8(False{}, True{} && False{}, True{} && False{}, True{} && _, prefixo4(hi)) == C.Parcial{C.Continua{3n, U32{W.juntar(3n, 29n, hi, Word.zero(29n))}, 65536}} : C.Escalar}
  Equal.cong(U32, C.Escalar, cp => C.Parcial{C.Continua{3n, cp, 65536}},
    (prefixo4(hi) - 240 : U32), U32{W.juntar(3n, 29n, hi, Word.zero(29n))}, prefixo4_subtrair(hi))

law passo_continuacao:
  for +n: Nat
  for +cp: U32
  for +minimo: U32
  for +lo: Word(6n)
  {C.passo_utf8(C.Continua{1n+n, cp, minimo}, X.continuacao(lo)) ==
    C.completar_utf8(n, U32{W.juntar(6n, 26n, lo, W.ajustar(26n, 32n, X.bits(cp)))}, minimo) : C.Escalar}
def passo_continuacao(n, cp, minimo, lo):
  %Equal.sym(Bool, U32.is_ge(X.continuacao(lo), 128), True{}, continuacao_ge_128(lo)) :
    {C.continuar_utf8(_ && U32.is_le(X.continuacao(lo), 191), n, cp, minimo, X.continuacao(lo)) == C.completar_utf8(n, U32{W.juntar(6n, 26n, lo, W.ajustar(26n, 32n, X.bits(cp)))}, minimo) : C.Escalar}
  %Equal.sym(Bool, U32.is_le(X.continuacao(lo), 191), True{}, continuacao_le_191(lo)) :
    {C.continuar_utf8(True{} && _, n, cp, minimo, X.continuacao(lo)) == C.completar_utf8(n, U32{W.juntar(6n, 26n, lo, W.ajustar(26n, 32n, X.bits(cp)))}, minimo) : C.Escalar}
  Equal.cong(U32, C.Escalar, z => C.completar_utf8(n, z, minimo),
    (cp * 64 + X.continuacao(lo) - 128 : U32), U32{W.juntar(6n, 26n, lo, W.ajustar(26n, 32n, X.bits(cp)))}, X.continuar_reconstroi_seis_bits_exatos(cp, lo))

law escalar4_prefixo_limitado:
  for +hi: Word(3n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  for +b2: Word(6n)
  for valido: {B.codigo_valido(X.escalar4(hi, b0, b1, b2)) == True{} : Bool}
  {U32.is_le(prefixo4(hi), 244) == True{} : Bool}
def escalar4_prefixo_limitado(hi, b0, b1, b2, valido):
  match b0 b1 b2:
    case WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}} WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WNil{}}}}}}} WCon{+b20, WCon{+b21, WCon{+b22, WCon{+b23, WCon{+b24, WCon{+b25, WNil{}}}}}}}:
      +limite = F.e_booleano_esquerda(U32.is_le(X.escalar4(hi, b0, b1, b2), 1114111),
        U32.is_lt(X.escalar4(hi, b0, b1, b2), 55296) || U32.is_gt(X.escalar4(hi, b0, b1, b2), 57343), valido)
      +alto = blocos_limite_hi(18n, 14n, W.juntar(6n, 12n, b2, W.juntar(6n, 6n, b1, b0)),
        W.juntar(3n, 11n, hi, Word.zero(11n)), W.ajustar(18n, 32n, X.bits(65535)), W.ajustar(14n, 32n, X.bits(4)), limite)
      %Equal.sym(Bool, U32.is_le(prefixo4(hi), 244), Cmp.is_le(Word.cmp(3n, hi, W.ajustar(3n, 32n, X.bits(4)))), prefixo4_le_244(hi)) :
        {_ == True{} : Bool}
      Equal.trans(Bool,
        Cmp.is_le(Word.cmp(3n, hi, W.ajustar(3n, 32n, X.bits(4)))),
        Cmp.is_le(Word.cmp(14n, W.juntar(3n, 11n, hi, Word.zero(11n)), W.ajustar(14n, 32n, X.bits(4)))), True{},
        Equal.cong(Cmp, Bool, c => Cmp.is_le(c),
          Word.cmp(3n, hi, W.ajustar(3n, 32n, X.bits(4))),
          Word.cmp(14n, W.juntar(3n, 11n, hi, Word.zero(11n)), W.ajustar(14n, 32n, X.bits(4))),
          Equal.sym(Cmp,
            Word.cmp(14n, W.juntar(3n, 11n, hi, Word.zero(11n)), W.ajustar(14n, 32n, X.bits(4))),
            Word.cmp(3n, hi, W.ajustar(3n, 32n, X.bits(4))),
            X.comparar_blocos(3n, 11n, hi, W.ajustar(3n, 32n, X.bits(4)), Word.zero(11n), Word.zero(11n)))), alto)
