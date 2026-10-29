# Lemas gerais sobre os escalares REALMENTE emitidos pelo parser.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./Ordens.bend as O

# Um incremento de Word so e usado abaixo quando existe um bit zero.
def sem_transporte(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          True{}
        case WCon{True{}, t}:
          sem_transporte(p, t)

law comparacao_bit_sucessor:
  for b: Bool
  for c: Cmp
  {Cmp.is_le(Word.cmp.fin(b, False{}, c)) ==
    Cmp.is_lt(Word.cmp.fin(b, True{}, c)) : Bool}
def comparacao_bit_sucessor(b, c):
  match b c:
    case False{} LT{}:
      {==}
    case False{} EQ{}:
      {==}
    case False{} GT{}:
      {==}
    case True{} LT{}:
      {==}
    case True{} EQ{}:
      {==}
    case True{} GT{}:
      {==}

law comparacao_bit_transporte:
  for b: Bool
  for c: Cmp
  for d: Cmp
  for e: {Cmp.is_le(c) == Cmp.is_lt(d) : Bool}
  {Cmp.is_le(Word.cmp.fin(b, True{}, c)) ==
    Cmp.is_lt(Word.cmp.fin(b, False{}, d)) : Bool}
def comparacao_bit_transporte(b, c, d, e):
  match b:
    case False{}:
      match c d:
        case LT{} LT{}:
          {==}
        case LT{} EQ{}:
          F.absurdo_booleano({Cmp.is_le(Word.cmp.fin(False{}, True{}, LT{})) == Cmp.is_lt(Word.cmp.fin(False{}, False{}, EQ{})) : Bool}, Equal.sym(Bool, True{}, False{}, e))
        case LT{} GT{}:
          F.absurdo_booleano({Cmp.is_le(Word.cmp.fin(False{}, True{}, LT{})) == Cmp.is_lt(Word.cmp.fin(False{}, False{}, GT{})) : Bool}, Equal.sym(Bool, True{}, False{}, e))
        case EQ{} LT{}:
          {==}
        case EQ{} EQ{}:
          F.absurdo_booleano({Cmp.is_le(Word.cmp.fin(False{}, True{}, EQ{})) == Cmp.is_lt(Word.cmp.fin(False{}, False{}, EQ{})) : Bool}, Equal.sym(Bool, True{}, False{}, e))
        case EQ{} GT{}:
          F.absurdo_booleano({Cmp.is_le(Word.cmp.fin(False{}, True{}, EQ{})) == Cmp.is_lt(Word.cmp.fin(False{}, False{}, GT{})) : Bool}, Equal.sym(Bool, True{}, False{}, e))
        case GT{} LT{}:
          F.absurdo_booleano({Cmp.is_le(Word.cmp.fin(False{}, True{}, GT{})) == Cmp.is_lt(Word.cmp.fin(False{}, False{}, LT{})) : Bool}, e)
        case GT{} EQ{}:
          {==}
        case GT{} GT{}:
          {==}
    case True{}:
      match c d:
        case LT{} LT{}:
          {==}
        case LT{} EQ{}:
          F.absurdo_booleano({Cmp.is_le(Word.cmp.fin(True{}, True{}, LT{})) == Cmp.is_lt(Word.cmp.fin(True{}, False{}, EQ{})) : Bool}, Equal.sym(Bool, True{}, False{}, e))
        case LT{} GT{}:
          F.absurdo_booleano({Cmp.is_le(Word.cmp.fin(True{}, True{}, LT{})) == Cmp.is_lt(Word.cmp.fin(True{}, False{}, GT{})) : Bool}, Equal.sym(Bool, True{}, False{}, e))
        case EQ{} LT{}:
          {==}
        case EQ{} EQ{}:
          F.absurdo_booleano({Cmp.is_le(Word.cmp.fin(True{}, True{}, EQ{})) == Cmp.is_lt(Word.cmp.fin(True{}, False{}, EQ{})) : Bool}, Equal.sym(Bool, True{}, False{}, e))
        case EQ{} GT{}:
          F.absurdo_booleano({Cmp.is_le(Word.cmp.fin(True{}, True{}, EQ{})) == Cmp.is_lt(Word.cmp.fin(True{}, False{}, GT{})) : Bool}, Equal.sym(Bool, True{}, False{}, e))
        case GT{} LT{}:
          F.absurdo_booleano({Cmp.is_le(Word.cmp.fin(True{}, True{}, GT{})) == Cmp.is_lt(Word.cmp.fin(True{}, False{}, LT{})) : Bool}, e)
        case GT{} EQ{}:
          {==}
        case GT{} GT{}:
          {==}

law word_limite_sucessor:
  for +n: Nat
  for +x: Word(n)
  for +y: Word(n)
  for cabe: {sem_transporte(n, y) == True{} : Bool}
  {Cmp.is_le(Word.cmp(n, x, y)) == Cmp.is_lt(Word.cmp(n, x, Word.inc(n, y))) : Bool}
def word_limite_sucessor(n, x, y, cabe):
  match n:
    case 0n:
      F.absurdo_booleano({Cmp.is_le(Word.cmp(0n, x, y)) == Cmp.is_lt(Word.cmp(0n, x, Word.inc(0n, y))) : Bool}, cabe)
    case 1n+p:
      match x y:
        case WCon{b, +xt} WCon{False{}, +yt}:
          comparacao_bit_sucessor(b, Word.cmp(p, xt, yt))
        case WCon{b, +xt} WCon{True{}, +yt}:
          comparacao_bit_transporte(b, Word.cmp(p, xt, yt), Word.cmp(p, xt, Word.inc(p, yt)), word_limite_sucessor(p, xt, yt, cabe))

law comparacoes_complementares:
  for c: Cmp
  for d: Cmp
  for e: {Cmp.is_le(c) == Cmp.is_lt(d) : Bool}
  {Cmp.is_gt(c) == Cmp.is_ge(d) : Bool}
def comparacoes_complementares(c, d, e):
  match c d:
    case LT{} LT{}:
      {==}
    case EQ{} LT{}:
      {==}
    case GT{} EQ{}:
      {==}
    case GT{} GT{}:
      {==}
    case GT{} LT{}:
      Equal.sym(Bool, Cmp.is_le(c), Cmp.is_lt(d), e)
    case LT{} EQ{}:
      Equal.sym(Bool, Cmp.is_le(c), Cmp.is_lt(d), e)
    case LT{} GT{}:
      Equal.sym(Bool, Cmp.is_le(c), Cmp.is_lt(d), e)
    case EQ{} EQ{}:
      Equal.sym(Bool, Cmp.is_le(c), Cmp.is_lt(d), e)
    case EQ{} GT{}:
      Equal.sym(Bool, Cmp.is_le(c), Cmp.is_lt(d), e)

def bits(x: U32) -> Word(32n):
  U32{w} = x
  w

law limite_u32_sucessor:
  for x: U32
  for y: U32
  for cabe: {sem_transporte(32n, bits(y)) == True{} : Bool}
  {U32.is_le(x, y) == U32.is_lt(x, U32{Word.inc(32n, bits(y))}) : Bool}
def limite_u32_sucessor(x, y, cabe):
  match x y:
    case U32{a} U32{b}:
      word_limite_sucessor(32n, a, b, cabe)

law predicados_unicode_concordam:
  for +cp: U32
  {B.codigo_valido(cp) == D.escalar_valido(cp) : Bool}
def predicados_unicode_concordam(cp):
  %Equal.sym(Bool, U32.is_le(cp, 1114111), U32.is_lt(cp, 1114112), limite_u32_sucessor(cp, 1114111, {==})) :
    {_ && (U32.is_lt(cp, 55296) || U32.is_gt(cp, 57343)) == D.escalar_valido(cp) : Bool}
  %Equal.sym(Bool, U32.is_gt(cp, 57343), U32.is_ge(cp, 57344),
    comparacoes_complementares(U32.cmp(cp, 57343), U32.cmp(cp, 57344), limite_u32_sucessor(cp, 57343, {==}))) :
    {U32.is_lt(cp, 1114112) && (U32.is_lt(cp, 55296) || _) == D.escalar_valido(cp) : Bool}
  {==}

law u32_lt_transitivo:
  for +a: U32
  for +b: U32
  for +c: U32
  for ab: {U32.is_lt(a, b) == True{} : Bool}
  for bc: {U32.is_lt(b, c) == True{} : Bool}
  {U32.is_lt(a, c) == True{} : Bool}
def u32_lt_transitivo(a, b, c, ab, bc):
  h1 = {(%O.cmp_lt(U32.cmp(a, b), ab) : O.Coerente(_, U32.cmp(b, c), U32.cmp(a, c))
    O.u32_coerente(a, b, c)) : O.Coerente(LT{}, U32.cmp(b, c), U32.cmp(a, c))}
  h2 = {(%O.cmp_lt(U32.cmp(b, c), bc) : O.Coerente(LT{}, _, U32.cmp(a, c))
    h1) : O.Coerente(LT{}, LT{}, U32.cmp(a, c))}
  Equal.cong(Cmp, Bool, k => Cmp.is_lt(k), U32.cmp(a, c), LT{}, h2)

law ascii_e_escalar:
  for +cp: U32
  for ascii: {U32.is_lt(cp, 128) == True{} : Bool}
  {D.escalar_valido(cp) == True{} : Bool}
def ascii_e_escalar(cp, ascii):
  +menor = u32_lt_transitivo(cp, 128, 55296, ascii, {==})
  maior = u32_lt_transitivo(cp, 55296, 1114112, menor, {==})
  %Equal.sym(Bool, U32.is_lt(cp, 1114112), True{}, maior) : {_ && (U32.is_lt(cp, 55296) || U32.is_ge(cp, 57344)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_lt(cp, 55296), True{}, menor) : {True{} && (_ || U32.is_ge(cp, 57344)) == True{} : Bool}
  {==}

def EscalarValido(e: C.Escalar) -> Type:
  match e:
    case C.Caractere{cp}:
      {D.escalar_valido(cp) == True{} : Bool}
    case _:
      Unit

law escalar_conferido_valido:
  for +ok: Bool
  for +cp: U32
  for valido: {ok == True{} : Bool} -> {B.codigo_valido(cp) == True{} : Bool}
  EscalarValido(C.escalar_conferido(ok, cp))
def escalar_conferido_valido(ok, cp, valido):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      Equal.trans(Bool, D.escalar_valido(cp), B.codigo_valido(cp), True{}, Equal.sym(Bool, B.codigo_valido(cp), D.escalar_valido(cp), predicados_unicode_concordam(cp)), valido({==}))

law completar_utf8_emite_escalar_valido:
  for n: Nat
  for +cp: U32
  for +minimo: U32
  EscalarValido(C.completar_utf8(n, cp, minimo))
def completar_utf8_emite_escalar_valido(n, cp, minimo):
  match n:
    case 0n:
      escalar_conferido_valido(U32.is_ge(cp, minimo) && B.codigo_valido(cp), cp,
        e => F.e_booleano_direita(U32.is_ge(cp, minimo), B.codigo_valido(cp), e))
    case 1n+p:
      Unit{}

law continuar_utf8_emite_escalar_valido:
  for ok: Bool
  for n: Nat
  for cp: U32
  for minimo: U32
  for b: U32
  EscalarValido(C.continuar_utf8(ok, n, cp, minimo, b))
def continuar_utf8_emite_escalar_valido(ok, n, cp, minimo, b):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      completar_utf8_emite_escalar_valido(n, (cp * 64 + b - 128 : U32), minimo)

law iniciar_utf8_emite_escalar_valido:
  for +ascii: Bool
  for dois: Bool
  for tres: Bool
  for quatro: Bool
  for +b: U32
  for e: {ascii == True{} : Bool} -> {U32.is_lt(b, 128) == True{} : Bool}
  EscalarValido(C.iniciar_utf8(ascii, dois, tres, quatro, b))
def iniciar_utf8_emite_escalar_valido(ascii, dois, tres, quatro, b, e):
  match ascii dois tres quatro:
    case True{} _ _ _:
      ascii_e_escalar(b, e({==}))
    case False{} True{} _ _:
      Unit{}
    case False{} False{} True{} _:
      Unit{}
    case False{} False{} False{} True{}:
      Unit{}
    case False{} False{} False{} False{}:
      Unit{}

law passo_utf8_so_emite_escalares_validos:
  for u: C.Unicode
  for +b: U32
  EscalarValido(C.passo_utf8(u, b))
def passo_utf8_so_emite_escalares_validos(u, b):
  match u:
    case C.Inicio{}:
      iniciar_utf8_emite_escalar_valido(U32.is_lt(b, 128), U32.is_ge(b, 194) && U32.is_le(b, 223), U32.is_ge(b, 224) && U32.is_le(b, 239), U32.is_ge(b, 240) && U32.is_le(b, 244), b, e => e)
    case C.Continua{0n, cp, minimo}:
      Unit{}
    case C.Continua{1n+p, cp, minimo}:
      continuar_utf8_emite_escalar_valido(U32.is_ge(b, 128) && U32.is_le(b, 191), p, cp, minimo, b)

law reverse_preserva_unicode_acumulado:
  for +s: String
  for +acc: String
  for +valida: {D.unicode_valido(s) == True{} : Bool}
  for acumulada: {D.unicode_valido(acc) == True{} : Bool}
  {D.unicode_valido(String.reverse.go(s, acc)) == True{} : Bool}
def reverse_preserva_unicode_acumulado(s, acc, valida, acumulada):
  match s:
    case SNil{}:
      acumulada
    case SCon{Chr{+cp}, +t}:
      reverse_preserva_unicode_acumulado(t, SCon{Chr{cp}, acc},
        F.e_booleano_direita(D.escalar_valido(cp), D.unicode_valido(t), valida),
        F.e_booleano_intro(D.escalar_valido(cp), D.unicode_valido(acc),
          F.e_booleano_esquerda(D.escalar_valido(cp), D.unicode_valido(t), valida), acumulada))

law reverse_preserva_unicode:
  for +s: String
  for +valida: {D.unicode_valido(s) == True{} : Bool}
  {D.unicode_valido(String.reverse(s)) == True{} : Bool}
def reverse_preserva_unicode(s, valida):
  reverse_preserva_unicode_acumulado(s, "", valida, {==})
