# Soma verificada para qualquer largura: carry explicito e overflow absorvente.
# Nenhum limite de largura ou de valor e usado como combustivel.
import Base
import ./Fundamentos.bend as F
import ./CodecContadores.bend as N
import ./CodecPalavrasWord.bend as W

def fim(-n: Nat, overflow: Bool, w: Word(n)) -> Maybe<&2, Word(n)>:
  match overflow:
    case False{}:
      Some{w}
    case True{}:
      None{}

def anexar(-n: Nat, b: Bool, m: Maybe<&2, Word(n)>) -> Maybe<&2, Word(1n+n)>:
  match m:
    case None{}:
      None{}
    case Some{w}:
      Some{WCon{b, w}}

def soma(n: Nat, a: Word(n), b: Word(n), c: Bool) -> Maybe<&2, Word(n)>:
  match n:
    case 0n:
      fim(0n, c, WNil{})
    case 1n+p:
      match a b c:
        case WCon{False{}, at} WCon{False{}, bt} False{}:
          anexar(p, False{}, soma(p, at, bt, False{}))
        case WCon{False{}, at} WCon{False{}, bt} True{}:
          anexar(p, True{}, soma(p, at, bt, False{}))
        case WCon{False{}, at} WCon{True{}, bt} False{}:
          anexar(p, True{}, soma(p, at, bt, False{}))
        case WCon{False{}, at} WCon{True{}, bt} True{}:
          anexar(p, False{}, soma(p, at, bt, True{}))
        case WCon{True{}, at} WCon{False{}, bt} False{}:
          anexar(p, True{}, soma(p, at, bt, False{}))
        case WCon{True{}, at} WCon{False{}, bt} True{}:
          anexar(p, False{}, soma(p, at, bt, True{}))
        case WCon{True{}, at} WCon{True{}, bt} False{}:
          anexar(p, False{}, soma(p, at, bt, True{}))
        case WCon{True{}, at} WCon{True{}, bt} True{}:
          anexar(p, True{}, soma(p, at, bt, True{}))

def carry(n: Nat, a: Word(n), b: Word(n), c: Bool) -> Bool:
  match n:
    case 0n:
      c
    case 1n+p:
      match a b c:
        case WCon{False{}, at} WCon{False{}, bt} False{}:
          carry(p, at, bt, False{})
        case WCon{False{}, at} WCon{False{}, bt} True{}:
          carry(p, at, bt, False{})
        case WCon{False{}, at} WCon{True{}, bt} False{}:
          carry(p, at, bt, False{})
        case WCon{False{}, at} WCon{True{}, bt} True{}:
          carry(p, at, bt, True{})
        case WCon{True{}, at} WCon{False{}, bt} False{}:
          carry(p, at, bt, False{})
        case WCon{True{}, at} WCon{False{}, bt} True{}:
          carry(p, at, bt, True{})
        case WCon{True{}, at} WCon{True{}, bt} False{}:
          carry(p, at, bt, True{})
        case WCon{True{}, at} WCon{True{}, bt} True{}:
          carry(p, at, bt, True{})

def incrementar(+n: Nat, m: Maybe<&2, Word(n)>) -> Maybe<&2, Word(n)>:
  match m:
    case None{}:
      None{}
    case Some{+w}:
      fim(n, N.uns(n, w), Word.inc(n, w))

def somar_opcionais(n: Nat, a: Maybe<&2, Word(n)>, b: Maybe<&2, Word(n)>) -> Maybe<&2, Word(n)>:
  match a b:
    case Some{x} Some{y}:
      soma(n, x, y, False{})
    case _ _:
      None{}

def natural(+n: Nat, v: Nat) -> Maybe<&2, Word(n)>:
  match v:
    case 0n:
      Some{Word.zero(n)}
    case 1n+p:
      incrementar(n, natural(n, p))

law anexar_fim:
  for +n: Nat
  for +b: Bool
  for +c: Bool
  for +w: Word(n)
  {anexar(n, b, fim(n, c, w)) == fim(1n+n, c, WCon{b, w}) : Maybe<&2, Word(1n+n)>}
def anexar_fim(n, b, c, w):
  match c:
    case False{}:
      {==}
    case True{}:
      {==}

law soma_exata:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Bool
  {soma(n, a, b, c) == fim(n, carry(n, a, b, c), Word.adc(n, a, b, False{}, c)) : Maybe<&2, Word(n)>}
def soma_exata(n, a, b, c):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          Equal.trans(Maybe<&2, Word(1n+p)>,
            anexar(p, False{}, soma(p, at, bt, False{})),
            anexar(p, False{}, fim(p, carry(p, at, bt, False{}), Word.adc(p, at, bt, False{}, False{}))),
            fim(1n+p, carry(p, at, bt, False{}), WCon{False{}, Word.adc(p, at, bt, False{}, False{})}),
            Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => anexar(p, False{}, m),
              soma(p, at, bt, False{}), fim(p, carry(p, at, bt, False{}), Word.adc(p, at, bt, False{}, False{})), soma_exata(p, at, bt, False{})),
            anexar_fim(p, False{}, carry(p, at, bt, False{}), Word.adc(p, at, bt, False{}, False{})))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          Equal.trans(Maybe<&2, Word(1n+p)>,
            anexar(p, True{}, soma(p, at, bt, False{})),
            anexar(p, True{}, fim(p, carry(p, at, bt, False{}), Word.adc(p, at, bt, False{}, False{}))),
            fim(1n+p, carry(p, at, bt, False{}), WCon{True{}, Word.adc(p, at, bt, False{}, False{})}),
            Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => anexar(p, True{}, m),
              soma(p, at, bt, False{}), fim(p, carry(p, at, bt, False{}), Word.adc(p, at, bt, False{}, False{})), soma_exata(p, at, bt, False{})),
            anexar_fim(p, True{}, carry(p, at, bt, False{}), Word.adc(p, at, bt, False{}, False{})))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          Equal.trans(Maybe<&2, Word(1n+p)>,
            anexar(p, True{}, soma(p, at, bt, False{})),
            anexar(p, True{}, fim(p, carry(p, at, bt, False{}), Word.adc(p, at, bt, False{}, False{}))),
            fim(1n+p, carry(p, at, bt, False{}), WCon{True{}, Word.adc(p, at, bt, False{}, False{})}),
            Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => anexar(p, True{}, m),
              soma(p, at, bt, False{}), fim(p, carry(p, at, bt, False{}), Word.adc(p, at, bt, False{}, False{})), soma_exata(p, at, bt, False{})),
            anexar_fim(p, True{}, carry(p, at, bt, False{}), Word.adc(p, at, bt, False{}, False{})))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          Equal.trans(Maybe<&2, Word(1n+p)>,
            anexar(p, False{}, soma(p, at, bt, True{})),
            anexar(p, False{}, fim(p, carry(p, at, bt, True{}), Word.adc(p, at, bt, False{}, True{}))),
            fim(1n+p, carry(p, at, bt, True{}), WCon{False{}, Word.adc(p, at, bt, False{}, True{})}),
            Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => anexar(p, False{}, m),
              soma(p, at, bt, True{}), fim(p, carry(p, at, bt, True{}), Word.adc(p, at, bt, False{}, True{})), soma_exata(p, at, bt, True{})),
            anexar_fim(p, False{}, carry(p, at, bt, True{}), Word.adc(p, at, bt, False{}, True{})))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          Equal.trans(Maybe<&2, Word(1n+p)>,
            anexar(p, True{}, soma(p, at, bt, False{})),
            anexar(p, True{}, fim(p, carry(p, at, bt, False{}), Word.adc(p, at, bt, False{}, False{}))),
            fim(1n+p, carry(p, at, bt, False{}), WCon{True{}, Word.adc(p, at, bt, False{}, False{})}),
            Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => anexar(p, True{}, m),
              soma(p, at, bt, False{}), fim(p, carry(p, at, bt, False{}), Word.adc(p, at, bt, False{}, False{})), soma_exata(p, at, bt, False{})),
            anexar_fim(p, True{}, carry(p, at, bt, False{}), Word.adc(p, at, bt, False{}, False{})))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          Equal.trans(Maybe<&2, Word(1n+p)>,
            anexar(p, False{}, soma(p, at, bt, True{})),
            anexar(p, False{}, fim(p, carry(p, at, bt, True{}), Word.adc(p, at, bt, False{}, True{}))),
            fim(1n+p, carry(p, at, bt, True{}), WCon{False{}, Word.adc(p, at, bt, False{}, True{})}),
            Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => anexar(p, False{}, m),
              soma(p, at, bt, True{}), fim(p, carry(p, at, bt, True{}), Word.adc(p, at, bt, False{}, True{})), soma_exata(p, at, bt, True{})),
            anexar_fim(p, False{}, carry(p, at, bt, True{}), Word.adc(p, at, bt, False{}, True{})))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          Equal.trans(Maybe<&2, Word(1n+p)>,
            anexar(p, False{}, soma(p, at, bt, True{})),
            anexar(p, False{}, fim(p, carry(p, at, bt, True{}), Word.adc(p, at, bt, False{}, True{}))),
            fim(1n+p, carry(p, at, bt, True{}), WCon{False{}, Word.adc(p, at, bt, False{}, True{})}),
            Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => anexar(p, False{}, m),
              soma(p, at, bt, True{}), fim(p, carry(p, at, bt, True{}), Word.adc(p, at, bt, False{}, True{})), soma_exata(p, at, bt, True{})),
            anexar_fim(p, False{}, carry(p, at, bt, True{}), Word.adc(p, at, bt, False{}, True{})))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          Equal.trans(Maybe<&2, Word(1n+p)>,
            anexar(p, True{}, soma(p, at, bt, True{})),
            anexar(p, True{}, fim(p, carry(p, at, bt, True{}), Word.adc(p, at, bt, False{}, True{}))),
            fim(1n+p, carry(p, at, bt, True{}), WCon{True{}, Word.adc(p, at, bt, False{}, True{})}),
            Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => anexar(p, True{}, m),
              soma(p, at, bt, True{}), fim(p, carry(p, at, bt, True{}), Word.adc(p, at, bt, False{}, True{})), soma_exata(p, at, bt, True{})),
            anexar_fim(p, True{}, carry(p, at, bt, True{}), Word.adc(p, at, bt, False{}, True{})))


law incrementar_anexar_zero:
  for +n: Nat
  for +m: Maybe<&2, Word(n)>
  {incrementar(1n+n, anexar(n, False{}, m)) == anexar(n, True{}, m) : Maybe<&2, Word(1n+n)>}
def incrementar_anexar_zero(n, m):
  match m:
    case None{}:
      {==}
    case Some{w}:
      {==}

law incrementar_anexar_um:
  for +n: Nat
  for +m: Maybe<&2, Word(n)>
  {incrementar(1n+n, anexar(n, True{}, m)) == anexar(n, False{}, incrementar(n, m)) : Maybe<&2, Word(1n+n)>}
def incrementar_anexar_um(n, m):
  match m:
    case None{}:
      {==}
    case Some{+w}:
      Equal.sym(Maybe<&2, Word(1n+n)>,
        anexar(n, False{}, fim(n, N.uns(n, w), Word.inc(n, w))),
        fim(1n+n, N.uns(n, w), WCon{False{}, Word.inc(n, w)}),
        anexar_fim(n, False{}, N.uns(n, w), Word.inc(n, w)))

law carry_inicial_e_incremento:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {soma(n, a, b, True{}) == incrementar(n, soma(n, a, b, False{})) : Maybe<&2, Word(n)>}
def carry_inicial_e_incremento(n, a, b):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          Equal.sym(Maybe<&2, Word(1n+p)>, incrementar(1n+p, anexar(p, False{}, soma(p, at, bt, False{}))), anexar(p, True{}, soma(p, at, bt, False{})),
            incrementar_anexar_zero(p, soma(p, at, bt, False{})))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          Equal.trans(Maybe<&2, Word(1n+p)>,
            anexar(p, False{}, soma(p, at, bt, True{})), anexar(p, False{}, incrementar(p, soma(p, at, bt, False{}))),
            incrementar(1n+p, anexar(p, True{}, soma(p, at, bt, False{}))),
            Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => anexar(p, False{}, m),
              soma(p, at, bt, True{}), incrementar(p, soma(p, at, bt, False{})), carry_inicial_e_incremento(p, at, bt)),
            Equal.sym(Maybe<&2, Word(1n+p)>, incrementar(1n+p, anexar(p, True{}, soma(p, at, bt, False{}))), anexar(p, False{}, incrementar(p, soma(p, at, bt, False{}))),
              incrementar_anexar_um(p, soma(p, at, bt, False{}))))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Equal.trans(Maybe<&2, Word(1n+p)>,
            anexar(p, False{}, soma(p, at, bt, True{})), anexar(p, False{}, incrementar(p, soma(p, at, bt, False{}))),
            incrementar(1n+p, anexar(p, True{}, soma(p, at, bt, False{}))),
            Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => anexar(p, False{}, m),
              soma(p, at, bt, True{}), incrementar(p, soma(p, at, bt, False{})), carry_inicial_e_incremento(p, at, bt)),
            Equal.sym(Maybe<&2, Word(1n+p)>, incrementar(1n+p, anexar(p, True{}, soma(p, at, bt, False{}))), anexar(p, False{}, incrementar(p, soma(p, at, bt, False{}))),
              incrementar_anexar_um(p, soma(p, at, bt, False{}))))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          Equal.sym(Maybe<&2, Word(1n+p)>, incrementar(1n+p, anexar(p, False{}, soma(p, at, bt, True{}))), anexar(p, True{}, soma(p, at, bt, True{})),
            incrementar_anexar_zero(p, soma(p, at, bt, True{})))

law incrementar_argumento_sem_overflow:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for cabe: {N.uns(n, a) == False{} : Bool}
  {soma(n, Word.inc(n, a), b, False{}) == soma(n, a, b, True{}) : Maybe<&2, Word(n)>}
def incrementar_argumento_sem_overflow(n, a, b, cabe):
  match n:
    case 0n:
      F.absurdo_booleano({soma(0n, Word.inc(0n, a), b, False{}) == soma(0n, a, b, True{}) : Maybe<&2, Word(0n)>}, Equal.sym(Bool, True{}, False{}, cabe))
    case 1n+p:
      match a b:
        case WCon{False{}, at} WCon{False{}, bt}:
          {==}
        case WCon{False{}, at} WCon{True{}, bt}:
          {==}
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => anexar(p, False{}, m),
            soma(p, Word.inc(p, at), bt, False{}), soma(p, at, bt, True{}), incrementar_argumento_sem_overflow(p, at, bt, cabe))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => anexar(p, True{}, m),
            soma(p, Word.inc(p, at), bt, False{}), soma(p, at, bt, True{}), incrementar_argumento_sem_overflow(p, at, bt, cabe))

law maximo_com_carry_transborda:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for maximo: {N.uns(n, a) == True{} : Bool}
  {soma(n, a, b, True{}) == None{} : Maybe<&2, Word(n)>}
def maximo_com_carry_transborda(n, a, b, maximo):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{False{}, at} WCon{y, bt}:
          F.absurdo_booleano({soma(1n+p, WCon{False{}, at}, WCon{y, bt}, True{}) == None{} : Maybe<&2, Word(1n+p)>}, maximo)
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => anexar(p, False{}, m),
            soma(p, at, bt, True{}), None{}, maximo_com_carry_transborda(p, at, bt, maximo))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => anexar(p, True{}, m),
            soma(p, at, bt, True{}), None{}, maximo_com_carry_transborda(p, at, bt, maximo))

def soma_incremento_casos(maximo: Bool, +n: Nat, +a: Word(n), +b: Word(n),
  e: {N.uns(n, a) == maximo : Bool}) ->
  {somar_opcionais(n, fim(n, maximo, Word.inc(n, a)), Some{b}) == incrementar(n, soma(n, a, b, False{})) : Maybe<&2, Word(n)>}:
  match maximo:
    case False{}:
      Equal.trans(Maybe<&2, Word(n)>, soma(n, Word.inc(n, a), b, False{}), soma(n, a, b, True{}), incrementar(n, soma(n, a, b, False{})),
        incrementar_argumento_sem_overflow(n, a, b, e), carry_inicial_e_incremento(n, a, b))
    case True{}:
      Equal.sym(Maybe<&2, Word(n)>, incrementar(n, soma(n, a, b, False{})), None{},
        Equal.trans(Maybe<&2, Word(n)>, incrementar(n, soma(n, a, b, False{})), soma(n, a, b, True{}), None{},
          Equal.sym(Maybe<&2, Word(n)>, soma(n, a, b, True{}), incrementar(n, soma(n, a, b, False{})), carry_inicial_e_incremento(n, a, b)),
          maximo_com_carry_transborda(n, a, b, e)))

law soma_none_direita:
  for n: Nat
  for a: Maybe<&2, Word(n)>
  {somar_opcionais(n, a, None{}) == None{} : Maybe<&2, Word(n)>}
def soma_none_direita(n, a):
  match a:
    case None{}:
      {==}
    case Some{x}:
      {==}

law soma_opcional_preserva_incremento:
  for +n: Nat
  for +a: Maybe<&2, Word(n)>
  for +b: Maybe<&2, Word(n)>
  {somar_opcionais(n, incrementar(n, a), b) == incrementar(n, somar_opcionais(n, a, b)) : Maybe<&2, Word(n)>}
def soma_opcional_preserva_incremento(n, a, b):
  match a b:
    case None{} _:
      {==}
    case Some{+x} None{}:
      soma_none_direita(n, incrementar(n, Some{x}))
    case Some{+x} Some{+y}:
      soma_incremento_casos(N.uns(n, x), n, x, y, {==})

law soma_zero:
  for +n: Nat
  for +a: Word(n)
  {soma(n, Word.zero(n), a, False{}) == Some{a} : Maybe<&2, Word(n)>}
def soma_zero(n, a):
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{False{}, +t}:
          Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => anexar(p, False{}, m),
            soma(p, Word.zero(p), t, False{}), Some{t}, soma_zero(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => anexar(p, True{}, m),
            soma(p, Word.zero(p), t, False{}), Some{t}, soma_zero(p, t))

law soma_opcional_zero:
  for +n: Nat
  for +a: Maybe<&2, Word(n)>
  {somar_opcionais(n, Some{Word.zero(n)}, a) == a : Maybe<&2, Word(n)>}
def soma_opcional_zero(n, a):
  match a:
    case None{}:
      {==}
    case Some{+w}:
      soma_zero(n, w)

# Homomorfismo TOTAL: tambem cobre operandos e resultados nao representaveis.
law soma_naturais:
  for +largura: Nat
  for +a: Nat
  for +b: Nat
  {somar_opcionais(largura, natural(largura, a), natural(largura, b)) == natural(largura, Nat.add(a, b)) : Maybe<&2, Word(largura)>}
def soma_naturais(largura, a, b):
  match a:
    case 0n:
      soma_opcional_zero(largura, natural(largura, b))
    case 1n+p:
      Equal.trans(Maybe<&2, Word(largura)>,
        somar_opcionais(largura, incrementar(largura, natural(largura, p)), natural(largura, b)),
        incrementar(largura, somar_opcionais(largura, natural(largura, p), natural(largura, b))),
        incrementar(largura, natural(largura, Nat.add(p, b))),
        soma_opcional_preserva_incremento(largura, natural(largura, p), natural(largura, b)),
        Equal.cong(Maybe<&2, Word(largura)>, Maybe<&2, Word(largura)>, m => incrementar(largura, m),
          somar_opcionais(largura, natural(largura, p), natural(largura, b)), natural(largura, Nat.add(p, b)), soma_naturais(largura, p, b)))

# O carry de a+b e exatamente a queda modular abaixo de a.
# Com carry de entrada, a igualdade com a tambem sinaliza overflow.
def teste(c: Bool, ordem: Cmp) -> Bool:
  match c:
    case False{}:
      Cmp.is_lt(ordem)
    case True{}:
      Cmp.is_le(ordem)

def primeiro(par: Bool & Bool) -> Bool:
  (s, k) = par
  s

def segundo(par: Bool & Bool) -> Bool:
  (s, k) = par
  k

def bit_soma(a: Bool, b: Bool, c: Bool) -> Bool:
  primeiro(Bool.full_add(a, b, c))

def bit_carry(a: Bool, b: Bool, c: Bool) -> Bool:
  segundo(Bool.full_add(a, b, c))

law teste_bit:
  for a: Bool
  for b: Bool
  for c: Bool
  for t: Cmp
  {teste(c, Word.cmp.fin(bit_soma(a, b, c), a, t)) == teste(bit_carry(a, b, c), t) : Bool}
def teste_bit(a, b, c, t):
  match a b c t:
    case False{} False{} False{} LT{}:
      {==}
    case False{} False{} False{} EQ{}:
      {==}
    case False{} False{} False{} GT{}:
      {==}
    case False{} False{} True{} LT{}:
      {==}
    case False{} False{} True{} EQ{}:
      {==}
    case False{} False{} True{} GT{}:
      {==}
    case False{} True{} False{} LT{}:
      {==}
    case False{} True{} False{} EQ{}:
      {==}
    case False{} True{} False{} GT{}:
      {==}
    case False{} True{} True{} LT{}:
      {==}
    case False{} True{} True{} EQ{}:
      {==}
    case False{} True{} True{} GT{}:
      {==}
    case True{} False{} False{} LT{}:
      {==}
    case True{} False{} False{} EQ{}:
      {==}
    case True{} False{} False{} GT{}:
      {==}
    case True{} False{} True{} LT{}:
      {==}
    case True{} False{} True{} EQ{}:
      {==}
    case True{} False{} True{} GT{}:
      {==}
    case True{} True{} False{} LT{}:
      {==}
    case True{} True{} False{} EQ{}:
      {==}
    case True{} True{} False{} GT{}:
      {==}
    case True{} True{} True{} LT{}:
      {==}
    case True{} True{} True{} EQ{}:
      {==}
    case True{} True{} True{} GT{}:
      {==}

law carry_equivale_comparacao:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Bool
  {carry(n, a, b, c) == teste(c, Word.cmp(n, Word.adc(n, a, b, False{}, c), a)) : Bool}
def carry_equivale_comparacao(n, a, b, c):
  match n:
    case 0n:
      match c:
        case False{}:
          {==}
        case True{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          Equal.trans(Bool, carry(p, at, bt, False{}),
            teste(False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at)),
            teste(False{}, Word.cmp.fin(False{}, False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at))),
            carry_equivale_comparacao(p, at, bt, False{}),
            Equal.sym(Bool,
              teste(False{}, Word.cmp.fin(False{}, False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at))),
              teste(False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at)),
              teste_bit(False{}, False{}, False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at))))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          Equal.trans(Bool, carry(p, at, bt, False{}),
            teste(False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at)),
            teste(True{}, Word.cmp.fin(True{}, False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at))),
            carry_equivale_comparacao(p, at, bt, False{}),
            Equal.sym(Bool,
              teste(True{}, Word.cmp.fin(True{}, False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at))),
              teste(False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at)),
              teste_bit(False{}, False{}, True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at))))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          Equal.trans(Bool, carry(p, at, bt, False{}),
            teste(False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at)),
            teste(False{}, Word.cmp.fin(True{}, False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at))),
            carry_equivale_comparacao(p, at, bt, False{}),
            Equal.sym(Bool,
              teste(False{}, Word.cmp.fin(True{}, False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at))),
              teste(False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at)),
              teste_bit(False{}, True{}, False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at))))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          Equal.trans(Bool, carry(p, at, bt, True{}),
            teste(True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at)),
            teste(True{}, Word.cmp.fin(False{}, False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at))),
            carry_equivale_comparacao(p, at, bt, True{}),
            Equal.sym(Bool,
              teste(True{}, Word.cmp.fin(False{}, False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at))),
              teste(True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at)),
              teste_bit(False{}, True{}, True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at))))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          Equal.trans(Bool, carry(p, at, bt, False{}),
            teste(False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at)),
            teste(False{}, Word.cmp.fin(True{}, True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at))),
            carry_equivale_comparacao(p, at, bt, False{}),
            Equal.sym(Bool,
              teste(False{}, Word.cmp.fin(True{}, True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at))),
              teste(False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at)),
              teste_bit(True{}, False{}, False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at))))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          Equal.trans(Bool, carry(p, at, bt, True{}),
            teste(True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at)),
            teste(True{}, Word.cmp.fin(False{}, True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at))),
            carry_equivale_comparacao(p, at, bt, True{}),
            Equal.sym(Bool,
              teste(True{}, Word.cmp.fin(False{}, True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at))),
              teste(True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at)),
              teste_bit(True{}, False{}, True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at))))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          Equal.trans(Bool, carry(p, at, bt, True{}),
            teste(True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at)),
            teste(False{}, Word.cmp.fin(False{}, True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at))),
            carry_equivale_comparacao(p, at, bt, True{}),
            Equal.sym(Bool,
              teste(False{}, Word.cmp.fin(False{}, True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at))),
              teste(True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at)),
              teste_bit(True{}, True{}, False{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at))))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          Equal.trans(Bool, carry(p, at, bt, True{}),
            teste(True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at)),
            teste(True{}, Word.cmp.fin(True{}, True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at))),
            carry_equivale_comparacao(p, at, bt, True{}),
            Equal.sym(Bool,
              teste(True{}, Word.cmp.fin(True{}, True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at))),
              teste(True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at)),
              teste_bit(True{}, True{}, True{}, Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at))))

def juntar_opcional(+k: Nat, -n: Nat, lo: Word(k), m: Maybe<&2, Word(n)>) -> Maybe<&2, Word(Nat.add(k, n))>:
  match m:
    case None{}:
      None{}
    case Some{hi}:
      Some{W.juntar(k, n, lo, hi)}

law juntar_opcional_zero:
  for n: Nat
  for lo: Word(0n)
  for m: Maybe<&2, Word(n)>
  {juntar_opcional(0n, n, lo, m) == m : Maybe<&2, Word(n)>}
def juntar_opcional_zero(n, lo, m):
  match m:
    case None{}:
      {==}
    case Some{hi}:
      {==}

law anexar_juntar:
  for +k: Nat
  for n: Nat
  for +b: Bool
  for +lo: Word(k)
  for +m: Maybe<&2, Word(n)>
  {anexar(Nat.add(k, n), b, juntar_opcional(k, n, lo, m)) == juntar_opcional(1n+k, n, WCon{b, lo}, m) : Maybe<&2, Word(1n+Nat.add(k, n))>}
def anexar_juntar(k, n, b, lo, m):
  match m:
    case None{}:
      {==}
    case Some{hi}:
      {==}

law soma_blocos:
  for +k: Nat
  for +n: Nat
  for +al: Word(k)
  for +bl: Word(k)
  for +ah: Word(n)
  for +bh: Word(n)
  for +c: Bool
  {soma(Nat.add(k, n), W.juntar(k, n, al, ah), W.juntar(k, n, bl, bh), c) ==
    juntar_opcional(k, n, Word.adc(k, al, bl, False{}, c), soma(n, ah, bh, carry(k, al, bl, c))) : Maybe<&2, Word(Nat.add(k, n))>}
def soma_blocos(k, n, al, bl, ah, bh, c):
  match k:
    case 0n:
      Equal.sym(Maybe<&2, Word(n)>, juntar_opcional(0n, n, WNil{}, soma(n, ah, bh, c)), soma(n, ah, bh, c),
        juntar_opcional_zero(n, WNil{}, soma(n, ah, bh, c)))
    case 1n+p:
      match al bl c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          Equal.trans(Maybe<&2, Word(1n+Nat.add(p, n))>,
            anexar(Nat.add(p, n), False{}, soma(Nat.add(p, n), W.juntar(p, n, at, ah), W.juntar(p, n, bt, bh), False{})),
            anexar(Nat.add(p, n), False{}, juntar_opcional(p, n, Word.adc(p, at, bt, False{}, False{}), soma(n, ah, bh, carry(p, at, bt, False{})))),
            juntar_opcional(1n+p, n, WCon{False{}, Word.adc(p, at, bt, False{}, False{})}, soma(n, ah, bh, carry(p, at, bt, False{}))),
            Equal.cong(Maybe<&2, Word(Nat.add(p, n))>, Maybe<&2, Word(1n+Nat.add(p, n))>, m => anexar(Nat.add(p, n), False{}, m),
              soma(Nat.add(p, n), W.juntar(p, n, at, ah), W.juntar(p, n, bt, bh), False{}),
              juntar_opcional(p, n, Word.adc(p, at, bt, False{}, False{}), soma(n, ah, bh, carry(p, at, bt, False{}))),
              soma_blocos(p, n, at, bt, ah, bh, False{})),
            anexar_juntar(p, n, False{}, Word.adc(p, at, bt, False{}, False{}), soma(n, ah, bh, carry(p, at, bt, False{}))))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          Equal.trans(Maybe<&2, Word(1n+Nat.add(p, n))>,
            anexar(Nat.add(p, n), True{}, soma(Nat.add(p, n), W.juntar(p, n, at, ah), W.juntar(p, n, bt, bh), False{})),
            anexar(Nat.add(p, n), True{}, juntar_opcional(p, n, Word.adc(p, at, bt, False{}, False{}), soma(n, ah, bh, carry(p, at, bt, False{})))),
            juntar_opcional(1n+p, n, WCon{True{}, Word.adc(p, at, bt, False{}, False{})}, soma(n, ah, bh, carry(p, at, bt, False{}))),
            Equal.cong(Maybe<&2, Word(Nat.add(p, n))>, Maybe<&2, Word(1n+Nat.add(p, n))>, m => anexar(Nat.add(p, n), True{}, m),
              soma(Nat.add(p, n), W.juntar(p, n, at, ah), W.juntar(p, n, bt, bh), False{}),
              juntar_opcional(p, n, Word.adc(p, at, bt, False{}, False{}), soma(n, ah, bh, carry(p, at, bt, False{}))),
              soma_blocos(p, n, at, bt, ah, bh, False{})),
            anexar_juntar(p, n, True{}, Word.adc(p, at, bt, False{}, False{}), soma(n, ah, bh, carry(p, at, bt, False{}))))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          Equal.trans(Maybe<&2, Word(1n+Nat.add(p, n))>,
            anexar(Nat.add(p, n), True{}, soma(Nat.add(p, n), W.juntar(p, n, at, ah), W.juntar(p, n, bt, bh), False{})),
            anexar(Nat.add(p, n), True{}, juntar_opcional(p, n, Word.adc(p, at, bt, False{}, False{}), soma(n, ah, bh, carry(p, at, bt, False{})))),
            juntar_opcional(1n+p, n, WCon{True{}, Word.adc(p, at, bt, False{}, False{})}, soma(n, ah, bh, carry(p, at, bt, False{}))),
            Equal.cong(Maybe<&2, Word(Nat.add(p, n))>, Maybe<&2, Word(1n+Nat.add(p, n))>, m => anexar(Nat.add(p, n), True{}, m),
              soma(Nat.add(p, n), W.juntar(p, n, at, ah), W.juntar(p, n, bt, bh), False{}),
              juntar_opcional(p, n, Word.adc(p, at, bt, False{}, False{}), soma(n, ah, bh, carry(p, at, bt, False{}))),
              soma_blocos(p, n, at, bt, ah, bh, False{})),
            anexar_juntar(p, n, True{}, Word.adc(p, at, bt, False{}, False{}), soma(n, ah, bh, carry(p, at, bt, False{}))))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          Equal.trans(Maybe<&2, Word(1n+Nat.add(p, n))>,
            anexar(Nat.add(p, n), False{}, soma(Nat.add(p, n), W.juntar(p, n, at, ah), W.juntar(p, n, bt, bh), True{})),
            anexar(Nat.add(p, n), False{}, juntar_opcional(p, n, Word.adc(p, at, bt, False{}, True{}), soma(n, ah, bh, carry(p, at, bt, True{})))),
            juntar_opcional(1n+p, n, WCon{False{}, Word.adc(p, at, bt, False{}, True{})}, soma(n, ah, bh, carry(p, at, bt, True{}))),
            Equal.cong(Maybe<&2, Word(Nat.add(p, n))>, Maybe<&2, Word(1n+Nat.add(p, n))>, m => anexar(Nat.add(p, n), False{}, m),
              soma(Nat.add(p, n), W.juntar(p, n, at, ah), W.juntar(p, n, bt, bh), True{}),
              juntar_opcional(p, n, Word.adc(p, at, bt, False{}, True{}), soma(n, ah, bh, carry(p, at, bt, True{}))),
              soma_blocos(p, n, at, bt, ah, bh, True{})),
            anexar_juntar(p, n, False{}, Word.adc(p, at, bt, False{}, True{}), soma(n, ah, bh, carry(p, at, bt, True{}))))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          Equal.trans(Maybe<&2, Word(1n+Nat.add(p, n))>,
            anexar(Nat.add(p, n), True{}, soma(Nat.add(p, n), W.juntar(p, n, at, ah), W.juntar(p, n, bt, bh), False{})),
            anexar(Nat.add(p, n), True{}, juntar_opcional(p, n, Word.adc(p, at, bt, False{}, False{}), soma(n, ah, bh, carry(p, at, bt, False{})))),
            juntar_opcional(1n+p, n, WCon{True{}, Word.adc(p, at, bt, False{}, False{})}, soma(n, ah, bh, carry(p, at, bt, False{}))),
            Equal.cong(Maybe<&2, Word(Nat.add(p, n))>, Maybe<&2, Word(1n+Nat.add(p, n))>, m => anexar(Nat.add(p, n), True{}, m),
              soma(Nat.add(p, n), W.juntar(p, n, at, ah), W.juntar(p, n, bt, bh), False{}),
              juntar_opcional(p, n, Word.adc(p, at, bt, False{}, False{}), soma(n, ah, bh, carry(p, at, bt, False{}))),
              soma_blocos(p, n, at, bt, ah, bh, False{})),
            anexar_juntar(p, n, True{}, Word.adc(p, at, bt, False{}, False{}), soma(n, ah, bh, carry(p, at, bt, False{}))))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          Equal.trans(Maybe<&2, Word(1n+Nat.add(p, n))>,
            anexar(Nat.add(p, n), False{}, soma(Nat.add(p, n), W.juntar(p, n, at, ah), W.juntar(p, n, bt, bh), True{})),
            anexar(Nat.add(p, n), False{}, juntar_opcional(p, n, Word.adc(p, at, bt, False{}, True{}), soma(n, ah, bh, carry(p, at, bt, True{})))),
            juntar_opcional(1n+p, n, WCon{False{}, Word.adc(p, at, bt, False{}, True{})}, soma(n, ah, bh, carry(p, at, bt, True{}))),
            Equal.cong(Maybe<&2, Word(Nat.add(p, n))>, Maybe<&2, Word(1n+Nat.add(p, n))>, m => anexar(Nat.add(p, n), False{}, m),
              soma(Nat.add(p, n), W.juntar(p, n, at, ah), W.juntar(p, n, bt, bh), True{}),
              juntar_opcional(p, n, Word.adc(p, at, bt, False{}, True{}), soma(n, ah, bh, carry(p, at, bt, True{}))),
              soma_blocos(p, n, at, bt, ah, bh, True{})),
            anexar_juntar(p, n, False{}, Word.adc(p, at, bt, False{}, True{}), soma(n, ah, bh, carry(p, at, bt, True{}))))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          Equal.trans(Maybe<&2, Word(1n+Nat.add(p, n))>,
            anexar(Nat.add(p, n), False{}, soma(Nat.add(p, n), W.juntar(p, n, at, ah), W.juntar(p, n, bt, bh), True{})),
            anexar(Nat.add(p, n), False{}, juntar_opcional(p, n, Word.adc(p, at, bt, False{}, True{}), soma(n, ah, bh, carry(p, at, bt, True{})))),
            juntar_opcional(1n+p, n, WCon{False{}, Word.adc(p, at, bt, False{}, True{})}, soma(n, ah, bh, carry(p, at, bt, True{}))),
            Equal.cong(Maybe<&2, Word(Nat.add(p, n))>, Maybe<&2, Word(1n+Nat.add(p, n))>, m => anexar(Nat.add(p, n), False{}, m),
              soma(Nat.add(p, n), W.juntar(p, n, at, ah), W.juntar(p, n, bt, bh), True{}),
              juntar_opcional(p, n, Word.adc(p, at, bt, False{}, True{}), soma(n, ah, bh, carry(p, at, bt, True{}))),
              soma_blocos(p, n, at, bt, ah, bh, True{})),
            anexar_juntar(p, n, False{}, Word.adc(p, at, bt, False{}, True{}), soma(n, ah, bh, carry(p, at, bt, True{}))))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          Equal.trans(Maybe<&2, Word(1n+Nat.add(p, n))>,
            anexar(Nat.add(p, n), True{}, soma(Nat.add(p, n), W.juntar(p, n, at, ah), W.juntar(p, n, bt, bh), True{})),
            anexar(Nat.add(p, n), True{}, juntar_opcional(p, n, Word.adc(p, at, bt, False{}, True{}), soma(n, ah, bh, carry(p, at, bt, True{})))),
            juntar_opcional(1n+p, n, WCon{True{}, Word.adc(p, at, bt, False{}, True{})}, soma(n, ah, bh, carry(p, at, bt, True{}))),
            Equal.cong(Maybe<&2, Word(Nat.add(p, n))>, Maybe<&2, Word(1n+Nat.add(p, n))>, m => anexar(Nat.add(p, n), True{}, m),
              soma(Nat.add(p, n), W.juntar(p, n, at, ah), W.juntar(p, n, bt, bh), True{}),
              juntar_opcional(p, n, Word.adc(p, at, bt, False{}, True{}), soma(n, ah, bh, carry(p, at, bt, True{}))),
              soma_blocos(p, n, at, bt, ah, bh, True{})),
            anexar_juntar(p, n, True{}, Word.adc(p, at, bt, False{}, True{}), soma(n, ah, bh, carry(p, at, bt, True{}))))

law soma_zero_direita:
  for +n: Nat
  for +a: Word(n)
  {soma(n, a, Word.zero(n), False{}) == Some{a} : Maybe<&2, Word(n)>}
def soma_zero_direita(n, a):
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{False{}, +t}:
          Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => anexar(p, False{}, m),
            soma(p, t, Word.zero(p), False{}), Some{t}, soma_zero_direita(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => anexar(p, True{}, m),
            soma(p, t, Word.zero(p), False{}), Some{t}, soma_zero_direita(p, t))

law soma_incremento:
  for +n: Nat
  for +a: Word(n)
  {soma(n, a, Word.zero(n), True{}) == incrementar(n, Some{a}) : Maybe<&2, Word(n)>}
def soma_incremento(n, a):
  Equal.trans(Maybe<&2, Word(n)>, soma(n, a, Word.zero(n), True{}), incrementar(n, soma(n, a, Word.zero(n), False{})), incrementar(n, Some{a}),
    carry_inicial_e_incremento(n, a, Word.zero(n)),
    Equal.cong(Maybe<&2, Word(n)>, Maybe<&2, Word(n)>, m => incrementar(n, m), soma(n, a, Word.zero(n), False{}), Some{a}, soma_zero_direita(n, a)))

law carry_zero:
  for +n: Nat
  for +a: Word(n)
  {carry(n, a, Word.zero(n), False{}) == False{} : Bool}
def carry_zero(n, a):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a:
        case WCon{False{}, t}:
          carry_zero(p, t)
        case WCon{True{}, t}:
          carry_zero(p, t)

law carry_incremento:
  for +n: Nat
  for +a: Word(n)
  {carry(n, a, Word.zero(n), True{}) == N.uns(n, a) : Bool}
def carry_incremento(n, a):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a:
        case WCon{False{}, t}:
          carry_zero(p, t)
        case WCon{True{}, t}:
          carry_incremento(p, t)

law incremento_maximo_zero:
  for +n: Nat
  for +a: Word(n)
  for maximo: {N.uns(n, a) == True{} : Bool}
  {Word.inc(n, a) == Word.zero(n) : Word(n)}
def incremento_maximo_zero(n, a, maximo):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a:
        case WCon{False{}, t}:
          F.absurdo_booleano({Word.inc(1n+p, WCon{False{}, t}) == Word.zero(1n+p) : Word(1n+p)}, maximo)
        case WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.inc(p, t), Word.zero(p), incremento_maximo_zero(p, t, maximo))
