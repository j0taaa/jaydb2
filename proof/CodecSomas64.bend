# Ponte entre a soma binaria verificada e as funcoes reais do codec.
import Base
import ../contrato/Bytes.bend as B
import ../src/Codec.bend as C
import ./CodecContadores.bend as N
import ./CodecPalavrasWord.bend as W
import ./CodecSomasBits.bend as S

def bits(q: B.Numero64) -> Word(64n):
  B.Numero64{U32{hi}, U32{lo}} = q
  W.juntar(32n, 32n, lo, hi)

def representar(m: Maybe<&2, B.Numero64>) -> Maybe<&2, Word(64n)>:
  match m:
    case None{}:
      None{}
    case Some{q}:
      Some{bits(q)}

def aplicar_carry(+n: Nat, c: Bool, m: Maybe<&2, Word(n)>) -> Maybe<&2, Word(n)>:
  match c:
    case False{}:
      m
    case True{}:
      S.incrementar(n, m)

law incrementar_fim:
  for +n: Nat
  for +overflow: Bool
  for +w: Word(n)
  {S.incrementar(n, S.fim(n, overflow, w)) == S.fim(n, overflow || N.uns(n, w), Word.inc(n, w)) : Maybe<&2, Word(n)>}
def incrementar_fim(n, overflow, w):
  match overflow:
    case False{}:
      {==}
    case True{}:
      {==}

law representar_soma_fim:
  for +overflow: Bool
  for +hi: Word(32n)
  for +lo: Word(32n)
  {representar(C.soma64_fim(overflow, U32{hi}, U32{lo})) == S.juntar_opcional(32n, 32n, lo, S.fim(32n, overflow, hi)) : Maybe<&2, Word(64n)>}
def representar_soma_fim(overflow, hi, lo):
  match overflow:
    case False{}:
      {==}
    case True{}:
      {==}

law representar_soma_transporte:
  for +c: Bool
  for +overflow: Bool
  for +hi: Word(32n)
  for +lo: Word(32n)
  {representar(C.soma64_transporte(c, U32{hi}, U32{lo}, overflow)) ==
    S.juntar_opcional(32n, 32n, lo, aplicar_carry(32n, c, S.fim(32n, overflow, hi))) : Maybe<&2, Word(64n)>}
def representar_soma_transporte(c, overflow, hi, lo):
  match c:
    case False{}:
      representar_soma_fim(overflow, hi, lo)
    case True{}:
      %Equal.sym(Word(32n), Word.add(32n, hi, N.um(31n)), Word.inc(32n, hi), N.somar_um_incrementa(31n, hi)) :
        {representar(C.soma64_fim(overflow || Cmp.is_eq(Word.cmp(32n, hi, N.maximo(32n))), U32{_}, U32{lo})) ==
          S.juntar_opcional(32n, 32n, lo, S.incrementar(32n, S.fim(32n, overflow, hi))) : Maybe<&2, Word(64n)>}
      %Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, hi, N.maximo(32n))), N.uns(32n, hi), N.comparacao_maximo_reconhece_bits(32n, hi)) :
        {representar(C.soma64_fim(overflow || _, U32{Word.inc(32n, hi)}, U32{lo})) ==
          S.juntar_opcional(32n, 32n, lo, S.incrementar(32n, S.fim(32n, overflow, hi))) : Maybe<&2, Word(64n)>}
      Equal.trans(Maybe<&2, Word(64n)>,
        representar(C.soma64_fim(overflow || N.uns(32n, hi), U32{Word.inc(32n, hi)}, U32{lo})),
        S.juntar_opcional(32n, 32n, lo, S.fim(32n, overflow || N.uns(32n, hi), Word.inc(32n, hi))),
        S.juntar_opcional(32n, 32n, lo, S.incrementar(32n, S.fim(32n, overflow, hi))),
        representar_soma_fim(overflow || N.uns(32n, hi), Word.inc(32n, hi), lo),
        Equal.cong(Maybe<&2, Word(32n)>, Maybe<&2, Word(64n)>, m => S.juntar_opcional(32n, 32n, lo, m),
          S.fim(32n, overflow || N.uns(32n, hi), Word.inc(32n, hi)), S.incrementar(32n, S.fim(32n, overflow, hi)),
          Equal.sym(Maybe<&2, Word(32n)>, S.incrementar(32n, S.fim(32n, overflow, hi)), S.fim(32n, overflow || N.uns(32n, hi), Word.inc(32n, hi)), incrementar_fim(32n, overflow, hi))))

law aplicar_carry_soma:
  for +n: Nat
  for +c: Bool
  for +a: Word(n)
  for +b: Word(n)
  {aplicar_carry(n, c, S.fim(n, S.carry(n, a, b, False{}), Word.add(n, a, b))) == S.soma(n, a, b, c) : Maybe<&2, Word(n)>}
def aplicar_carry_soma(n, c, a, b):
  match c:
    case False{}:
      Equal.sym(Maybe<&2, Word(n)>, S.soma(n, a, b, False{}), S.fim(n, S.carry(n, a, b, False{}), Word.add(n, a, b)), S.soma_exata(n, a, b, False{}))
    case True{}:
      Equal.trans(Maybe<&2, Word(n)>,
        S.incrementar(n, S.fim(n, S.carry(n, a, b, False{}), Word.add(n, a, b))),
        S.incrementar(n, S.soma(n, a, b, False{})), S.soma(n, a, b, True{}),
        Equal.cong(Maybe<&2, Word(n)>, Maybe<&2, Word(n)>, m => S.incrementar(n, m),
          S.fim(n, S.carry(n, a, b, False{}), Word.add(n, a, b)), S.soma(n, a, b, False{}),
          Equal.sym(Maybe<&2, Word(n)>, S.soma(n, a, b, False{}), S.fim(n, S.carry(n, a, b, False{}), Word.add(n, a, b)), S.soma_exata(n, a, b, False{}))),
        Equal.sym(Maybe<&2, Word(n)>, S.soma(n, a, b, True{}), S.incrementar(n, S.soma(n, a, b, False{})), S.carry_inicial_e_incremento(n, a, b)))

# Igualdade estrutural para TODOS os pares de Numero64; nao recebe
# nenhuma premissa sobre o resultado da soma.
law somar64_representa_soma_binaria:
  for +a: B.Numero64
  for +b: B.Numero64
  {representar(C.somar64(a, b)) == S.soma(64n, bits(a), bits(b), False{}) : Maybe<&2, Word(64n)>}
def somar64_representa_soma_binaria(a, b):
  match a b:
    case B.Numero64{U32{+ah}, U32{+al}} B.Numero64{U32{+bh}, U32{+bl}}:
      %S.carry_equivale_comparacao(32n, al, bl, False{}) :
        {representar(C.soma64_transporte(_, U32{Word.add(32n, ah, bh)}, U32{Word.add(32n, al, bl)}, Cmp.is_lt(Word.cmp(32n, Word.add(32n, ah, bh), ah)))) ==
          S.soma(64n, W.juntar(32n, 32n, al, ah), W.juntar(32n, 32n, bl, bh), False{}) : Maybe<&2, Word(64n)>}
      %S.carry_equivale_comparacao(32n, ah, bh, False{}) :
        {representar(C.soma64_transporte(S.carry(32n, al, bl, False{}), U32{Word.add(32n, ah, bh)}, U32{Word.add(32n, al, bl)}, _)) ==
          S.soma(64n, W.juntar(32n, 32n, al, ah), W.juntar(32n, 32n, bl, bh), False{}) : Maybe<&2, Word(64n)>}
      Equal.trans(Maybe<&2, Word(64n)>,
        representar(C.soma64_transporte(S.carry(32n, al, bl, False{}), U32{Word.add(32n, ah, bh)}, U32{Word.add(32n, al, bl)}, S.carry(32n, ah, bh, False{}))),
        S.juntar_opcional(32n, 32n, Word.add(32n, al, bl), aplicar_carry(32n, S.carry(32n, al, bl, False{}), S.fim(32n, S.carry(32n, ah, bh, False{}), Word.add(32n, ah, bh)))),
        S.soma(64n, W.juntar(32n, 32n, al, ah), W.juntar(32n, 32n, bl, bh), False{}),
        representar_soma_transporte(S.carry(32n, al, bl, False{}), S.carry(32n, ah, bh, False{}), Word.add(32n, ah, bh), Word.add(32n, al, bl)),
        Equal.trans(Maybe<&2, Word(64n)>,
          S.juntar_opcional(32n, 32n, Word.add(32n, al, bl), aplicar_carry(32n, S.carry(32n, al, bl, False{}), S.fim(32n, S.carry(32n, ah, bh, False{}), Word.add(32n, ah, bh)))),
          S.juntar_opcional(32n, 32n, Word.add(32n, al, bl), S.soma(32n, ah, bh, S.carry(32n, al, bl, False{}))),
          S.soma(64n, W.juntar(32n, 32n, al, ah), W.juntar(32n, 32n, bl, bh), False{}),
          Equal.cong(Maybe<&2, Word(32n)>, Maybe<&2, Word(64n)>, m => S.juntar_opcional(32n, 32n, Word.add(32n, al, bl), m),
            aplicar_carry(32n, S.carry(32n, al, bl, False{}), S.fim(32n, S.carry(32n, ah, bh, False{}), Word.add(32n, ah, bh))),
            S.soma(32n, ah, bh, S.carry(32n, al, bl, False{})), aplicar_carry_soma(32n, S.carry(32n, al, bl, False{}), ah, bh)),
          Equal.sym(Maybe<&2, Word(64n)>, S.soma(64n, W.juntar(32n, 32n, al, ah), W.juntar(32n, 32n, bl, bh), False{}),
            S.juntar_opcional(32n, 32n, Word.add(32n, al, bl), S.soma(32n, ah, bh, S.carry(32n, al, bl, False{}))), S.soma_blocos(32n, 32n, al, bl, ah, bh, False{}))))

law somar_opcionais_representa_soma_binaria:
  for +a: Maybe<&2, B.Numero64>
  for +b: Maybe<&2, B.Numero64>
  {representar(C.somar_opcionais(a, b)) == S.somar_opcionais(64n, representar(a), representar(b)) : Maybe<&2, Word(64n)>}
def somar_opcionais_representa_soma_binaria(a, b):
  match a b:
    case None{} _:
      {==}
    case Some{x} None{}:
      {==}
    case Some{+x} Some{+y}:
      somar64_representa_soma_binaria(x, y)

law juntar_zeros:
  for +k: Nat
  for +n: Nat
  {W.juntar(k, n, Word.zero(k), Word.zero(n)) == Word.zero(Nat.add(k, n)) : Word(Nat.add(k, n))}
def juntar_zeros(k, n):
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), w => WCon{False{}, w},
        W.juntar(p, n, Word.zero(p), Word.zero(n)), Word.zero(Nat.add(p, n)), juntar_zeros(p, n))

law soma_carry_zero:
  for +n: Nat
  for +c: Bool
  for +a: Word(n)
  {S.soma(n, a, Word.zero(n), c) == aplicar_carry(n, c, Some{a}) : Maybe<&2, Word(n)>}
def soma_carry_zero(n, c, a):
  match c:
    case False{}:
      S.soma_zero_direita(n, a)
    case True{}:
      S.soma_incremento(n, a)

law soma_incremento_blocos:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  {S.soma(Nat.add(k, n), W.juntar(k, n, lo, hi), Word.zero(Nat.add(k, n)), True{}) ==
    S.juntar_opcional(k, n, Word.inc(k, lo), aplicar_carry(n, N.uns(k, lo), Some{hi})) : Maybe<&2, Word(Nat.add(k, n))>}
def soma_incremento_blocos(k, n, lo, hi):
  %juntar_zeros(k, n) :
    {S.soma(Nat.add(k, n), W.juntar(k, n, lo, hi), _, True{}) ==
      S.juntar_opcional(k, n, Word.inc(k, lo), aplicar_carry(n, N.uns(k, lo), Some{hi})) : Maybe<&2, Word(Nat.add(k, n))>}
  %N.adc_zero_incrementa(k, lo) :
    {S.soma(Nat.add(k, n), W.juntar(k, n, lo, hi), W.juntar(k, n, Word.zero(k), Word.zero(n)), True{}) ==
      S.juntar_opcional(k, n, _, aplicar_carry(n, N.uns(k, lo), Some{hi})) : Maybe<&2, Word(Nat.add(k, n))>}
  %S.carry_incremento(k, lo) :
    {S.soma(Nat.add(k, n), W.juntar(k, n, lo, hi), W.juntar(k, n, Word.zero(k), Word.zero(n)), True{}) ==
      S.juntar_opcional(k, n, Word.adc(k, lo, Word.zero(k), False{}, True{}), aplicar_carry(n, _, Some{hi})) : Maybe<&2, Word(Nat.add(k, n))>}
  Equal.trans(Maybe<&2, Word(Nat.add(k, n))>,
    S.soma(Nat.add(k, n), W.juntar(k, n, lo, hi), W.juntar(k, n, Word.zero(k), Word.zero(n)), True{}),
    S.juntar_opcional(k, n, Word.adc(k, lo, Word.zero(k), False{}, True{}), S.soma(n, hi, Word.zero(n), S.carry(k, lo, Word.zero(k), True{}))),
    S.juntar_opcional(k, n, Word.adc(k, lo, Word.zero(k), False{}, True{}), aplicar_carry(n, S.carry(k, lo, Word.zero(k), True{}), Some{hi})),
    S.soma_blocos(k, n, lo, Word.zero(k), hi, Word.zero(n), True{}),
    Equal.cong(Maybe<&2, Word(n)>, Maybe<&2, Word(Nat.add(k, n))>, m => S.juntar_opcional(k, n, Word.adc(k, lo, Word.zero(k), False{}, True{}), m),
      S.soma(n, hi, Word.zero(n), S.carry(k, lo, Word.zero(k), True{})), aplicar_carry(n, S.carry(k, lo, Word.zero(k), True{}), Some{hi}),
      soma_carry_zero(n, S.carry(k, lo, Word.zero(k), True{}), hi)))

law incrementar_blocos:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  {S.incrementar(Nat.add(k, n), Some{W.juntar(k, n, lo, hi)}) ==
    S.juntar_opcional(k, n, Word.inc(k, lo), aplicar_carry(n, N.uns(k, lo), Some{hi})) : Maybe<&2, Word(Nat.add(k, n))>}
def incrementar_blocos(k, n, lo, hi):
  Equal.trans(Maybe<&2, Word(Nat.add(k, n))>,
    S.incrementar(Nat.add(k, n), Some{W.juntar(k, n, lo, hi)}),
    S.soma(Nat.add(k, n), W.juntar(k, n, lo, hi), Word.zero(Nat.add(k, n)), True{}),
    S.juntar_opcional(k, n, Word.inc(k, lo), aplicar_carry(n, N.uns(k, lo), Some{hi})),
    Equal.sym(Maybe<&2, Word(Nat.add(k, n))>,
      S.soma(Nat.add(k, n), W.juntar(k, n, lo, hi), Word.zero(Nat.add(k, n)), True{}),
      S.incrementar(Nat.add(k, n), Some{W.juntar(k, n, lo, hi)}), S.soma_incremento(Nat.add(k, n), W.juntar(k, n, lo, hi))),
    soma_incremento_blocos(k, n, lo, hi))

def representar_incremento_casos(transporte: Bool, esgotado: Bool, +hi: Word(32n), +lo: Word(32n),
  elo: {N.uns(32n, lo) == transporte : Bool},
  ehi: {N.uns(32n, hi) == esgotado : Bool}) ->
  {representar(B.incrementar64_casos(U32{hi}, U32{lo}, transporte, esgotado)) ==
    S.juntar_opcional(32n, 32n, Word.inc(32n, lo), aplicar_carry(32n, transporte, Some{hi})) : Maybe<&2, Word(64n)>}:
  match transporte esgotado:
    case False{} _:
      Equal.cong(Word(32n), Maybe<&2, Word(64n)>, w => Some{W.juntar(32n, 32n, w, hi)},
        Word.add(32n, lo, N.um(31n)), Word.inc(32n, lo), N.somar_um_incrementa(31n, lo))
    case True{} False{}:
      %Equal.sym(Bool, N.uns(32n, hi), False{}, ehi) :
        {Some{W.juntar(32n, 32n, Word.zero(32n), Word.add(32n, hi, N.um(31n)))} ==
          S.juntar_opcional(32n, 32n, Word.inc(32n, lo), S.fim(32n, _, Word.inc(32n, hi))) : Maybe<&2, Word(64n)>}
      %S.incremento_maximo_zero(32n, lo, elo) :
        {Some{W.juntar(32n, 32n, _, Word.add(32n, hi, N.um(31n)))} ==
          Some{W.juntar(32n, 32n, Word.inc(32n, lo), Word.inc(32n, hi))} : Maybe<&2, Word(64n)>}
      Equal.cong(Word(32n), Maybe<&2, Word(64n)>, w => Some{W.juntar(32n, 32n, Word.inc(32n, lo), w)},
        Word.add(32n, hi, N.um(31n)), Word.inc(32n, hi), N.somar_um_incrementa(31n, hi))
    case True{} True{}:
      %Equal.sym(Bool, N.uns(32n, hi), True{}, ehi) :
        {None{} == S.juntar_opcional(32n, 32n, Word.inc(32n, lo), S.fim(32n, _, Word.inc(32n, hi))) : Maybe<&2, Word(64n)>}
      {==}

law incrementar64_representa_incremento_binario:
  for +m: Maybe<&2, B.Numero64>
  {representar(B.incrementar64(m)) == S.incrementar(64n, representar(m)) : Maybe<&2, Word(64n)>}
def incrementar64_representa_incremento_binario(m):
  match m:
    case None{}:
      {==}
    case Some{B.Numero64{U32{+hi}, U32{+lo}}}:
      %Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, lo, N.maximo(32n))), N.uns(32n, lo), N.comparacao_maximo_reconhece_bits(32n, lo)) :
        {representar(B.incrementar64_casos(U32{hi}, U32{lo}, _, Cmp.is_eq(Word.cmp(32n, hi, N.maximo(32n))))) ==
          S.incrementar(64n, Some{W.juntar(32n, 32n, lo, hi)}) : Maybe<&2, Word(64n)>}
      %Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, hi, N.maximo(32n))), N.uns(32n, hi), N.comparacao_maximo_reconhece_bits(32n, hi)) :
        {representar(B.incrementar64_casos(U32{hi}, U32{lo}, N.uns(32n, lo), _)) ==
          S.incrementar(64n, Some{W.juntar(32n, 32n, lo, hi)}) : Maybe<&2, Word(64n)>}
      Equal.trans(Maybe<&2, Word(64n)>,
        representar(B.incrementar64_casos(U32{hi}, U32{lo}, N.uns(32n, lo), N.uns(32n, hi))),
        S.juntar_opcional(32n, 32n, Word.inc(32n, lo), aplicar_carry(32n, N.uns(32n, lo), Some{hi})),
        S.incrementar(64n, Some{W.juntar(32n, 32n, lo, hi)}),
        representar_incremento_casos(N.uns(32n, lo), N.uns(32n, hi), hi, lo, {==}, {==}),
        Equal.sym(Maybe<&2, Word(64n)>, S.incrementar(64n, Some{W.juntar(32n, 32n, lo, hi)}),
          S.juntar_opcional(32n, 32n, Word.inc(32n, lo), aplicar_carry(32n, N.uns(32n, lo), Some{hi})), incrementar_blocos(32n, 32n, lo, hi)))

law nat64_representa_natural_binario:
  for +n: Nat
  {representar(B.nat64(n)) == S.natural(64n, n) : Maybe<&2, Word(64n)>}
def nat64_representa_natural_binario(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Maybe<&2, Word(64n)>,
        representar(B.incrementar64(B.nat64(p))), S.incrementar(64n, representar(B.nat64(p))), S.incrementar(64n, S.natural(64n, p)),
        incrementar64_representa_incremento_binario(B.nat64(p)),
        Equal.cong(Maybe<&2, Word(64n)>, Maybe<&2, Word(64n)>, m => S.incrementar(64n, m),
          representar(B.nat64(p)), S.natural(64n, p), nat64_representa_natural_binario(p)))

# Projecoes estruturais usadas somente para mostrar a fidelidade da ponte.
def baixos(k: Nat, -n: Nat, w: Word(Nat.add(k, n))) -> Word(k):
  match k:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{b, baixos(p, n, t)}

def altos(k: Nat, -n: Nat, w: Word(Nat.add(k, n))) -> Word(n):
  match k:
    case 0n:
      w
    case 1n+p:
      match w:
        case WCon{b, t}:
          altos(p, n, t)

law baixos_juntar:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  {baixos(k, n, W.juntar(k, n, lo, hi)) == lo : Word(k)}
def baixos_juntar(k, n, lo, hi):
  match k:
    case 0n:
      match lo:
        case WNil{}:
          {==}
    case 1n+p:
      match lo:
        case WCon{b, +t}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{b, w}, baixos(p, n, W.juntar(p, n, t, hi)), t, baixos_juntar(p, n, t, hi))

law altos_juntar:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  {altos(k, n, W.juntar(k, n, lo, hi)) == hi : Word(n)}
def altos_juntar(k, n, lo, hi):
  match k:
    case 0n:
      {==}
    case 1n+p:
      match lo:
        case WCon{b, t}:
          altos_juntar(p, n, t, hi)

def recuperar_bits(+w: Word(64n)) -> B.Numero64:
  B.Numero64{U32{altos(32n, 32n, w)}, U32{baixos(32n, 32n, w)}}

def recuperar(m: Maybe<&2, Word(64n)>) -> Maybe<&2, B.Numero64>:
  match m:
    case None{}:
      None{}
    case Some{w}:
      Some{recuperar_bits(w)}

law recuperar_bits_exato:
  for +q: B.Numero64
  {recuperar_bits(bits(q)) == q : B.Numero64}
def recuperar_bits_exato(q):
  match q:
    case B.Numero64{U32{+hi}, U32{+lo}}:
      %Equal.sym(Word(32n), altos(32n, 32n, W.juntar(32n, 32n, lo, hi)), hi, altos_juntar(32n, 32n, lo, hi)) :
        {B.Numero64{U32{_}, U32{baixos(32n, 32n, W.juntar(32n, 32n, lo, hi))}} == B.Numero64{U32{hi}, U32{lo}} : B.Numero64}
      Equal.cong(Word(32n), B.Numero64, w => B.Numero64{U32{hi}, U32{w}},
        baixos(32n, 32n, W.juntar(32n, 32n, lo, hi)), lo, baixos_juntar(32n, 32n, lo, hi))

law recuperar_representar:
  for +m: Maybe<&2, B.Numero64>
  {recuperar(representar(m)) == m : Maybe<&2, B.Numero64>}
def recuperar_representar(m):
  match m:
    case None{}:
      {==}
    case Some{+q}:
      Equal.cong(B.Numero64, Maybe<&2, B.Numero64>, x => Some{x}, recuperar_bits(bits(q)), q, recuperar_bits_exato(q))

law representar_injetiva:
  for +a: Maybe<&2, B.Numero64>
  for +b: Maybe<&2, B.Numero64>
  for e: {representar(a) == representar(b) : Maybe<&2, Word(64n)>}
  {a == b : Maybe<&2, B.Numero64>}
def representar_injetiva(a, b, e):
  Equal.trans(Maybe<&2, B.Numero64>, a, recuperar(representar(a)), b,
    Equal.sym(Maybe<&2, B.Numero64>, recuperar(representar(a)), a, recuperar_representar(a)),
    Equal.trans(Maybe<&2, B.Numero64>, recuperar(representar(a)), recuperar(representar(b)), b,
      Equal.cong(Maybe<&2, Word(64n)>, Maybe<&2, B.Numero64>, m => recuperar(m), representar(a), representar(b), e),
      recuperar_representar(b)))

law soma_naturais_representados:
  for +n: Nat
  for +m: Nat
  {S.somar_opcionais(64n, representar(B.nat64(n)), representar(B.nat64(m))) == S.natural(64n, Nat.add(n, m)) : Maybe<&2, Word(64n)>}
def soma_naturais_representados(n, m):
  %Equal.sym(Maybe<&2, Word(64n)>, representar(B.nat64(n)), S.natural(64n, n), nat64_representa_natural_binario(n)) :
    {S.somar_opcionais(64n, _, representar(B.nat64(m))) == S.natural(64n, Nat.add(n, m)) : Maybe<&2, Word(64n)>}
  %Equal.sym(Maybe<&2, Word(64n)>, representar(B.nat64(m)), S.natural(64n, m), nat64_representa_natural_binario(m)) :
    {S.somar_opcionais(64n, S.natural(64n, n), _) == S.natural(64n, Nat.add(n, m)) : Maybe<&2, Word(64n)>}
  S.soma_naturais(64n, n, m)
