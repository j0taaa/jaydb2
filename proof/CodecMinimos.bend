# Algebra de limites/minimos: lemas sobre a implementacao real.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./Ordens.bend as O
import ./CodecContadores.bend as N
import ./CodecUnicode.bend as U
import ./CodecPalavrasWord.bend as W
import ./CodecPalavrasBE64.bend as H
import ./CodecUTF8Bits.bend as A
import ./CodecPercurso.bend as R

law somar_zero_u32:
  for +x: U32
  {(x + 0 : U32) == x : U32}
def somar_zero_u32(x):
  match x:
    case U32{+w}:
      Equal.cong(Word(32n), U32, r => U32{r}, Word.add(32n, w, Word.zero(32n)), w, N.adc_zero_identidade(32n, w))

law menor_igual64_reflexivo:
  for +n: B.Numero64
  {C.menor_igual64(n, n) == True{} : Bool}
def menor_igual64_reflexivo(n):
  match n:
    case B.Numero64{+a, +b}:
      %Equal.sym(Cmp, U32.cmp(a, a), EQ{}, O.u32_refl(a)) :
        {Cmp.is_lt(_) || (Cmp.is_eq(U32.cmp(a, a)) && U32.is_le(b, b)) == True{} : Bool}
      %Equal.sym(Cmp, U32.cmp(a, a), EQ{}, O.u32_refl(a)) :
        {False{} || (Cmp.is_eq(_) && U32.is_le(b, b)) == True{} : Bool}
      Equal.cong(Cmp, Bool, c => Cmp.is_le(c), U32.cmp(b, b), EQ{}, O.u32_refl(b))

law somar64_zero_direito:
  for +n: B.Numero64
  {C.somar64(n, B.Numero64{0, 0}) == Some{n} : Maybe<&2, B.Numero64>}
def somar64_zero_direito(n):
  match n:
    case B.Numero64{+a, +b}:
      %Equal.sym(U32, (b + 0 : U32), b, somar_zero_u32(b)) :
        {C.soma64_transporte(U32.is_lt(_, b), (a + 0 : U32), (b + 0 : U32), U32.is_lt((a + 0 : U32), a)) == Some{B.Numero64{a, b}} : Maybe<&2, B.Numero64>}
      %Equal.sym(U32, (a + 0 : U32), a, somar_zero_u32(a)) :
        {C.soma64_transporte(U32.is_lt(b, b), _, (b + 0 : U32), U32.is_lt((a + 0 : U32), a)) == Some{B.Numero64{a, b}} : Maybe<&2, B.Numero64>}
      %Equal.sym(U32, (b + 0 : U32), b, somar_zero_u32(b)) :
        {C.soma64_transporte(U32.is_lt(b, b), a, _, U32.is_lt((a + 0 : U32), a)) == Some{B.Numero64{a, b}} : Maybe<&2, B.Numero64>}
      %Equal.sym(U32, (a + 0 : U32), a, somar_zero_u32(a)) :
        {C.soma64_transporte(U32.is_lt(b, b), a, b, U32.is_lt(_, a)) == Some{B.Numero64{a, b}} : Maybe<&2, B.Numero64>}
      %Equal.sym(Cmp, U32.cmp(b, b), EQ{}, O.u32_refl(b)) :
        {C.soma64_transporte(Cmp.is_lt(_), a, b, U32.is_lt(a, a)) == Some{B.Numero64{a, b}} : Maybe<&2, B.Numero64>}
      %Equal.sym(Cmp, U32.cmp(a, a), EQ{}, O.u32_refl(a)) :
        {C.soma64_transporte(False{}, a, b, Cmp.is_lt(_)) == Some{B.Numero64{a, b}} : Maybe<&2, B.Numero64>}
      {==}

law minimo_textual_na_raiz_e_exatamente_a_contagem:
  for +q: B.Numero64
  {C.somar_opcionais(C.minimo_campo(C.Texto{}, q), C.minimo_pilha(C.Raiz{})) == Some{q} : Maybe<&2, B.Numero64>}
def minimo_textual_na_raiz_e_exatamente_a_contagem(q):
  somar64_zero_direito(q)

law conferir_minimo_igual_ao_corpo_permite_limite:
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {C.conferir(Some{corpo}, corpo, teto) == C.Cabe{} : C.Conferencia}
def conferir_minimo_igual_ao_corpo_permite_limite(corpo, teto, cabe):
  %Equal.sym(Bool, C.menor_igual64(corpo, teto), True{}, cabe) :
    {C.conferir_casos(_, C.menor_igual64(corpo, corpo)) == C.Cabe{} : C.Conferencia}
  %Equal.sym(Bool, C.menor_igual64(corpo, corpo), True{}, menor_igual64_reflexivo(corpo)) :
    {C.conferir_casos(True{}, _) == C.Cabe{} : C.Conferencia}
  {==}

# Esta equivalencia relaciona o indicador de carry do sucessor ao teste
# exato de maximo; e util sem converter nenhuma palavra para Nat.
law sem_transporte_equivale_a_nao_maximo:
  for +n: Nat
  for +w: Word(n)
  {U.sem_transporte(n, w) == Bool.not(N.uns(n, w)) : Bool}
def sem_transporte_equivale_a_nao_maximo(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          {==}
        case WCon{True{}, t}:
          sem_transporte_equivale_a_nao_maximo(p, t)

law predecessor_positivo_pode_ser_incrementado:
  for +n: Nat
  for +w: Word(n)
  for nao_zero: {N.zeros(n, w) == False{} : Bool}
  {U.sem_transporte(n, N.predecessor(n, w)) == True{} : Bool}
def predecessor_positivo_pode_ser_incrementado(n, w, nao_zero):
  Equal.trans(Bool, U.sem_transporte(n, N.predecessor(n, w)), Bool.not(N.uns(n, N.predecessor(n, w))), True{},
    sem_transporte_equivale_a_nao_maximo(n, N.predecessor(n, w)),
    Equal.cong(Bool, Bool, b => Bool.not(b), N.uns(n, N.predecessor(n, w)), False{},
      Equal.trans(Bool, N.uns(n, N.predecessor(n, w)), N.zeros(n, w), False{}, N.predecessor_maximo_exatamente_no_zero(n, w), nao_zero)))

law comparar_com_predecessor_positivo:
  for +n: Nat
  for +z: Word(n)
  for +w: Word(n)
  for nao_zero: {N.zeros(n, w) == False{} : Bool}
  {Cmp.is_le(Word.cmp(n, z, N.predecessor(n, w))) == Cmp.is_lt(Word.cmp(n, z, w)) : Bool}
def comparar_com_predecessor_positivo(n, z, w, nao_zero):
  Equal.trans(Bool, Cmp.is_le(Word.cmp(n, z, N.predecessor(n, w))), Cmp.is_lt(Word.cmp(n, z, Word.inc(n, N.predecessor(n, w)))), Cmp.is_lt(Word.cmp(n, z, w)),
    U.word_limite_sucessor(n, z, N.predecessor(n, w), predecessor_positivo_pode_ser_incrementado(n, w, nao_zero)),
    Equal.cong(Word(n), Bool, r => Cmp.is_lt(Word.cmp(n, z, r)), Word.inc(n, N.predecessor(n, w)), w, N.incremento_do_predecessor(n, w)))

law predecessor_positivo_e_estritamente_menor:
  for +n: Nat
  for +w: Word(n)
  for nao_zero: {N.zeros(n, w) == False{} : Bool}
  {Cmp.is_lt(Word.cmp(n, N.predecessor(n, w), w)) == True{} : Bool}
def predecessor_positivo_e_estritamente_menor(n, w, nao_zero):
  Equal.trans(Bool, Cmp.is_lt(Word.cmp(n, N.predecessor(n, w), w)), Cmp.is_le(Word.cmp(n, N.predecessor(n, w), N.predecessor(n, w))), True{},
    Equal.sym(Bool, Cmp.is_le(Word.cmp(n, N.predecessor(n, w), N.predecessor(n, w))), Cmp.is_lt(Word.cmp(n, N.predecessor(n, w), w)),
      comparar_com_predecessor_positivo(n, N.predecessor(n, w), w, nao_zero)),
    Equal.cong(Cmp, Bool, c => Cmp.is_le(c), Word.cmp(n, N.predecessor(n, w), N.predecessor(n, w)), EQ{}, O.word_refl(n, N.predecessor(n, w))))

# Transitividade LT/LE, incluindo igualdade no limite.
def coerencia_lt_le(bc: Cmp, -ac: Cmp, coerente: O.Coerente(LT{}, bc, ac),
  le: {Cmp.is_le(bc) == True{} : Bool}) -> {ac == LT{} : Cmp}:
  match bc:
    case EQ{}:
      coerente
    case LT{}:
      coerente
    case GT{}:
      F.absurdo_booleano({ac == LT{} : Cmp}, le)

law word_lt_le_transitivo:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Word(n)
  for ab: {Cmp.is_lt(Word.cmp(n, a, b)) == True{} : Bool}
  for bc: {Cmp.is_le(Word.cmp(n, b, c)) == True{} : Bool}
  {Cmp.is_lt(Word.cmp(n, a, c)) == True{} : Bool}
def word_lt_le_transitivo(n, a, b, c, ab, bc):
  h = {(%O.cmp_lt(Word.cmp(n, a, b), ab) : O.Coerente(_, Word.cmp(n, b, c), Word.cmp(n, a, c))
    O.word_coerente(n, a, b, c)) : O.Coerente(LT{}, Word.cmp(n, b, c), Word.cmp(n, a, c))}
  Equal.cong(Cmp, Bool, k => Cmp.is_lt(k), Word.cmp(n, a, c), LT{}, coerencia_lt_le(Word.cmp(n, b, c), Word.cmp(n, a, c), h, bc))

law predecessor_preserva_ordem_positiva:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for le: {Cmp.is_le(Word.cmp(n, a, b)) == True{} : Bool}
  for positivo_a: {N.zeros(n, a) == False{} : Bool}
  for positivo_b: {N.zeros(n, b) == False{} : Bool}
  {Cmp.is_le(Word.cmp(n, N.predecessor(n, a), N.predecessor(n, b))) == True{} : Bool}
def predecessor_preserva_ordem_positiva(n, a, b, le, positivo_a, positivo_b):
  Equal.trans(Bool, Cmp.is_le(Word.cmp(n, N.predecessor(n, a), N.predecessor(n, b))), Cmp.is_lt(Word.cmp(n, N.predecessor(n, a), b)), True{},
    comparar_com_predecessor_positivo(n, N.predecessor(n, a), b, positivo_b),
    word_lt_le_transitivo(n, N.predecessor(n, a), a, b, predecessor_positivo_e_estritamente_menor(n, a, positivo_a), le))

law e_booleano_comuta:
  for a: Bool
  for b: Bool
  {a && b == b && a : Bool}
def e_booleano_comuta(a, b):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

law zeros_de_blocos:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  {N.zeros(Nat.add(k, n), W.juntar(k, n, lo, hi)) == N.zeros(k, lo) && N.zeros(n, hi) : Bool}
def zeros_de_blocos(k, n, lo, hi):
  match k:
    case 0n:
      {==}
    case 1n+p:
      match lo:
        case WCon{False{}, t}:
          zeros_de_blocos(p, n, t, hi)
        case WCon{True{}, t}:
          {==}

def bits64(q: B.Numero64) -> Word(64n):
  B.Numero64{a, b} = q
  W.juntar(32n, 32n, H.bits(b), H.bits(a))

law zero64_equivale_bits_zero:
  for +q: B.Numero64
  {C.zero64(q) == N.zeros(64n, bits64(q)) : Bool}
def zero64_equivale_bits_zero(q):
  match q:
    case B.Numero64{U32{+a}, U32{+b}}:
      %Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, a, Word.zero(32n))), N.zeros(32n, a), N.comparacao_zero_reconhece_bits(32n, a)) :
        {_ && Cmp.is_eq(Word.cmp(32n, b, Word.zero(32n))) == N.zeros(64n, W.juntar(32n, 32n, b, a)) : Bool}
      %Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, b, Word.zero(32n))), N.zeros(32n, b), N.comparacao_zero_reconhece_bits(32n, b)) :
        {N.zeros(32n, a) && _ == N.zeros(64n, W.juntar(32n, 32n, b, a)) : Bool}
      Equal.trans(Bool, N.zeros(32n, a) && N.zeros(32n, b), N.zeros(32n, b) && N.zeros(32n, a), N.zeros(64n, W.juntar(32n, 32n, b, a)),
        e_booleano_comuta(N.zeros(32n, a), N.zeros(32n, b)),
        Equal.sym(Bool, N.zeros(64n, W.juntar(32n, 32n, b, a)), N.zeros(32n, b) && N.zeros(32n, a), zeros_de_blocos(32n, 32n, b, a)))

law predecessor_bloco_baixo_positivo:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  for positivo: {N.zeros(k, lo) == False{} : Bool}
  {N.predecessor(Nat.add(k, n), W.juntar(k, n, lo, hi)) == W.juntar(k, n, N.predecessor(k, lo), hi) : Word(Nat.add(k, n))}
def predecessor_bloco_baixo_positivo(k, n, lo, hi, positivo):
  match k:
    case 0n:
      F.absurdo_booleano({N.predecessor(n, W.juntar(0n, n, lo, hi)) == W.juntar(0n, n, N.predecessor(0n, lo), hi) : Word(n)}, Equal.sym(Bool, True{}, False{}, positivo))
    case 1n+p:
      match lo:
        case WCon{True{}, t}:
          {==}
        case WCon{False{}, +t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{True{}, r},
            N.predecessor(Nat.add(p, n), W.juntar(p, n, t, hi)), W.juntar(p, n, N.predecessor(p, t), hi),
            predecessor_bloco_baixo_positivo(p, n, t, hi, positivo))

law predecessor_bloco_baixo_zero:
  for +k: Nat
  for +n: Nat
  for +hi: Word(n)
  {N.predecessor(Nat.add(k, n), W.zeros_baixos(k, n, hi)) == W.juntar(k, n, W.uns(k), N.predecessor(n, hi)) : Word(Nat.add(k, n))}
def predecessor_bloco_baixo_zero(k, n, hi):
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{True{}, r},
        N.predecessor(Nat.add(p, n), W.zeros_baixos(p, n, hi)), W.juntar(p, n, W.uns(p), N.predecessor(n, hi)), predecessor_bloco_baixo_zero(p, n, hi))

def diminuir_bits_sem_transporte(+a: U32, +b: U32,
  nao_zero: {U32.is_eq(b, 0) == False{} : Bool}) ->
  {bits64(B.Numero64{a, (b - 1 : U32)}) == N.predecessor(64n, bits64(B.Numero64{a, b})) : Word(64n)}:
  match a b:
    case U32{+hi} U32{+lo}:
      %Equal.sym(Word(32n), Word.sub(32n, lo, N.um(31n)), N.predecessor(32n, lo), N.subtrair_um_decrementa(31n, lo)) :
        {W.juntar(32n, 32n, _, hi) == N.predecessor(64n, W.juntar(32n, 32n, lo, hi)) : Word(64n)}
      Equal.sym(Word(64n), N.predecessor(64n, W.juntar(32n, 32n, lo, hi)), W.juntar(32n, 32n, N.predecessor(32n, lo), hi),
        predecessor_bloco_baixo_positivo(32n, 32n, lo, hi,
          Equal.trans(Bool, N.zeros(32n, lo), Cmp.is_eq(Word.cmp(32n, lo, Word.zero(32n))), False{},
            Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, lo, Word.zero(32n))), N.zeros(32n, lo), N.comparacao_zero_reconhece_bits(32n, lo)), nao_zero)))

def diminuir_bits_com_transporte(+a: U32) ->
  {bits64(B.Numero64{(a - 1 : U32), 4294967295}) == N.predecessor(64n, bits64(B.Numero64{a, 0})) : Word(64n)}:
  match a:
    case U32{+hi}:
      %Equal.sym(Word(32n), Word.sub(32n, hi, N.um(31n)), N.predecessor(32n, hi), N.subtrair_um_decrementa(31n, hi)) :
        {W.juntar(32n, 32n, W.uns(32n), _) == N.predecessor(64n, W.juntar(32n, 32n, Word.zero(32n), hi)) : Word(64n)}
      Equal.sym(Word(64n), N.predecessor(64n, W.zeros_baixos(32n, 32n, hi)), W.juntar(32n, 32n, W.uns(32n), N.predecessor(32n, hi)), predecessor_bloco_baixo_zero(32n, 32n, hi))

def diminuir_bits_casos(baixo_zero: Bool, alto_zero: Bool, +a: U32, +b: U32,
  eb: {U32.is_eq(b, 0) == baixo_zero : Bool},
  ea: {U32.is_eq(a, 0) == alto_zero : Bool},
  positivo: {alto_zero && baixo_zero == False{} : Bool}) ->
  {bits64(C.diminuir64_casos(baixo_zero, alto_zero, a, b)) == N.predecessor(64n, bits64(B.Numero64{a, b})) : Word(64n)}:
  match baixo_zero alto_zero:
    case False{} _:
      diminuir_bits_sem_transporte(a, b, eb)
    case True{} False{}:
      %Equal.sym(U32, b, 0, N.igualdade_u32(b, 0, eb)) :
        {bits64(B.Numero64{(a - 1 : U32), 4294967295}) == N.predecessor(64n, bits64(B.Numero64{a, _})) : Word(64n)}
      diminuir_bits_com_transporte(a)
    case True{} True{}:
      F.absurdo_booleano({bits64(B.Numero64{0, 0}) == N.predecessor(64n, bits64(B.Numero64{a, b})) : Word(64n)}, Equal.sym(Bool, True{}, False{}, positivo))


law diminuir64_representa_predecessor_positivo:
  for +q: B.Numero64
  for positivo: {C.zero64(q) == False{} : Bool}
  {bits64(C.diminuir64(q)) == N.predecessor(64n, bits64(q)) : Word(64n)}
def diminuir64_representa_predecessor_positivo(q, positivo):
  match q:
    case B.Numero64{+a, +b}:
      diminuir_bits_casos(U32.is_eq(b, 0), U32.is_eq(a, 0), a, b, {==}, {==}, positivo)

law comparacao_lexicografica:
  for a: Cmp
  for b: Cmp
  {Cmp.is_lt(a) || (Cmp.is_eq(a) && Cmp.is_le(b)) == Cmp.is_le(O.prioridade(a, b)) : Bool}
def comparacao_lexicografica(a, b):
  match a:
    case EQ{}:
      {==}
    case LT{}:
      {==}
    case GT{}:
      {==}

law menor_igual64_equivale_ordem_dos_bits:
  for +a: B.Numero64
  for +b: B.Numero64
  {C.menor_igual64(a, b) == Cmp.is_le(Word.cmp(64n, bits64(a), bits64(b))) : Bool}
def menor_igual64_equivale_ordem_dos_bits(a, b):
  match a b:
    case B.Numero64{U32{+ah}, U32{+al}} B.Numero64{U32{+bh}, U32{+bl}}:
      Equal.trans(Bool, Cmp.is_lt(Word.cmp(32n, ah, bh)) || (Cmp.is_eq(Word.cmp(32n, ah, bh)) && Cmp.is_le(Word.cmp(32n, al, bl))),
        Cmp.is_le(O.prioridade(Word.cmp(32n, ah, bh), Word.cmp(32n, al, bl))), Cmp.is_le(Word.cmp(64n, W.juntar(32n, 32n, al, ah), W.juntar(32n, 32n, bl, bh))),
        comparacao_lexicografica(Word.cmp(32n, ah, bh), Word.cmp(32n, al, bl)),
        Equal.cong(Cmp, Bool, c => Cmp.is_le(c), O.prioridade(Word.cmp(32n, ah, bh), Word.cmp(32n, al, bl)), Word.cmp(64n, W.juntar(32n, 32n, al, ah), W.juntar(32n, 32n, bl, bh)),
          Equal.sym(Cmp, Word.cmp(64n, W.juntar(32n, 32n, al, ah), W.juntar(32n, 32n, bl, bh)), O.prioridade(Word.cmp(32n, ah, bh), Word.cmp(32n, al, bl)), A.comparar_blocos(32n, 32n, al, bl, ah, bh))))

law cmp_zero_bit_nao_maior:
  for b: Bool
  for c: Cmp
  for e: {Cmp.is_le(c) == True{} : Bool}
  {Cmp.is_le(Word.cmp.fin(False{}, b, c)) == True{} : Bool}
def cmp_zero_bit_nao_maior(b, c, e):
  match b c:
    case False{} EQ{}:
      {==}
    case True{} EQ{}:
      {==}
    case False{} LT{}:
      {==}
    case True{} LT{}:
      {==}
    case False{} GT{}:
      F.absurdo_booleano({False{} == True{} : Bool}, e)
    case True{} GT{}:
      F.absurdo_booleano({False{} == True{} : Bool}, e)

law palavra_zero_nao_maior:
  for +n: Nat
  for +w: Word(n)
  {Cmp.is_le(Word.cmp(n, Word.zero(n), w)) == True{} : Bool}
def palavra_zero_nao_maior(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, +t}:
          cmp_zero_bit_nao_maior(b, Word.cmp(p, Word.zero(p), t), palavra_zero_nao_maior(p, t))

law zero64_nao_maior:
  for +q: B.Numero64
  {C.menor_igual64(B.Numero64{0, 0}, q) == True{} : Bool}
def zero64_nao_maior(q):
  Equal.trans(Bool, C.menor_igual64(B.Numero64{0, 0}, q), Cmp.is_le(Word.cmp(64n, Word.zero(64n), bits64(q))), True{},
    menor_igual64_equivale_ordem_dos_bits(B.Numero64{0, 0}, q), palavra_zero_nao_maior(64n, bits64(q)))

law menor_igual_a_zero64_e_zero:
  for +q: B.Numero64
  for le: {C.menor_igual64(q, B.Numero64{0, 0}) == True{} : Bool}
  {C.zero64(q) == True{} : Bool}
def menor_igual_a_zero64_e_zero(q, le):
  limitado = Equal.trans(Bool, Cmp.is_le(Word.cmp(64n, bits64(q), Word.zero(64n))), C.menor_igual64(q, B.Numero64{0, 0}), True{},
    Equal.sym(Bool, C.menor_igual64(q, B.Numero64{0, 0}), Cmp.is_le(Word.cmp(64n, bits64(q), Word.zero(64n))), menor_igual64_equivale_ordem_dos_bits(q, B.Numero64{0, 0})), le)
  Equal.trans(Bool, C.zero64(q), N.zeros(64n, bits64(q)), True{}, zero64_equivale_bits_zero(q),
    Equal.cong(Word(64n), Bool, w => N.zeros(64n, w), bits64(q), Word.zero(64n), W.palavra_ate_zero(64n, bits64(q), limitado)))

law limite_de_positivo_e_positivo:
  for +a: B.Numero64
  for +b: B.Numero64
  for le: {C.menor_igual64(a, b) == True{} : Bool}
  for positivo: {C.zero64(a) == False{} : Bool}
  {C.zero64(b) == False{} : Bool}
def limite_de_positivo_e_positivo(a, b, le, positivo):
  N.falso_se_verdadeiro_impossivel(C.zero64(b), e =>
    F.falso_nao_verdadeiro(Equal.trans(Bool, False{}, C.zero64(a), True{}, Equal.sym(Bool, C.zero64(a), False{}, positivo),
      menor_igual_a_zero64_e_zero(a,
        (%N.zero64_so_reconhece_zero(b, e) : {C.menor_igual64(a, _) == True{} : Bool}
          le)))))

def diminuir_limites_casos(zero_a: Bool, +a: B.Numero64, +b: B.Numero64,
  +ea: {C.zero64(a) == zero_a : Bool}, +le: {C.menor_igual64(a, b) == True{} : Bool}) ->
  {C.menor_igual64(C.diminuir64(a), C.diminuir64(b)) == True{} : Bool}:
  match zero_a:
    case True{}:
      %Equal.sym(B.Numero64, a, B.Numero64{0, 0}, N.zero64_so_reconhece_zero(a, ea)) :
        {C.menor_igual64(C.diminuir64(_), C.diminuir64(b)) == True{} : Bool}
      zero64_nao_maior(C.diminuir64(b))
    case False{}:
      +positivo_b = limite_de_positivo_e_positivo(a, b, le, ea)
      ordem = Equal.trans(Bool, Cmp.is_le(Word.cmp(64n, bits64(a), bits64(b))), C.menor_igual64(a, b), True{},
        Equal.sym(Bool, C.menor_igual64(a, b), Cmp.is_le(Word.cmp(64n, bits64(a), bits64(b))), menor_igual64_equivale_ordem_dos_bits(a, b)), le)
      zeros_a = Equal.trans(Bool, N.zeros(64n, bits64(a)), C.zero64(a), False{}, Equal.sym(Bool, C.zero64(a), N.zeros(64n, bits64(a)), zero64_equivale_bits_zero(a)), ea)
      zeros_b = Equal.trans(Bool, N.zeros(64n, bits64(b)), C.zero64(b), False{}, Equal.sym(Bool, C.zero64(b), N.zeros(64n, bits64(b)), zero64_equivale_bits_zero(b)), positivo_b)
      Equal.trans(Bool, C.menor_igual64(C.diminuir64(a), C.diminuir64(b)), Cmp.is_le(Word.cmp(64n, bits64(C.diminuir64(a)), bits64(C.diminuir64(b)))), True{},
        menor_igual64_equivale_ordem_dos_bits(C.diminuir64(a), C.diminuir64(b)),
        (%Equal.sym(Word(64n), bits64(C.diminuir64(a)), N.predecessor(64n, bits64(a)), diminuir64_representa_predecessor_positivo(a, ea)) :
          {Cmp.is_le(Word.cmp(64n, _, bits64(C.diminuir64(b)))) == True{} : Bool}
          %Equal.sym(Word(64n), bits64(C.diminuir64(b)), N.predecessor(64n, bits64(b)), diminuir64_representa_predecessor_positivo(b, positivo_b)) :
            {Cmp.is_le(Word.cmp(64n, N.predecessor(64n, bits64(a)), _)) == True{} : Bool}
          predecessor_preserva_ordem_positiva(64n, bits64(a), bits64(b), ordem, zeros_a, zeros_b)))

law diminuir64_preserva_ordem_dos_limites:
  for +a: B.Numero64
  for +b: B.Numero64
  for le: {C.menor_igual64(a, b) == True{} : Bool}
  {C.menor_igual64(C.diminuir64(a), C.diminuir64(b)) == True{} : Bool}
def diminuir64_preserva_ordem_dos_limites(a, b, le):
  diminuir_limites_casos(C.zero64(a), a, b, {==}, le)

law diminuir_repetido_preserva_ordem_dos_limites:
  for +n: Nat
  for +a: B.Numero64
  for +b: B.Numero64
  for le: {C.menor_igual64(a, b) == True{} : Bool}
  {C.menor_igual64(H.diminuir(n, a), H.diminuir(n, b)) == True{} : Bool}
def diminuir_repetido_preserva_ordem_dos_limites(n, a, b, le):
  match n:
    case 0n:
      le
    case 1n+p:
      diminuir64_preserva_ordem_dos_limites(H.diminuir(p, a), H.diminuir(p, b), diminuir_repetido_preserva_ordem_dos_limites(p, a, b, le))

def teto_quadro(q: R.Quadro) -> B.Numero64:
  R.Quadro{corpo, teto, m} = q
  teto

law qualquer_prefixo_preserva_corpo_dentro_do_teto:
  for bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +m: C.Maquina
  for le: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {C.menor_igual64(N.corpo_quadro(R.executar(bs, R.Quadro{corpo, teto, m})), teto_quadro(R.executar(bs, R.Quadro{corpo, teto, m}))) == True{} : Bool}
def qualquer_prefixo_preserva_corpo_dentro_do_teto(bs, corpo, teto, m, le):
  match bs:
    case Nil{}:
      le
    case Con{+b, t}:
      +resto = C.diminuir64(corpo)
      +livre = C.diminuir64(teto)
      qualquer_prefixo_preserva_corpo_dentro_do_teto(t, resto, livre, C.passo(m, b, resto, livre), diminuir64_preserva_ordem_dos_limites(corpo, teto, le))
