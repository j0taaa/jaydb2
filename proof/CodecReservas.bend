# Conferencias por uma reserva natural dentro do corpo real. O teto e u64
# arbitrario: nao se exige converte-lo para Nat nem assumir minimo cabe.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./Ordens.bend as O
import ./CodecMinimos.bend as M
import ./CodecSomasOrdem.bend as S
import ./CodecSomasMinimos.bend as A

def coerencia_le_le(ab: Cmp, bc: Cmp, -ac: Cmp,
  h: O.Coerente(ab, bc, ac),
  le1: {Cmp.is_le(ab) == True{} : Bool},
  le2: {Cmp.is_le(bc) == True{} : Bool}) -> {Cmp.is_le(ac) == True{} : Bool}:
  match ab bc:
    case EQ{} EQ{}:
      Equal.cong(Cmp, Bool, k => Cmp.is_le(k), ac, EQ{}, h)
    case EQ{} LT{}:
      Equal.cong(Cmp, Bool, k => Cmp.is_le(k), ac, LT{}, h)
    case LT{} EQ{}:
      Equal.cong(Cmp, Bool, k => Cmp.is_le(k), ac, LT{}, h)
    case LT{} LT{}:
      Equal.cong(Cmp, Bool, k => Cmp.is_le(k), ac, LT{}, h)
    case GT{} _:
      F.absurdo_booleano({Cmp.is_le(ac) == True{} : Bool}, le1)
    case EQ{} GT{}:
      F.absurdo_booleano({Cmp.is_le(ac) == True{} : Bool}, le2)
    case LT{} GT{}:
      F.absurdo_booleano({Cmp.is_le(ac) == True{} : Bool}, le2)

law menor_igual64_transitivo:
  for +a: B.Numero64
  for +b: B.Numero64
  for +c: B.Numero64
  for ab: {C.menor_igual64(a, b) == True{} : Bool}
  for bc: {C.menor_igual64(b, c) == True{} : Bool}
  {C.menor_igual64(a, c) == True{} : Bool}
def menor_igual64_transitivo(a, b, c, ab, bc):
  Equal.trans(Bool, C.menor_igual64(a, c), Cmp.is_le(Word.cmp(64n, M.bits64(a), M.bits64(c))), True{},
    M.menor_igual64_equivale_ordem_dos_bits(a, c),
    coerencia_le_le(Word.cmp(64n, M.bits64(a), M.bits64(b)), Word.cmp(64n, M.bits64(b), M.bits64(c)), Word.cmp(64n, M.bits64(a), M.bits64(c)),
      O.word_coerente(64n, M.bits64(a), M.bits64(b), M.bits64(c)),
      Equal.trans(Bool, Cmp.is_le(Word.cmp(64n, M.bits64(a), M.bits64(b))), C.menor_igual64(a, b), True{},
        Equal.sym(Bool, C.menor_igual64(a, b), Cmp.is_le(Word.cmp(64n, M.bits64(a), M.bits64(b))), M.menor_igual64_equivale_ordem_dos_bits(a, b)), ab),
      Equal.trans(Bool, Cmp.is_le(Word.cmp(64n, M.bits64(b), M.bits64(c))), C.menor_igual64(b, c), True{},
        Equal.sym(Bool, C.menor_igual64(b, c), Cmp.is_le(Word.cmp(64n, M.bits64(b), M.bits64(c))), M.menor_igual64_equivale_ordem_dos_bits(b, c)), bc)))

def conferir_representado_no_corpo(+n: Nat, +c: Nat, +corpo: B.Numero64, +teto: B.Numero64,
  +mc: {B.nat64(c) == Some{corpo} : Maybe<&2, B.Numero64>},
  nc: {Nat.is_le(n, c) == True{} : Bool},
  ct: {C.menor_igual64(corpo, teto) == True{} : Bool},
  representado: S.NumeroRepresentado<B.nat64(n)>) -> {C.conferir(B.nat64(n), corpo, teto) == C.Cabe{} : C.Conferencia}:
  match representado:
    case S.Representado{+minimo, +mn}:
      +cabe_corpo = S.menor_igual64_preserva_ordem_nat(n, c, minimo, corpo, mn, mc, nc)
      cabe_teto = menor_igual64_transitivo(minimo, corpo, teto, cabe_corpo, ct)
      %Equal.sym(Maybe<&2, B.Numero64>, B.nat64(n), Some{minimo}, mn) :
        {C.conferir(_, corpo, teto) == C.Cabe{} : C.Conferencia}
      %Equal.sym(Bool, C.menor_igual64(minimo, teto), True{}, cabe_teto) :
        {C.conferir_casos(_, C.menor_igual64(minimo, corpo)) == C.Cabe{} : C.Conferencia}
      %Equal.sym(Bool, C.menor_igual64(minimo, corpo), True{}, cabe_corpo) :
        {C.conferir_casos(True{}, _) == C.Cabe{} : C.Conferencia}
      {==}

law minimo_natural_dentro_do_corpo_e_teto_u64_cabe:
  for +n: Nat
  for +c: Nat
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +mc: {B.nat64(c) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +nc: {Nat.is_le(n, c) == True{} : Bool}
  for ct: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {C.conferir(B.nat64(n), corpo, teto) == C.Cabe{} : C.Conferencia}
def minimo_natural_dentro_do_corpo_e_teto_u64_cabe(n, c, corpo, teto, mc, nc, ct):
  conferir_representado_no_corpo(n, c, corpo, teto, mc, nc, ct,
    S.nat64_representabilidade_fechada_para_baixo(n, c, corpo, mc, nc))

law conferir_minimo_composto_pelo_corpo_real:
  for +f: C.Finalidade
  for +n: Nat
  for +r: Nat
  for +c: Nat
  for +q: B.Numero64
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for medido: {B.nat64(n) == Some{q} : Maybe<&2, B.Numero64>}
  for pai: {C.minimo_pilha(pilha) == B.nat64(r) : Maybe<&2, B.Numero64>}
  for +mc: {B.nat64(c) == Some{corpo} : Maybe<&2, B.Numero64>}
  for nc: {Nat.is_le(Nat.add(A.minimo_campo_natural(f, n), r), c) == True{} : Bool}
  for ct: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {C.conferir(C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(pilha)), corpo, teto) == C.Cabe{} : C.Conferencia}
def conferir_minimo_composto_pelo_corpo_real(f, n, r, c, q, pilha, corpo, teto, medido, pai, mc, nc, ct):
  %Equal.sym(Maybe<&2, B.Numero64>, C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(pilha)), B.nat64(Nat.add(A.minimo_campo_natural(f, n), r)),
    A.minimo_campo_com_pilha_nat64_exato(f, n, r, q, pilha, medido, pai)) :
    {C.conferir(_, corpo, teto) == C.Cabe{} : C.Conferencia}
  minimo_natural_dentro_do_corpo_e_teto_u64_cabe(Nat.add(A.minimo_campo_natural(f, n), r), c, corpo, teto, mc, nc, ct)
