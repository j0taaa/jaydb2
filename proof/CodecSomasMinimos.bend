# Aplicacoes dos teoremas gerais aos minimos reais do codec.
import Base
import ../contrato/Bytes.bend as B
import ../src/Codec.bend as C
import ./CodecContadores.bend as N
import ./CodecSomas.bend as A
import ./CodecSomasOrdem.bend as O

law nat_multiplicar_zero_direita:
  for +k: Nat
  {Nat.mul(k, 0n) == 0n : Nat}
def nat_multiplicar_zero_direita(k):
  match k:
    case 0n:
      {==}
    case 1n+p:
      nat_multiplicar_zero_direita(p)

# O atalho para pendencia vazia preserva exatamente a soma matematica,
# inclusive se o resto ou o produto nao forem representaveis.
law somar_pendencia_nat64_exato:
  for +n: Nat
  for +fator: Nat
  for +r: Nat
  for +q: B.Numero64
  for +medido: {B.nat64(n) == Some{q} : Maybe<&2, B.Numero64>}
  {C.somar_pendencia(q, fator, B.nat64(r)) == B.nat64(Nat.add(Nat.mul(fator, n), r)) : Maybe<&2, B.Numero64>}
def somar_pendencia_nat64_exato(n, fator, r, q, medido):
  match n:
    case 0n:
      %Equal.sym(Bool, C.zero64(q), True{}, N.zero64_reflete_contagem_natural(0n, q, medido)) :
        {C.somar_pendencia_casos(_, q, fator, B.nat64(r)) == B.nat64(Nat.add(Nat.mul(fator, 0n), r)) : Maybe<&2, B.Numero64>}
      %Equal.sym(Nat, Nat.mul(fator, 0n), 0n, nat_multiplicar_zero_direita(fator)) :
        {B.nat64(r) == B.nat64(Nat.add(_, r)) : Maybe<&2, B.Numero64>}
      {==}
    case 1n+p:
      %Equal.sym(Bool, C.zero64(q), False{}, N.zero64_reflete_contagem_natural(1n+p, q, medido)) :
        {C.somar_pendencia_casos(_, q, fator, B.nat64(r)) == B.nat64(Nat.add(Nat.mul(fator, 1n+p), r)) : Maybe<&2, B.Numero64>}
      %Equal.sym(Maybe<&2, B.Numero64>, C.multiplicar_pequeno(fator, q), B.nat64(Nat.mul(fator, 1n+p)), A.multiplicar_pequeno_nat64_exato(fator, 1n+p, q, medido)) :
        {C.somar_opcionais(_, B.nat64(r)) == B.nat64(Nat.add(Nat.mul(fator, 1n+p), r)) : Maybe<&2, B.Numero64>}
      A.somar_opcionais_nat64_exato(Nat.mul(fator, 1n+p), r)

def minimo_campo_natural(f: C.Finalidade, n: Nat) -> Nat:
  match f:
    case C.ContaRegistro{}:
      Nat.mul(11n, n)
    case _:
      n

law minimo_campo_nat64_exato:
  for +f: C.Finalidade
  for +n: Nat
  for +q: B.Numero64
  for medido: {B.nat64(n) == Some{q} : Maybe<&2, B.Numero64>}
  {C.minimo_campo(f, q) == B.nat64(minimo_campo_natural(f, n)) : Maybe<&2, B.Numero64>}
def minimo_campo_nat64_exato(f, n, q, medido):
  match f:
    case C.ContaRegistro{}:
      A.multiplicar_pequeno_nat64_exato(11n, n, q, medido)
    case C.Inteiro{}:
      Equal.sym(Maybe<&2, B.Numero64>, B.nat64(n), Some{q}, medido)
    case C.Texto{}:
      Equal.sym(Maybe<&2, B.Numero64>, B.nat64(n), Some{q}, medido)
    case C.NomeTexto{}:
      Equal.sym(Maybe<&2, B.Numero64>, B.nat64(n), Some{q}, medido)
    case C.ContaLista{}:
      Equal.sym(Maybe<&2, B.Numero64>, B.nat64(n), Some{q}, medido)

# Hipotese local sobre a pilha pai: permite aplicar o teorema como passo
# indutivo, sem presumir a correção da conferencia composta.
law minimo_campo_com_pilha_nat64_exato:
  for +f: C.Finalidade
  for +n: Nat
  for +r: Nat
  for +q: B.Numero64
  for +pilha: C.Pilha
  for medido: {B.nat64(n) == Some{q} : Maybe<&2, B.Numero64>}
  for pai: {C.minimo_pilha(pilha) == B.nat64(r) : Maybe<&2, B.Numero64>}
  {C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(pilha)) ==
    B.nat64(Nat.add(minimo_campo_natural(f, n), r)) : Maybe<&2, B.Numero64>}
def minimo_campo_com_pilha_nat64_exato(f, n, r, q, pilha, medido, pai):
  %Equal.sym(Maybe<&2, B.Numero64>, C.minimo_campo(f, q), B.nat64(minimo_campo_natural(f, n)), minimo_campo_nat64_exato(f, n, q, medido)) :
    {C.somar_opcionais(_, C.minimo_pilha(pilha)) == B.nat64(Nat.add(minimo_campo_natural(f, n), r)) : Maybe<&2, B.Numero64>}
  %Equal.sym(Maybe<&2, B.Numero64>, C.minimo_pilha(pilha), B.nat64(r), pai) :
    {C.somar_opcionais(B.nat64(minimo_campo_natural(f, n)), _) == B.nat64(Nat.add(minimo_campo_natural(f, n), r)) : Maybe<&2, B.Numero64>}
  A.somar_opcionais_nat64_exato(minimo_campo_natural(f, n), r)

# Aplicacao direta aos limites reais: o minimo composto nao precisa vir
# acompanhado de uma hipotese de que sua conversao para u64 foi aceita.
law conferir_minimo_campo_com_pilha_por_limites_nat:
  for +f: C.Finalidade
  for +n: Nat
  for +r: Nat
  for +c: Nat
  for +t: Nat
  for +q: B.Numero64
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for medido: {B.nat64(n) == Some{q} : Maybe<&2, B.Numero64>}
  for pai: {C.minimo_pilha(pilha) == B.nat64(r) : Maybe<&2, B.Numero64>}
  for +mc: {B.nat64(c) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +mt: {B.nat64(t) == Some{teto} : Maybe<&2, B.Numero64>}
  for +lc: {Nat.is_le(Nat.add(minimo_campo_natural(f, n), r), c) == True{} : Bool}
  for lt: {Nat.is_le(Nat.add(minimo_campo_natural(f, n), r), t) == True{} : Bool}
  {C.conferir(C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(pilha)), corpo, teto) == C.Cabe{} : C.Conferencia}
def conferir_minimo_campo_com_pilha_por_limites_nat(f, n, r, c, t, q, pilha, corpo, teto, medido, pai, mc, mt, lc, lt):
  %Equal.sym(Maybe<&2, B.Numero64>,
    C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(pilha)),
    B.nat64(Nat.add(minimo_campo_natural(f, n), r)),
    minimo_campo_com_pilha_nat64_exato(f, n, r, q, pilha, medido, pai)) :
    {C.conferir(_, corpo, teto) == C.Cabe{} : C.Conferencia}
  O.conferir_natural_limitado(Nat.add(minimo_campo_natural(f, n), r), c, t, corpo, teto, mc, mt, lc, lt)
