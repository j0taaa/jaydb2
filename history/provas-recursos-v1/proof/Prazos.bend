# Algebra dos prazos absolutos usados na fronteira Python/C.
# Nao presume que um relogio ou uma medicao tenha ocorrido no host.
import Base
import ./CodecSomasOrdem.bend as O

law subtrair_inicio_recupera_intervalo:
  for inicio: Nat
  for +intervalo: Nat
  {Nat.sub(Nat.add(inicio, intervalo), inicio) == intervalo : Nat}
def subtrair_inicio_recupera_intervalo(inicio, intervalo):
  match inicio:
    case 0n:
      O.nat_subtrair_zero(intervalo)
    case 1n+p:
      subtrair_inicio_recupera_intervalo(p, intervalo)

law comparar_instantes_preserva_intervalos:
  for inicio: Nat
  for +decorrido: Nat
  for +orcamento: Nat
  {Nat.cmp(Nat.add(inicio, decorrido), Nat.add(inicio, orcamento)) == Nat.cmp(decorrido, orcamento) : Cmp}
def comparar_instantes_preserva_intervalos(inicio, decorrido, orcamento):
  match inicio:
    case 0n:
      {==}
    case 1n+p:
      comparar_instantes_preserva_intervalos(p, decorrido, orcamento)

law prazo_absoluto_e_intervalo_expiram_juntos:
  for +inicio: Nat
  for +decorrido: Nat
  for +orcamento: Nat
  {Nat.is_ge(Nat.add(inicio, decorrido), Nat.add(inicio, orcamento)) == Nat.is_ge(decorrido, orcamento) : Bool}
def prazo_absoluto_e_intervalo_expiram_juntos(inicio, decorrido, orcamento):
  Equal.cong(Cmp, Bool, c => Cmp.is_ge(c),
    Nat.cmp(Nat.add(inicio, decorrido), Nat.add(inicio, orcamento)), Nat.cmp(decorrido, orcamento),
    comparar_instantes_preserva_intervalos(inicio, decorrido, orcamento))

# Recalcular apenas a diferenca no instante nativo conserva o MESMO prazo.
# Adicionar um intervalo antigo ao novo instante, em vez disso, nao e este termo.
law converter_prazo_no_instante_nativo_conserva_expiracao:
  for +inicio: Nat
  for +decorrido: Nat
  for +saldo: Nat
  {Nat.is_ge(Nat.sub(Nat.add(inicio, decorrido), inicio),
    Nat.sub(Nat.add(inicio, saldo), inicio)) ==
    Nat.is_ge(Nat.add(inicio, decorrido), Nat.add(inicio, saldo)) : Bool}
def converter_prazo_no_instante_nativo_conserva_expiracao(inicio, decorrido, saldo):
  %Equal.sym(Nat, Nat.sub(Nat.add(inicio, decorrido), inicio), decorrido,
    subtrair_inicio_recupera_intervalo(inicio, decorrido)) :
      {Nat.is_ge(_, Nat.sub(Nat.add(inicio, saldo), inicio)) ==
        Nat.is_ge(Nat.add(inicio, decorrido), Nat.add(inicio, saldo)) : Bool}
  %Equal.sym(Nat, Nat.sub(Nat.add(inicio, saldo), inicio), saldo,
    subtrair_inicio_recupera_intervalo(inicio, saldo)) :
      {Nat.is_ge(decorrido, _) == Nat.is_ge(Nat.add(inicio, decorrido), Nat.add(inicio, saldo)) : Bool}
  Equal.sym(Bool, Nat.is_ge(Nat.add(inicio, decorrido), Nat.add(inicio, saldo)), Nat.is_ge(decorrido, saldo),
    prazo_absoluto_e_intervalo_expiram_juntos(inicio, decorrido, saldo))
