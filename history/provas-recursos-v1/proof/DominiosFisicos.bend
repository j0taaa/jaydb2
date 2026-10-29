# Comparacoes de limites Nat com representacoes fisicas saturadas.
# Nao afirma o dominio real de um relogio, uma medida ou uma alocacao.
# Memoria exige valor <= maximo; prazo exige instante ESTRITAMENTE menor.
import Base
import ./Fundamentos.bend as F
import ../contrato/Logica.bend as L

law saturar_teto_preserva_excesso_de_memoria:
  for +valor: Nat
  for +teto: Nat
  for +maximo: Nat
  for cabe: {Nat.is_le(valor, maximo) == True{} : Bool}
  {Nat.is_gt(valor, Nat.min(teto, maximo)) == Nat.is_gt(valor, teto) : Bool}
def saturar_teto_preserva_excesso_de_memoria(valor, teto, maximo, cabe):
  match valor teto maximo:
    case _ 0n _:
      {==}
    case 0n 1n+t 0n:
      {==}
    case 0n 1n+t 1n+m:
      {==}
    case 1n+v 1n+t 0n:
      F.absurdo_booleano({True{} == Nat.is_gt(v, t) : Bool}, cabe)
    case 1n+v 1n+t 1n+m:
      saturar_teto_preserva_excesso_de_memoria(v, t, m, cabe)

law saturar_prazo_preserva_expiracao:
  for +instante: Nat
  for +prazo: Nat
  for +maximo: Nat
  for anterior: {Nat.is_lt(instante, maximo) == True{} : Bool}
  {Nat.is_ge(instante, Nat.min(prazo, maximo)) == Nat.is_ge(instante, prazo) : Bool}
def saturar_prazo_preserva_expiracao(instante, prazo, maximo, anterior):
  match instante prazo maximo:
    case _ 0n _:
      {==}
    case 0n 1n+p 0n:
      F.absurdo_booleano({True{} == False{} : Bool}, anterior)
    case 0n 1n+p 1n+m:
      {==}
    case 1n+t 1n+p 0n:
      F.absurdo_booleano({True{} == Nat.is_ge(t, p) : Bool}, anterior)
    case 1n+t 1n+p 1n+m:
      saturar_prazo_preserva_expiracao(t, p, m, anterior)

law aumentar_maximo_preserva_instante_anterior:
  for +instante: Nat
  for +maximo: Nat
  for anterior: {Nat.is_lt(instante, maximo) == True{} : Bool}
  {Nat.is_lt(instante, 1n+maximo) == True{} : Bool}
def aumentar_maximo_preserva_instante_anterior(instante, maximo, anterior):
  match instante maximo:
    case 0n 0n:
      F.absurdo_booleano({True{} == True{} : Bool}, anterior)
    case 1n+t 0n:
      F.absurdo_booleano({Nat.is_lt(t, 0n) == True{} : Bool}, anterior)
    case 0n 1n+m:
      {==}
    case 1n+t 1n+m:
      aumentar_maximo_preserva_instante_anterior(t, m, anterior)

law retirar_sucessor_preserva_instante_anterior:
  for +instante: Nat
  for +maximo: Nat
  for anterior: {Nat.is_lt(1n+instante, maximo) == True{} : Bool}
  {Nat.is_lt(instante, maximo) == True{} : Bool}
def retirar_sucessor_preserva_instante_anterior(instante, maximo, anterior):
  match instante maximo:
    case 0n 0n:
      F.absurdo_booleano({False{} == True{} : Bool}, anterior)
    case 1n+t 0n:
      F.absurdo_booleano({False{} == True{} : Bool}, anterior)
    case 0n 1n+m:
      {==}
    case 1n+t 1n+m:
      aumentar_maximo_preserva_instante_anterior(1n+t, m, anterior)

law saturar_intervalo_preserva_prazo_somado:
  for +inicio: Nat
  for +instante: Nat
  for +intervalo: Nat
  for +maximo: Nat
  for anterior: {Nat.is_lt(instante, maximo) == True{} : Bool}
  {Nat.is_ge(instante, Nat.add(inicio, Nat.min(intervalo, maximo))) ==
    Nat.is_ge(instante, Nat.add(inicio, intervalo)) : Bool}
def saturar_intervalo_preserva_prazo_somado(inicio, instante, intervalo, maximo, anterior):
  match inicio instante:
    case 0n _:
      saturar_prazo_preserva_expiracao(instante, intervalo, maximo, anterior)
    case 1n+i 0n:
      {==}
    case 1n+i 1n+t:
      saturar_intervalo_preserva_prazo_somado(i, t, intervalo, maximo,
        retirar_sucessor_preserva_instante_anterior(t, maximo, anterior))

law saturar_intervalo_e_soma_preserva_expiracao:
  for +inicio: Nat
  for +instante: Nat
  for +intervalo: Nat
  for +maximo: Nat
  for +anterior: {Nat.is_lt(instante, maximo) == True{} : Bool}
  {Nat.is_ge(instante, Nat.min(Nat.add(inicio, Nat.min(intervalo, maximo)), maximo)) ==
    Nat.is_ge(instante, Nat.add(inicio, intervalo)) : Bool}
def saturar_intervalo_e_soma_preserva_expiracao(inicio, instante, intervalo, maximo, anterior):
  Equal.trans(Bool,
    Nat.is_ge(instante, Nat.min(Nat.add(inicio, Nat.min(intervalo, maximo)), maximo)),
    Nat.is_ge(instante, Nat.add(inicio, Nat.min(intervalo, maximo))),
    Nat.is_ge(instante, Nat.add(inicio, intervalo)),
    saturar_prazo_preserva_expiracao(instante, Nat.add(inicio, Nat.min(intervalo, maximo)), maximo, anterior),
    saturar_intervalo_preserva_prazo_somado(inicio, instante, intervalo, maximo, anterior))

law minimo_sucessor_com_maximo:
  for maximo: Nat
  {Nat.min(1n+maximo, maximo) == maximo : Nat}
def minimo_sucessor_com_maximo(maximo):
  match maximo:
    case 0n:
      {==}
    case 1n+m:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.min(1n+m, m), m,
        minimo_sucessor_com_maximo(m))

law instante_anterior_ao_sucessor_nao_expirou:
  for instante: Nat
  {Nat.is_ge(instante, 1n+instante) == False{} : Bool}
def instante_anterior_ao_sucessor_nao_expirou(instante):
  match instante:
    case 0n:
      {==}
    case 1n+t:
      instante_anterior_ao_sucessor_nao_expirou(t)

# A hipotese estrita para tempo e necessaria: NO maximo, um prazo maior
# pode virar expirado ao saturar. Nao autoriza limitar o relogio real aqui.
law igualdade_no_maximo_nao_basta_para_saturar_prazo:
  for +maximo: Nat
  L.E<{Nat.is_ge(maximo, Nat.min(1n+maximo, maximo)) == True{} : Bool},
      {Nat.is_ge(maximo, 1n+maximo) == False{} : Bool}>
def igualdade_no_maximo_nao_basta_para_saturar_prazo(maximo):
  L.Ambos{Equal.trans(Bool,
    Nat.is_ge(maximo, Nat.min(1n+maximo, maximo)), Nat.is_ge(maximo, maximo), True{},
    Equal.cong(Nat, Bool, n => Nat.is_ge(maximo, n),
      Nat.min(1n+maximo, maximo), maximo, minimo_sucessor_com_maximo(maximo)),
    Nat.ge_refl(maximo)), instante_anterior_ao_sucessor_nao_expirou(maximo)}
