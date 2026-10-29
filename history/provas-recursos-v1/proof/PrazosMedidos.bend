# Ponte entre os instantes absolutos e a quantidade temporal do contrato.
# Nao afirma que o relogio foi consultado nem fabrica MedicaoReal.
import Base
import ./Prazos.bend as P
import ./DominiosFisicos.bend as F
import ./CodecSomasOrdem.bend as O
import ../contrato/Semantica.bend as S
import ../contrato/Recursos.bend as X
import ../contrato/Interface.bend as I
import ../contrato/Logica.bend as L

law orcamento_positivo_no_inicio_nao_expirou:
  for inicio: Nat
  for +orcamento: Nat
  {Nat.is_ge(inicio, Nat.add(inicio, 1n+orcamento)) == False{} : Bool}
def orcamento_positivo_no_inicio_nao_expirou(inicio, orcamento):
  match inicio:
    case 0n:
      {==}
    case 1n+i:
      orcamento_positivo_no_inicio_nao_expirou(i, orcamento)

law renovar_epoch_no_prazo_original_oculta_expiracao:
  for +inicio: Nat
  for +orcamento: Nat
  L.E<{Nat.is_ge(Nat.add(inicio, 1n+orcamento), Nat.add(inicio, 1n+orcamento)) == True{} : Bool},
      {Nat.is_ge(Nat.add(inicio, 1n+orcamento),
        Nat.add(Nat.add(inicio, 1n+orcamento), 1n+orcamento)) == False{} : Bool}>
def renovar_epoch_no_prazo_original_oculta_expiracao(inicio, orcamento):
  L.Ambos{Nat.ge_refl(Nat.add(inicio, 1n+orcamento)),
    orcamento_positivo_no_inicio_nao_expirou(Nat.add(inicio, 1n+orcamento), orcamento)}

law comparar_prazo_desde_os_instantes_reais:
  for +inicio: Nat
  for +agora: Nat
  for +orcamento: Nat
  for monotono: {Nat.is_le(inicio, agora) == True{} : Bool}
  {Nat.is_ge(agora, Nat.add(inicio, orcamento)) ==
    Nat.is_ge(Nat.sub(agora, inicio), orcamento) : Bool}
def comparar_prazo_desde_os_instantes_reais(inicio, agora, orcamento, monotono):
  Equal.trans(Bool,
    Nat.is_ge(agora, Nat.add(inicio, orcamento)),
    Nat.is_ge(Nat.add(inicio, Nat.sub(agora, inicio)), Nat.add(inicio, orcamento)),
    Nat.is_ge(Nat.sub(agora, inicio), orcamento),
    Equal.cong(Nat, Bool, n => Nat.is_ge(n, Nat.add(inicio, orcamento)),
      agora, Nat.add(inicio, Nat.sub(agora, inicio)),
      Equal.sym(Nat, Nat.add(inicio, Nat.sub(agora, inicio)), agora,
        O.nat_decompor_limite(inicio, agora, monotono))),
    P.prazo_absoluto_e_intervalo_expiram_juntos(inicio, Nat.sub(agora, inicio), orcamento))

law prazo_saturado_equivale_ao_tempo_decorrido:
  for +inicio: Nat
  for +agora: Nat
  for +orcamento: Nat
  for +maximo: Nat
  for monotono: {Nat.is_le(inicio, agora) == True{} : Bool}
  for anterior: {Nat.is_lt(agora, maximo) == True{} : Bool}
  {Nat.is_ge(agora, Nat.min(Nat.add(inicio, Nat.min(orcamento, maximo)), maximo)) ==
    Nat.is_ge(Nat.sub(agora, inicio), orcamento) : Bool}
def prazo_saturado_equivale_ao_tempo_decorrido(inicio, agora, orcamento, maximo, monotono, anterior):
  Equal.trans(Bool,
    Nat.is_ge(agora, Nat.min(Nat.add(inicio, Nat.min(orcamento, maximo)), maximo)),
    Nat.is_ge(agora, Nat.add(inicio, orcamento)),
    Nat.is_ge(Nat.sub(agora, inicio), orcamento),
    F.saturar_intervalo_e_soma_preserva_expiracao(inicio, agora, orcamento, maximo, anterior),
    comparar_prazo_desde_os_instantes_reais(inicio, agora, orcamento, monotono))

law prazo_atingido_fornece_quantidade_temporal_original:
  for c: S.Configuracao
  for +etapa: X.Etapa
  for +inicio: Nat
  for +agora: Nat
  for monotono: {Nat.is_le(inicio, agora) == True{} : Bool}
  for atingiu: {Nat.is_ge(agora, Nat.add(inicio, X.limite_tempo(etapa, S.limites(c)))) == True{} : Bool}
  X.LimiteAtingido(c, X.Medicao{X.Tempo{etapa}, Nat.sub(agora, inicio)})
def prazo_atingido_fornece_quantidade_temporal_original(c, etapa, inicio, agora, monotono, atingiu):
  +limites = S.limites(c)
  Equal.trans(Bool,
    Nat.is_ge(Nat.sub(agora, inicio), X.limite_tempo(etapa, limites)),
    Nat.is_ge(agora, Nat.add(inicio, X.limite_tempo(etapa, limites))), True{},
    Equal.sym(Bool,
      Nat.is_ge(agora, Nat.add(inicio, X.limite_tempo(etapa, limites))),
      Nat.is_ge(Nat.sub(agora, inicio), X.limite_tempo(etapa, limites)),
      comparar_prazo_desde_os_instantes_reais(inicio, agora,
        X.limite_tempo(etapa, limites), monotono)), atingiu)

law medicao_temporal_real_justifica_limite:
  for -a: I.Ambiente
  for -k: String
  for x: I.Cenario
  for -t: Nat
  for u: Nat
  for +etapa: X.Etapa
  for +inicio: Nat
  for +agora: Nat
  for antes: {Nat.is_lt(u, t) == True{} : Bool}
  for monotono: {Nat.is_le(inicio, agora) == True{} : Bool}
  for mediu: I.Acontece(a, k, x, u, I.Mediu{X.Medicao{X.Tempo{etapa}, Nat.sub(agora, inicio)}})
  for real: I.MedicaoReal(a, k, x, u, X.Medicao{X.Tempo{etapa}, Nat.sub(agora, inicio)})
  for atingiu: {Nat.is_ge(agora, Nat.add(inicio, X.limite_tempo(etapa, S.limites(I.configuracao(x))))) == True{} : Bool}
  L.E<I.RespostaJustificada(S.resposta_erro(S.Limite{}), a, k, x, t),
    I.MedicaoReal(a, k, x, u, X.Medicao{X.Tempo{etapa}, Nat.sub(agora, inicio)})>
def medicao_temporal_real_justifica_limite(a, k, x, t, u, etapa, inicio, agora, antes, monotono, mediu, real, atingiu):
  L.Ambos{L.Direita{L.Esquerda{(X.Medicao{X.Tempo{etapa}, Nat.sub(agora, inicio)},
    L.Ambos{(u, L.Ambos{antes, mediu}),
      prazo_atingido_fornece_quantidade_temporal_original(I.configuracao(x), etapa,
        inicio, agora, monotono, atingiu)})}}, real}
