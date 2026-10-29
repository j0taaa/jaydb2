# Preparacao original de limite justificado por tempo real.
# Nao exige medida de memoria, nao cria fatos nem conclui o host.
import Base
import ../contrato/LAWS.bend as Leis
import ../contrato/Interface.bend as I
import ../contrato/Recursos.bend as X
import ../contrato/Semantica.bend as S
import ../contrato/Requisitos.bend as R
import ../contrato/Logica.bend as L
import ./PrazosMedidos.bend as T
import ./Preparacao.bend as P
import ./ErroLimiteFixo.bend as B

def montar(-a: I.Ambiente, -k: String, -x: I.Cenario, -t: Nat,
  preparavel: P.Preparavel(S.limites(I.configuracao(x)), S.resposta_erro(S.Limite{})),
  justificada: I.RespostaJustificada(S.resposta_erro(S.Limite{}), a, k, x, t)) ->
  Leis.Regra7(I.Preparou{S.resposta_erro(S.Limite{}), B.bytes()}, a, k, x, t):
  match preparavel:
    case L.Ambos{payload, cabe}:
      L.Ambos{payload,
        L.Ambos{B.erro_limite_preparado_e_exatamente_a_mensagem_original(),
          L.Ambos{cabe, justificada}}}

law tempo_real_justifica_preparacao_original_sem_medida_de_memoria:
  for -a: I.Ambiente
  for -k: String
  for x: I.Cenario
  for -t: Nat
  for u: Nat
  for +etapa: X.Etapa
  for +inicio: Nat
  for +agora: Nat
  for limites: {R.limites_validos(S.limites(I.configuracao(x))) == True{} : Bool}
  for antes: {Nat.is_lt(u, t) == True{} : Bool}
  for monotono: {Nat.is_le(inicio, agora) == True{} : Bool}
  for mediu: I.Acontece(a, k, x, u, I.Mediu{X.Medicao{X.Tempo{etapa}, Nat.sub(agora, inicio)}})
  for real: I.MedicaoReal(a, k, x, u, X.Medicao{X.Tempo{etapa}, Nat.sub(agora, inicio)})
  for atingiu: {Nat.is_ge(agora, Nat.add(inicio, X.limite_tempo(etapa, S.limites(I.configuracao(x))))) == True{} : Bool}
  L.E<Leis.Regra7(I.Preparou{S.resposta_erro(S.Limite{}), B.bytes()}, a, k, x, t),
    I.MedicaoReal(a, k, x, u, X.Medicao{X.Tempo{etapa}, Nat.sub(agora, inicio)})>
def tempo_real_justifica_preparacao_original_sem_medida_de_memoria(a, k, x, t, u,
    etapa, inicio, agora, limites, antes, monotono, mediu, real, atingiu):
  +l = S.limites(I.configuracao(x))
  +orcamento = X.limite_tempo(etapa, l)
  excedeu = Equal.trans(Bool,
    Nat.is_ge(Nat.sub(agora, inicio), orcamento),
    Nat.is_ge(agora, Nat.add(inicio, orcamento)), True{},
    Equal.sym(Bool, Nat.is_ge(agora, Nat.add(inicio, orcamento)),
      Nat.is_ge(Nat.sub(agora, inicio), orcamento),
      T.comparar_prazo_desde_os_instantes_reais(inicio, agora, orcamento, monotono)), atingiu)
  L.Ambos{montar(a, k, x, t,
    P.erro_preparavel(S.Limite{}, l, limites, Unit{}),
    L.Direita{L.Esquerda{(X.Medicao{X.Tempo{etapa}, Nat.sub(agora, inicio)},
      L.Ambos{(u, L.Ambos{antes, mediu}), excedeu})}}), real}
