# Fronteira pequena para medidas/falhas reais. Nao define MedicaoReal,
# nao estima uma alocacao futura e nao fabrica um Ambiente.
import Base
import ../contrato/Semantica.bend as S
import ../contrato/Requisitos.bend as R
import ../contrato/Recursos.bend as X
import ../contrato/Interface.bend as I
import ../contrato/Logica.bend as L

law nat_comparar_consigo:
  for n: Nat
  {Nat.cmp(n, n) == EQ{} : Cmp}
def nat_comparar_consigo(n):
  match n:
    case 0n:
      {==}
    case 1n+k:
      nat_comparar_consigo(k)

law memoria_igual_ao_teto_e_permitida:
  for c: S.Configuracao
  {X.excedeu(c, X.Medicao{X.Memoria{}, R.limite_memoria(S.limites(c))}) == False{} : Bool}
def memoria_igual_ao_teto_e_permitida(c):
  Equal.cong(Cmp, Bool, x => Cmp.is_gt(x),
    Nat.cmp(R.limite_memoria(S.limites(c)), R.limite_memoria(S.limites(c))), EQ{},
    nat_comparar_consigo(R.limite_memoria(S.limites(c))))

law tempo_igual_ao_prazo_expirou:
  for c: S.Configuracao
  for +etapa: X.Etapa
  {X.excedeu(c, X.Medicao{X.Tempo{etapa}, X.limite_tempo(etapa, S.limites(c))}) == True{} : Bool}
def tempo_igual_ao_prazo_expirou(c, etapa):
  Equal.cong(Cmp, Bool, x => Cmp.is_ge(x),
    Nat.cmp(X.limite_tempo(etapa, S.limites(c)), X.limite_tempo(etapa, S.limites(c))), EQ{},
    nat_comparar_consigo(X.limite_tempo(etapa, S.limites(c))))

law excesso_real_de_memoria_justifica_limite:
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for -t: Nat
  for u: Nat
  for n: Nat
  for antes: {Nat.is_lt(u, t) == True{} : Bool}
  for mediu: I.Acontece(a, k, x, u, I.Mediu{X.Medicao{X.Memoria{}, n}})
  for real: I.MedicaoReal(a, k, x, u, X.Medicao{X.Memoria{}, n})
  for excedeu: {Nat.is_gt(n, R.limite_memoria(S.limites(I.configuracao(x)))) == True{} : Bool}
  L.E<I.RespostaJustificada(S.resposta_erro(S.Limite{}), a, k, x, t),
    I.MedicaoReal(a, k, x, u, X.Medicao{X.Memoria{}, n})>
def excesso_real_de_memoria_justifica_limite(a, k, x, t, u, n, antes, mediu, real, excedeu):
  L.Ambos{L.Direita{L.Esquerda{(X.Medicao{X.Memoria{}, n},
    L.Ambos{(u, L.Ambos{antes, mediu}), excedeu})}}, real}

law falha_real_de_ferramenta_justifica_falha:
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for -t: Nat
  for u: Nat
  for etapa: X.Etapa
  for id: String
  for fatal: Bool
  for antes: {Nat.is_lt(u, t) == True{} : Bool}
  for ocorreu: I.Acontece(a, k, x, u, I.FalhouAmbiente{etapa, id, fatal})
  for real: I.FalhaReal(a, k, x, u, etapa, id, fatal)
  L.E<I.RespostaJustificada(S.resposta_erro(S.Falha{}), a, k, x, t),
    I.FalhaReal(a, k, x, u, etapa, id, fatal)>
def falha_real_de_ferramenta_justifica_falha(a, k, x, t, u, etapa, id, fatal, antes, ocorreu, real):
  L.Ambos{(etapa, id, fatal, u, L.Ambos{antes, ocorreu}), real}
