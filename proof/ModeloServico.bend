# Instancia o protocolo com os cenarios alcancaveis da mesma configuracao.
# Os demais campos sao os contratos independentes das ferramentas e do ambiente.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Interface.bend as I
import ../contrato/Semantica.bend as S
import ./FonteServico.bend as F
import ./CenariosServico.bend as C
import ./HistoricoServico.bend as H

def com_cenarios(base: F.Fonte, cenarios: Nat -> I.Cenario) -> F.Fonte:
  match base:
    case F.Fonte{id, k, anteriores, iniciais, chamadas, programa, elabora, deriva, processavel, falha, entrega}:
      F.Fonte{id, k, cenarios, iniciais, chamadas, programa, elabora, deriva, processavel, falha, entrega}

def fonte(~base: F.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, H.Registro>, ~momento: Nat -> C.Momento,
  ~prova_inicial: String) -> F.Fonte:
  com_cenarios(base, mundo => C.canonico(c, seed, historico, momento, prova_inicial, mundo))

def consulta_substituida(base: F.Fonte, -cenarios: Nat -> I.Cenario, -mundo: Nat) ->
  {F.cenario(com_cenarios(base, cenarios), mundo) == cenarios(mundo) : I.Cenario}:
  match base:
    case F.Fonte{id, k, cs, ins, hs, ps, el, de, pr, fr, ef}: {==}

law cenario_do_modelo:
  for ~base: F.Fonte
  for ~c: S.Configuracao
  for ~seed: Unit -> D.Estado
  for ~historico: Nat -> List<&2, H.Registro>
  for ~momento: Nat -> C.Momento
  for ~prova_inicial: String
  for -mundo: Nat
  {F.cenario(fonte(base, c, seed, historico, momento, prova_inicial), mundo) ==
    C.canonico(c, seed, historico, momento, prova_inicial, mundo) : I.Cenario}
def cenario_do_modelo(base, c, seed, historico, momento, prova_inicial, mundo):
  consulta_substituida(base, m => C.canonico(c, seed, historico, momento, prova_inicial, m), mundo)
