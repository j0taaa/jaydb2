# Cenarios alcancaveis de uma instancia: seed + conclusoes reais anteriores.
# Metateoria somente; os dados privados nao entram no Book de uma submissao.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Interface.bend as I
import ../contrato/Requisitos.bend as R
import ../contrato/Recursos.bend as X
import ../contrato/Semantica.bend as S
import ./HistoricoServico.bend as H

type Momento is Data:
  Inicializacao{}
  Atendimento{recepcao: X.Recepcao}

def de_momento(~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, H.Registro>, ~prova_inicial: String,
  m: Momento, +mundo: Nat) -> I.Cenario:
  match m:
    case Inicializacao{}: I.Inicializar{mundo, c, seed(Unit{}), prova_inicial}
    case Atendimento{r}: I.Atender{mundo, c, H.estado(historico(mundo), seed(Unit{})), r}

def canonico(~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, H.Registro>, ~momento: Nat -> Momento,
  ~prova_inicial: String, +mundo: Nat) -> I.Cenario:
  de_momento(c, seed, historico, prova_inicial, momento(mundo), mundo)

def EstadoDaChamada(x: I.Cenario) -> Type:
  match x:
    case I.Inicializar{m, c, s, pi}: Unit
    case I.Atender{m, c, s, r}: R.Valido(c, s)

def estado_do_momento(~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, H.Registro>, ~prova_inicial: String,
  m: Momento, +mundo: Nat, inicial: R.Valido(c, seed(Unit{})),
  fontes: H.Fontes(c, historico(mundo), seed(Unit{}))) ->
  EstadoDaChamada(de_momento(c, seed, historico, prova_inicial, m, mundo)):
  match m:
    case Inicializacao{}: Unit{}
    case Atendimento{r}:
      H.historico_preserva_validade(c, historico(mundo), seed(Unit{}), inicial, fontes)

# A unica validade recebida e a do seed; a publicada e uma conclusao da inducao.
law estado_de_cada_chamada_e_valido:
  for ~c: S.Configuracao
  for ~seed: Unit -> D.Estado
  for ~historico: Nat -> List<&2, H.Registro>
  for ~momento: Nat -> Momento
  for ~prova_inicial: String
  for +mundo: Nat
  for inicial: R.Valido(c, seed(Unit{}))
  for fontes: H.Fontes(c, historico(mundo), seed(Unit{}))
  EstadoDaChamada(canonico(c, seed, historico, momento, prova_inicial, mundo))
def estado_de_cada_chamada_e_valido(c, seed, historico, momento, prova_inicial, mundo, inicial, fontes):
  estado_do_momento(c, seed, historico, prova_inicial, momento(mundo), mundo, inicial, fontes)

