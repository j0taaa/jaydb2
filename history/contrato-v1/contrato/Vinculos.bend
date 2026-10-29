# Ligacoes entre operacoes REAIS do programa e seus prefixos semanticos.
# Os instantes sao posicoes da semantica do ambiente, nao tempos fisicos.
# Um snapshot nao exige um log armazenado pelo servidor.
import Base
import ./Logica.bend as L
import ./Dados.bend as D
import ./Protocolo.bend as P
import ./Semantica.bend as S
import ./Interface.bend as I

# Uma chamada concluida nao pode voltar a executar codigo do solicitante.
def SemConclusaoAnterior(-a: I.Ambiente, -k: String, -x: I.Cenario,
  -t: Nat) -> Type:
  @resposta: S.Resposta -> @publicado: D.Estado -> @fecha: Bool ->
    I.Antes(a, k, x, t, I.Concluiu{resposta, publicado, fecha}) -> Empty

# Um percurso Final e terminal mesmo antes de preparar/entregar a resposta.
def PrefixosNaoTerminaram(-a: I.Ambiente, -k: String, -x: I.Cenario,
  -t: Nat) -> Type:
  @req: P.Requisicao -> @ctx: D.Contexto -> @programa: S.Programa ->
    @trabalho: D.Estado -> @eventos: List<&2, S.Evento> -> @resposta: S.Resposta ->
      I.Antes(a, k, x, t,
        I.Avaliou{req, ctx, programa, S.Final{trabalho, eventos, resposta}}) -> Empty

def Janela(-antes: Nat, -operacao: Nat, -depois: Nat) -> Type:
  L.E<{Nat.is_lt(antes, operacao) == True{} : Bool},
    {Nat.is_lt(operacao, depois) == True{} : Bool}>

# Alem de ligar cada operacao a um evento, impede que duas operacoes
# reais diferentes usem a mesma transicao de um unico evento como prova.
def UnicaOperacaoNaJanela(-a: I.Ambiente, -k: String, -x: I.Cenario,
  -antes: Nat, -depois: Nat, -t: Nat, -esquema: D.Esquema,
  -estado: D.Estado, -operacao: D.Operacao, -resultado: D.ResultadoOp) -> Type:
  @u: Nat -> @e2: D.Esquema -> @s2: D.Estado ->
    @o2: D.Operacao -> @r2: D.ResultadoOp ->
      {Nat.is_lt(antes, u) == True{} : Bool} ->
      {Nat.is_lt(u, depois) == True{} : Bool} ->
      I.Acontece(a, k, x, u, I.Operou{e2, s2, o2, r2}) ->
        L.E<{u == t : Nat},
          {I.Operou{e2, s2, o2, r2} ==
            I.Operou{esquema, estado, operacao, resultado} : I.Fato}>

# O evento nao esconde ausencia, erros ou escritas sem efeito.
# Um resultado de escrita nao aparece como observacao do estado anterior.
def AposOperacao(resultado: D.ResultadoOp, -estado: D.Estado,
  -operacao: D.Operacao, -eventos: List<&2, S.Evento>, -apos: S.Percurso) -> Type:
  match resultado:
    case D.FalhaDados{}:
      {apos == S.Final{estado,
        S.acrescentar(eventos, S.Evento{operacao, S.ErroDeDados{}}),
        S.Resposta{S.Dados{}, D.VAusente{}}} : S.Percurso}
    case D.Observado{observacao}:
      L.E<{S.estado_percurso(apos) == estado : D.Estado},
        {S.eventos_percurso(apos) ==
          S.acrescentar(eventos, S.Evento{operacao, S.Leitura{observacao}})
            : List<&2, S.Evento>}>
    case D.Alterado{trabalho}:
      L.E<{S.estado_percurso(apos) == trabalho : D.Estado},
        {S.eventos_percurso(apos) ==
          S.acrescentar(eventos, S.Evento{operacao, S.Escrita{}})
            : List<&2, S.Evento>}>

def OperacaoVinculada(-a: I.Ambiente, -k: String, -x: I.Cenario,
  -t: Nat, -esquema: D.Esquema, -estado: D.Estado,
  -operacao: D.Operacao, -resultado: D.ResultadoOp) -> Type:
  &req: P.Requisicao -> &ctx: D.Contexto -> &programa: S.Programa ->
    &eventos: List<&2, S.Evento> -> &antes: Nat -> &depois: Nat ->
      &apos: S.Percurso ->
        L.E<{esquema == S.esquema(I.configuracao(x)) : D.Esquema},
          L.E<Janela(antes, t, depois),
            L.E<I.Acontece(a, k, x, antes,
              I.Avaliou{req, ctx, programa, S.Prefixo{estado, eventos}}),
              L.E<I.Acontece(a, k, x, depois,
                I.Avaliou{req, ctx, programa, apos}),
                L.E<AposOperacao(resultado, estado, operacao, eventos, apos),
                  UnicaOperacaoNaJanela(a, k, x, antes, depois, t,
                    esquema, estado, operacao, resultado)>>>>>
