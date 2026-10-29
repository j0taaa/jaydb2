# Adaptador puro da maquina ao loop do runtime: nenhuma repeticao de acessos.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Semantica.bend as S
import ./Nucleo.bend as N
import ./Transporte.bend as T

type EstadoExecucao is Type:
  EstadoExecucao{inicial: D.Estado, maquina: N.Maquina}

type Iteracao is Type:
  Continuar{estado: EstadoExecucao}
  Preparar{estado: EstadoExecucao}
  Encerrar{bytes: List<&2, U32>}
  Inconsistente{}

def iniciar(programa: S.Programa, contexto: D.Contexto, argumentos: D.Valor,
  +inicial: D.Estado) -> EstadoExecucao:
  EstadoExecucao{inicial, N.iniciar(programa, contexto, argumentos, inicial)}

def pacote_pronto(bytes: Maybe<&2, List<&2, U32>>) -> Iteracao:
  match bytes:
    case None{}:
      Inconsistente{}
    case Some{bs}:
      Encerrar{Con{1, bs}}

def estado_codificado(estado: Maybe<&2, List<&2, U32>>,
  resposta: List<&2, U32>) -> Iteracao:
  match estado:
    case None{}:
      Inconsistente{}
    case Some{bs}:
      pacote_pronto(T.juntar(bs, resposta))

def concluir(conclusao: N.Conclusao) -> Iteracao:
  match conclusao:
    case N.Conclusao{estado, S.Resposta{S.Sucesso{}, valor}, bytes}:
      estado_codificado(P.codificar(D.estado_valor(estado)), bytes)
    case N.Conclusao{estado, S.Resposta{status, valor}, bytes}:
      Encerrar{Con{0, bytes}}

def preparada(preparada: Maybe<&2, N.Preparada>, inicial: D.Estado) -> Iteracao:
  match preparada:
    case None{}:
      Inconsistente{}
    case Some{p}:
      concluir(N.concluir(p, inicial))

def apos_passo(maquina: N.Maquina, inicial: D.Estado) -> Iteracao:
  match maquina:
    case N.EmCurso{w, a, ts}:
      Continuar{EstadoExecucao{inicial, N.EmCurso{w, a, ts}}}
    case N.Parada{w, ts, r}:
      Preparar{EstadoExecucao{inicial, N.Parada{w, ts, r}}}

def avancar(estado: EstadoExecucao, configuracao: S.Configuracao) -> Iteracao:
  match estado:
    case EstadoExecucao{inicial, N.EmCurso{w, acao, eventos}}:
      apos_passo(N.avancar(N.EmCurso{w, acao, eventos}, S.esquema(configuracao)), inicial)
    case EstadoExecucao{inicial, N.Parada{w, eventos, resposta}}:
      preparada(N.preparar(N.Parada{w, eventos, resposta}, configuracao), inicial)

law recusa_nao_emite_estado_para_publicacao:
  for -estado: D.Estado
  for -valor: D.Valor
  for -bytes: List<&2, U32>
  {concluir(N.Conclusao{estado, S.Resposta{S.Recusa{}, valor}, bytes}) ==
    Encerrar{Con{0, bytes}} : Iteracao}
def recusa_nao_emite_estado_para_publicacao(estado, valor, bytes):
  {==}
