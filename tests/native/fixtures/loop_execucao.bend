import Base
import ../../../native/effects.bend as Native
import ../../../src/Execucao.bend as E
import ../../../src/Nucleo.bend as N
import ../../../contrato/Dados.bend as D
import ../../../contrato/Semantica.bend as S

def step(state: E.EstadoExecucao) -> Native.Iteracao<E.EstadoExecucao>:
  match state:
    case E.EstadoExecucao{inicial, N.EmCurso{w, acao, eventos}}:
      Native.Inconsistente{}
    case E.EstadoExecucao{inicial, N.Parada{w, eventos, resposta}}:
      Native.Encerrar{[7, 0, 255]}

def main() -> IO(Unit):
  do IO<Unit>:
    Unit <- Native.enter(1)
    input : List<&2, U32> <- Native.read()
    Native.loop(E.EstadoExecucao, step,
      E.EstadoExecucao{D.Estado{Nil{}, Nil{}},
        N.Parada{D.Estado{Nil{}, Nil{}}, Nil{}, S.Resposta{S.Recusa{}, D.VAusente{}}}})
