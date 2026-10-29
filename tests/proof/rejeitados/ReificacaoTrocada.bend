import Base
import ../../../contrato/Dados.bend as D
import ../../../src/Reificacao.bend as R

law falso:
  {R.argumentos(R.texto([3, 0, 0, 0, 0, 0, 0, 0, 1]), 0, 9) == D.VInt{0, 2} : D.Valor}
def falso():
  {==}
