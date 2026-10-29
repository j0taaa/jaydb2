# Mutacao deliberada: deve falhar em falso, com corpo preenchido.
import Base
import ../../contrato/Dados.bend as D
import ../../contrato/Protocolo.bend as P
import ../../contrato/Semantica.bend as S
import ../../src/Entrada.bend as E
import ./Entrada.bend as F

law falso:
  {E.decodificar(F.pacote(F.estado_bytes(), Nil{}), F.esquema(), F.limites()) ==
    E.Pronta{F.publicado(), F.requisicao()} : E.PreAutenticacao}
def falso():
  {==}
