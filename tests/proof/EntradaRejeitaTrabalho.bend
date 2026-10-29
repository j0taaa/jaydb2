# Mutacao deliberada: deve falhar em falso, com corpo preenchido.
import Base
import ../../contrato/Dados.bend as D
import ../../contrato/Protocolo.bend as P
import ../../contrato/Semantica.bend as S
import ../../src/Entrada.bend as E
import ./Entrada.bend as F

law falso:
  {D.autenticar(D.Estado{Nil{}, [F.usuario("a", ""), F.usuario("b", "")]}, "") ==
    None{} : Maybe<&2, D.Contexto>}
def falso():
  {==}
