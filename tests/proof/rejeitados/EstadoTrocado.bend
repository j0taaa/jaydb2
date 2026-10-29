import Base
import ../../../contrato/Dados.bend as D
import ../../../src/Estado.bend as E
import ../Certificado.bend as T

law falso:
  {E.decodificar(D.estado_valor(T.inicial()), S_esquema()) == Some{D.Estado{Nil{}, Nil{}}} : Maybe<&2, D.Estado>}
def S_esquema() -> D.Esquema:
  D.Esquema{Nil{}}
def falso():
  {==}
