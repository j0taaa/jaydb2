import Base
import ../../../contrato/Bytes.bend as B
import ../../../src/Codec.bend as C

law falso:
  {C.conferir(Some{B.Numero64{0, 1}}, B.Numero64{0, 0}, B.Numero64{0, 1}) == C.Cabe{} : C.Conferencia}
def falso():
  {==}
