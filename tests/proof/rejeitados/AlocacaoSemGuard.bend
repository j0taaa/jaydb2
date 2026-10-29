import Base
import ../../../contrato/Bytes.bend as B
import ../../../src/Codec.bend as C
import ../../../proof/AlocacoesComprimentos.bend as A

law falso:
  {A.em_construcao(C.abrir_conferido(C.Curto{}, C.Texto{}, B.Numero64{0, 1}, C.Raiz{})) == True{} : Bool}
def falso():
  {==}
