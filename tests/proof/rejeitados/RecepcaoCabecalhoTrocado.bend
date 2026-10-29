import Base
import ../../../contrato/Bytes.bend as B
import ../../../contrato/Recursos.bend as X
import ../../../proof/RecepcaoLimites.bend as Q

# Uma declaracao de zero nao pode ser substituida pela contagem um.
law falso:
  {X.declarado_igual(0,0,1n) == True{} : Bool}
def falso():
  Q.cabecalho_medido_estabelece_declaracao_original(0,0,1n,{==})
