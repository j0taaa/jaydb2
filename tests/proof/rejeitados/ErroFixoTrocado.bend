import Base
import ../../../proof/ErrosFixos.bend as F
import ../../../contrato/Semantica.bend as S
import ../../../contrato/Protocolo.bend as P

law falso:
  {P.enquadrar(S.resposta_valor(S.resposta_erro(S.Entrada{}))) == Some{F.bytes(F.Certificado{})} : Maybe<&2, List<&2, U32>>}

def falso():
  {==}
