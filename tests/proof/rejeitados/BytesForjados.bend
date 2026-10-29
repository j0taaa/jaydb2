import Base
import ../../../contrato/Protocolo.bend as P
import ../../../contrato/Semantica.bend as S
import ../Certificado.bend as T

law falso:
  P.Mensagem(S.resposta_valor(T.resposta()), [0])
def falso():
  {==}
