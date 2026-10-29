# Bytes pre-preparados pela fronteira C, comparados ao encoder ORIGINAL.
# Nao recebe uma equivalencia de codec como premissa.
import Base
import ../contrato/Semantica.bend as S
import ../contrato/Protocolo.bend as P

def bytes() -> List<&2, U32>:
  [0, 0, 0, 0, 0, 0, 0, 54, 6, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 6, 115, 116, 97, 116, 117, 115, 4, 0, 0, 0, 0, 0, 0, 0, 6, 108, 105, 109, 105, 116, 101, 4, 0, 0, 0, 0, 0, 0, 0, 5, 118, 97, 108, 111, 114, 0]

law erro_limite_preparado_e_exatamente_a_mensagem_original:
  {P.enquadrar(S.resposta_valor(S.resposta_erro(S.Limite{}))) == Some{bytes()} : Maybe<&2, List<&2, U32>>}
def erro_limite_preparado_e_exatamente_a_mensagem_original():
  {==}
