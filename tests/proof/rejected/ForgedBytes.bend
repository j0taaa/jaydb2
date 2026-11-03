import Base
import ../../../contract/Protocol.bend as P
import ../../../contract/Semantics.bend as S
import ../Certificate.bend as T

law false:
  P.Message(S.response_value(T.response()), [0])
def false():
  {==}
