import Base
import ../../../contract/Protocol.bend as P
import ../../../contract/Semantics.bend as S
law false:
  {P.frame(S.response_value(S.response_error(S.Certificate{}))) == Some{Nil{}} : Maybe<&2, List<&2, U32>>}
def false(): {==}
