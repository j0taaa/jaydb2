# Intended false proof: tag7 cannot be reinterpreted as an ordinary request.
import Base
import ../../../contract/Protocol.bend as P

law false:
  for +request: P.Request
  for +tail: List<&2, U32>
  P.Encoding(P.request_value(request), Con{7, tail})
def false(request, tail):
  {==}
