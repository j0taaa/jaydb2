# A malformed message must keep its Input error ahead of authentication.
import Base
import ../../../proof/Preprocessing.bend as Route
import ../../../contract/Semantics.bend as S
import ../../../src/Input.bend as E
import ../../../src/Messages.bend as M

law false:
  {Route.gated(E.ErrorMessage{S.Input{}}) == M.error(S.Authentication{}) : List<&2, U32>}
def false():
  {==}
