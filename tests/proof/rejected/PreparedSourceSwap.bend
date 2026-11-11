# The wire handle cannot replace the source identity used by administrator laws.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/RequestFacts.bend as I
import ../../../src/Prepared.bend as H
import ../../../contract/Protocol.bend as P

law false:
  {I.code(H.resolve_request(P.Request{"credential", "handle", D.VAbsent{}, ""},
    "original-source", "universal-proof")) == "handle" : String}
def false():
  {==}
