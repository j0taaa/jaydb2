# The wire handle cannot replace the source identity used by administrator laws.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/RequestFacts.bend as I
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/Protocol.bend as P

law false_handle_is_original_source:
  {I.code(H.resolved(P.Request{"credential", "handle", D.VAbsent{}, ""},
    G.Entry{"instance", "handle", "original-source", "universal-proof", False{}, "seal"})) == "handle" : String}
def false_handle_is_original_source():
  {==}
