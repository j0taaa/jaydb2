# Deliberately false functional claim; must reject at its proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I

law false_reject_nonunique_target_lost:
  {String.eq(D.row_key(I.nonunique(["x"],"a")),D.row_key(I.nonunique(["x"],"b"))) == True{} : Bool}
def false_reject_nonunique_target_lost(): {==}
