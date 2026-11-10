# Deliberately false functional claim; must reject at its proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I

law false_reject_mixed_arity_always_disjoint:
  {String.eq(D.row_key(I.unique(["x","y"],"a")),D.row_key(I.nonunique(["x"],"y"))) == False{} : Bool}
def false_reject_mixed_arity_always_disjoint(): {==}
