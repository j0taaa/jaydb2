# Deliberately false functional claim; must reject at its proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I

law false:
  {String.eq(D.row_key(I.unique(["x"],"a")),D.row_key(I.unique(["x"],"b"))) == False{} : Bool}
def false(): {==}
