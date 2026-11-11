# Deliberately false functional claim; must reject at its proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../library/Key.bend as K

law false:
  {D.unicode_valid(K.encode([SCon{Chr{55296},SNil{}}])) == True{} : Bool}
def false(): {==}
