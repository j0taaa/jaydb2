# Deliberately false receipt behavior; must reject at the proof body.
import Base
import ../../../library/Receipts.bend as H



law false:
  {H.matches("op","input","op","other") == True{} : Bool}
def false(): {==}
