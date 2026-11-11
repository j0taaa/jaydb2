# Deliberately false receipt behavior; must reject at the proof body.
import Base
import ../../../library/Receipts.bend as H



law false:
  {H.matches("op","é","op","é") == True{} : Bool}
def false(): {==}
