# Deliberately false receipt behavior; must reject at the proof body.
import Base
import ../../../library/Receipts.bend as H



law false_reject_receipt_binding_normalizes_unicode:
  {H.matches("op","é","op","é") == True{} : Bool}
def false_reject_receipt_binding_normalizes_unicode(): {==}
