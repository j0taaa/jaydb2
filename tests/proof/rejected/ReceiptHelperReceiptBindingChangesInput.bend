# Deliberately false receipt behavior; must reject at the proof body.
import Base
import ../../../library/Receipts.bend as H



law false_reject_receipt_binding_changes_input:
  {H.matches("op","input","op","other") == True{} : Bool}
def false_reject_receipt_binding_changes_input(): {==}
