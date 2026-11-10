# Deliberately false actual voucher behavior; must reject at the proof body.
import Base
import ../../../../contract/Data.bend as D



law false_reject_voucher_upsert_frames_its_same_key_without_exclusion:
  {D.find_row(D.insert_row([D.Row{"q",Nil{}}],D.Row{"q",[D.Field{"new",D.VBool{True{}}}]}),"q") == D.find_row([D.Row{"q",Nil{}}],"q") : Maybe<&2,D.Row>}
def false_reject_voucher_upsert_frames_its_same_key_without_exclusion(): {==}
