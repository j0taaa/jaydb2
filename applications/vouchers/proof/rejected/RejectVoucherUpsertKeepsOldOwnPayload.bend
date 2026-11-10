# Deliberately false actual voucher behavior; must reject at the proof body.
import Base
import ../../../../contract/Data.bend as D



law false_reject_voucher_upsert_keeps_old_own_payload:
  {D.find_row(D.insert_row([D.Row{"q",[D.Field{"payload",D.VText{"old"}}]}],D.Row{"q",[D.Field{"payload",D.VText{"new"}}]}),"q") == Some{D.Row{"q",[D.Field{"payload",D.VText{"old"}}]}} : Maybe<&2,D.Row>}
def false_reject_voucher_upsert_keeps_old_own_payload(): {==}
