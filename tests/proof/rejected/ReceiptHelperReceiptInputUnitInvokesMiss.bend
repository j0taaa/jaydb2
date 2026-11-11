# Deliberately false receipt behavior; must reject at the proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/Receipts.bend as H

def done(r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Cell{value}}: S.Finish{value}
    case _: S.Refuse{D.VText{"bad result"}}

def missing() -> S.Action: S.Finish{D.VText{"miss"}}

law false:
  {H.input_seen("owner","r","op","input",missing(),done,S.UnitValue{}) == missing() : S.Action}
def false(): {==}
