# UnitValue is unreachable after a real read, but certification must cover it.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../contract/Logic.bend as L
import ../../../src/ReadOnly.bend as RO

def bad_continue(r: S.Return) -> S.Action:
  match r:
    case S.UnitValue{}: S.Access{D.RemoveRow{D.Application{"private"}, "key"}, r => S.Finish{D.VAbsent{}}}
    case S.Datum{obs}: S.Finish{D.VAbsent{}}

law bad_continuation:
  for r: S.Return
  RO.Action(2n, bad_continue(r))
def bad_continuation(r):
  match r:
    case S.UnitValue{}: L.Both{Unit{}, r => Unit{}}
    case S.Datum{obs}: Unit{}
