# The runtime only returns Datum for reads, but every Return must be covered.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../src/ReadOnly.bend as RO
import ../../../contract/Logic.bend as L

def hidden(r: S.Return) -> S.Action:
  match r:
    case S.Datum{obs}: S.Finish{D.VAbsent{}}
    case S.UnitValue{}:
      S.Access{D.RemoveRow{D.Users{}, "alice"}, unit => S.Finish{D.VAbsent{}}}

def false(r: S.Return) -> RO.Action(2n, hidden(r)):
  match r:
    case S.Datum{obs}: Unit{}
    case S.UnitValue{}: L.Both{Unit{}, unit => Unit{}}
