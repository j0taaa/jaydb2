# Optional sequential row writes within the caller's existing transaction.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S

def written(next: S.Action, r: S.Return) -> S.Action:
  match r:
    case S.UnitValue{}: next
    case _: S.Refuse{D.VText{"unexpected write return"}}

def define_rows(+collection: D.Collection, rows: List<&2, D.Row>,
  done: S.Action) -> S.Action:
  match rows:
    case Nil{}: done
    case Con{D.Row{key, fields}, rest}:
      S.Access{D.DefineRow{collection, key, fields},
        r => written(define_rows(collection, rest, done), r)}
