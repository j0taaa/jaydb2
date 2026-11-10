# DATA source plan for fixed Index.visit calls in ORIGINAL key-occurrence order.
# No visitor Action or callback outcome is a premise. Stops discard subsequent
# source DATA (not issued events); Some payloads preserve repeats and order.
import Base
import ./IndexVisitProofs.bend as Visit
import ./QueryFilterMapModel.bend as Projection
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S

type MapPlan is Data:
  ScanYield{items: List<&2,D.Value>,events: List<&2,S.OperationEvent>}
  ScanDenied{response: S.Response,events: List<&2,S.OperationEvent>}

def events(first: List<&2,S.OperationEvent>,later: List<&2,S.OperationEvent>) -> List<&2,S.OperationEvent>:
  match first:
    case Nil{}: later
    case Con{event,tail}: Con{event,events(tail,later)}

def combine(head: Visit.VisitPlan,tail: MapPlan) -> MapPlan:
  match head tail:
    case Visit.VisitDenied{response,seen} tail: ScanDenied{response,seen}
    case Visit.VisitYield{item,seen} ScanYield{items,later}: ScanYield{Projection.push(item,items),events(seen,later)}
    case Visit.VisitYield{item,seen} ScanDenied{response,later}: ScanDenied{response,events(seen,later)}

def plan(keys: List<&2,String>,+schema: D.Schema,+state: D.State,+collection: D.Collection,+value: String) -> MapPlan:
  match keys:
    case Nil{}: ScanYield{Nil{},Nil{}}
    case Con{key,tail}: combine(Visit.plan(schema,state,collection,key,value),plan(tail,schema,state,collection,value))

def owned(keys: List<&2,String>) -> Nat:
  match keys:
    case Nil{}: 0n
    case Con{key,tail}: 2n+owned(tail)

def depth(keys: List<&2,String>,remaining: Nat) -> Nat:
  1n+Nat.add(owned(keys),remaining)
