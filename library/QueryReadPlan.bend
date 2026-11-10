# Total source-state DATA meaning: inspect each requested named D.operate;
# keep its Reading event or the first ErrorOfData and stop. Ready payloads and
# status use independent field order/first-noncell classification, never Action
# evaluation, a continuation, Query.combine, or an assumed successful outcome.
import Base
import ./QuerySelectionModel.bend as M
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S

type Plan is Data:
  ReadsReady{problem: M.Problem,record: D.Value,events: List<&2,S.OperationEvent>}
  ReadsFailed{events: List<&2,S.OperationEvent>}

def observed(+op: D.Operation,name: String,+observation: D.Observation,tail: Plan) -> Plan:
  match tail:
    case ReadsReady{problem,record,events}: ReadsReady{M.head_problem(S.Datum{observation},problem),D.VRecord{name,M.payload(S.Datum{observation}),record},Con{S.OperationEvent{op,S.Reading{observation}},events}}
    case ReadsFailed{events}: ReadsFailed{Con{S.OperationEvent{op,S.Reading{observation}},events}}

def extend(+op: D.Operation,name: String,result: D.ResultOp,tail: Plan) -> Plan:
  match result:
    case D.FailureData{}: ReadsFailed{[S.OperationEvent{op,S.ErrorOfData{}}]}
    case D.Observed{observation}: observed(op,name,observation,tail)
    # Real named reads cannot change state: Operate proves this branch absent.
    case D.Changed{state}: ReadsFailed{[S.OperationEvent{op,S.ErrorOfData{}}]}

def plan(+schema: D.Schema,+state: D.State,+collection: D.Collection,+key: String,names: List<&2,String>) -> Plan:
  match names:
    case Nil{}: ReadsReady{M.Clear{},D.VRecordEmpty{},Nil{}}
    case Con{+name,tail}: extend(D.ReadCell{collection,key,name},name,D.operate(schema,state,D.ReadCell{collection,key,name}),plan(schema,state,collection,key,tail))
