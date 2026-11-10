# A finite DATA account of the three named source reads and early stopping.
# It contains no Action, continuation, trace, policy or desired final outcome.
# The pinned pure Return classifier is used with its independent exact literal
# meaning proved in Adapters, rather than pretending to add a second decoder.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Receipts.bend as H

type Plan is Data:
  ReceiptMissing{events: List<&2,S.OperationEvent>}
  ReceiptResult{reply: S.Return,events: List<&2,S.OperationEvent>}
  ReceiptRefused{reason: D.Value,events: List<&2,S.OperationEvent>}
  ReceiptFailure{events: List<&2,S.OperationEvent>}

def read(owner: String,key: String,name: String) -> D.Operation: D.ReadCell{D.Application{owner},key,name}
def prepend(+event: S.OperationEvent,plan: Plan) -> Plan:
  match plan:
    case ReceiptMissing{events}: ReceiptMissing{Con{event,events}}
    case ReceiptResult{reply,events}: ReceiptResult{reply,Con{event,events}}
    case ReceiptRefused{reason,events}: ReceiptRefused{reason,Con{event,events}}
    case ReceiptFailure{events}: ReceiptFailure{Con{event,events}}

def result(owner: String,key: String,r: D.ResultOp) -> Plan:
  match r:
    case D.FailureData{}: ReceiptFailure{[S.OperationEvent{read(owner,key,"result"),S.ErrorOfData{}}]}
    case D.Observed{+observation}: ReceiptResult{S.Datum{observation},[S.OperationEvent{read(owner,key,"result"),S.Reading{observation}}]}
    # Actual named reads NEVER change state: the total proof derives this.
    case D.Changed{state}: ReceiptFailure{[S.OperationEvent{read(owner,key,"result"),S.ErrorOfData{}}]}

def operation_value(value: H.Lookup,+expected: String,next: Plan) -> Plan:
  match value:
    case H.StoredText{actual}: Bool.pick(Plan,String.eq(actual,expected),next,ReceiptRefused{D.VText{"request conflict"},Nil{}})
    case H.Missing{}: ReceiptRefused{D.VText{"invalid receipt"},Nil{}}
    case H.Unexpected{}: ReceiptRefused{D.VText{"invalid receipt"},Nil{}}

def operation(owner: String,key: String,expected: String,r: D.ResultOp,next: Plan) -> Plan:
  match r:
    case D.FailureData{}: ReceiptFailure{[S.OperationEvent{read(owner,key,"operation"),S.ErrorOfData{}}]}
    case D.Observed{+observation}: prepend(S.OperationEvent{read(owner,key,"operation"),S.Reading{observation}},operation_value(H.observed(S.Datum{observation}),expected,next))
    case D.Changed{state}: ReceiptFailure{[S.OperationEvent{read(owner,key,"operation"),S.ErrorOfData{}}]}

def input_value(value: H.Lookup,+expected: String,next: Plan) -> Plan:
  match value:
    case H.Missing{}: ReceiptMissing{Nil{}}
    case H.StoredText{actual}: Bool.pick(Plan,String.eq(actual,expected),next,ReceiptRefused{D.VText{"request conflict"},Nil{}})
    case H.Unexpected{}: ReceiptRefused{D.VText{"invalid receipt"},Nil{}}

def input(owner: String,key: String,expected: String,r: D.ResultOp,next: Plan) -> Plan:
  match r:
    case D.FailureData{}: ReceiptFailure{[S.OperationEvent{read(owner,key,"input"),S.ErrorOfData{}}]}
    case D.Observed{+observation}: prepend(S.OperationEvent{read(owner,key,"input"),S.Reading{observation}},input_value(H.observed(S.Datum{observation}),expected,next))
    case D.Changed{state}: ReceiptFailure{[S.OperationEvent{read(owner,key,"input"),S.ErrorOfData{}}]}

def result_plan(+schema: D.Schema,+state: D.State,+owner: String,+key: String) -> Plan:
  result(owner,key,D.operate(schema,state,read(owner,key,"result")))
def operation_plan(+schema: D.Schema,+state: D.State,+owner: String,+key: String,expected: String) -> Plan:
  operation(owner,key,expected,D.operate(schema,state,read(owner,key,"operation")),result_plan(schema,state,owner,key))
def plan(+schema: D.Schema,+state: D.State,+owner: String,+key: String,expected_operation: String,expected_input: String) -> Plan:
  input(owner,key,expected_input,D.operate(schema,state,read(owner,key,"input")),operation_plan(schema,state,owner,key,expected_operation))
