# A live mismatched input/cancellation can NEVER finish with Success at ANY
# mathematical fuel, including permission/length/data failure and prefixes.
# All public premises are initial schema/table/row data and literal inequality.
import Base
import ./VoucherSourceEffects.bend as Source
import ../Voucher.bend as V
import ./VoucherPairProofs.bend as P
import ./VoucherKeyProofs.bend as K
import ../../../library/ReceiptInputProofs.bend as Input
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../contract/Logic.bend as L
import ../../../library/Receipts.bend as H
import ../../../library/ReceiptLaws.bend as RL
import ../../../library/Proofs.bend as Event
import ../../../library/ReadOperationProofs.bend as Read
import ../../../proof/Foundations.bend as F
import ../../../src/Termination.bend as T

def NoSuccessResponse(response: S.Response) -> Data:
  match response:
    case S.Response{S.Success{},value}: {False{} == True{} : Bool}
    case _: Unit
def NoSuccess(trace: S.Trace) -> Data:
  match trace:
    case S.Prefix{working,events}: Unit
    case S.Final{working,events,response}: NoSuccessResponse(response)

def refusal(fuel: Nat,+initial: D.State,+schema: D.Schema,+history: List<&2,S.OperationEvent>,+reason: D.Value) -> NoSuccess(T.observe(fuel,S.Refuse{reason},schema,initial,history)):
  match fuel:
    case 0n: Unit{}
    case 1n+n:
      %Equal.sym(S.Trace,T.observe(1n+n,S.Refuse{reason},schema,initial,history),S.Final{initial,history,S.Response{S.Refusal{},reason}},T.stopped(n,initial,S.Response{S.Refusal{},reason},schema,history)) : NoSuccess(_)
      Unit{}

def read_case(+result: D.ResultOp,+remaining: Nat,+initial: D.State,+schema: D.Schema,+collection: D.Collection,+key: String,+name: String,-resume: S.Return -> S.Action,+history: List<&2,S.OperationEvent>,actual: {D.operate(schema,initial,D.ReadCell{collection,key,name}) == result : D.ResultOp},kind: Read.ResultKind(Read.Cell{},result),handler: @+observation: D.Observation -> NoSuccess(T.observe(remaining,resume(S.Datum{observation}),schema,initial,S.append(history,S.OperationEvent{D.ReadCell{collection,key,name},S.Reading{observation}})))) -> NoSuccess(T.observe(1n+remaining,S.Access{D.ReadCell{collection,key,name},resume},schema,initial,history)):
  match result:
    case D.FailureData{}:
      %Equal.sym(S.Trace,T.observe(1n+remaining,S.Access{D.ReadCell{collection,key,name},resume},schema,initial,history),S.Final{initial,S.append(history,S.OperationEvent{D.ReadCell{collection,key,name},S.ErrorOfData{}}),S.Response{S.DataError{},D.VAbsent{}}},Read.actual_data_failure_retains_its_event_and_finishes_without_a_return_callback(remaining,schema,initial,D.ReadCell{collection,key,name},resume,history,actual)) : NoSuccess(_)
      Unit{}
    case D.Observed{+observation}:
      %Equal.sym(S.Trace,T.observe(1n+remaining,S.Access{D.ReadCell{collection,key,name},resume},schema,initial,history),T.observe(remaining,resume(S.Datum{observation}),schema,initial,S.append(history,S.OperationEvent{D.ReadCell{collection,key,name},S.Reading{observation}})),Event.read_continuation(remaining,schema,initial,D.ReadCell{collection,key,name},observation,resume,history,actual)) : NoSuccess(_)
      handler(observation)
    case D.Changed{working}: F.absurd_boolean(NoSuccess(T.observe(1n+remaining,S.Access{D.ReadCell{collection,key,name},resume},schema,initial,history)),kind)

def cell_read(+remaining: Nat,+initial: D.State,+schema: D.Schema,+collection: D.Collection,+key: String,+name: String,-resume: S.Return -> S.Action,+history: List<&2,S.OperationEvent>,handler: @+observation: D.Observation -> NoSuccess(T.observe(remaining,resume(S.Datum{observation}),schema,initial,S.append(history,S.OperationEvent{D.ReadCell{collection,key,name},S.Reading{observation}})))) -> NoSuccess(T.observe(1n+remaining,S.Access{D.ReadCell{collection,key,name},resume},schema,initial,history)):
  read_case(D.operate(schema,initial,D.ReadCell{collection,key,name}),remaining,initial,schema,collection,key,name,resume,history,{==},Read.real_named_read_operations_have_only_the_expected_observation_or_data_failure(Read.Cell{},schema,initial,collection,key,name),handler)

def ActualInput(+initial: D.State,+schema: D.Schema,+owner: String,request: String,saved: String) -> Data:
  {D.operate(schema,initial,D.ReadCell{D.Application{owner},V.receipt(request),"input"}) == D.Observed{D.Cell{D.VText{V.canonical(saved,False{})}}} : D.ResultOp}
def Different(saved: String,requested: String,cancel: Bool) -> Data:
  {String.eq(V.canonical(saved,False{}),V.canonical(requested,cancel)) == False{} : Bool}

def command(fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,+request: String,+saved: String,+requested: String,+cancel: Bool,+history: List<&2,S.OperationEvent>,actual: ActualInput(initial,schema,owner,request,saved),different: Different(saved,requested,cancel)) -> NoSuccess(T.observe(fuel,V.command(owner,V.Issue{request,requested,cancel}),schema,initial,history)):
  match fuel:
    case 0n: Unit{}
    case 1n+ +n:
      %Equal.sym(S.Trace,T.observe(1n+n,V.command(owner,V.Issue{request,requested,cancel}),schema,initial,history),T.observe(n,H.input_seen(owner,V.receipt(request),V.operation(),V.canonical(requested,cancel),V.create(owner,request,requested,cancel),V.result(request),S.Datum{D.Cell{D.VText{V.canonical(saved,False{})}}}),schema,initial,S.append(history,S.OperationEvent{D.ReadCell{D.Application{owner},V.receipt(request),"input"},S.Reading{D.Cell{D.VText{V.canonical(saved,False{})}}}})),Event.read_continuation(n,schema,initial,D.ReadCell{D.Application{owner},V.receipt(request),"input"},D.Cell{D.VText{V.canonical(saved,False{})}},H.input_seen(owner,V.receipt(request),V.operation(),V.canonical(requested,cancel),V.create(owner,request,requested,cancel),V.result(request)),history,actual)) : NoSuccess(_)
      %Equal.sym(Bool,String.eq(V.canonical(saved,False{}),V.canonical(requested,cancel)),False{},different) : NoSuccess(T.observe(n,H.input_match(_,owner,V.receipt(request),V.operation(),V.result(request)),schema,initial,S.append(history,S.OperationEvent{D.ReadCell{D.Application{owner},V.receipt(request),"input"},S.Reading{D.Cell{D.VText{V.canonical(saved,False{})}}}})))
      refusal(n,initial,schema,S.append(history,S.OperationEvent{D.ReadCell{D.Application{owner},V.receipt(request),"input"},S.Reading{D.Cell{D.VText{V.canonical(saved,False{})}}}}),D.VText{"request conflict"})

def permitted(allowed: Bool,+fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,+request: String,+saved: String,+requested: String,+cancel: Bool,+history: List<&2,S.OperationEvent>,actual: ActualInput(initial,schema,owner,request,saved),different: Different(saved,requested,cancel)) -> NoSuccess(T.observe(fuel,V.permit(allowed,owner,V.Issue{request,requested,cancel}),schema,initial,history)):
  match allowed:
    case True{}: command(fuel,initial,schema,owner,request,saved,requested,cancel,history,actual,different)
    case False{}: refusal(fuel,initial,schema,history,D.VText{"permission denied"})

def gate(fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,+request: String,+saved: String,+requested: String,+cancel: Bool,+history: List<&2,S.OperationEvent>,+actual: ActualInput(initial,schema,owner,request,saved),+different: Different(saved,requested,cancel)) -> NoSuccess(T.observe(fuel,S.Access{D.ReadCell{D.Application{owner},"permission","enabled"},V.permitted(owner,V.Issue{request,requested,cancel})},schema,initial,history)):
  match fuel:
    case 0n: Unit{}
    case 1n+ +n: cell_read(n,initial,schema,D.Application{owner},"permission","enabled",V.permitted(owner,V.Issue{request,requested,cancel}),history,observation => permitted(V.enabled(S.Datum{observation}),n,initial,schema,owner,request,saved,requested,cancel,S.append(history,S.OperationEvent{D.ReadCell{D.Application{owner},"permission","enabled"},S.Reading{observation}}),actual,different))

def sized(allowed: Bool,+fuel: Nat,+initial: D.State,+schema: D.Schema,+owner: String,+request: String,+saved: String,+requested: String,+cancel: Bool,+history: List<&2,S.OperationEvent>,actual: ActualInput(initial,schema,owner,request,saved),different: Different(saved,requested,cancel)) -> NoSuccess(T.observe(fuel,V.sized(allowed,owner,request,requested,cancel),schema,initial,history)):
  match allowed:
    case True{}: gate(fuel,initial,schema,owner,request,saved,requested,cancel,history,actual,different)
    case False{}: refusal(fuel,initial,schema,history,D.VText{"request ID too long"})

def arguments(request: String,input: String,cancel: Bool) -> D.Value:
  D.VList{D.VText{"issue"},D.VList{D.VText{request},D.VList{D.VText{input},D.VList{D.VBool{cancel},D.VListEmpty{}}}}}

def success_flag(response: S.Response) -> Bool:
  match response:
    case S.Response{status,value}: S.is_success(status)
def finished_response(+response: S.Response,+value: D.Value,non_success: NoSuccessResponse(response),finished: {response == S.Response{S.Success{},value} : S.Response}) -> Empty:
  match response:
    case S.Response{S.Success{},actual}: F.false_negative_true(non_success)
    case S.Response{S.Refusal{},actual}: F.false_negative_true(Equal.cong(S.Response,Bool,success_flag,S.Response{S.Refusal{},actual},S.Response{S.Success{},value},finished))
    case S.Response{S.DataError{},actual}: F.false_negative_true(Equal.cong(S.Response,Bool,success_flag,S.Response{S.DataError{},actual},S.Response{S.Success{},value},finished))
    case S.Response{S.Limit{},actual}: F.false_negative_true(Equal.cong(S.Response,Bool,success_flag,S.Response{S.Limit{},actual},S.Response{S.Success{},value},finished))
    case S.Response{S.Failure{},actual}: F.false_negative_true(Equal.cong(S.Response,Bool,success_flag,S.Response{S.Failure{},actual},S.Response{S.Success{},value},finished))
    case S.Response{S.Input{},actual}: F.false_negative_true(Equal.cong(S.Response,Bool,success_flag,S.Response{S.Input{},actual},S.Response{S.Success{},value},finished))
    case S.Response{S.Authentication{},actual}: F.false_negative_true(Equal.cong(S.Response,Bool,success_flag,S.Response{S.Authentication{},actual},S.Response{S.Success{},value},finished))
    case S.Response{S.Certificate{},actual}: F.false_negative_true(Equal.cong(S.Response,Bool,success_flag,S.Response{S.Certificate{},actual},S.Response{S.Success{},value},finished))
def finished_trace(+trace: S.Trace,+value: D.Value,non_success: NoSuccess(trace),finished: RL.Finished(trace,value)) -> Empty:
  match trace:
    case S.Prefix{working,events}: finished
    case S.Final{working,events,response}: finished_response(response,value,non_success,finished)

# PUBLIC ALL-FUEL LIVE CONFLICT

law no_actual_frozen_reference_execution_of_a_live_conflicting_issue_can_succeed:
  for +fuel: Nat
  for +schema: D.Schema
  for +initial: D.State
  for +owner: String
  for +kind: String
  for +request: String
  for +saved: String
  for +requested: String
  for +cancel: Bool
  for +table_name: String
  for +primary: String
  for +columns: List<&2,D.Column>
  for +rows: List<&2,D.Row>
  for +input_column: D.Column
  for +valid_request: {D.unicode_valid(request) == True{} : Bool}
  for +schema_found: {D.schema_collection(D.Application{owner},schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(D.Application{owner},initial) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for +column_found: {D.find_column(columns,"input") == Some{input_column} : Maybe<&2,D.Column>}
  for +row_found: {D.find_row(rows,V.receipt(request)) == Some{P.receipt_row(owner,request,saved,False{})} : Maybe<&2,D.Row>}
  for different: L.E<{saved == requested : String},{False{} == cancel : Bool}> -> Empty
  NoSuccess(S.execute(fuel,V.program(),schema,initial,D.Context{owner,kind},arguments(request,requested,cancel)))
def no_actual_frozen_reference_execution_of_a_live_conflicting_issue_can_succeed(fuel,schema,initial,owner,kind,request,saved,requested,cancel,table_name,primary,columns,rows,input_column,valid_request,schema_found,rows_found,column_found,row_found,different):
  %Source.observing_with_empty_history_is_the_ordinary_program_observation(fuel,V.start(D.Context{owner,kind},arguments(request,requested,cancel)),schema,initial) : NoSuccess(_)
  sized(Nat.is_le(String.length(request),64n),fuel,initial,schema,owner,request,saved,requested,cancel,Nil{},Input.a_declared_cell_of_the_input_receipt_row_has_its_exact_stored_payload(schema,initial,owner,V.receipt(request),table_name,primary,columns,rows,V.fields(owner,V.receipt(request),V.canonical(saved,False{}),V.operation(),V.voucher(request)),"input",input_column,D.VText{V.canonical(saved,False{})},valid_request,schema_found,rows_found,column_found,row_found,{==}),Input.different_literal_texts_have_a_false_string_equality_comparison(V.canonical(saved,False{}),V.canonical(requested,cancel),same => different(K.actual_canonical_input_is_injective_in_both_text_and_cancellation_flag(saved,False{},requested,cancel,same))))

law no_closed_frozen_reference_success_witness_exists_for_a_live_conflicting_issue:
  for +schema: D.Schema
  for +initial: D.State
  for +owner: String
  for +kind: String
  for +request: String
  for +saved: String
  for +requested: String
  for +cancel: Bool
  for +table_name: String
  for +primary: String
  for +columns: List<&2,D.Column>
  for +rows: List<&2,D.Row>
  for +input_column: D.Column
  for +limits: S.Limits
  for +working: D.State
  for +events: List<&2,S.OperationEvent>
  for +value: D.Value
  for +valid_request: {D.unicode_valid(request) == True{} : Bool}
  for +schema_found: {D.schema_collection(D.Application{owner},schema) == Some{D.SchemaTable{table_name,primary,columns}} : Maybe<&2,D.SchemaTable>}
  for +rows_found: {D.rows_collection(D.Application{owner},initial) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for +column_found: {D.find_column(columns,"input") == Some{input_column} : Maybe<&2,D.Column>}
  for +row_found: {D.find_row(rows,V.receipt(request)) == Some{P.receipt_row(owner,request,saved,False{})} : Maybe<&2,D.Row>}
  for different: L.E<{saved == requested : String},{False{} == cancel : Bool}> -> Empty
  for closed: RL.Closed(~V.program(),schema,limits,initial,D.Context{owner,kind},arguments(request,requested,cancel),working,events,S.Response{S.Success{},value})
  Empty
def no_closed_frozen_reference_success_witness_exists_for_a_live_conflicting_issue(schema,initial,owner,kind,request,saved,requested,cancel,table_name,primary,columns,rows,input_column,limits,working,events,value,valid_request,schema_found,rows_found,column_found,row_found,different,closed):
  match closed:
    case (+fuel,RL.Both{at,finished}): finished_trace(S.execute(fuel,V.program(),schema,initial,D.Context{owner,kind},arguments(request,requested,cancel)),value,no_actual_frozen_reference_execution_of_a_live_conflicting_issue_can_succeed(fuel,schema,initial,owner,kind,request,saved,requested,cancel,table_name,primary,columns,rows,input_column,valid_request,schema_found,rows_found,column_found,row_found,different),finished)
