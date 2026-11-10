# Constructive pointwise consequence of the unchanged replay law. It returns
# DATA facts about BOTH rows, so callers can reuse these concrete equalities;
# no arbitrary Type-valued invariant proof is cast/copied into Data.
import Base
import ./VoucherLifetimeProofs.bend as Replay
import ./VoucherLifetimeMeaning.bend as I
import ./VoucherLifetimeState.bend as State
import ../Voucher.bend as V
import ../Initial.bend as Initial
import ./VoucherPairProofs.bend as P
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../library/ReceiptLaws.bend as RL
import ../../../library/ValueScalarProofs.bend as Pair

type Instance is Data:
  NoLiveInstance{}
  LiveInstance{input: String}
def Meaning(instance: Instance,+owner: String,+request: String,+rows: List<&2,D.Row>) -> Data:
  match instance:
    case NoLiveInstance{}: Pair.Both<{D.find_row(rows,V.receipt(request)) == None{} : Maybe<&2,D.Row>},{D.find_row(rows,V.voucher(request)) == None{} : Maybe<&2,D.Row>}>
    case LiveInstance{+input}: Pair.Both<{D.find_row(rows,V.receipt(request)) == Some{P.receipt_row(owner,request,input,False{})} : Maybe<&2,D.Row>},{D.find_row(rows,V.voucher(request)) == Some{P.voucher_row(owner,request,input)} : Maybe<&2,D.Row>}>

def live(+receipt: D.Row,+voucher: D.Row,+owner: String,+request: String,+rows: List<&2,D.Row>,actual_receipt: {D.find_row(rows,V.receipt(request)) == Some{receipt} : Maybe<&2,D.Row>},actual_voucher: {D.find_row(rows,V.voucher(request)) == Some{voucher} : Maybe<&2,D.Row>},point: I.At(owner,request,Some{receipt},Some{voucher})) -> Sigma<&2,&2,Instance,instance => Meaning(instance,owner,request,rows)>:
  match point:
    case (+input,Pair.Both{receipt_shape,voucher_shape}):
      (LiveInstance{input},Pair.Both{Equal.trans(Maybe<&2,D.Row>,D.find_row(rows,V.receipt(request)),Some{receipt},Some{P.receipt_row(owner,request,input,False{})},actual_receipt,Equal.cong(D.Row,Maybe<&2,D.Row>,row => Some{row},receipt,P.receipt_row(owner,request,input,False{}),receipt_shape)),Equal.trans(Maybe<&2,D.Row>,D.find_row(rows,V.voucher(request)),Some{voucher},Some{P.voucher_row(owner,request,input)},actual_voucher,Equal.cong(D.Row,Maybe<&2,D.Row>,row => Some{row},voucher,P.voucher_row(owner,request,input),voucher_shape))})

def classify(receipt: Maybe<&2,D.Row>,voucher: Maybe<&2,D.Row>,+owner: String,+request: String,+rows: List<&2,D.Row>,actual_receipt: {D.find_row(rows,V.receipt(request)) == receipt : Maybe<&2,D.Row>},actual_voucher: {D.find_row(rows,V.voucher(request)) == voucher : Maybe<&2,D.Row>},point: I.At(owner,request,receipt,voucher)) -> Sigma<&2,&2,Instance,instance => Meaning(instance,owner,request,rows)>:
  match receipt voucher:
    case None{} None{}: (NoLiveInstance{},Pair.Both{actual_receipt,actual_voucher})
    case Some{receipt} Some{voucher}: live(receipt,voucher,owner,request,rows,actual_receipt,actual_voucher,point)
    case None{} Some{voucher}: Empty.absurd(Sigma<&2,&2,Instance,instance => Meaning(instance,owner,request,rows)>,point)
    case Some{receipt} None{}: Empty.absurd(Sigma<&2,&2,Instance,instance => Meaning(instance,owner,request,rows)>,point)

def point_from_global(+owner: String,+request: String,+current: D.State,+rows: List<&2,D.Row>,found: {D.rows_collection(D.Application{owner},current) == Some{rows} : Maybe<&2,List<&2,D.Row>>},global: State.Global(current)) -> I.Request(owner,request,rows):
  State.local_from_owner(owner,current,rows,found,global(owner))(request)

law the_unchanged_administrator_replay_state_classifies_both_rows_of_every_owned_request:
  for +schema: D.Schema
  for +limits: S.Limits
  for +current: D.State
  for +owner: String
  for +request: String
  for +rows: List<&2,D.Row>
  for found: {D.rows_collection(D.Application{owner},current) == Some{rows} : Maybe<&2,List<&2,D.Row>>}
  for history: RL.State(~V.program(),~Initial.origin,schema,limits,current)
  Sigma<&2,&2,Instance,instance => Meaning(instance,owner,request,rows)>
def the_unchanged_administrator_replay_state_classifies_both_rows_of_every_owned_request(schema,limits,current,owner,request,rows,found,history):
  classify(D.find_row(rows,V.receipt(request)),D.find_row(rows,V.voucher(request)),owner,request,rows,{==},{==},point_from_global(owner,request,current,rows,found,Replay.the_unchanged_administrator_replay_state_law_implies_the_independent_global_lifetime_invariant(schema,limits,current,history)))
