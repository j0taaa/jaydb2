# Deliberately false actual protocol/certificate claim; reject at proof body.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Semantics.bend as S
import ../../../../library/ReceiptLaws.bend as RL
import ../../Voucher.bend as V
import ../../Initial.bend as Initial
import ../VoucherPairProofs.bend as P

def columns() -> List<&2,D.Column>: [D.Column{"enabled",D.Boolean{},True{}},D.Column{"id",D.TextValue{},False{}},D.Column{"input",D.TextValue{},True{}},D.Column{"operation",D.TextValue{},True{}},D.Column{"owner",D.TextValue{},False{}},D.Column{"result",D.TextValue{},True{}}]

def table(name: String) -> D.SchemaTable: D.SchemaTable{name,"id",columns()}

def schema() -> D.Schema: D.Schema{[table("alice"),table("bob")]}

def limits() -> S.Limits: S.Limits{10000n,10000n,10000n}

def seed() -> D.State: D.State{Initial.tables(),Nil{}}

def context(owner: String) -> D.Context: D.Context{owner,"person"}

def args(input: String,cancel: Bool) -> D.Value: D.VList{D.VText{"issue"},D.VList{D.VText{"q"},D.VList{D.VText{input},D.VList{D.VBool{cancel},D.VListEmpty{}}}}}

def created() -> D.State: P.state("alice",seed(),[Initial.gate("alice")],"q","tea",False{})

def gate_event(enabled: Bool) -> S.OperationEvent: S.OperationEvent{D.ReadCell{D.Application{"alice"},"permission","enabled"},S.Reading{D.Cell{D.VBool{enabled}}}}

def input_event() -> S.OperationEvent: S.OperationEvent{D.ReadCell{D.Application{"alice"},V.receipt("q"),"input"},S.Reading{D.Cell{D.VText{V.canonical("tea",False{})}}}}

def hit_events() -> List<&2,S.OperationEvent>: [gate_event(True{}),input_event(),S.OperationEvent{D.ReadCell{D.Application{"alice"},V.receipt("q"),"operation"},S.Reading{D.Cell{D.VText{V.operation()}}}},S.OperationEvent{D.ReadCell{D.Application{"alice"},V.receipt("q"),"result"},S.Reading{D.Cell{D.VText{V.voucher("q")}}}}]

law false_reject_closed_hit_invents_a_result_despite_exact_state_and_events:
  RL.Closed(~V.program(),schema(),limits(),created(),context("alice"),args("tea",False{}),created(),hit_events(),S.Response{S.Success{},D.VText{"invented"}})
def false_reject_closed_hit_invents_a_result_despite_exact_state_and_events(): (12n,RL.Both{RL.Both{{==},{==}},{==}})
