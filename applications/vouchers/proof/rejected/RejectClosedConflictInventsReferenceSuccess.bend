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

law false_reject_closed_conflict_invents_reference_success:
  RL.Closed(~V.program(),schema(),limits(),created(),context("alice"),args("coffee",False{}),created(),[gate_event(True{}),input_event()],S.Response{S.Success{},D.VText{V.voucher("q")}})
def false_reject_closed_conflict_invents_reference_success(): (12n,RL.Both{RL.Both{{==},{==}},{==}})
