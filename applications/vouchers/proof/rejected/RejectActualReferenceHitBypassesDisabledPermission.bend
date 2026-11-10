# Deliberately false actual protocol/certificate claim; reject at proof body.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Semantics.bend as S
import ../../Voucher.bend as V
import ../../Initial.bend as Initial
import ../VoucherPairProofs.bend as P
import ../VoucherLifetimeState.bend as State

def columns() -> List<&2,D.Column>: [D.Column{"enabled",D.Boolean{},True{}},D.Column{"id",D.TextValue{},False{}},D.Column{"input",D.TextValue{},True{}},D.Column{"operation",D.TextValue{},True{}},D.Column{"owner",D.TextValue{},False{}},D.Column{"result",D.TextValue{},True{}}]

def table(name: String) -> D.SchemaTable: D.SchemaTable{name,"id",columns()}

def schema() -> D.Schema: D.Schema{[table("alice"),table("bob")]}

def seed() -> D.State: D.State{Initial.tables(),Nil{}}

def context(owner: String) -> D.Context: D.Context{owner,"person"}

def args(input: String,cancel: Bool) -> D.Value: D.VList{D.VText{"issue"},D.VList{D.VText{"q"},D.VList{D.VText{input},D.VList{D.VBool{cancel},D.VListEmpty{}}}}}

def created_rows() -> List<&2,D.Row>: P.rows("alice","q","tea",False{},[Initial.gate("alice")])

def created() -> D.State: P.state("alice",seed(),[Initial.gate("alice")],"q","tea",False{})

def gate_event(enabled: Bool) -> S.OperationEvent: S.OperationEvent{D.ReadCell{D.Application{"alice"},"permission","enabled"},S.Reading{D.Cell{D.VBool{enabled}}}}

def disabled() -> D.State: State.transformed_state(State.GateUpdated{False{}},"alice",created(),created_rows())

law false_reject_actual_reference_hit_bypasses_disabled_permission:
  {S.execute(8n,V.program(),schema(),disabled(),context("alice"),args("tea",False{})) == S.Final{disabled(),[gate_event(False{})],S.Response{S.Success{},D.VText{V.voucher("q")}}} : S.Trace}
def false_reject_actual_reference_hit_bypasses_disabled_permission(): {==}
