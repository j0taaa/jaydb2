# Deliberately false actual protocol/certificate claim; reject at proof body.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Semantics.bend as S
import ../../Voucher.bend as V
import ../../Initial.bend as Initial
import ../VoucherLifetimeMeaning.bend as I

def columns() -> List<&2,D.Column>: [D.Column{"enabled",D.Boolean{},True{}},D.Column{"id",D.TextValue{},False{}},D.Column{"input",D.TextValue{},True{}},D.Column{"operation",D.TextValue{},True{}},D.Column{"owner",D.TextValue{},False{}},D.Column{"result",D.TextValue{},True{}}]

def table(name: String) -> D.SchemaTable: D.SchemaTable{name,"id",columns()}

def schema() -> D.Schema: D.Schema{[table("alice"),table("bob")]}

def seed() -> D.State: D.State{Initial.tables(),Nil{}}

def context(owner: String) -> D.Context: D.Context{owner,"person"}

def args(input: String,cancel: Bool) -> D.Value: D.VList{D.VText{"issue"},D.VList{D.VText{"q"},D.VList{D.VText{input},D.VList{D.VBool{cancel},D.VListEmpty{}}}}}

def rows_from(view: Maybe<&2,List<&2,D.Row>>) -> List<&2,D.Row>:
  match view:
    case None{}: Nil{}
    case Some{rows}: rows

def alice_rows(state: D.State) -> List<&2,D.Row>: rows_from(D.rows_collection(D.Application{"alice"},state))

def partial() -> D.State: S.state_execution_trace(S.execute(3n,V.program(),schema(),seed(),context("alice"),args("tea",False{})))

law false_reject_partial_working_prefix_already_has_complete_lifetime:
  I.Request("alice","q",alice_rows(partial()))
def false_reject_partial_working_prefix_already_has_complete_lifetime(): Unit{}
