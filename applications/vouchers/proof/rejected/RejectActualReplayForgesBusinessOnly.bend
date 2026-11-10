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

def bad_business() -> D.State: D.swap_collection(D.Application{"alice"},seed(),[P.voucher_row("alice","q","tea")])

def calls() -> List<&2,RL.Call>: [RL.Call{context("alice"),args("tea",False{}),8n}]

law false_reject_actual_replay_forges_business_only:
  RL.State(~V.program(),~Initial.origin,schema(),limits(),bad_business())
def false_reject_actual_replay_forges_business_only(): (seed(),calls(),RL.Both{{==},{==}})
