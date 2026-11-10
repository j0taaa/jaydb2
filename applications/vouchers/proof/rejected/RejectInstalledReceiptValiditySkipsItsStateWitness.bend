# Deliberately false actual protocol/certificate claim; reject at proof body.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Semantics.bend as S
import ../../../../contract/Requirements.bend as R
import ../../../../contract/Logic.bend as L
import ../../../../library/ReceiptLaws.bend as RL
import ../../Initial.bend as Initial
import ../VoucherPairProofs.bend as P
import ../VoucherConfigurationProofs.bend as Boundary

def columns() -> List<&2,D.Column>: [D.Column{"enabled",D.Boolean{},True{}},D.Column{"id",D.TextValue{},False{}},D.Column{"input",D.TextValue{},True{}},D.Column{"operation",D.TextValue{},True{}},D.Column{"owner",D.TextValue{},False{}},D.Column{"result",D.TextValue{},True{}}]

def table(name: String) -> D.SchemaTable: D.SchemaTable{name,"id",columns()}

def schema() -> D.Schema: D.Schema{[table("alice"),table("bob")]}

def limits() -> S.Limits: S.Limits{10000n,10000n,10000n}

def seed() -> D.State: D.State{Initial.tables(),Nil{}}

def context(owner: String) -> D.Context: D.Context{owner,"person"}

def args(input: String,cancel: Bool) -> D.Value: D.VList{D.VText{"issue"},D.VList{D.VText{"q"},D.VList{D.VText{input},D.VList{D.VBool{cancel},D.VListEmpty{}}}}}

def bad_receipt() -> D.State: D.swap_collection(D.Application{"alice"},seed(),[P.receipt_row("alice","q","tea",False{})])

def calls() -> List<&2,RL.Call>: [RL.Call{context("alice"),args("tea",False{}),8n}]

def fixture_prior(situation: S.Situation) -> Type: Unit

def installed() -> S.Configuration: Boundary.installed(fixture_prior,schema(),limits(),"")

law false_reject_installed_receipt_validity_skips_its_state_witness:
  R.Valid(installed(),bad_receipt())
def false_reject_installed_receipt_validity_skips_its_state_witness(): L.Both{{==},L.Both{Unit{},L.Both{(seed(),calls(),RL.Both{{==},{==}}),Unit{}}}}
