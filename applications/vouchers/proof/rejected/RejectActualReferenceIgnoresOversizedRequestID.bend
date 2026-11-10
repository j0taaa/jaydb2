# Deliberately false actual protocol/certificate claim; reject at proof body.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Semantics.bend as S
import ../../Voucher.bend as V
import ../../Initial.bend as Initial

def columns() -> List<&2,D.Column>: [D.Column{"enabled",D.Boolean{},True{}},D.Column{"id",D.TextValue{},False{}},D.Column{"input",D.TextValue{},True{}},D.Column{"operation",D.TextValue{},True{}},D.Column{"owner",D.TextValue{},False{}},D.Column{"result",D.TextValue{},True{}}]

def table(name: String) -> D.SchemaTable: D.SchemaTable{name,"id",columns()}

def schema() -> D.Schema: D.Schema{[table("alice"),table("bob")]}

def seed() -> D.State: D.State{Initial.tables(),Nil{}}

def context(owner: String) -> D.Context: D.Context{owner,"person"}

law false_reject_actual_reference_ignores_oversized_request_i_d:
  {S.execute(8n,V.program(),schema(),seed(),context("alice"),D.VList{D.VText{"issue"},D.VList{D.VText{"xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"},D.VList{D.VText{"tea"},D.VList{D.VBool{False{}},D.VListEmpty{}}}}}) == S.Final{seed(),Nil{},S.Response{S.Success{},D.VText{"v:xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"}}} : S.Trace}
def false_reject_actual_reference_ignores_oversized_request_i_d(): {==}
