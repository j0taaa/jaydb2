# Deliberately false actual protocol/certificate claim; reject at proof body.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Semantics.bend as S
import ../../Voucher.bend as V
import ../../Initial.bend as Initial
import ../VoucherPairProofs.bend as P
import ../VoucherLifetimePermission.bend as Gate
import ../../../../library/MutationStateShapeProofs.bend as Shape
import ../VoucherWriteEffects.bend as W

def columns() -> List<&2,D.Column>: [D.Column{"enabled",D.Boolean{},True{}},D.Column{"id",D.TextValue{},False{}},D.Column{"input",D.TextValue{},True{}},D.Column{"operation",D.TextValue{},True{}},D.Column{"owner",D.TextValue{},False{}},D.Column{"result",D.TextValue{},True{}}]

def table(name: String) -> D.SchemaTable: D.SchemaTable{name,"id",columns()}

def schema() -> D.Schema: D.Schema{[table("alice"),table("bob")]}

def seed() -> D.State: D.State{Initial.tables(),Nil{}}

def context(owner: String) -> D.Context: D.Context{owner,"person"}

def created() -> D.State: P.state("alice",seed(),[Initial.gate("alice")],"q","tea",False{})

law false_reject_actual_permission_update_drops_existing_pairs:
  {S.execute(2n,S.Program{ctx => arguments => V.command("alice",V.Permission{False{}})},schema(),created(),context("alice"),D.VAbsent{}) == S.Final{D.swap_collection(D.Application{"alice"},seed(),[Gate.row("alice",False{})]),[S.OperationEvent{Shape.operation(D.Application{"alice"},W.gate_transform("alice",False{})),S.Write{}}],S.Response{S.Success{},D.VText{"permission updated"}}} : S.Trace}
def false_reject_actual_permission_update_drops_existing_pairs(): {==}
