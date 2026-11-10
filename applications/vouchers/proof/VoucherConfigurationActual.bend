# Checked in the EXISTING flat application namespace. C and Policy are the
# exact original application sources. Generic B is universal over environment,
# so these consequences assert no deployed environment identity or real-history
# provenance. They do show the actual unchanged law-list installation.
import Base
import ../Configuration.bend as C
import ../../tasks/Policy.bend as Policy
import ../Seed.bend as Seed
import ./VoucherConfigurationProofs.bend as B
import ./VoucherLifetimeState.bend as State
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../contract/Requirements.bend as R
import ../../../library/ReceiptLaws.bend as RL
import ../Voucher.bend as V
import ../Initial.bend as Initial

law actual_configuration_stable_validity_contains_the_exact_frozen_receipt_state_law:
  for +current: D.State
  for valid: R.Valid(C.config(),current)
  RL.State(~V.program(),~Initial.origin,C.schema(),C.limits(),current)
def actual_configuration_stable_validity_contains_the_exact_frozen_receipt_state_law(current,valid):
  B.stable_validity_of_the_installed_receipt_configuration_contains_its_exact_replay_state_witness(Policy.Rule,C.schema(),C.limits(),C.environment(),current,valid)

law actual_configuration_stable_validity_implies_the_complete_independent_lifetime_invariant:
  for +current: D.State
  for valid: R.Valid(C.config(),current)
  State.Global(current)
def actual_configuration_stable_validity_implies_the_complete_independent_lifetime_invariant(current,valid):
  B.stable_validity_of_the_installed_receipt_configuration_implies_complete_global_lifetime(Policy.Rule,C.schema(),C.limits(),C.environment(),current,valid)

law the_actual_existing_seed_validity_proof_inhabits_the_complete_lifetime_invariant:
  State.Global(Seed.state())
def the_actual_existing_seed_validity_proof_inhabits_the_complete_lifetime_invariant():
  actual_configuration_stable_validity_implies_the_complete_independent_lifetime_invariant(Seed.state(),Seed.initial_valid())

# Any program must actually SUPPLY the existing checked final certificate;
# this theorem does not manufacture certifiability for arbitrary code.
law actual_configuration_successful_final_certification_implies_complete_published_lifetime:
  for +initial: D.State
  for +context: D.Context
  for +code: String
  for +arguments: D.Value
  for +working: D.State
  for +events: List<&2,S.OperationEvent>
  for +value: D.Value
  for safe: R.SafetyFinal(C.config(),initial,context,code,arguments,working,events,S.Response{S.Success{},value})
  State.Global(working)
def actual_configuration_successful_final_certification_implies_complete_published_lifetime(initial,context,code,arguments,working,events,value,safe):
  B.an_installed_successful_final_certificate_implies_complete_published_lifetime(Policy.Rule,C.schema(),C.limits(),C.environment(),initial,context,code,arguments,working,events,value,safe)
