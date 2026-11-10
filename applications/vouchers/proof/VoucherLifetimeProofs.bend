# Final actual-program/replay closure. Public heads take INPUTS only, plus the
# legitimate previous invariant or unchanged administrator origin/provenance.
# No desired trace, operation result, completed state effect, successful Boolean
# or callback outcome is a premise. The actual source certificate is derived.
import Base
import ./VoucherSuccessEffects.bend as E
import ./VoucherSourceEffects.bend as Source
import ../Voucher.bend as V
import ../Initial.bend as Initial
import ./VoucherLifetimeState.bend as State
import ../../../contract/Data.bend as D
import ../../../library/ReceiptLaws.bend as RL
import ../../../contract/Semantics.bend as S

law every_actual_reference_advance_preserves_the_complete_global_lifetime_invariant:
  for +fuel: Nat
  for +schema: D.Schema
  for +limits: S.Limits
  for +initial: D.State
  for +context: D.Context
  for +arguments: D.Value
  for previous: State.Global(initial)
  State.Global(RL.advance(S.execute(fuel,V.program(),schema,initial,context,arguments),schema,limits,initial))
def every_actual_reference_advance_preserves_the_complete_global_lifetime_invariant(fuel,schema,limits,initial,context,arguments,previous):
  E.advance_preserves(S.execute(fuel,V.program(),schema,initial,context,arguments),schema,limits,initial,Source.actual_frozen_reference_execution_derives_a_complete_success_effect_for_every_input_and_fuel(fuel,initial,schema,context,arguments),previous)

law every_actual_reference_replay_preserves_the_complete_global_seed_invariant:
  for +calls: List<&2,RL.Call>
  for +seed: D.State
  for +schema: D.Schema
  for +limits: S.Limits
  for previous: State.Global(seed)
  State.Global(RL.replay(~V.program(),schema,limits,seed,calls))
def every_actual_reference_replay_preserves_the_complete_global_seed_invariant(calls,seed,schema,limits,previous):
  match calls:
    case Nil{}: previous
    case Con{RL.Call{context,arguments,depth},+rest}:
      +initial = RL.replay(~V.program(),schema,limits,seed,rest)
      every_actual_reference_advance_preserves_the_complete_global_lifetime_invariant(depth,schema,limits,initial,context,arguments,every_actual_reference_replay_preserves_the_complete_global_seed_invariant(rest,seed,schema,limits,previous))

law all_actual_reference_replays_from_the_unchanged_origin_have_complete_lifetime_meaning:
  for +calls: List<&2,RL.Call>
  for +seed: D.State
  for +schema: D.Schema
  for +limits: S.Limits
  for origin: Initial.origin(seed)
  State.Global(RL.replay(~V.program(),schema,limits,seed,calls))
def all_actual_reference_replays_from_the_unchanged_origin_have_complete_lifetime_meaning(calls,seed,schema,limits,origin):
  every_actual_reference_replay_preserves_the_complete_global_seed_invariant(calls,seed,schema,limits,State.the_unchanged_administrator_origin_predicate_implies_the_independent_global_lifetime_invariant(seed,origin))

law the_unchanged_administrator_replay_state_law_implies_the_independent_global_lifetime_invariant:
  for +schema: D.Schema
  for +limits: S.Limits
  for +current: D.State
  for history: RL.State(~V.program(),~Initial.origin,schema,limits,current)
  State.Global(current)
def the_unchanged_administrator_replay_state_law_implies_the_independent_global_lifetime_invariant(schema,limits,current,history):
  match history:
    case (seed,calls,RL.Both{origin,same}):
      %same : State.Global(_)
      all_actual_reference_replays_from_the_unchanged_origin_have_complete_lifetime_meaning(calls,seed,schema,limits,origin)
