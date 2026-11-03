# Actual failures, without a physical budget or Environment construction.
import Base
import ../contract/Semantics.bend as S
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as R
import ../contract/Resources.bend as X
import ../contract/Interface.bend as I
import ../contract/Logic.bend as L
import ../contract/LAWS.bend as Laws

law check_previous_establishes_rule2_of_field:
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for -t: Nat
  for -pos: Nat
  for -n: Nat
  for before: I.Before(a, k, x, t, I.CheckedLength{pos, n})
  Laws.Rule2(I.AllocatedField{pos, n}, a, k, x, t)
def check_previous_establishes_rule2_of_field(a, k, x, t, pos, n, before):
  before

law limit_logical_in_input_justifies_limit:
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for -t: Nat
  for exceeded: I.LimitInInput(x)
  I.ResponseJustified(S.response_error(S.Limit{}), a, k, x, t)
def limit_logical_in_input_justifies_limit(a, k, x, t, exceeded):
  L.Left{exceeded}

law limit_logical_final_justifies_limit:
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for -t: Nat
  for u: Nat
  for req: P.Request
  for ctx: D.Context
  for p: S.Program
  for w: D.State
  for ts: List<&2, S.OperationEvent>
  for proposal: S.Response
  for before: {Nat.is_lt(u, t) == True{} : Bool}
  for evaluated: I.Happens(a, k, x, u, I.Evaluated{req, ctx, p, S.Final{w, ts, proposal}})
  for exceeded: {R.finalize(proposal, I.configuration(x), w) == S.response_error(S.Limit{}) : S.Response}
  I.ResponseJustified(S.response_error(S.Limit{}), a, k, x, t)
def limit_logical_final_justifies_limit(a, k, x, t, u, req, ctx, p, w, ts, proposal,
  before, evaluated, exceeded):
  L.Right{(w, req, ctx, p, ts, proposal, L.Both{(u, L.Both{before, evaluated}), exceeded})}

law failure_real_of_tool_justifies_failure:
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for -t: Nat
  for u: Nat
  for stage: X.Stage
  for id: String
  for fatal: Bool
  for before: {Nat.is_lt(u, t) == True{} : Bool}
  for occurred: I.Happens(a, k, x, u, I.FailedEnvironment{stage, id, fatal})
  for real: I.FailureReal(a, k, x, u, stage, id, fatal)
  L.E<I.ResponseJustified(S.response_error(S.Failure{}), a, k, x, t),
    I.FailureReal(a, k, x, u, stage, id, fatal)>
def failure_real_of_tool_justifies_failure(a, k, x, t, u, stage, id, fatal, before, occurred, real):
  L.Both{(stage, id, fatal, u, L.Both{before, occurred}), real}
