# The universal Core, unified and fold theorems applied to a concrete valid step: the
# premises are satisfiable, so the theorems are not vacuous. The tasks
# configuration's limits exceed the BendTT kernel's evaluation fuel, so the
# instance uses the small control configuration with a real oracle proof.
import Base
import ../../contract/Data.bend as D
import ../../contract/Semantics.bend as S
import ../../contract/Requirements.bend as R
import ../../contract/Logic.bend as L
import ../../contract/Protocol.bend as P
import ../../contract/Theorems.bend as G
import ../../proof/CoreClauses.bend as Core
import ../../proof/Ingress.bend as Ingress
import ../../src/Resolve.bend as Resolve
import ../../proof/Iteration.bend as Iteration
import ./Controls.bend as X
import ./WrongSteps.bend as Wrong

def refusal_safe(+ctx: D.Context, +s: D.State, n: Nat) ->
  R.SafetyTrace(S.execute(n, X.program(), D.Schema{Nil{}}, s, ctx, D.VAbsent{}),
    X.configuration(), s, ctx, "refuse", D.VAbsent{}):
  match n:
    case 0n: L.Both{Unit{}, Unit{}}
    case 1n+0n: L.Both{L.Both{Unit{}, Unit{}}, L.Both{Unit{}, Unit{}}}
    case 1n+1n+k: L.Both{L.Both{Unit{}, Unit{}}, L.Both{Unit{}, Unit{}}}

# Wrong.accept admits X.program for every authenticated context.
law controls_oracle_sound:
  G.OracleSoundness(X.configuration(), X.request(), Wrong.accept)
def controls_oracle_sound(ctx):
  +ctx = ctx
  L.Both{+s => valid => identity => n => refusal_safe(ctx, s, n),
    +s => (1n, s, Nil{}, S.Response{S.Refusal{}, D.VAbsent{}}, {==})}

law controls_configured:
  {R.configuration_is_valid(X.configuration()) == True{} : Bool}
def controls_configured(): {==}

law controls_core:
  for k: G.Clause
  G.Core(k, X.configuration(), X.seed(), X.request(), Wrong.accept)
def controls_core(k):
  Core.core_theorem()(k, X.configuration(), X.seed(), X.request(), Wrong.accept,
    controls_configured(), X.seed_valid(), controls_oracle_sound)


# A direct request reaches Core unchanged after the actual selection.
law controls_unified:
  for k: G.Clause
  G.UnifiedCore(k, X.configuration(), X.seed(), Nil{}, Resolve.Direct{X.request()}, Wrong.accept)
def controls_unified(k):
  Ingress.unified_core_theorem()(k, X.configuration(), X.seed(), Nil{}, Resolve.Direct{X.request()},
    Wrong.accept, controls_configured(), X.seed_valid(), controls_oracle_sound)


# A one-step run: Wrong.accept admits X.program, which refuses; the finished
# root is exactly the seed.
def refused() -> S.Response:
  R.finalize(S.Response{S.Refusal{}, D.VAbsent{}}, X.configuration(), X.seed())

def refused_bytes() -> List<&2, U32>:
  Maybe.default(&2, List<&2, U32>, P.frame(S.response_value(refused())), Nil{})

def run() -> G.Run<X.configuration(), X.seed()>:
  G.RunStep{X.request(), Wrong.accept, X.seed(), controls_oracle_sound,
    G.StepRan{X.context(), X.program(), 1n, X.seed(), Nil{}, S.Response{S.Refusal{}, D.VAbsent{}},
      refused(), refused_bytes(), {==}, {==}, {==}, {==}},
    G.RunEnd{}}

law controls_started:
  {G.init(X.configuration(), X.seed(), G.SeedAccept{X.seed_valid()}) == Some{X.seed()} : Maybe<&2, D.State>}
def controls_started(): {==}

law controls_fold:
  for a: G.Aspect
  for j: Nat
  G.FoldAt(a, X.configuration(), X.seed(), run(), j)
def controls_fold(a, j):
  Iteration.fold_theorem()(a, X.configuration(), X.seed(), G.SeedAccept{X.seed_valid()}, run(),
    controls_started(), j)
