# Pure M7: finite serial runs from an Init-accepted seed under a fixed
# configuration. The validity of each reached root is derived step by step
# from the previous one; at step j the universal Core theorem is applied.
import Base
import ../contract/Theorems.bend as C
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../contract/Logic.bend as L
import ../src/Core.bend as N
import ../src/Gate.bend as K
import ./Foundations.bend as F
import ./Init.bend as Init
import ./CoreClauses.bend as Core

# The root a successful conclusion publishes; d when nothing was concluded.
def root(m: Maybe<&2, N.Conclusion>, d: D.State) -> D.State:
  match m:
    case None{}: d
    case Some{N.Conclusion{state, response, bytes}}: state

def rooted(q: Maybe<&2, List<&2, U32>>, -w: D.State, -ts: List<&2, S.OperationEvent>,
  -response: S.Response, -s: D.State) ->
  {root(K.conclude(N.prepare_bytes(q, w, ts, response), s), S.publish(response, s, w)) ==
    S.publish(response, s, w) : D.State}:
  match q:
    case None{}: {==}
    case Some{bytes}: {==}

def concluded(-a: Maybe<&2, N.Conclusion>, -next: D.State, -response: S.Response,
  -bytes: List<&2, U32>, -d: D.State, published: {a == Some{N.Conclusion{next, response, bytes}} : Maybe<&2, N.Conclusion>}) ->
  {root(a, d) == next : D.State}:
  Equal.cong(Maybe<&2, N.Conclusion>, D.State, m => root(m, d), a, Some{N.Conclusion{next, response, bytes}}, published)

# A halted gate publishes exactly the previous root.
def kept(+response: S.Response, +s: D.State, -next: D.State, -bytes: List<&2, U32>,
  published: {K.early(response, s) == Some{N.Conclusion{next, response, bytes}} : Maybe<&2, N.Conclusion>}) ->
  {s == next : D.State}:
  Equal.trans(D.State, s, root(K.early(response, s), S.publish(response, s, s)), next,
    Equal.trans(D.State, s, S.publish(response, s, s), root(K.early(response, s), S.publish(response, s, s)),
      Equal.sym(D.State, S.publish(response, s, s), s, Core.publish_same(response, s)),
      Equal.sym(D.State, root(K.early(response, s), S.publish(response, s, s)), S.publish(response, s, s),
        rooted(P.frame(S.response_value(response)), s, Nil{}, response, s))),
    concluded(K.early(response, s), next, response, bytes, S.publish(response, s, s), published))

# The finished root equals the root of the Completion clause's conclusion.
def completed(-c: S.Configuration, -s: D.State, -w: D.State, -ts: List<&2, S.OperationEvent>,
  -proposal: S.Response, -next: D.State, -response: S.Response, -bytes: List<&2, U32>,
  published: {K.finish(S.Final{w, ts, proposal}, c, s) == Some{N.Conclusion{next, response, bytes}} : Maybe<&2, N.Conclusion>},
  completion: C.Completion(c, s, w, ts, proposal)) -> R.Valid(c, next):
  match completion:
    case (other, answer, encoded, L.Both{finish, L.Both{final, L.Both{publication, L.Both{valid, rest}}}}):
      %Equal.sym(D.State, next, other,
        Equal.trans(D.State, next, root(K.finish(S.Final{w, ts, proposal}, c, s), next), other,
          Equal.sym(D.State, root(K.finish(S.Final{w, ts, proposal}, c, s), next), next,
            concluded(K.finish(S.Final{w, ts, proposal}, c, s), next, response, bytes, next, published)),
          concluded(K.finish(S.Final{w, ts, proposal}, c, s), other, answer, encoded, next, finish))) :
        R.Valid(c, _)
      valid

# One step preserves validity of the published root.
def advanced(+e: D.Schema, -laws: S.Laws, +lim: S.Limits, +amb: String, +s: D.State, +r: P.Request,
  -admit: K.Oracle(), -next: D.State,
  step: C.Step<S.Configuration{e, laws, lim, amb}, s, r, admit, next>,
  sound: C.OracleSoundness(S.Configuration{e, laws, lim, amb}, r, admit),
  valid: R.Valid(S.Configuration{e, laws, lim, amb}, s),
  +configured: {R.configuration_is_valid(S.Configuration{e, laws, lim, amb}) == True{} : Bool}) ->
  R.Valid(S.Configuration{e, laws, lim, amb}, next):
  match step:
    case C.StepHalted{+response, bytes, halted, published}:
      %kept(response, s, next, bytes, published) : R.Valid(S.Configuration{e, laws, lim, amb}, _)
      valid
    case C.StepRan{+ctx, p, +n, +w, +ts, +proposal, response, bytes, +authenticated, admitted, finished, published}:
      F.combined_pair(R.Valid(S.Configuration{e, laws, lim, amb}, next),
        R.Certifies(S.Configuration{e, laws, lim, amb}, K.code(r), p, ctx, K.arguments(r)),
        @state: D.State -> C.Terminates(p, S.Configuration{e, laws, lim, amb}, state, ctx, K.arguments(r)),
        (%admitted : C.VerdictSound(_, S.Configuration{e, laws, lim, amb}, r, ctx) sound(ctx)),
        certificate => termination =>
          F.combined_pair(R.Valid(S.Configuration{e, laws, lim, amb}, next),
            {N.traverse(n, N.start(p, ctx, K.arguments(r), s), e) == S.execute(n, p, e, s, ctx, K.arguments(r)) : S.Trace},
            Core.TraceGood(S.execute(n, p, e, s, ctx, K.arguments(r))),
            Core.faithful_good(n, p, ctx, K.arguments(r), e, s),
            faithful => good =>
              +reference = Equal.trans(S.Trace, S.execute(n, p, e, s, ctx, K.arguments(r)),
                N.traverse(n, N.start(p, ctx, K.arguments(r), s), e), S.Final{w, ts, proposal},
                Equal.sym(S.Trace, N.traverse(n, N.start(p, ctx, K.arguments(r), s), e),
                  S.execute(n, p, e, s, ctx, K.arguments(r)), faithful), finished)
              completed(S.Configuration{e, laws, lim, amb}, s, w, ts, proposal, next, response, bytes, published,
                Core.completion(e, laws, lim, amb, K.code(r), p, ctx, K.arguments(r), certificate, s, valid,
                  K.credential(r), authenticated, n, w, ts, proposal, reference,
                  (%reference : Core.TraceGood(_) good), configured))))

def valid_at(j: Nat, +e: D.Schema, -laws: S.Laws, +lim: S.Limits, +amb: String, +s: D.State,
  run: C.Run<S.Configuration{e, laws, lim, amb}, s>,
  +configured: {R.configuration_is_valid(S.Configuration{e, laws, lim, amb}) == True{} : Bool},
  valid: R.Valid(S.Configuration{e, laws, lim, amb}, s)) ->
  C.ValidAt(j, S.Configuration{e, laws, lim, amb}, s, run):
  match j run:
    case _ C.RunEnd{}: valid
    case 0n C.RunStep{r, admit, next, sound, step, rest}: valid
    case 1n+i C.RunStep{+r, admit, +next, sound, step, rest}:
      valid_at(i, e, laws, lim, amb, next, rest, configured,
        advanced(e, laws, lim, amb, s, r, admit, next, step, sound, valid, configured))

def core_at(j: Nat, k: C.Clause, +e: D.Schema, laws: S.Laws, +lim: S.Limits, +amb: String, +s: D.State,
  run: C.Run<S.Configuration{e, laws, lim, amb}, s>,
  +configured: {R.configuration_is_valid(S.Configuration{e, laws, lim, amb}) == True{} : Bool},
  valid: R.Valid(S.Configuration{e, laws, lim, amb}, s)) ->
  C.CoreAt(j, k, S.Configuration{e, laws, lim, amb}, s, run):
  match j run:
    case _ C.RunEnd{}: Unit{}
    case 0n C.RunStep{+r, admit, next, sound, step, rest}:
      Core.core_theorem()(k, S.Configuration{e, laws, lim, amb}, s, r, admit, configured, valid, sound)
    case 1n+i C.RunStep{+r, admit, +next, sound, step, rest}:
      core_at(i, k, e, laws, lim, amb, next, rest, configured,
        advanced(e, laws, lim, amb, s, r, admit, next, step, sound, valid, configured))

def aspect(a: C.Aspect, j: Nat, +e: D.Schema, laws: S.Laws, +lim: S.Limits, +amb: String, +seed: D.State,
  run: C.Run<S.Configuration{e, laws, lim, amb}, seed>,
  +configured: {R.configuration_is_valid(S.Configuration{e, laws, lim, amb}) == True{} : Bool},
  valid: R.Valid(S.Configuration{e, laws, lim, amb}, seed)) ->
  C.FoldAt(a, S.Configuration{e, laws, lim, amb}, seed, run, j):
  match a:
    case C.StepCore{k}: core_at(j, k, e, laws, lim, amb, seed, run, configured, valid)
    case C.Reached{}: valid_at(j, e, laws, lim, amb, seed, run, configured, valid)

# Init's accepted seed supplies the configuration check and seed validity.
def seeded(a: C.Aspect, j: Nat, +e: D.Schema, laws: S.Laws, +lim: S.Limits, +amb: String, +seed: D.State,
  run: C.Run<S.Configuration{e, laws, lim, amb}, seed>,
  start: L.E<{seed == seed : D.State},
    L.E<{R.configuration_is_valid(S.Configuration{e, laws, lim, amb}) == True{} : Bool},
      R.Valid(S.Configuration{e, laws, lim, amb}, seed)>>) ->
  C.FoldAt(a, S.Configuration{e, laws, lim, amb}, seed, run, j):
  match start:
    case L.Both{same, L.Both{+configured, valid}}:
      aspect(a, j, e, laws, lim, amb, seed, run, configured, valid)

def initialized(a: C.Aspect, j: Nat, +e: D.Schema, laws: S.Laws, +lim: S.Limits, +amb: String, +seed: D.State,
  run: C.Run<S.Configuration{e, laws, lim, amb}, seed>,
  -v: C.SeedVerdict<S.Configuration{e, laws, lim, amb}, seed>,
  started: {C.init(S.Configuration{e, laws, lim, amb}, seed, v) == Some{seed} : Maybe<&2, D.State>},
  init: C.Init(S.Configuration{e, laws, lim, amb}, seed, v)) ->
  C.FoldAt(a, S.Configuration{e, laws, lim, amb}, seed, run, j):
  match init:
    case L.Both{accepted, rest}:
      seeded(a, j, e, laws, lim, amb, seed, run, accepted(seed, started))

def folded(c: S.Configuration, a: C.Aspect, +seed: D.State, v: C.SeedVerdict<c, seed>,
  run: C.Run<c, seed>, started: {C.init(c, seed, v) == Some{seed} : Maybe<&2, D.State>}, j: Nat) ->
  C.FoldAt(a, c, seed, run, j):
  match c:
    case S.Configuration{+e, laws, +lim, +amb}:
      initialized(a, j, e, laws, lim, amb, seed, run, v, started,
        Init.seed_cases(S.Configuration{e, laws, lim, amb}, seed,
          R.configuration_is_valid(S.Configuration{e, S.NoneLaw{}, lim, amb}), v, {==}))

def fold_theorem() -> C.FoldTheorem():
  a => c => +seed => v => run => started => j => folded(c, a, seed, v, run, started, j)
