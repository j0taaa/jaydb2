# Inhabitants of the four Core clauses for the actual executable gate.
# Each clause theorem receives its own copy of the universal premises; the
# configuration is opened once, its law list is consumed only by the oracle
# call, and every other use reads the copyable schema, limits and environment.
import Base
import ../contract/Theorems.bend as C
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../contract/Logic.bend as L
import ../contract/RequestFacts.bend as I
import ../src/Core.bend as N
import ../src/Gate.bend as K
import ./Foundations.bend as F
import ./Authentication.bend as A
import ./Preparation.bend as Q
import ./Call.bend as Call

# Continuation eliminators: computed pairs cannot be matched directly.
def opened(-A: Type, -B: @-x: A -> Type, -T: Type, pair: &x: A -> B(x), k: @x: A -> B(x) -> T) -> T:
  match pair:
    case (x, b): k(x, b)

def opened_data(-A: Type, -B: @-x: A -> Data, -T: Type, pair: &x: A -> B(x), k: @x: A -> B(x) -> T) -> T:
  match pair:
    case (x, b): k(x, b)

# ---------------------------------------------------------------------------
# Configuration and finalization facts on the opened configuration.

def limits_valid(+e: D.Schema, -laws: S.Laws, +lim: S.Limits, +amb: String,
  configured: {R.configuration_is_valid(S.Configuration{e, laws, lim, amb}) == True{} : Bool}) ->
  {R.limits_all_valid(lim) == True{} : Bool}:
  F.and_boolean_right(D.schema_valid(e), R.limits_all_valid(lim),
    F.and_boolean_left(D.schema_valid(e) && R.limits_all_valid(lim), D.unicode_valid(amb), configured))

# Finalization reads only schema and limits; this is the copyable witness.
def finalized(proposal: S.Response, +e: D.Schema, +lim: S.Limits, +amb: String, +w: D.State) -> S.Response:
  R.finalize(proposal, S.Configuration{e, S.NoneLaw{}, lim, amb}, w)

def finalized_exact(+proposal: S.Response, +e: D.Schema, -laws: S.Laws, +lim: S.Limits, +amb: String, +w: D.State) ->
  {R.finalize(proposal, S.Configuration{e, laws, lim, amb}, w) == finalized(proposal, e, lim, amb, w) : S.Response}:
  Call.finalize_independent_of_list_of_laws(proposal, e, laws, lim, amb, w)

def publish_same(r: S.Response, -s: D.State) -> {S.publish(r, s, s) == s : D.State}:
  match r:
    case S.Response{S.Success{}, v}: {==}
    case S.Response{S.Refusal{}, v}: {==}
    case S.Response{S.Input{}, v}: {==}
    case S.Response{S.Authentication{}, v}: {==}
    case S.Response{S.Certificate{}, v}: {==}
    case S.Response{S.DataError{}, v}: {==}
    case S.Response{S.Limit{}, v}: {==}
    case S.Response{S.Failure{}, v}: {==}

# The actual finisher returns the framed response and its publication.
def finished(-c: S.Configuration, +s: D.State, +w: D.State, +ts: List<&2, S.OperationEvent>,
  -proposal: S.Response, +response: S.Response, +lim: S.Limits,
  +exact: {R.finalize(proposal, c, w) == response : S.Response},
  limits: {R.limits_all_valid(lim) == True{} : Bool},
  fits: {R.fits(R.limit_response(lim), S.response_value(response)) == True{} : Bool}) ->
  &bytes: List<&2, U32> ->
    L.E<{K.finish(S.Final{w, ts, proposal}, c, s) ==
        Some{N.Conclusion{S.publish(response, s, w), response, bytes}} : Maybe<&2, N.Conclusion>},
      {P.frame(S.response_value(response)) == Some{bytes} : Maybe<&2, List<&2, U32>>}>:
  opened_data(List<&2, U32>, bytes => {P.frame(S.response_value(response)) == Some{bytes} : Maybe<&2, List<&2, U32>>},
    (&bytes: List<&2, U32> ->
      L.E<{K.finish(S.Final{w, ts, proposal}, c, s) ==
          Some{N.Conclusion{S.publish(response, s, w), response, bytes}} : Maybe<&2, N.Conclusion>},
        {P.frame(S.response_value(response)) == Some{bytes} : Maybe<&2, List<&2, U32>>}>),
    Call.response_preparable_has_framing(S.response_value(response), lim, limits, fits),
    +bytes => +framed =>
      (bytes, L.Both{
        (%Equal.sym(S.Response, R.finalize(proposal, c, w), response, exact) : {K.conclude(N.prepare_response(_, w, ts), s) ==
            Some{N.Conclusion{S.publish(response, s, w), response, bytes}} : Maybe<&2, N.Conclusion>}
          Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, N.Conclusion>,
            q => K.conclude(N.prepare_bytes(q, w, ts, response), s),
            P.frame(S.response_value(response)), Some{bytes}, framed)),
        framed}))

# Fixed early errors are framed within the response limit and keep the root.
def early_error(+status: S.Status, -e: D.Schema, -laws: S.Laws, +lim: S.Limits, -amb: String,
  +s: D.State, +limits: {R.limits_all_valid(lim) == True{} : Bool}, error: Q.Error(status)) ->
  C.Early(S.Configuration{e, laws, lim, amb}, s, S.response_error(status)):
  F.combined_pair(C.Early(S.Configuration{e, laws, lim, amb}, s, S.response_error(status)),
    I.ErrorFixed(S.response_error(status)),
    {R.fits(R.limit_response(lim), S.response_value(S.response_error(status))) == True{} : Bool},
    Q.error_preparable(status, lim, limits, error),
    payload => +fits =>
      opened_data(List<&2, U32>, bytes => {P.frame(S.response_value(S.response_error(status))) == Some{bytes} : Maybe<&2, List<&2, U32>>},
        C.Early(S.Configuration{e, laws, lim, amb}, s, S.response_error(status)),
        Call.response_preparable_has_framing(S.response_value(S.response_error(status)), lim, limits, fits),
        +bytes => +framed =>
          (bytes, L.Both{
            (%publish_same(S.response_error(status), s) :
              {K.early(S.response_error(status), s) == Some{N.Conclusion{_, S.response_error(status), bytes}} : Maybe<&2, N.Conclusion>}
              Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, N.Conclusion>,
                q => K.conclude(N.prepare_bytes(q, s, Nil{}, S.response_error(status)), s),
                P.frame(S.response_value(S.response_error(status))), Some{bytes}, framed)),
            L.Both{framed, fits}})))

# ---------------------------------------------------------------------------
# One pass over the actual program: reference fidelity plus no generic failure.

def StepGood(step: S.Step) -> Type:
  match step:
    case S.Stopped{w, r}: C.NoFailure(r)
    case _: Unit

def TraceGood(t: S.Trace) -> Type:
  match t:
    case S.Final{w, ts, r}: C.NoFailure(r)
    case _: Unit

def applied(result: D.ResultOp, +s: D.State, +o: D.Operation, k: S.Return -> S.Action) ->
  &step: S.Step -> L.E<{step == S.apply(result, s, o, k) : S.Step}, StepGood(step)>:
  match result:
    case D.FailureData{}:
      (S.OperationFailed{s, S.OperationEvent{o, S.ErrorOfData{}}}, L.Both{{==}, Unit{}})
    case D.Observed{+v}:
      (S.Continue{s, k(S.Datum{v}), S.OperationEvent{o, S.Reading{v}}}, L.Both{{==}, Unit{}})
    case D.Changed{w}:
      (S.Continue{w, k(S.UnitValue{}), S.OperationEvent{o, S.Write{}}}, L.Both{{==}, Unit{}})

# The action is consumed once; the returned step is exactly S.step's result.
def stepped(a: S.Action, +e: D.Schema, +s: D.State) ->
  &step: S.Step -> L.E<{step == S.step(a, e, s) : S.Step}, StepGood(step)>:
  match a:
    case S.Finish{v}: (S.Stopped{s, S.Response{S.Success{}, v}}, L.Both{{==}, Unit{}})
    case S.Refuse{v}: (S.Stopped{s, S.Response{S.Refusal{}, v}}, L.Both{{==}, Unit{}})
    case S.Access{+o, k}: applied(D.operate(e, s, o), s, o, k)

def Corresponds(-n: Nat, -step: S.Step, -e: D.Schema, -events: List<&2, S.OperationEvent>) -> Type:
  L.E<{N.traverse(n, N.step_machine(step, events), e) == S.resume_execution_trace(n, step, e, events) : S.Trace},
    TraceGood(S.resume_execution_trace(n, step, e, events))>

def corresponds_good(n: Nat, step: S.Step, +e: D.Schema, +events: List<&2, S.OperationEvent>,
  good: StepGood(step)) -> Corresponds(n, step, e, events):
  match n step:
    case 0n S.Continue{w, a, event}: L.Both{{==}, Unit{}}
    case 0n S.Stopped{w, response}: L.Both{{==}, good}
    case 0n S.OperationFailed{w, event}: L.Both{{==}, Unit{}}
    case 1n+m S.Continue{+w, a, +event}:
      opened(S.Step, next => L.E<{next == S.step(a, e, w) : S.Step}, StepGood(next)>,
        Corresponds(m, S.step(a, e, w), e, S.append(events, event)),
        stepped(a, e, w),
        next => facts =>
          F.combined_pair(Corresponds(m, S.step(a, e, w), e, S.append(events, event)),
            {next == S.step(a, e, w) : S.Step}, StepGood(next), facts,
            exact => next_good =>
              %exact : Corresponds(m, _, e, S.append(events, event))
              corresponds_good(m, next, e, S.append(events, event), next_good)))
    case 1n+m S.Stopped{w, response}:
      %Equal.sym(S.Trace, N.traverse(m, N.Stopped{w, events, response}, e), S.Final{w, events, response},
        N.stopped_absorbs(m, w, events, response, e)) : L.E<{_ == S.Final{w, events, response} : S.Trace}, C.NoFailure(response)>
      L.Both{{==}, good}
    case 1n+m S.OperationFailed{w, event}:
      %Equal.sym(S.Trace, N.traverse(m, N.Stopped{w, S.append(events, event), S.response_error(S.DataError{})}, e),
        S.Final{w, S.append(events, event), S.response_error(S.DataError{})},
        N.stopped_absorbs(m, w, S.append(events, event), S.response_error(S.DataError{}), e)) :
        L.E<{_ == S.Final{w, S.append(events, event), S.Response{S.DataError{}, D.VAbsent{}}} : S.Trace}, Unit>
      L.Both{{==}, Unit{}}

def Faithful(-n: Nat, -p: S.Program, -ctx: D.Context, -args: D.Value, -e: D.Schema, -s: D.State) -> Type:
  L.E<{N.traverse(n, N.start(p, ctx, args, s), e) == S.execute(n, p, e, s, ctx, args) : S.Trace},
    TraceGood(S.execute(n, p, e, s, ctx, args))>

def faithful_good(n: Nat, p: S.Program, +ctx: D.Context, +args: D.Value, +e: D.Schema, +s: D.State) ->
  Faithful(n, p, ctx, args, e, s):
  match n:
    case 0n: L.Both{{==}, Unit{}}
    case 1n+m:
      opened(S.Step, first => L.E<{first == S.step(S.start(p, ctx, args), e, s) : S.Step}, StepGood(first)>,
        Corresponds(m, S.step(S.start(p, ctx, args), e, s), e, Nil{}),
        stepped(S.start(p, ctx, args), e, s),
        first => facts =>
          F.combined_pair(Corresponds(m, S.step(S.start(p, ctx, args), e, s), e, Nil{}),
            {first == S.step(S.start(p, ctx, args), e, s) : S.Step}, StepGood(first), facts,
            exact => good =>
              %exact : Corresponds(m, _, e, Nil{})
              corresponds_good(m, first, e, Nil{}, good)))

# ---------------------------------------------------------------------------
# Completion of one final trace from the certificate.

# The certificate is applied only on success; otherwise the root is kept.
def publication_valid(response: S.Response, -c: S.Configuration, -s: D.State, -ctx: D.Context,
  -code: String, -args: D.Value, -w: D.State, -ts: List<&2, S.OperationEvent>,
  final: R.Valid(c, s) -> R.SafetyFinal(c, s, ctx, code, args, w, ts, response), valid: R.Valid(c, s)) ->
  R.Valid(c, S.publish(response, s, w)):
  match response:
    case S.Response{S.Success{}, v}:
      L.and_right(S.Satisfies(c, S.Closed{s, ctx, code, args, w, ts, S.Response{S.Success{}, v}}),
        R.Valid(c, w), final(valid))
    case S.Response{S.Refusal{}, v}: valid
    case S.Response{S.Input{}, v}: valid
    case S.Response{S.Authentication{}, v}: valid
    case S.Response{S.Certificate{}, v}: valid
    case S.Response{S.DataError{}, v}: valid
    case S.Response{S.Limit{}, v}: valid
    case S.Response{S.Failure{}, v}: valid

def technique_no_failure(ok: Bool, fits: Bool, r: S.Response, h: C.NoFailure(r)) ->
  C.NoFailure(R.response_technique_cases(ok, fits, r)):
  match ok fits:
    case False{} _: Unit{}
    case True{} False{}: Unit{}
    case True{} True{}: h

def state_no_failure(ok: Bool, fits: Bool, r: S.Response, h: C.NoFailure(r)) ->
  C.NoFailure(R.state_technical_cases(ok, fits, r)):
  match ok fits:
    case False{} _: Unit{}
    case True{} False{}: Unit{}
    case True{} True{}: h

def finalize_no_failure(r: S.Response, c: S.Configuration, +w: D.State, h: C.NoFailure(r)) ->
  C.NoFailure(R.finalize(r, c, w)):
  match r c:
    case S.Response{S.Success{}, +v} S.Configuration{e, laws, +lim, amb}:
      state_no_failure(D.structure(e, w), R.fits(R.limit_state(lim), D.state_value(w)),
        R.response_technique_cases(D.value_valid(v),
          R.fits(R.limit_response(lim), S.response_value(S.Response{S.Success{}, v})), S.Response{S.Success{}, v}),
        technique_no_failure(D.value_valid(v),
          R.fits(R.limit_response(lim), S.response_value(S.Response{S.Success{}, v})), S.Response{S.Success{}, v}, Unit{}))
    case S.Response{S.Refusal{}, +v} S.Configuration{e, laws, +lim, amb}:
      technique_no_failure(D.value_valid(v),
        R.fits(R.limit_response(lim), S.response_value(S.Response{S.Refusal{}, v})), S.Response{S.Refusal{}, v}, Unit{})
    case S.Response{S.Failure{}, v} S.Configuration{e, laws, lim, amb}: h
    case S.Response{S.Input{}, v} S.Configuration{e, laws, lim, amb}: Unit{}
    case S.Response{S.Authentication{}, v} S.Configuration{e, laws, lim, amb}: Unit{}
    case S.Response{S.Certificate{}, v} S.Configuration{e, laws, lim, amb}: Unit{}
    case S.Response{S.DataError{}, v} S.Configuration{e, laws, lim, amb}: Unit{}
    case S.Response{S.Limit{}, v} S.Configuration{e, laws, lim, amb}: Unit{}

# The certificate is applied once, at the reference trace equal to the final.
def completion(+e: D.Schema, -laws: S.Laws, +lim: S.Limits, +amb: String,
  -code: String, -p: S.Program, +ctx: D.Context, +args: D.Value,
  certificate: R.Certifies(S.Configuration{e, laws, lim, amb}, code, p, ctx, args),
  +s: D.State, valid: R.Valid(S.Configuration{e, laws, lim, amb}, s), +cred: String,
  aut: {D.authenticate(s, cred) == Some{ctx} : Maybe<&2, D.Context>},
  +n: Nat, +w: D.State, +ts: List<&2, S.OperationEvent>, +proposal: S.Response,
  reference: {S.execute(n, p, e, s, ctx, args) == S.Final{w, ts, proposal} : S.Trace},
  good: C.NoFailure(proposal),
  configured: {R.configuration_is_valid(S.Configuration{e, laws, lim, amb}) == True{} : Bool}) ->
  C.Completion(S.Configuration{e, laws, lim, amb}, s, w, ts, proposal):
  +limits = limits_valid(e, laws, lim, amb, configured)
  +exact = finalized_exact(proposal, e, laws, lim, amb, w)
  +response = finalized(proposal, e, lim, amb, w)
  F.combined_pair(C.Completion(S.Configuration{e, laws, lim, amb}, s, w, ts, proposal),
    I.ErrorFixed(response), {R.fits(R.limit_response(lim), S.response_value(response)) == True{} : Bool},
    Q.finalize_guarantees_payload_and_size(proposal, S.Configuration{e, S.NoneLaw{}, lim, amb}, w, limits),
    payload => +fits =>
      opened(List<&2, U32>, bytes =>
          L.E<{K.finish(S.Final{w, ts, proposal}, S.Configuration{e, laws, lim, amb}, s) ==
              Some{N.Conclusion{S.publish(response, s, w), response, bytes}} : Maybe<&2, N.Conclusion>},
            {P.frame(S.response_value(response)) == Some{bytes} : Maybe<&2, List<&2, U32>>}>,
        C.Completion(S.Configuration{e, laws, lim, amb}, s, w, ts, proposal),
        finished(S.Configuration{e, laws, lim, amb}, s, w, ts, proposal, response, lim, exact, limits, fits),
        +bytes => framing =>
          F.combined_pair(C.Completion(S.Configuration{e, laws, lim, amb}, s, w, ts, proposal),
            {K.finish(S.Final{w, ts, proposal}, S.Configuration{e, laws, lim, amb}, s) ==
              Some{N.Conclusion{S.publish(response, s, w), response, bytes}} : Maybe<&2, N.Conclusion>},
            {P.frame(S.response_value(response)) == Some{bytes} : Maybe<&2, List<&2, U32>>}, framing,
            finish => framed =>
              (S.publish(response, s, w), response, bytes, L.Both{finish,
                L.Both{Equal.sym(S.Response, R.finalize(proposal, S.Configuration{e, laws, lim, amb}, w), response, exact),
                  L.Both{{==}, L.Both{
                    publication_valid(response, S.Configuration{e, laws, lim, amb}, s, ctx, code, args, w, ts,
                      initial =>
                      F.combined_pair(R.SafetyFinal(S.Configuration{e, laws, lim, amb}, s, ctx, code, args, w, ts, response),
                        {R.structure(S.Configuration{e, laws, lim, amb}, s) == True{} : Bool},
                        S.Satisfies(S.Configuration{e, laws, lim, amb}, S.Stable{s}), initial,
                        +structure => stable =>
                          (%exact : R.SafetyFinal(S.Configuration{e, laws, lim, amb}, s, ctx, code, args, w, ts, _)
                            L.and_right(R.SafetyPrefix(S.Configuration{e, laws, lim, amb}, s, ctx, code, args, w, ts),
                              R.SafetyFinal(S.Configuration{e, laws, lim, amb}, s, ctx, code, args, w, ts,
                                R.finalize(proposal, S.Configuration{e, laws, lim, amb}, w)),
                              (%reference : R.SafetyTrace(_, S.Configuration{e, laws, lim, amb}, s, ctx, code, args)
                                certificate(s, L.Both{structure, stable},
                                  A.authentication_implies_context_present(e, s, cred, ctx,
                                    F.and_boolean_left(D.structure(e, s), R.fits(R.limit_state(lim), D.state_value(s)), structure), aut), n))))),
                      valid),
                    L.Both{framed, L.Both{fits,
                      finalize_no_failure(proposal, S.Configuration{e, S.NoneLaw{}, lim, amb}, w, good)}}}}}}))))

# ---------------------------------------------------------------------------
# Safety of every prefix of the actual machine.

def safety_trace(+e: D.Schema, -laws: S.Laws, +lim: S.Limits, +amb: String,
  -code: String, p: S.Program, +ctx: D.Context, +args: D.Value,
  certificate: R.Certifies(S.Configuration{e, laws, lim, amb}, code, p, ctx, args),
  +s: D.State, valid: R.Valid(S.Configuration{e, laws, lim, amb}, s), +cred: String,
  aut: {D.authenticate(s, cred) == Some{ctx} : Maybe<&2, D.Context>}, +n: Nat) ->
  R.SafetyTrace(N.traverse(n, N.start(p, ctx, args, s), e),
    S.Configuration{e, laws, lim, amb}, s, ctx, code, args):
  F.combined_pair(
    R.SafetyTrace(N.traverse(n, N.start(p, ctx, args, s), e),
      S.Configuration{e, laws, lim, amb}, s, ctx, code, args),
    {R.structure(S.Configuration{e, laws, lim, amb}, s) == True{} : Bool},
    S.Satisfies(S.Configuration{e, laws, lim, amb}, S.Stable{s}), valid,
    +structure => stable =>
      %Equal.sym(S.Trace, N.traverse(n, N.start(p, ctx, args, s), e),
        S.execute(n, p, e, s, ctx, args),
        N.fidelity_of_all_os_prefixes(n, p, ctx, args, e, s)) :
          R.SafetyTrace(_, S.Configuration{e, laws, lim, amb}, s, ctx, code, args)
      certificate(s, L.Both{structure, stable},
        A.authentication_implies_context_present(e, s, cred, ctx,
          F.and_boolean_left(D.structure(e, s),
            R.fits(R.limit_state(lim), D.state_value(s)), structure), aut), n))

# ---------------------------------------------------------------------------
# Progress: the admitted termination proof reaches a final, finalizable trace.

def limited(+e: D.Schema, -laws: S.Laws, +lim: S.Limits, +amb: String, +s: D.State,
  +w: D.State, +ts: List<&2, S.OperationEvent>, +proposal: S.Response,
  +limits: {R.limits_all_valid(lim) == True{} : Bool},
  +exact: {R.finalize(proposal, S.Configuration{e, laws, lim, amb}, w) == finalized(proposal, e, lim, amb, w) : S.Response},
  within: C.WithinLimits(S.Final{w, ts, proposal}, S.Configuration{e, laws, lim, amb})) ->
  &next: D.State -> &response: S.Response -> &bytes: List<&2, U32> ->
    L.E<{K.finish(S.Final{w, ts, proposal}, S.Configuration{e, laws, lim, amb}, s) ==
        Some{N.Conclusion{next, response, bytes}} : Maybe<&2, N.Conclusion>},
      C.ProgramOutcome(response)>:
  F.combined_pair((&next: D.State -> &response: S.Response -> &bytes: List<&2, U32> ->
      L.E<{K.finish(S.Final{w, ts, proposal}, S.Configuration{e, laws, lim, amb}, s) ==
          Some{N.Conclusion{next, response, bytes}} : Maybe<&2, N.Conclusion>},
        C.ProgramOutcome(response)>),
    C.ProgramOutcome(proposal), {R.finalize(proposal, S.Configuration{e, laws, lim, amb}, w) == proposal : S.Response},
    within,
    outcome => +same =>
      F.combined_pair((&next: D.State -> &response: S.Response -> &bytes: List<&2, U32> ->
          L.E<{K.finish(S.Final{w, ts, proposal}, S.Configuration{e, laws, lim, amb}, s) ==
              Some{N.Conclusion{next, response, bytes}} : Maybe<&2, N.Conclusion>},
            C.ProgramOutcome(response)>),
        I.ErrorFixed(finalized(proposal, e, lim, amb, w)),
        {R.fits(R.limit_response(lim), S.response_value(finalized(proposal, e, lim, amb, w))) == True{} : Bool},
        Q.finalize_guarantees_payload_and_size(proposal, S.Configuration{e, S.NoneLaw{}, lim, amb}, w, limits),
        payload => fits =>
          opened(List<&2, U32>, bytes =>
              L.E<{K.finish(S.Final{w, ts, proposal}, S.Configuration{e, laws, lim, amb}, s) ==
                  Some{N.Conclusion{S.publish(proposal, s, w), proposal, bytes}} : Maybe<&2, N.Conclusion>},
                {P.frame(S.response_value(proposal)) == Some{bytes} : Maybe<&2, List<&2, U32>>}>,
            (&next: D.State -> &response: S.Response -> &bytes: List<&2, U32> ->
              L.E<{K.finish(S.Final{w, ts, proposal}, S.Configuration{e, laws, lim, amb}, s) ==
                  Some{N.Conclusion{next, response, bytes}} : Maybe<&2, N.Conclusion>},
                C.ProgramOutcome(response)>),
            finished(S.Configuration{e, laws, lim, amb}, s, w, ts, proposal, proposal, lim, same, limits,
              (%Equal.trans(S.Response, finalized(proposal, e, lim, amb, w),
                  R.finalize(proposal, S.Configuration{e, laws, lim, amb}, w), proposal,
                  Equal.sym(S.Response, R.finalize(proposal, S.Configuration{e, laws, lim, amb}, w),
                    finalized(proposal, e, lim, amb, w), exact), same) :
                {R.fits(R.limit_response(lim), S.response_value(_)) == True{} : Bool}
                fits)),
            +bytes => framing =>
              F.combined_pair((&next: D.State -> &response: S.Response -> &bytes: List<&2, U32> ->
                  L.E<{K.finish(S.Final{w, ts, proposal}, S.Configuration{e, laws, lim, amb}, s) ==
                      Some{N.Conclusion{next, response, bytes}} : Maybe<&2, N.Conclusion>},
                    C.ProgramOutcome(response)>),
                {K.finish(S.Final{w, ts, proposal}, S.Configuration{e, laws, lim, amb}, s) ==
                  Some{N.Conclusion{S.publish(proposal, s, w), proposal, bytes}} : Maybe<&2, N.Conclusion>},
                {P.frame(S.response_value(proposal)) == Some{bytes} : Maybe<&2, List<&2, U32>>}, framing,
                finish => framed => (S.publish(proposal, s, w), proposal, bytes, L.Both{finish, outcome})))))

def progressed(+e: D.Schema, -laws: S.Laws, +lim: S.Limits, +amb: String,
  -code: String, p: S.Program, +ctx: D.Context, +args: D.Value,
  certificate: R.Certifies(S.Configuration{e, laws, lim, amb}, code, p, ctx, args),
  +s: D.State, valid: R.Valid(S.Configuration{e, laws, lim, amb}, s), +cred: String,
  aut: {D.authenticate(s, cred) == Some{ctx} : Maybe<&2, D.Context>},
  +configured: {R.configuration_is_valid(S.Configuration{e, laws, lim, amb}) == True{} : Bool},
  +n: Nat, +w: D.State, +ts: List<&2, S.OperationEvent>, +proposal: S.Response,
  +reference: {S.execute(n, p, e, s, ctx, args) == S.Final{w, ts, proposal} : S.Trace}) ->
  C.Progress(S.Configuration{e, laws, lim, amb}, s, N.start(p, ctx, args, s)):
  F.combined_pair(C.Progress(S.Configuration{e, laws, lim, amb}, s, N.start(p, ctx, args, s)),
    {N.traverse(n, N.start(p, ctx, args, s), e) == S.execute(n, p, e, s, ctx, args) : S.Trace},
    TraceGood(S.execute(n, p, e, s, ctx, args)),
    faithful_good(n, p, ctx, args, e, s),
    faithful => good =>
      (n, w, ts, proposal, L.Both{
        Equal.trans(S.Trace, N.traverse(n, N.start(p, ctx, args, s), e), S.execute(n, p, e, s, ctx, args),
          S.Final{w, ts, proposal}, faithful, reference),
        L.Both{
          completion(e, laws, lim, amb, code, p, ctx, args, certificate, s, valid, cred, aut,
            n, w, ts, proposal, reference, (%reference : TraceGood(_) good), configured),
          within => limited(e, laws, lim, amb, s, w, ts, proposal,
            limits_valid(e, laws, lim, amb, configured), finalized_exact(proposal, e, laws, lim, amb, w), within)}}))

def progress(+e: D.Schema, -laws: S.Laws, +lim: S.Limits, +amb: String,
  -code: String, p: S.Program, +ctx: D.Context, +args: D.Value,
  certificate: R.Certifies(S.Configuration{e, laws, lim, amb}, code, p, ctx, args),
  +s: D.State, valid: R.Valid(S.Configuration{e, laws, lim, amb}, s), +cred: String,
  aut: {D.authenticate(s, cred) == Some{ctx} : Maybe<&2, D.Context>},
  +configured: {R.configuration_is_valid(S.Configuration{e, laws, lim, amb}) == True{} : Bool},
  terminated: I.Terminates(p, e, s, ctx, args)) ->
  C.Progress(S.Configuration{e, laws, lim, amb}, s, N.start(p, ctx, args, s)):
  match terminated:
    case (n, w, ts, proposal, reference):
      progressed(e, laws, lim, amb, code, p, ctx, args, certificate, s, valid, cred, aut, configured,
        n, w, ts, proposal, reference)

# ---------------------------------------------------------------------------
# Clause dispatch over the actual gate result.

def accepted(k: C.Clause, v: K.Verdict, +e: D.Schema, -laws: S.Laws, +lim: S.Limits, +amb: String,
  +s: D.State, +r: P.Request, -admit: K.Oracle(), +ctx: D.Context,
  verdict: {admit(S.Configuration{e, laws, lim, amb}, r, ctx) == v : K.Verdict},
  sound: C.VerdictSound(v, S.Configuration{e, laws, lim, amb}, r, ctx),
  +identity: {D.authenticate(s, K.credential(r)) == Some{ctx} : Maybe<&2, D.Context>},
  +configured: {R.configuration_is_valid(S.Configuration{e, laws, lim, amb}) == True{} : Bool},
  valid: R.Valid(S.Configuration{e, laws, lim, amb}, s)) ->
  C.EntryCore(k, K.admitted(v, ctx, K.arguments(r), s), S.Configuration{e, laws, lim, amb}, s, r, admit):
  match k v:
    case C.Admitted{} K.Reject{}:
      L.Both{(%Equal.sym(Maybe<&2, D.Context>, D.authenticate(s, K.credential(r)), Some{ctx}, identity) :
          {K.authenticated(S.Configuration{e, laws, lim, amb}, _, r, s, admit) == K.Halted{S.response_error(S.Certificate{})} : K.Entry}
          %Equal.sym(K.Verdict, admit(S.Configuration{e, laws, lim, amb}, r, ctx), K.Reject{}, verdict) :
            {K.admitted(_, ctx, K.arguments(r), s) == K.Halted{S.response_error(S.Certificate{})} : K.Entry}
          {==}),
        early_error(S.Certificate{}, e, laws, lim, amb, s, limits_valid(e, laws, lim, amb, configured), Unit{})}
    case C.Admitted{} K.ToolFailure{}:
      L.Both{(%Equal.sym(Maybe<&2, D.Context>, D.authenticate(s, K.credential(r)), Some{ctx}, identity) :
          {K.authenticated(S.Configuration{e, laws, lim, amb}, _, r, s, admit) == K.Halted{S.response_error(S.Failure{})} : K.Entry}
          %Equal.sym(K.Verdict, admit(S.Configuration{e, laws, lim, amb}, r, ctx), K.ToolFailure{}, verdict) :
            {K.admitted(_, ctx, K.arguments(r), s) == K.Halted{S.response_error(S.Failure{})} : K.Entry}
          {==}),
        early_error(S.Failure{}, e, laws, lim, amb, s, limits_valid(e, laws, lim, amb, configured), Unit{})}
    case C.Admitted{} K.Accept{p}:
      L.Both{identity, (p, L.Both{verdict, {==}})}
    case C.Safe{} K.Reject{}: Unit{}
    case C.Safe{} K.ToolFailure{}: Unit{}
    case C.Safe{} K.Accept{p}:
      F.combined_pair(C.EntryCore(C.Safe{}, K.admitted(K.Accept{p}, ctx, K.arguments(r), s), S.Configuration{e, laws, lim, amb}, s, r, admit),
        R.Certifies(S.Configuration{e, laws, lim, amb}, K.code(r), p, ctx, K.arguments(r)),
        @state: D.State -> C.Terminates(p, S.Configuration{e, laws, lim, amb}, state, ctx, K.arguments(r)),
        sound,
        certificate => termination =>
          +n => safety_trace(e, laws, lim, amb, K.code(r), p, ctx, K.arguments(r), certificate,
            s, valid, K.credential(r), identity, n))
    case C.Completed{} K.Reject{}: Unit{}
    case C.Completed{} K.ToolFailure{}: Unit{}
    case C.Completed{} K.Accept{p}:
      F.combined_pair(C.EntryCore(C.Completed{}, K.admitted(K.Accept{p}, ctx, K.arguments(r), s), S.Configuration{e, laws, lim, amb}, s, r, admit),
        R.Certifies(S.Configuration{e, laws, lim, amb}, K.code(r), p, ctx, K.arguments(r)),
        @state: D.State -> C.Terminates(p, S.Configuration{e, laws, lim, amb}, state, ctx, K.arguments(r)),
        sound,
        certificate => termination =>
          +n => +w => +ts => +proposal => obtained =>
            F.combined_pair(C.Completion(S.Configuration{e, laws, lim, amb}, s, w, ts, proposal),
              {N.traverse(n, N.start(p, ctx, K.arguments(r), s), e) == S.execute(n, p, e, s, ctx, K.arguments(r)) : S.Trace},
              TraceGood(S.execute(n, p, e, s, ctx, K.arguments(r))),
              faithful_good(n, p, ctx, K.arguments(r), e, s),
              faithful => good =>
                +reference = Equal.trans(S.Trace, S.execute(n, p, e, s, ctx, K.arguments(r)),
                  N.traverse(n, N.start(p, ctx, K.arguments(r), s), e), S.Final{w, ts, proposal},
                  Equal.sym(S.Trace, N.traverse(n, N.start(p, ctx, K.arguments(r), s), e),
                    S.execute(n, p, e, s, ctx, K.arguments(r)), faithful), obtained)
                completion(e, laws, lim, amb, K.code(r), p, ctx, K.arguments(r), certificate, s, valid,
                  K.credential(r), identity, n, w, ts, proposal, reference,
                  (%reference : TraceGood(_) good), configured)))
    case C.Progressing{} K.Reject{}: Unit{}
    case C.Progressing{} K.ToolFailure{}: Unit{}
    case C.Progressing{} K.Accept{p}:
      F.combined_pair(C.EntryCore(C.Progressing{}, K.admitted(K.Accept{p}, ctx, K.arguments(r), s), S.Configuration{e, laws, lim, amb}, s, r, admit),
        R.Certifies(S.Configuration{e, laws, lim, amb}, K.code(r), p, ctx, K.arguments(r)),
        @state: D.State -> C.Terminates(p, S.Configuration{e, laws, lim, amb}, state, ctx, K.arguments(r)),
        sound,
        certificate => termination =>
          progress(e, laws, lim, amb, K.code(r), p, ctx, K.arguments(r), certificate, s, valid,
            K.credential(r), identity, configured, termination(s)))

def unauthenticated(k: C.Clause, +e: D.Schema, -laws: S.Laws, +lim: S.Limits, +amb: String,
  +s: D.State, -r: P.Request, -admit: K.Oracle(),
  absent: {D.authenticate(s, K.credential(r)) == None{} : Maybe<&2, D.Context>},
  configured: {R.configuration_is_valid(S.Configuration{e, laws, lim, amb}) == True{} : Bool}) ->
  C.EntryCore(k, K.Halted{S.response_error(S.Authentication{})}, S.Configuration{e, laws, lim, amb}, s, r, admit):
  match k:
    case C.Admitted{}:
      L.Both{(%Equal.sym(Maybe<&2, D.Context>, D.authenticate(s, K.credential(r)), None{}, absent) :
          {K.authenticated(S.Configuration{e, laws, lim, amb}, _, r, s, admit) == K.Halted{S.response_error(S.Authentication{})} : K.Entry}
          {==}),
        early_error(S.Authentication{}, e, laws, lim, amb, s, limits_valid(e, laws, lim, amb, configured), Unit{})}
    case C.Safe{}: Unit{}
    case C.Completed{}: Unit{}
    case C.Progressing{}: Unit{}

def authenticated(k: C.Clause, authentication: Maybe<&2, D.Context>, +e: D.Schema, laws: S.Laws,
  +lim: S.Limits, +amb: String, +s: D.State, +r: P.Request, admit: K.Oracle(),
  identity: {D.authenticate(s, K.credential(r)) == authentication : Maybe<&2, D.Context>},
  configured: {R.configuration_is_valid(S.Configuration{e, laws, lim, amb}) == True{} : Bool},
  valid: R.Valid(S.Configuration{e, laws, lim, amb}, s),
  sound: C.OracleSoundness(S.Configuration{e, laws, lim, amb}, r, admit)) ->
  C.EntryCore(k, K.authenticated(S.Configuration{e, laws, lim, amb}, authentication, r, s, admit),
    S.Configuration{e, laws, lim, amb}, s, r, admit):
  match authentication:
    case None{}:
      unauthenticated(k, e, laws, lim, amb, s, r, admit, identity, configured)
    case Some{+ctx}:
      accepted(k, admit(S.Configuration{e, laws, lim, amb}, r, ctx), e, laws, lim, amb, s, r, admit, ctx,
        {==}, sound(ctx), identity, configured, valid)

# The configuration is opened once; only the oracle call consumes its laws.
def configured(k: C.Clause, c: S.Configuration, +s: D.State, +r: P.Request, admit: K.Oracle(),
  valid_configuration: {R.configuration_is_valid(c) == True{} : Bool}, valid: R.Valid(c, s),
  sound: C.OracleSoundness(c, r, admit)) -> C.Core(k, c, s, r, admit):
  match c:
    case S.Configuration{+e, laws, +lim, +amb}:
      authenticated(k, D.authenticate(s, K.credential(r)), e, laws, lim, amb, s, r, admit, {==},
        valid_configuration, valid, sound)

# CoreTheorem: all four clauses, each under its own copy of the premises.
def core_theorem() -> C.CoreTheorem():
  k => c => +s => +r => admit => valid_configuration => valid => sound =>
    configured(k, c, s, r, admit, valid_configuration, valid, sound)

def core_admitted() -> C.CoreClauseTheorem(C.Admitted{}):
  core_theorem()(C.Admitted{})

def core_safe() -> C.CoreClauseTheorem(C.Safe{}):
  core_theorem()(C.Safe{})

def core_completed() -> C.CoreClauseTheorem(C.Completed{}):
  core_theorem()(C.Completed{})

def core_progressing() -> C.CoreClauseTheorem(C.Progressing{}):
  core_theorem()(C.Progressing{})
