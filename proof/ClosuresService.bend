# One inversion of the same suffix, shared by Laws 6/7.
import Base
import ./PrimitivesService.bend as M
import ./Law5Service.bend as Five
import ./Publication.bend as U
import ../contract/Resources.bend as X
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../contract/Semantics.bend as S
import ../contract/Protocol.bend as P
import ../src/Core.bend as N
import ./ProtocolService.bend as Q
import ./RoutesService.bend as R
import ./PhasesService.bend as Phases
import ./ErrorsFixed.bend as Errors
import ./SourceService.bend as Source
import ./ExecutionService.bend as Exec
import ./Foundations.bend as F

type Closure is Data:
  Closure{before: List<&2, Q.Frame>, conclusion: N.Conclusion, closes: Bool,
    delivery: R.Delivery, origin: R.Branch}

def error(q: Maybe<&2, List<&2, U32>>, before: List<&2, Q.Frame>, s: D.State,
  e: Errors.Error, closes: Bool, delivery: R.Delivery, origin: R.Branch) -> Maybe<&2, Closure>:
  match q:
    case None{}: None{}
    case Some{bs}: Some{Closure{before, N.Conclusion{s, S.response_error(Errors.status(e)), bs}, closes, delivery, origin}}

def close_error(before: List<&2, Q.Frame>, s: D.State, +e: Errors.Error,
  closes: Bool, delivery: R.Delivery, origin: R.Branch) -> Maybe<&2, Closure>:
  error(P.frame(S.response_value(S.response_error(Errors.status(e)))), before, s, e, closes, delivery, origin)

def error_of_input(e: R.ErrorInput) -> Errors.Error:
  match e:
    case R.Input{}: Errors.Input{}
    case R.Limit{}: Errors.Limit{}

def before_authentication(+m: R.Micro, +r: P.Request) -> List<&2, Q.Frame>:
  Q.concatenate(R.render_received(m, r), Q.concatenate(R.micro_authentication(m), [Q.Authenticated{r, None{}}]))

def before_gate(m: R.Micro, +r: P.Request, +ctx: D.Context) -> List<&2, Q.Frame>:
  Q.concatenate(R.render_authenticated(m, r, ctx), [Q.Rejected{r, ctx}])

def before_execution(+m: R.Micro, r: P.Request, ctx: D.Context,
  xs: List<&2, Q.FrameExec>) -> List<&2, Q.Frame>:
  Q.concatenate(R.render_execution(m, r, ctx, xs), R.micro_output(m))

def before_failure(m: R.Micro, phase: R.PhaseBefore, stage: X.Stage, id: String, fatal: Bool) -> List<&2, Q.Frame>:
  Q.concatenate(R.render_phase(m, phase), [Q.Failed{stage, id, fatal}])


def of_branch(+m: R.Micro, +s: D.State, branch: R.Branch) -> Maybe<&2, Closure>:
  match branch:
    case R.InputRefusal{+e, +closes, +delivery}:
      close_error(R.micro_input(m), s, error_of_input(e), closes, delivery, R.InputRefusal{e, closes, delivery})
    case R.AutRefusal{+r, +delivery}:
      close_error(before_authentication(m, r), s, Errors.Authentication{}, False{}, delivery, R.AutRefusal{r, delivery})
    case R.GateRefusal{+r, +ctx, +delivery}:
      close_error(before_gate(m, r, ctx), s, Errors.Certificate{}, False{}, delivery, R.GateRefusal{r, ctx, delivery})
    case R.Executed{+r, +ctx, +xs, +p, +delivery}:
      Some{Closure{before_execution(m, r, ctx, xs), N.conclude(p, s), False{}, delivery, R.Executed{r, ctx, xs, p, delivery}}}
    case R.FailureBefore{+phase, +stage, +id, fatal, +delivery}:
      match fatal:
        case True{}: None{}
        case False{}:
          close_error(before_failure(m, phase, stage, id, False{}), s, Errors.Failure{}, False{}, delivery,
            R.FailureBefore{phase, stage, id, False{}, delivery})
    case _: None{}

def configure(q: Maybe<&2, Closure>) -> Maybe<&2, Closure>:
  match q:
    case None{}: None{}
    case Some{Closure{before, c, closes, delivery, origin}}:
      Some{Closure{Con{Q.Configured{}, before}, c, closes, delivery, origin}}

def closure_of_branch(m: R.Micro, s: D.State, branch: R.Branch) -> Maybe<&2, Closure>:
  configure(of_branch(m, s, branch))

# Conclusion is absent only when no suffix of this kind executed.
# Does not assert absence of preparations before a cleanup failure.
def Form(-xs: List<&2, Q.Frame>, -branch: R.Branch, q: Maybe<&2, Closure>) -> Type:
  match q:
    case None{}: {Phases.absent(Phases.Conclusion{}, xs) == True{} : Bool}
    case Some{Closure{before, c, closes, delivery, origin}}:
      L.E<{origin == branch : R.Branch},
        L.E<{xs == Q.concatenate(before, R.render_conclusion(c, closes, delivery)) : List<&2, Q.Frame>},
          L.E<{Phases.absent(Phases.Publication{}, before) == True{} : Bool},
            {Phases.absent(Phases.Conclusion{}, before) == True{} : Bool}>>>

def error_equal_conclusion(+e: Errors.Error, s: D.State, bs: List<&2, U32>, closes: Bool, delivery: R.Delivery) ->
  {R.render_error_framed(Some{bs}, S.response_error(Errors.status(e)), s, closes, delivery) ==
    R.render_conclusion(N.Conclusion{s, S.response_error(Errors.status(e)), bs}, closes, delivery) : List<&2, Q.Frame>}:
  match e:
    case Errors.Input{}: {==}
    case Errors.Authentication{}: {==}
    case Errors.Certificate{}: {==}
    case Errors.DataError{}: {==}
    case Errors.Limit{}: {==}
    case Errors.Failure{}: {==}

def form_error(q: Maybe<&2, List<&2, U32>>, +before: List<&2, Q.Frame>, +s: D.State,
  +e: Errors.Error, +closes: Bool, +delivery: R.Delivery, +origin: R.Branch,
  pub: {Phases.absent(Phases.Publication{}, before) == True{} : Bool},
  concl: {Phases.absent(Phases.Conclusion{}, before) == True{} : Bool}) ->
  Form(Q.concatenate(before, R.render_error_framed(q, S.response_error(Errors.status(e)), s, closes, delivery)),
    origin, error(q, before, s, e, closes, delivery, origin)):
  match q:
    case None{}:
      Phases.concatenate_absence(Phases.Conclusion{}, before, Nil{}, concl, {==})
    case Some{+bs}: L.Both{{==}, L.Both{
      Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, tail => Q.concatenate(before, tail),
        R.render_error_framed(Some{bs}, S.response_error(Errors.status(e)), s, closes, delivery),
        R.render_conclusion(N.Conclusion{s, S.response_error(Errors.status(e)), bs}, closes, delivery),
        error_equal_conclusion(e, s, bs, closes, delivery)), L.Both{pub, concl}}}

def form_of_error(+before: List<&2, Q.Frame>, +s: D.State, +e: Errors.Error,
  +closes: Bool, +delivery: R.Delivery, +origin: R.Branch,
  pub: {Phases.absent(Phases.Publication{}, before) == True{} : Bool},
  concl: {Phases.absent(Phases.Conclusion{}, before) == True{} : Bool}) ->
  Form(Q.concatenate(before, R.render_error(Errors.status(e), s, closes, delivery)), origin,
    close_error(before, s, e, closes, delivery, origin)):
  form_error(P.frame(S.response_value(S.response_error(Errors.status(e)))), before, s, e, closes, delivery, origin, pub, concl)

def swap_form(-xs: List<&2, Q.Frame>, -ys: List<&2, Q.Frame>, -branch: R.Branch,
  -closure: Maybe<&2, Closure>, equal: {xs == ys : List<&2, Q.Frame>}, form: Form(xs, branch, closure)) -> Form(ys, branch, closure):
  %equal : Form(_, branch, closure)
  form

def group_three(+a: List<&2, Q.Frame>, +b: List<&2, Q.Frame>, +c: List<&2, Q.Frame>, +d: List<&2, Q.Frame>) ->
  {Q.concatenate(Q.concatenate(a, Q.concatenate(b, c)), d) == Q.concatenate(a, Q.concatenate(b, Q.concatenate(c, d))) : List<&2, Q.Frame>}:
  Equal.trans(List<&2, Q.Frame>, Q.concatenate(Q.concatenate(a, Q.concatenate(b, c)), d),
    Q.concatenate(a, Q.concatenate(Q.concatenate(b, c), d)), Q.concatenate(a, Q.concatenate(b, Q.concatenate(c, d))),
    Q.concatenate_assoc(a, Q.concatenate(b, c), d),
    Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, tail => Q.concatenate(a, tail),
      Q.concatenate(Q.concatenate(b, c), d), Q.concatenate(b, Q.concatenate(c, d)), Q.concatenate_assoc(b, c, d)))

def before_authentication_without_macros(+kind: Phases.FrameKind, +m: R.Micro, +r: P.Request) ->
  {Phases.absent(kind, before_authentication(m, r)) == True{} : Bool}:
  Phases.concatenate_absence(kind, R.render_received(m, r), Q.concatenate(R.micro_authentication(m), [Q.Authenticated{r, None{}}]),
    Phases.received_without_macros(kind, m, r),
    Phases.concatenate_absence(kind, R.micro_authentication(m), [Q.Authenticated{r, None{}}],
      Phases.micro_authentication_without_macros(kind, m), {==}))

def before_gate_without_macros(+kind: Phases.FrameKind, +m: R.Micro, +r: P.Request, +ctx: D.Context) ->
  {Phases.absent(kind, before_gate(m, r, ctx)) == True{} : Bool}:
  Phases.concatenate_absence(kind, R.render_authenticated(m, r, ctx), [Q.Rejected{r, ctx}],
    Phases.authenticated_without_macros(kind, m, r, ctx), {==})

def before_execution_without_macros(+kind: Phases.FrameKind, +m: R.Micro, +r: P.Request, +ctx: D.Context,
  +xs: List<&2, Q.FrameExec>) -> {Phases.absent(kind, before_execution(m, r, ctx, xs)) == True{} : Bool}:
  Phases.concatenate_absence(kind, R.render_execution(m, r, ctx, xs), R.micro_output(m),
    Phases.execution_host_without_macros(kind, m, r, ctx, xs), Phases.micro_output_without_macros(kind, m))

def before_failure_without_macros(+kind: Phases.FrameKind, +m: R.Micro, +phase: R.PhaseBefore,
  +stage: X.Stage, +id: String, +fatal: Bool) ->
  {Phases.absent(kind, before_failure(m, phase, stage, id, fatal)) == True{} : Bool}:
  Phases.concatenate_absence(kind, R.render_phase(m, phase), [Q.Failed{stage, id, fatal}],
    Phases.phase_previous_without_macros(kind, m, phase), {==})

def initial_without_conclusion(q: Maybe<&2, List<&2, U32>>, s: D.State) ->
  {Phases.absent(Phases.Conclusion{}, R.render_initial(q, s)) == True{} : Bool}:
  match q:
    case None{}: {==}
    case Some{bs}: {==}

def prefix_initial_without_conclusion(+m: R.Micro, accepts: Bool) ->
  {Phases.absent(Phases.Conclusion{}, R.prefix_initial(m, accepts)) == True{} : Bool}:
  match accepts:
    case False{}: {==}
    case True{}: Phases.micro_output_without_macros(Phases.Conclusion{}, m)

def fatal_without_conclusion(conclusion: N.Conclusion, stage: X.Stage, id: String) ->
  {Phases.absent(Phases.Conclusion{}, R.render_fatal_published(conclusion, stage, id)) == True{} : Bool}:
  match conclusion:
    case N.Conclusion{+s, +r, bs}:
      Phases.concatenate_absence(Phases.Conclusion{}, R.render_publication(r, s), [Q.Failed{stage, id, True{}}, Q.Closed{}],
        Phases.publication_negative_concludes(r, s), {==})

def form_of_branch(+m: R.Micro, +s: D.State, branch: R.Branch) -> Form(R.render_branch(m, s, branch), branch, of_branch(m, s, branch)):
  match branch:
    case R.InitialOk{}:
      Phases.concatenate_absence(Phases.Conclusion{}, R.micro_output(m), R.render_initial(P.encode(D.state_value(s)), s),
        Phases.micro_output_without_macros(Phases.Conclusion{}, m), initial_without_conclusion(P.encode(D.state_value(s)), s))
    case R.InitialRefusal{status}: {==}
    case R.InitialFailure{+accepts, +stage, +id, +fatal}:
      Phases.concatenate_absence(Phases.Conclusion{}, R.prefix_initial(m, accepts),
        [Q.Failed{stage, id, fatal}, Q.InitialRefused{S.Failure{}}], prefix_initial_without_conclusion(m, accepts), {==})
    case R.WithoutResponse{}: {==}
    case R.InputRefusal{e, +closes, +delivery}:
      match e:
        case R.Input{}:
          form_of_error(R.micro_input(m), s, Errors.Input{}, closes, delivery, R.InputRefusal{R.Input{}, closes, delivery},
            Phases.micro_input_without_macros(Phases.Publication{}, m), Phases.micro_input_without_macros(Phases.Conclusion{}, m))
        case R.Limit{}:
          form_of_error(R.micro_input(m), s, Errors.Limit{}, closes, delivery, R.InputRefusal{R.Limit{}, closes, delivery},
            Phases.micro_input_without_macros(Phases.Publication{}, m), Phases.micro_input_without_macros(Phases.Conclusion{}, m))
    case R.AutRefusal{+r, +delivery}:
      swap_form(Q.concatenate(before_authentication(m, r), R.render_error(S.Authentication{}, s, False{}, delivery)),
        R.render_branch(m, s, R.AutRefusal{r, delivery}), R.AutRefusal{r, delivery}, of_branch(m, s, R.AutRefusal{r, delivery}),
        group_three(R.render_received(m, r), R.micro_authentication(m), [Q.Authenticated{r, None{}}], R.render_error(S.Authentication{}, s, False{}, delivery)),
        form_of_error(before_authentication(m, r), s, Errors.Authentication{}, False{}, delivery, R.AutRefusal{r, delivery},
          before_authentication_without_macros(Phases.Publication{}, m, r), before_authentication_without_macros(Phases.Conclusion{}, m, r)))
    case R.GateRefusal{+r, +ctx, +delivery}:
      swap_form(Q.concatenate(before_gate(m, r, ctx), R.render_error(S.Certificate{}, s, False{}, delivery)),
        R.render_branch(m, s, R.GateRefusal{r, ctx, delivery}), R.GateRefusal{r, ctx, delivery}, of_branch(m, s, R.GateRefusal{r, ctx, delivery}),
        Q.concatenate_assoc(R.render_authenticated(m, r, ctx), [Q.Rejected{r, ctx}], R.render_error(S.Certificate{}, s, False{}, delivery)),
        form_of_error(before_gate(m, r, ctx), s, Errors.Certificate{}, False{}, delivery, R.GateRefusal{r, ctx, delivery},
          before_gate_without_macros(Phases.Publication{}, m, r, ctx), before_gate_without_macros(Phases.Conclusion{}, m, r, ctx)))
    case R.Executed{+r, +ctx, +xs, +p, +delivery}:
      L.Both{{==}, L.Both{
        Equal.sym(List<&2, Q.Frame>, Q.concatenate(before_execution(m, r, ctx, xs), R.render_final(p, s, False{}, delivery)),
          R.render_branch(m, s, R.Executed{r, ctx, xs, p, delivery}),
          Q.concatenate_assoc(R.render_execution(m, r, ctx, xs), R.micro_output(m), R.render_final(p, s, False{}, delivery))),
        L.Both{before_execution_without_macros(Phases.Publication{}, m, r, ctx, xs),
          before_execution_without_macros(Phases.Conclusion{}, m, r, ctx, xs)}}}
    case R.FailureBefore{+phase, +stage, +id, fatal, +delivery}:
      match fatal:
        case True{}:
          Phases.concatenate_absence(Phases.Conclusion{}, R.render_phase(m, phase),
            R.render_failure(s, stage, id, True{}, delivery), Phases.phase_previous_without_macros(Phases.Conclusion{}, m, phase), {==})
        case False{}:
          swap_form(Q.concatenate(before_failure(m, phase, stage, id, False{}), R.render_error(S.Failure{}, s, False{}, delivery)),
            R.render_branch(m, s, R.FailureBefore{phase, stage, id, False{}, delivery}), R.FailureBefore{phase, stage, id, False{}, delivery},
            of_branch(m, s, R.FailureBefore{phase, stage, id, False{}, delivery}),
            Q.concatenate_assoc(R.render_phase(m, phase), [Q.Failed{stage, id, False{}}], R.render_error(S.Failure{}, s, False{}, delivery)),
            form_of_error(before_failure(m, phase, stage, id, False{}), s, Errors.Failure{}, False{}, delivery,
              R.FailureBefore{phase, stage, id, False{}, delivery}, before_failure_without_macros(Phases.Publication{}, m, phase, stage, id, False{}),
              before_failure_without_macros(Phases.Conclusion{}, m, phase, stage, id, False{})))
    case R.FatalAfterPublication{+r, +ctx, +xs, +p, +stage, +id}:
      Phases.concatenate_absence(Phases.Conclusion{}, R.render_execution(m, r, ctx, xs),
        Q.concatenate(R.micro_output(m), R.render_fatal_published(N.conclude(p, s), stage, id)),
        Phases.execution_host_without_macros(Phases.Conclusion{}, m, r, ctx, xs),
        Phases.concatenate_absence(Phases.Conclusion{}, R.micro_output(m), R.render_fatal_published(N.conclude(p, s), stage, id),
          Phases.micro_output_without_macros(Phases.Conclusion{}, m), fatal_without_conclusion(N.conclude(p, s), stage, id)))
    case R.Pending{phase}: Phases.phase_previous_without_macros(Phases.Conclusion{}, m, phase)
    case R.InitialPending{accepts}: prefix_initial_without_conclusion(m, accepts)

def configure_form(+xs: List<&2, Q.Frame>, +branch: R.Branch, q: Maybe<&2, Closure>, form: Form(xs, branch, q)) ->
  Form(Con{Q.Configured{}, xs}, branch, configure(q)):
  match q:
    case None{}: form
    case Some{Closure{+before, +c, +closes, +delivery, +origin}}:
      match form:
        case L.Both{equal, L.Both{trace, L.Both{pub, concl}}}:
          L.Both{equal, L.Both{
            Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, tail => Con{Q.Configured{}, tail},
              xs, Q.concatenate(before, R.render_conclusion(c, closes, delivery)), trace), L.Both{pub, concl}}}

law form_of_route:
  for +m: R.Micro
  for +s: D.State
  for +branch: R.Branch
  Form(R.render(m, s, branch), branch, closure_of_branch(m, s, branch))
def form_of_route(m, s, branch):
  configure_form(R.render_branch(m, s, branch), branch, of_branch(m, s, branch), form_of_branch(m, s, branch))

# The actual query prevents choosing the no-conclusion branch.
def find_closure(+xs: List<&2, Q.Frame>, +branch: R.Branch, q: Maybe<&2, Closure>,
  +t: Nat, +r: S.Response, +s: D.State, +closes: Bool, form: Form(xs, branch, q),
  query_result: {Q.query(xs, t) == Some{Q.Completed{r, s, closes}} : Maybe<&2, Q.Frame>}) ->
  &closure: Closure -> Form(xs, branch, Some{closure}):
  match q:
    case None{}:
      L.ex_false((&closure: Closure -> Form(xs, branch, Some{closure})),
        Phases.absent_excludes_query(Phases.Conclusion{}, xs, t, Q.Completed{r, s, closes}, form, {==}, query_result))
    case Some{+closure}: (closure, form)

law invert_conclusion:
  for +m: R.Micro
  for +s: D.State
  for +branch: R.Branch
  for +t: Nat
  for +r: S.Response
  for +w: D.State
  for +closes: Bool
  for query_result: {Q.query(R.render(m, s, branch), t) == Some{Q.Completed{r, w, closes}} : Maybe<&2, Q.Frame>}
  exs closure: Closure
  Form(R.render(m, s, branch), branch, Some{closure})
def invert_conclusion(m, s, branch, t, r, w, closes, query_result):
  find_closure(R.render(m, s, branch), branch, closure_of_branch(m, s, branch), t, r, w, closes,
    form_of_route(m, s, branch), query_result)

# This follows from N.conclude/render_error, never a rollback premise.
def PreservesInitial(-s: D.State, c: N.Conclusion) -> Type:
  match c:
    case N.Conclusion{w, r, bs}:
      {U.status_success(r) == False{} : Bool} -> {w == s : D.State}

def StateOfClosure(-s: D.State, q: Maybe<&2, Closure>) -> Type:
  match q:
    case None{}: Unit
    case Some{Closure{before, c, closes, delivery, origin}}: PreservesInitial(s, c)

def state_of_error(q: Maybe<&2, List<&2, U32>>, +before: List<&2, Q.Frame>, +s: D.State,
  +e: Errors.Error, +closes: Bool, +delivery: R.Delivery, +origin: R.Branch) ->
  StateOfClosure(s, error(q, before, s, e, closes, delivery, origin)):
  match q:
    case None{}: Unit{}
    case Some{bs}: without_success => {==}

def state_of_conclusion(s: D.State, p: N.Prepared) -> PreservesInitial(s, N.conclude(p, s)):
  match p:
    case N.Prepared{+w, events, +r, bs}:
      without_success => U.all_status_without_success_preserves_published(r, s, w, without_success)

def state_of_branch(+m: R.Micro, +s: D.State, branch: R.Branch) -> StateOfClosure(s, of_branch(m, s, branch)):
  match branch:
    case R.InputRefusal{+e, +closes, +delivery}:
      state_of_error(P.frame(S.response_value(S.response_error(Errors.status(error_of_input(e))))),
        R.micro_input(m), s, error_of_input(e), closes, delivery, R.InputRefusal{e, closes, delivery})
    case R.AutRefusal{+r, +delivery}:
      state_of_error(P.frame(S.response_value(S.response_error(S.Authentication{}))),
        before_authentication(m, r), s, Errors.Authentication{}, False{}, delivery, R.AutRefusal{r, delivery})
    case R.GateRefusal{+r, +ctx, +delivery}:
      state_of_error(P.frame(S.response_value(S.response_error(S.Certificate{}))),
        before_gate(m, r, ctx), s, Errors.Certificate{}, False{}, delivery, R.GateRefusal{r, ctx, delivery})
    case R.Executed{r, ctx, xs, p, delivery}: state_of_conclusion(s, p)
    case R.FailureBefore{+phase, +stage, +id, fatal, +delivery}:
      match fatal:
        case True{}: Unit{}
        case False{}:
          state_of_error(P.frame(S.response_value(S.response_error(S.Failure{}))),
            before_failure(m, phase, stage, id, False{}), s, Errors.Failure{}, False{}, delivery, R.FailureBefore{phase, stage, id, False{}, delivery})
    case R.InitialOk{}: Unit{}
    case R.InitialRefusal{status}: Unit{}
    case R.InitialFailure{accepts, stage, id, fatal}: Unit{}
    case R.WithoutResponse{}: Unit{}
    case R.FatalAfterPublication{r, ctx, xs, p, stage, id}: Unit{}
    case R.Pending{phase}: Unit{}
    case R.InitialPending{accepts}: Unit{}

def configure_state(-s: D.State, q: Maybe<&2, Closure>, state: StateOfClosure(s, q)) -> StateOfClosure(s, configure(q)):
  match q:
    case None{}: Unit{}
    case Some{Closure{before, c, closes, delivery, origin}}: state

law state_of_route:
  for +m: R.Micro
  for +s: D.State
  for +branch: R.Branch
  StateOfClosure(s, closure_of_branch(m, s, branch))
def state_of_route(m, s, branch):
  configure_state(s, of_branch(m, s, branch), state_of_branch(m, s, branch))

def find_closure_combined_state(+xs: List<&2, Q.Frame>, +branch: R.Branch, +initial: D.State,
  q: Maybe<&2, Closure>, +t: Nat, +r: S.Response, +s: D.State, +closes: Bool,
  form: Form(xs, branch, q), state: StateOfClosure(initial, q),
  query_result: {Q.query(xs, t) == Some{Q.Completed{r, s, closes}} : Maybe<&2, Q.Frame>}) ->
  &closure: Closure -> L.E<Form(xs, branch, Some{closure}), StateOfClosure(initial, Some{closure})>:
  match q:
    case None{}:
      L.ex_false((&closure: Closure -> L.E<Form(xs, branch, Some{closure}), StateOfClosure(initial, Some{closure})>),
        Phases.absent_excludes_query(Phases.Conclusion{}, xs, t, Q.Completed{r, s, closes}, form, {==}, query_result))
    case Some{+closure}: (closure, L.Both{form, state})

law invert_conclusion_combined_state:
  for +m: R.Micro
  for +s: D.State
  for +branch: R.Branch
  for +t: Nat
  for +r: S.Response
  for +w: D.State
  for +closes: Bool
  for query_result: {Q.query(R.render(m, s, branch), t) == Some{Q.Completed{r, w, closes}} : Maybe<&2, Q.Frame>}
  exs closure: Closure
  L.E<Form(R.render(m, s, branch), branch, Some{closure}), StateOfClosure(s, Some{closure})>
def invert_conclusion_combined_state(m, s, branch, t, r, w, closes, query_result):
  find_closure_combined_state(R.render(m, s, branch), branch, s, closure_of_branch(m, s, branch), t, r, w, closes,
    form_of_route(m, s, branch), state_of_route(m, s, branch), query_result)

def is_next(q: Q.Frame) -> Bool:
  match q:
    case Q.Next{a, b}: True{}
    case _: False{}

def without_next_in_front(+h: Q.Frame, -xs: List<&2, Q.Frame>, -a: D.State, -b: D.State,
  neutral: {is_next(h) == False{} : Bool}, rest: Five.WithoutFrame(xs, Q.Next{a, b})) ->
  Five.WithoutFrame(Con{h, xs}, Q.Next{a, b}):
  Five.head_by_tag(is_next, h, Q.Next{a, b}, xs, neutral, {==}, rest)

def without_next_empty(-a: D.State, -b: D.State) -> Five.WithoutFrame(Nil{}, Q.Next{a, b}):
  t => h => F.none_negative_some(Q.Frame, Q.Next{a, b}, h)


# Every computed prefix before closure excludes the next call.
def WithoutNext(-xs: List<&2, Q.Frame>) -> Type:
  @a: D.State -> @b: D.State -> Five.WithoutFrame(xs, Q.Next{a, b})

def empty_without_next() -> WithoutNext(Nil{}):
  +a => +b => without_next_empty(a, b)

def prefix_without_next(+q: Q.Frame, -xs: List<&2, Q.Frame>,
  neutral: {is_next(q) == False{} : Bool}, tail: WithoutNext(xs)) -> WithoutNext(Con{q, xs}):
  +a => +b => without_next_in_front(q, xs, a, b, neutral, tail(a, b))

def concatenate_without_next(+xs: List<&2, Q.Frame>, -ys: List<&2, Q.Frame>,
  first: WithoutNext(xs), second: WithoutNext(ys)) -> WithoutNext(Q.concatenate(xs, ys)):
  +a => +b => Five.concatenate_without_frame(xs, ys, Q.Next{a, b}, first(a, b), second(a, b))

# One path for every marker that may occur only after closure.
def WithoutSubsequent(-xs: List<&2, Q.Frame>) -> Type:
  L.E<WithoutNext(xs), L.E<{Phases.absent(Phases.Complete{}, xs) == True{} : Bool},
    {Phases.absent(Phases.Interrupted{}, xs) == True{} : Bool}>>

def frame_previous(+q: Q.Frame) -> Bool:
  Bool.not(is_next(q)) && Bool.not(Phases.classify(q, Phases.Complete{})) && Bool.not(Phases.classify(q, Phases.Interrupted{}))

def Negative(-q: Q.Frame) -> Type:
  L.E<{is_next(q) == False{} : Bool}, L.E<{Phases.classify(q, Phases.Complete{}) == False{} : Bool},
    {Phases.classify(q, Phases.Interrupted{}) == False{} : Bool}>>

def negative_of_frame(+q: Q.Frame, neutral: {frame_previous(q) == True{} : Bool}) -> Negative(q):
  F.combined_pair(Negative(q), {Bool.not(is_next(q)) && Bool.not(Phases.classify(q, Phases.Complete{})) == True{} : Bool},
    {Bool.not(Phases.classify(q, Phases.Interrupted{})) == True{} : Bool},
    F.and_boolean_separate(Bool.not(is_next(q)) && Bool.not(Phases.classify(q, Phases.Complete{})), Bool.not(Phases.classify(q, Phases.Interrupted{})), neutral), ab => ci =>
      F.combined_pair(Negative(q), {Bool.not(is_next(q)) == True{} : Bool}, {Bool.not(Phases.classify(q, Phases.Complete{})) == True{} : Bool},
        F.and_boolean_separate(Bool.not(is_next(q)), Bool.not(Phases.classify(q, Phases.Complete{})), ab), a => b =>
          L.Both{F.negation_true(is_next(q), a), L.Both{F.negation_true(Phases.classify(q, Phases.Complete{}), b), F.negation_true(Phases.classify(q, Phases.Interrupted{}), ci)}}))

def prefix_absence(+kind: Phases.FrameKind, +q: Q.Frame, -xs: List<&2, Q.Frame>,
  neutral: {Phases.classify(q, kind) == False{} : Bool}, rest: {Phases.absent(kind, xs) == True{} : Bool}) ->
  {Phases.absent(kind, Con{q, xs}) == True{} : Bool}:
  %Equal.sym(Bool, Phases.classify(q, kind), False{}, neutral) : {Bool.not(_) && Phases.absent(kind, xs) == True{} : Bool}
  rest

def prefix_packet(+q: Q.Frame, -xs: List<&2, Q.Frame>, negative: Negative(q), tail: WithoutSubsequent(xs)) -> WithoutSubsequent(Con{q, xs}):
  match negative tail:
    case L.Both{n, L.Both{c, i}} L.Both{sn, L.Both{sc, si}}:
      L.Both{prefix_without_next(q, xs, n, sn), L.Both{prefix_absence(Phases.Complete{}, q, xs, c, sc), prefix_absence(Phases.Interrupted{}, q, xs, i, si)}}

def empty_without_subsequent() -> WithoutSubsequent(Nil{}):
  L.Both{empty_without_next(), L.Both{{==}, {==}}}

def prefix_without_subsequent(+q: Q.Frame, -xs: List<&2, Q.Frame>, neutral: {frame_previous(q) == True{} : Bool}, tail: WithoutSubsequent(xs)) -> WithoutSubsequent(Con{q, xs}):
  prefix_packet(q, xs, negative_of_frame(q, neutral), tail)

def concatenate_without_subsequent(+xs: List<&2, Q.Frame>, +ys: List<&2, Q.Frame>, first: WithoutSubsequent(xs), second: WithoutSubsequent(ys)) -> WithoutSubsequent(Q.concatenate(xs, ys)):
  match first second:
    case L.Both{sn1, L.Both{sc1, si1}} L.Both{sn2, L.Both{sc2, si2}}:
      L.Both{concatenate_without_next(xs, ys, sn1, sn2), L.Both{Phases.concatenate_absence(Phases.Complete{}, xs, ys, sc1, sc2), Phases.concatenate_absence(Phases.Interrupted{}, xs, ys, si1, si2)}}

def primitives_without_next(+ps: List<&2, M.Primitive>) -> WithoutNext(M.expand_primitives(ps)):
  +a => +b => Five.internal_negative_contains(M.expand_primitives(ps), Q.Next{a, b}, M.primitives_only_generate_internal(ps), {==})

def primitives_without_subsequent(+ps: List<&2, M.Primitive>) -> WithoutSubsequent(M.expand_primitives(ps)):
  L.Both{primitives_without_next(ps), L.Both{Phases.primitives_without_macros(Phases.Complete{}, ps), Phases.primitives_without_macros(Phases.Interrupted{}, ps)}}

def input_without_subsequent(m: R.Micro) -> WithoutSubsequent(R.micro_input(m)):
  match m:
    case R.Micro{a, b, c, d}: primitives_without_subsequent(a)

def authentication_without_subsequent(m: R.Micro) -> WithoutSubsequent(R.micro_authentication(m)):
  match m:
    case R.Micro{a, b, c, d}: primitives_without_subsequent(b)

def execution_micro_without_subsequent(m: R.Micro) -> WithoutSubsequent(R.micro_execution(m)):
  match m:
    case R.Micro{a, b, c, d}: primitives_without_subsequent(c)

def output_without_subsequent(m: R.Micro) -> WithoutSubsequent(R.micro_output(m)):
  match m:
    case R.Micro{a, b, c, d}: primitives_without_subsequent(d)

def received_without_subsequent(+m: R.Micro, +r: P.Request) -> WithoutSubsequent(R.render_received(m, r)):
  concatenate_without_subsequent(R.micro_input(m), [Q.Received{r}], input_without_subsequent(m),
    prefix_without_subsequent(Q.Received{r}, Nil{}, {==}, empty_without_subsequent()))

def authenticated_without_subsequent(+m: R.Micro, +r: P.Request, +ctx: D.Context) -> WithoutSubsequent(R.render_authenticated(m, r, ctx)):
  concatenate_without_subsequent(R.render_received(m, r), Q.concatenate(R.micro_authentication(m), [Q.Authenticated{r, Some{ctx}}]),
    received_without_subsequent(m, r),
    concatenate_without_subsequent(R.micro_authentication(m), [Q.Authenticated{r, Some{ctx}}], authentication_without_subsequent(m),
      prefix_without_subsequent(Q.Authenticated{r, Some{ctx}}, Nil{}, {==}, empty_without_subsequent())))

def verified_without_subsequent(+m: R.Micro, +r: P.Request, +ctx: D.Context) -> WithoutSubsequent(R.render_verified(m, r, ctx)):
  concatenate_without_subsequent(R.render_authenticated(m, r, ctx), [Q.Accepts{r, ctx}], authenticated_without_subsequent(m, r, ctx),
    prefix_without_subsequent(Q.Accepts{r, ctx}, Nil{}, {==}, empty_without_subsequent()))

def started_without_subsequent(+m: R.Micro, +r: P.Request, +ctx: D.Context) -> WithoutSubsequent(R.render_started(m, r, ctx)):
  concatenate_without_subsequent(R.render_verified(m, r, ctx), Q.concatenate(R.micro_execution(m), [Q.Started{r, ctx}]),
    verified_without_subsequent(m, r, ctx),
    concatenate_without_subsequent(R.micro_execution(m), [Q.Started{r, ctx}], execution_micro_without_subsequent(m),
      prefix_without_subsequent(Q.Started{r, ctx}, Nil{}, {==}, empty_without_subsequent())))

def steps_without_subsequent(+r: P.Request, +ctx: D.Context, xs: List<&2, Q.FrameExec>) -> WithoutSubsequent(Q.expand_exec(r, ctx, xs)):
  match xs:
    case Nil{}: empty_without_subsequent()
    case Con{Q.Evaluation{+p}, t}:
      prefix_without_subsequent(Q.Evaluated{r, ctx, p}, Q.expand_exec(r, ctx, t), {==}, steps_without_subsequent(r, ctx, t))
    case Con{Q.Operation{+e, +s, +o, +res}, t}:
      prefix_without_subsequent(Q.Operated{e, s, o, res}, Q.expand_exec(r, ctx, t), {==}, steps_without_subsequent(r, ctx, t))

def execution_without_subsequent(+m: R.Micro, +r: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>) ->
  WithoutSubsequent(R.render_execution(m, r, ctx, xs)):
  concatenate_without_subsequent(R.render_started(m, r, ctx), Q.expand_exec(r, ctx, xs),
    started_without_subsequent(m, r, ctx), steps_without_subsequent(r, ctx, xs))

def prepared_without_subsequent(p: N.Prepared) -> WithoutSubsequent([R.frame_prepared(p)]):
  match p:
    case N.Prepared{w, ts, +r, +bs}: prefix_without_subsequent(Q.Prepared{r, bs}, Nil{}, {==}, empty_without_subsequent())

def phase_without_subsequent(+m: R.Micro, phase: R.PhaseBefore) -> WithoutSubsequent(R.render_phase(m, phase)):
  match phase:
    case R.BeforeInput{}: input_without_subsequent(m)
    case R.AfterReceive{r}: received_without_subsequent(m, r)
    case R.AfterAuthenticate{r, ctx}: authenticated_without_subsequent(m, r, ctx)
    case R.AfterVerify{r, ctx}: verified_without_subsequent(m, r, ctx)
    case R.Executing{r, ctx, xs}: execution_without_subsequent(m, r, ctx, xs)
    case R.AfterPrepare{+r, +ctx, +xs, +p}:
      concatenate_without_subsequent(R.render_execution(m, r, ctx, xs), Q.concatenate(R.micro_output(m), [R.frame_prepared(p)]),
        execution_without_subsequent(m, r, ctx, xs),
        concatenate_without_subsequent(R.micro_output(m), [R.frame_prepared(p)], output_without_subsequent(m),
          prepared_without_subsequent(p)))


def BeforeWithoutSubsequent(q: Maybe<&2, Closure>) -> Type:
  match q:
    case None{}: Unit
    case Some{Closure{before, c, closes, delivery, origin}}: WithoutSubsequent(before)

def error_without_subsequent(q: Maybe<&2, List<&2, U32>>, +before: List<&2, Q.Frame>, +s: D.State,
  +e: Errors.Error, +closes: Bool, +delivery: R.Delivery, +origin: R.Branch, proof: WithoutSubsequent(before)) ->
  BeforeWithoutSubsequent(error(q, before, s, e, closes, delivery, origin)):
  match q:
    case None{}: Unit{}
    case Some{bs}: proof

def before_aut_without_subsequent(+m: R.Micro, +r: P.Request) -> WithoutSubsequent(before_authentication(m, r)):
  concatenate_without_subsequent(R.render_received(m, r), Q.concatenate(R.micro_authentication(m), [Q.Authenticated{r, None{}}]),
    received_without_subsequent(m, r),
    concatenate_without_subsequent(R.micro_authentication(m), [Q.Authenticated{r, None{}}], authentication_without_subsequent(m),
      prefix_without_subsequent(Q.Authenticated{r, None{}}, Nil{}, {==}, empty_without_subsequent())))

def branch_closure_without_subsequent(+m: R.Micro, +s: D.State, branch: R.Branch) -> BeforeWithoutSubsequent(of_branch(m, s, branch)):
  match branch:
    case R.InputRefusal{+e, +closes, +delivery}:
      error_without_subsequent(P.frame(S.response_value(S.response_error(Errors.status(error_of_input(e))))),
        R.micro_input(m), s, error_of_input(e), closes, delivery, R.InputRefusal{e, closes, delivery}, input_without_subsequent(m))
    case R.AutRefusal{+r, +delivery}:
      error_without_subsequent(P.frame(S.response_value(S.response_error(S.Authentication{}))), before_authentication(m, r), s,
        Errors.Authentication{}, False{}, delivery, R.AutRefusal{r, delivery}, before_aut_without_subsequent(m, r))
    case R.GateRefusal{+r, +ctx, +delivery}:
      error_without_subsequent(P.frame(S.response_value(S.response_error(S.Certificate{}))), before_gate(m, r, ctx), s,
        Errors.Certificate{}, False{}, delivery, R.GateRefusal{r, ctx, delivery},
        concatenate_without_subsequent(R.render_authenticated(m, r, ctx), [Q.Rejected{r, ctx}], authenticated_without_subsequent(m, r, ctx),
          prefix_without_subsequent(Q.Rejected{r, ctx}, Nil{}, {==}, empty_without_subsequent())))
    case R.Executed{+r, +ctx, +xs, p, delivery}:
      concatenate_without_subsequent(R.render_execution(m, r, ctx, xs), R.micro_output(m),
        execution_without_subsequent(m, r, ctx, xs), output_without_subsequent(m))
    case R.FailureBefore{+phase, +stage, +id, fatal, +delivery}:
      match fatal:
        case True{}: Unit{}
        case False{}:
          error_without_subsequent(P.frame(S.response_value(S.response_error(S.Failure{}))),
            before_failure(m, phase, stage, id, False{}), s, Errors.Failure{}, False{}, delivery, R.FailureBefore{phase, stage, id, False{}, delivery},
            concatenate_without_subsequent(R.render_phase(m, phase), [Q.Failed{stage, id, False{}}], phase_without_subsequent(m, phase),
              prefix_without_subsequent(Q.Failed{stage, id, False{}}, Nil{}, {==}, empty_without_subsequent())))
    case R.InitialOk{}: Unit{}
    case R.InitialRefusal{status}: Unit{}
    case R.InitialFailure{accepts, stage, id, fatal}: Unit{}
    case R.WithoutResponse{}: Unit{}
    case R.FatalAfterPublication{r, ctx, xs, p, stage, id}: Unit{}
    case R.Pending{phase}: Unit{}
    case R.InitialPending{accepts}: Unit{}

def configure_without_subsequent(q: Maybe<&2, Closure>, proof: BeforeWithoutSubsequent(q)) -> BeforeWithoutSubsequent(configure(q)):
  match q:
    case None{}: Unit{}
    case Some{Closure{+before, c, closes, delivery, origin}}:
      prefix_without_subsequent(Q.Configured{}, before, {==}, proof)

law before_of_closure_without_subsequent:
  for +m: R.Micro
  for +s: D.State
  for +branch: R.Branch
  BeforeWithoutSubsequent(closure_of_branch(m, s, branch))
def before_of_closure_without_subsequent(m, s, branch):
  configure_without_subsequent(of_branch(m, s, branch), branch_closure_without_subsequent(m, s, branch))

def error_has_closure(+before: List<&2, Q.Frame>, +s: D.State, +e: Errors.Error,
  +closes: Bool, +delivery: R.Delivery, +origin: R.Branch) ->
  &h: Closure -> {close_error(before, s, e, closes, delivery, origin) == Some{h} : Maybe<&2, Closure>}:
  (Closure{before, N.Conclusion{s, S.response_error(Errors.status(e)), Errors.bytes(e)}, closes, delivery, origin},
    Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, Closure>, q => error(q, before, s, e, closes, delivery, origin),
      P.frame(S.response_value(S.response_error(Errors.status(e)))), Some{Errors.bytes(e)},
      Errors.all_os_errors_prepared_are_exactly_messages_original(e)))

def some_closure_contradicts_absence(-T: Type, +q: Maybe<&2, Closure>,
  exists: &h: Closure -> {q == Some{h} : Maybe<&2, Closure>},
  absent: {q == None{} : Maybe<&2, Closure>}) -> T:
  match exists:
    case (+h, present):
      L.ex_false(T, F.none_negative_some(Closure, h,
        Equal.trans(Maybe<&2, Closure>, None{}, q, Some{h}, Equal.sym(Maybe<&2, Closure>, q, None{}, absent), present)))

def initial_without_subsequent(q: Maybe<&2, List<&2, U32>>, +s: D.State) -> WithoutSubsequent(R.render_initial(q, s)):
  match q:
    case None{}: prefix_without_subsequent(Q.Encoded{D.state_value(s), None{}}, Nil{}, {==}, empty_without_subsequent())
    case Some{+bs}:
      prefix_without_subsequent(Q.Encoded{D.state_value(s), Some{bs}}, [Q.Stored{s, bs, s}, Q.Initialized{s}], {==},
        prefix_without_subsequent(Q.Stored{s, bs, s}, [Q.Initialized{s}], {==},
          prefix_without_subsequent(Q.Initialized{s}, Nil{}, {==}, empty_without_subsequent())))

def prefix_initial_without_subsequent(+m: R.Micro, accepts: Bool) -> WithoutSubsequent(R.prefix_initial(m, accepts)):
  match accepts:
    case False{}: empty_without_subsequent()
    case True{}: prefix_without_subsequent(Q.InitialAccepts{}, R.micro_output(m), {==}, output_without_subsequent(m))

def publication_without_subsequent(r: S.Response, +s: D.State) -> WithoutSubsequent(R.render_publication(r, s)):
  match r:
    case S.Response{S.Success{}, v}: prefix_without_subsequent(Q.Published{s}, Nil{}, {==}, empty_without_subsequent())
    case S.Response{S.Refusal{}, v}: empty_without_subsequent()
    case S.Response{S.Input{}, v}: empty_without_subsequent()
    case S.Response{S.Authentication{}, v}: empty_without_subsequent()
    case S.Response{S.Certificate{}, v}: empty_without_subsequent()
    case S.Response{S.DataError{}, v}: empty_without_subsequent()
    case S.Response{S.Limit{}, v}: empty_without_subsequent()
    case S.Response{S.Failure{}, v}: empty_without_subsequent()

def fatal_without_subsequent(c: N.Conclusion, +stage: X.Stage, +id: String) -> WithoutSubsequent(R.render_fatal_published(c, stage, id)):
  match c:
    case N.Conclusion{+s, +r, +bs}:
      prefix_without_subsequent(Q.Prepared{r, bs}, Q.concatenate(R.render_publication(r, s), [Q.Failed{stage, id, True{}}, Q.Closed{}]), {==},
        concatenate_without_subsequent(R.render_publication(r, s), [Q.Failed{stage, id, True{}}, Q.Closed{}],
          publication_without_subsequent(r, s),
          prefix_without_subsequent(Q.Failed{stage, id, True{}}, [Q.Closed{}], {==},
            prefix_without_subsequent(Q.Closed{}, Nil{}, {==}, empty_without_subsequent()))))

def absence_of_branch_excludes_subsequent(+m: R.Micro, +s: D.State, +branch: R.Branch,
  absent: {of_branch(m, s, branch) == None{} : Maybe<&2, Closure>}) -> WithoutSubsequent(R.render_branch(m, s, branch)):
  match branch:
    case R.InitialOk{}:
      prefix_without_subsequent(Q.InitialAccepts{}, Q.concatenate(R.micro_output(m), R.render_initial(P.encode(D.state_value(s)), s)), {==},
        concatenate_without_subsequent(R.micro_output(m), R.render_initial(P.encode(D.state_value(s)), s),
          output_without_subsequent(m), initial_without_subsequent(P.encode(D.state_value(s)), s)))
    case R.InitialRefusal{+status}: prefix_without_subsequent(Q.InitialRefused{status}, Nil{}, {==}, empty_without_subsequent())
    case R.InitialFailure{+accepts, +stage, +id, +fatal}:
      concatenate_without_subsequent(R.prefix_initial(m, accepts), [Q.Failed{stage, id, fatal}, Q.InitialRefused{S.Failure{}}],
        prefix_initial_without_subsequent(m, accepts),
        prefix_without_subsequent(Q.Failed{stage, id, fatal}, [Q.InitialRefused{S.Failure{}}], {==},
          prefix_without_subsequent(Q.InitialRefused{S.Failure{}}, Nil{}, {==}, empty_without_subsequent())))
    case R.WithoutResponse{}: prefix_without_subsequent(Q.Closed{}, Nil{}, {==}, empty_without_subsequent())
    case R.InputRefusal{+e, +closes, +delivery}:
      some_closure_contradicts_absence(WithoutSubsequent(R.render_branch(m, s, R.InputRefusal{e, closes, delivery})),
        of_branch(m, s, R.InputRefusal{e, closes, delivery}),
        error_has_closure(R.micro_input(m), s, error_of_input(e), closes, delivery, R.InputRefusal{e, closes, delivery}), absent)
    case R.AutRefusal{+r, +delivery}:
      some_closure_contradicts_absence(WithoutSubsequent(R.render_branch(m, s, R.AutRefusal{r, delivery})), of_branch(m, s, R.AutRefusal{r, delivery}),
        error_has_closure(before_authentication(m, r), s, Errors.Authentication{}, False{}, delivery, R.AutRefusal{r, delivery}), absent)
    case R.GateRefusal{+r, +ctx, +delivery}:
      some_closure_contradicts_absence(WithoutSubsequent(R.render_branch(m, s, R.GateRefusal{r, ctx, delivery})), of_branch(m, s, R.GateRefusal{r, ctx, delivery}),
        error_has_closure(before_gate(m, r, ctx), s, Errors.Certificate{}, False{}, delivery, R.GateRefusal{r, ctx, delivery}), absent)
    case R.Executed{+r, +ctx, +xs, +p, +delivery}:
      some_closure_contradicts_absence(WithoutSubsequent(R.render_branch(m, s, R.Executed{r, ctx, xs, p, delivery})), of_branch(m, s, R.Executed{r, ctx, xs, p, delivery}),
        (Closure{before_execution(m, r, ctx, xs), N.conclude(p, s), False{}, delivery, R.Executed{r, ctx, xs, p, delivery}}, {==}), absent)
    case R.FailureBefore{+phase, +stage, +id, fatal, +delivery}:
      match fatal:
        case True{}:
          concatenate_without_subsequent(R.render_phase(m, phase), R.render_failure(s, stage, id, True{}, delivery), phase_without_subsequent(m, phase),
            prefix_without_subsequent(Q.Failed{stage, id, True{}}, [Q.Closed{}], {==}, prefix_without_subsequent(Q.Closed{}, Nil{}, {==}, empty_without_subsequent())))
        case False{}:
          some_closure_contradicts_absence(WithoutSubsequent(R.render_branch(m, s, R.FailureBefore{phase, stage, id, False{}, delivery})),
            of_branch(m, s, R.FailureBefore{phase, stage, id, False{}, delivery}),
            error_has_closure(before_failure(m, phase, stage, id, False{}), s, Errors.Failure{}, False{}, delivery, R.FailureBefore{phase, stage, id, False{}, delivery}), absent)
    case R.FatalAfterPublication{+r, +ctx, +xs, +p, +stage, +id}:
      concatenate_without_subsequent(R.render_execution(m, r, ctx, xs), Q.concatenate(R.micro_output(m), R.render_fatal_published(N.conclude(p, s), stage, id)),
        execution_without_subsequent(m, r, ctx, xs),
        concatenate_without_subsequent(R.micro_output(m), R.render_fatal_published(N.conclude(p, s), stage, id),
          output_without_subsequent(m), fatal_without_subsequent(N.conclude(p, s), stage, id)))
    case R.Pending{phase}: phase_without_subsequent(m, phase)
    case R.InitialPending{accepts}: prefix_initial_without_subsequent(m, accepts)

def remove_configuration_empty(q: Maybe<&2, Closure>, absent: {configure(q) == None{} : Maybe<&2, Closure>}) ->
  {q == None{} : Maybe<&2, Closure>}:
  match q:
    case None{}: {==}
    case Some{Closure{+before, +c, +closes, +delivery, +origin}}:
      L.ex_false({Some{Closure{before, c, closes, delivery, origin}} == None{} : Maybe<&2, Closure>},
        F.none_negative_some(Closure, Closure{Con{Q.Configured{}, before}, c, closes, delivery, origin},
          Equal.sym(Maybe<&2, Closure>, Some{Closure{Con{Q.Configured{}, before}, c, closes, delivery, origin}}, None{}, absent)))

law absence_of_closure_excludes_subsequent:
  for +m: R.Micro
  for +s: D.State
  for +branch: R.Branch
  for absent: {closure_of_branch(m, s, branch) == None{} : Maybe<&2, Closure>}
  WithoutSubsequent(R.render(m, s, branch))
def absence_of_closure_excludes_subsequent(m, s, branch, absent):
  prefix_without_subsequent(Q.Configured{}, R.render_branch(m, s, branch), {==},
    absence_of_branch_excludes_subsequent(m, s, branch, remove_configuration_empty(of_branch(m, s, branch), absent)))

# Adapters for APIs consumed by Law6, without another path.
def BeforeWithoutNext(q: Maybe<&2, Closure>) -> Type:
  match q:
    case None{}: Unit
    case Some{Closure{before, c, closes, delivery, origin}}: WithoutNext(before)

def extract_before_next(q: Maybe<&2, Closure>, proof: BeforeWithoutSubsequent(q)) -> BeforeWithoutNext(q):
  match q:
    case None{}: Unit{}
    case Some{Closure{before, c, closes, delivery, origin}}:
      L.and_left(WithoutNext(before), L.E<{Phases.absent(Phases.Complete{}, before) == True{} : Bool}, {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool}>, proof)

def before_of_closure_without_next(+m: R.Micro, +s: D.State, +branch: R.Branch) -> BeforeWithoutNext(closure_of_branch(m, s, branch)):
  extract_before_next(closure_of_branch(m, s, branch), before_of_closure_without_subsequent(m, s, branch))

def absence_of_closure_excludes_next(+m: R.Micro, +s: D.State, +branch: R.Branch, absent: {closure_of_branch(m, s, branch) == None{} : Maybe<&2, Closure>}) -> WithoutNext(R.render(m, s, branch)):
  L.and_left(WithoutNext(R.render(m, s, branch)), L.E<{Phases.absent(Phases.Complete{}, R.render(m, s, branch)) == True{} : Bool}, {Phases.absent(Phases.Interrupted{}, R.render(m, s, branch)) == True{} : Bool}>, absence_of_closure_excludes_subsequent(m, s, branch, absent))

def publication_without_next(r: S.Response, +s: D.State) -> WithoutNext(R.render_publication(r, s)):
  L.and_left(WithoutNext(R.render_publication(r, s)), L.E<{Phases.absent(Phases.Complete{}, R.render_publication(r, s)) == True{} : Bool}, {Phases.absent(Phases.Interrupted{}, R.render_publication(r, s)) == True{} : Bool}>, publication_without_subsequent(r, s))

def DeliveriesOfForm(-xs: List<&2, Q.Frame>, q: Maybe<&2, Closure>) -> Type:
  match q:
    case None{}: L.E<{Phases.absent(Phases.Complete{}, xs) == True{} : Bool}, {Phases.absent(Phases.Interrupted{}, xs) == True{} : Bool}>
    case Some{Closure{before, c, closes, delivery, origin}}:
      L.E<{Phases.absent(Phases.Complete{}, before) == True{} : Bool}, {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool}>

def deliveries_of_proofs(+xs: List<&2, Q.Frame>, q: Maybe<&2, Closure>, before: BeforeWithoutSubsequent(q),
  none: {q == None{} : Maybe<&2, Closure>} -> WithoutSubsequent(xs)) -> DeliveriesOfForm(xs, q):
  match q:
    case None{}:
      L.and_right(WithoutNext(xs), L.E<{Phases.absent(Phases.Complete{}, xs) == True{} : Bool}, {Phases.absent(Phases.Interrupted{}, xs) == True{} : Bool}>, none({==}))
    case Some{Closure{prefix, c, closes, delivery, origin}}:
      L.and_right(WithoutNext(prefix), L.E<{Phases.absent(Phases.Complete{}, prefix) == True{} : Bool}, {Phases.absent(Phases.Interrupted{}, prefix) == True{} : Bool}>, before)

law deliveries_of_form:
  for +m: R.Micro
  for +s: D.State
  for +branch: R.Branch
  DeliveriesOfForm(R.render(m, s, branch), closure_of_branch(m, s, branch))
def deliveries_of_form(m, s, branch):
  deliveries_of_proofs(R.render(m, s, branch), closure_of_branch(m, s, branch), before_of_closure_without_subsequent(m, s, branch), absence_of_closure_excludes_subsequent(m, s, branch))

def find_closure_next(+xs: List<&2, Q.Frame>, +branch: R.Branch, q: Maybe<&2, Closure>,
  +t: Nat, +a: D.State, +b: D.State, form: Form(xs, branch, q),
  before: BeforeWithoutNext(q), without_closure: {q == None{} : Maybe<&2, Closure>} -> WithoutNext(xs),
  query_result: {Q.query(xs, t) == Some{Q.Next{a, b}} : Maybe<&2, Q.Frame>}) ->
  &h: Closure -> L.E<Form(xs, branch, Some{h}), BeforeWithoutNext(Some{h})>:
  match q:
    case None{}:
      L.ex_false((&h: Closure -> L.E<Form(xs, branch, Some{h}), BeforeWithoutNext(Some{h})>),
        without_closure({==})(a, b, t, query_result))
    case Some{+h}: (h, L.Both{form, before})

law invert_next:
  for +m: R.Micro
  for +s: D.State
  for +branch: R.Branch
  for +t: Nat
  for +a: D.State
  for +b: D.State
  for query_result: {Q.query(R.render(m, s, branch), t) == Some{Q.Next{a, b}} : Maybe<&2, Q.Frame>}
  exs h: Closure
  L.E<Form(R.render(m, s, branch), branch, Some{h}), BeforeWithoutNext(Some{h})>
def invert_next(m, s, branch, t, a, b, query_result):
  find_closure_next(R.render(m, s, branch), branch, closure_of_branch(m, s, branch), t, a, b,
    form_of_route(m, s, branch), before_of_closure_without_next(m, s, branch),
    absence_of_closure_excludes_next(m, s, branch), query_result)

# Native preparation differs from the fixed error that may follow it.
type OriginPreparation is Data:
  Native{request: P.Request, context: D.Context, frames: List<&2, Q.FrameExec>, prepared: N.Prepared}
  Fixed{error: Errors.Error}

def milestone_preparation(origin: OriginPreparation) -> Q.Frame:
  match origin:
    case Native{r, ctx, xs, p}: R.frame_prepared(p)
    case Fixed{+e}: Q.Prepared{S.response_error(Errors.status(e)), Errors.bytes(e)}

def FixedOfBranch(-e: Errors.Error, branch: R.Branch) -> Type:
  match branch:
    case R.InputRefusal{error, closes, delivery}: {e == error_of_input(error) : Errors.Error}
    case R.AutRefusal{r, delivery}: {e == Errors.Authentication{} : Errors.Error}
    case R.GateRefusal{r, ctx, delivery}: {e == Errors.Certificate{} : Errors.Error}
    case R.FailureBefore{phase, stage, id, fatal, delivery}: L.E<{e == Errors.Failure{} : Errors.Error}, {fatal == False{} : Bool}>
    case _: Empty

def PrefixFixed(+m: R.Micro, branch: R.Branch, +before: List<&2, Q.Frame>) -> Type:
  match branch:
    case R.InputRefusal{e, closes, delivery}: {before == Con{Q.Configured{}, R.micro_input(m)} : List<&2, Q.Frame>}
    case R.AutRefusal{r, delivery}: {before == Con{Q.Configured{}, before_authentication(m, r)} : List<&2, Q.Frame>}
    case R.GateRefusal{r, ctx, delivery}: {before == Con{Q.Configured{}, before_gate(m, r, ctx)} : List<&2, Q.Frame>}
    case R.FailureBefore{phase, stage, id, fatal, delivery}: {before == Con{Q.Configured{}, before_failure(m, phase, stage, id, fatal)} : List<&2, Q.Frame>}
    case _: Empty

def PreparationOfOrigin(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, -s: D.State,
  +code: Source.JudgmentSyntactic, +branch: R.Branch, +before: List<&2, Q.Frame>, origin: OriginPreparation) -> Type:
  match origin:
    case Native{r, ctx, xs, p}:
      L.E<{before == Con{Q.Configured{}, before_execution(m, r, ctx, xs)} : List<&2, Q.Frame>}, Source.FinalReal(source, c, s, r, ctx, code, xs, p)>
    case Fixed{e}: L.E<FixedOfBranch(e, branch), PrefixFixed(m, branch, before)>

def PreparationInTrace(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, -s: D.State,
  +code: Source.JudgmentSyntactic, +branch: R.Branch, -qs: List<&2, Q.Frame>, -t: Nat, +r: S.Response, +bs: List<&2, U32>) -> Type:
  &before: List<&2, Q.Frame> -> &later: List<&2, Q.Frame> -> &origin: OriginPreparation ->
    L.E<{qs == Q.concatenate(before, Con{Q.Prepared{r, bs}, later}) : List<&2, Q.Frame>},
      L.E<{t == Nat.add(Q.size(before), 0n) : Nat},
        L.E<{Q.Prepared{r, bs} == milestone_preparation(origin) : Q.Frame}, PreparationOfOrigin(source, c, m, s, code, branch, before, origin)>>>

def is_preparation(q: Q.Frame) -> Bool:
  match q:
    case Q.Prepared{r, bs}: True{}
    case _: False{}

def WithoutPreparation(-qs: List<&2, Q.Frame>) -> Type:
  @r: S.Response -> @bs: List<&2, U32> -> Five.WithoutFrame(qs, Q.Prepared{r, bs})

def without_preparation_empty() -> WithoutPreparation(Nil{}):
  +r => +bs => Five.empty_without_frame(Q.Prepared{r, bs})

def prefix_without_preparation(+q: Q.Frame, -qs: List<&2, Q.Frame>, neutral: {is_preparation(q) == False{} : Bool}, rest: WithoutPreparation(qs)) -> WithoutPreparation(Con{q, qs}):
  +r => +bs => Five.head_by_tag(is_preparation, q, Q.Prepared{r, bs}, qs, neutral, {==}, rest(r, bs))

def concatenate_without_preparation(+xs: List<&2, Q.Frame>, -ys: List<&2, Q.Frame>, a: WithoutPreparation(xs), b: WithoutPreparation(ys)) -> WithoutPreparation(Q.concatenate(xs, ys)):
  +r => +bs => Five.concatenate_without_frame(xs, ys, Q.Prepared{r, bs}, a(r, bs), b(r, bs))

def primitives_without_preparation(+ps: List<&2, M.Primitive>) -> WithoutPreparation(M.expand_primitives(ps)):
  +r => +bs => Five.internal_negative_contains(M.expand_primitives(ps), Q.Prepared{r, bs}, M.primitives_only_generate_internal(ps), {==})

def input_without_preparation(m: R.Micro) -> WithoutPreparation(R.micro_input(m)):
  match m:
    case R.Micro{a, b, c, d}: primitives_without_preparation(a)

def authentication_without_preparation(m: R.Micro) -> WithoutPreparation(R.micro_authentication(m)):
  match m:
    case R.Micro{a, b, c, d}: primitives_without_preparation(b)

def execution_micro_without_preparation(m: R.Micro) -> WithoutPreparation(R.micro_execution(m)):
  match m:
    case R.Micro{a, b, c, d}: primitives_without_preparation(c)

def output_without_preparation(m: R.Micro) -> WithoutPreparation(R.micro_output(m)):
  match m:
    case R.Micro{a, b, c, d}: primitives_without_preparation(d)

def received_without_preparation(+m: R.Micro, +r: P.Request) -> WithoutPreparation(R.render_received(m, r)):
  concatenate_without_preparation(R.micro_input(m), [Q.Received{r}], input_without_preparation(m), prefix_without_preparation(Q.Received{r}, Nil{}, {==}, without_preparation_empty()))

def authenticated_without_preparation(+m: R.Micro, +r: P.Request, +ctx: D.Context) -> WithoutPreparation(R.render_authenticated(m, r, ctx)):
  concatenate_without_preparation(R.render_received(m, r), Q.concatenate(R.micro_authentication(m), [Q.Authenticated{r, Some{ctx}}]), received_without_preparation(m, r),
    concatenate_without_preparation(R.micro_authentication(m), [Q.Authenticated{r, Some{ctx}}], authentication_without_preparation(m), prefix_without_preparation(Q.Authenticated{r, Some{ctx}}, Nil{}, {==}, without_preparation_empty())))

def verified_without_preparation(+m: R.Micro, +r: P.Request, +ctx: D.Context) -> WithoutPreparation(R.render_verified(m, r, ctx)):
  concatenate_without_preparation(R.render_authenticated(m, r, ctx), [Q.Accepts{r, ctx}], authenticated_without_preparation(m, r, ctx), prefix_without_preparation(Q.Accepts{r, ctx}, Nil{}, {==}, without_preparation_empty()))

def started_without_preparation(+m: R.Micro, +r: P.Request, +ctx: D.Context) -> WithoutPreparation(R.render_started(m, r, ctx)):
  concatenate_without_preparation(R.render_verified(m, r, ctx), Q.concatenate(R.micro_execution(m), [Q.Started{r, ctx}]), verified_without_preparation(m, r, ctx),
    concatenate_without_preparation(R.micro_execution(m), [Q.Started{r, ctx}], execution_micro_without_preparation(m), prefix_without_preparation(Q.Started{r, ctx}, Nil{}, {==}, without_preparation_empty())))

def steps_without_preparation(+r: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>) -> WithoutPreparation(Q.expand_exec(r, ctx, xs)):
  +response => +bs => +t => query_result => Exec.expand_reflects_query(r, ctx, xs, t, Q.Prepared{response, bs}, query_result)

def execution_without_preparation(+m: R.Micro, +r: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>) -> WithoutPreparation(R.render_execution(m, r, ctx, xs)):
  concatenate_without_preparation(R.render_started(m, r, ctx), Q.expand_exec(r, ctx, xs), started_without_preparation(m, r, ctx), steps_without_preparation(r, ctx, xs))

def before_execution_without_preparation(+m: R.Micro, +r: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>) ->
  WithoutPreparation(Con{Q.Configured{}, before_execution(m, r, ctx, xs)}):
  prefix_without_preparation(Q.Configured{}, before_execution(m, r, ctx, xs), {==}, concatenate_without_preparation(R.render_execution(m, r, ctx, xs), R.micro_output(m), execution_without_preparation(m, r, ctx, xs), output_without_preparation(m)))

# Invert one marker. Prefixes may contain other preparations only in the
# two-marker combinator below; no global preparation uniqueness is asserted.
def return_value_preparation(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, -s: D.State, +code: Source.JudgmentSyntactic,
  +branch: R.Branch, +before: List<&2, Q.Frame>, +later: List<&2, Q.Frame>, +origin: OriginPreparation, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  position: {t == Nat.add(Q.size(before), 0n) : Nat}, +frame: {Q.Prepared{r, bs} == milestone_preparation(origin) : Q.Frame},
  source_real: PreparationOfOrigin(source, c, m, s, code, branch, before, origin)) ->
  PreparationInTrace(source, c, m, s, code, branch, Q.concatenate(before, Con{milestone_preparation(origin), later}), t, r, bs):
  (before, later, origin, L.Both{
    Equal.cong(Q.Frame, List<&2, Q.Frame>, q => Q.concatenate(before, Con{q, later}), milestone_preparation(origin), Q.Prepared{r, bs}, Equal.sym(Q.Frame, Q.Prepared{r, bs}, milestone_preparation(origin), frame)),
    L.Both{position, L.Both{frame, source_real}}})

def invert_mark_of_preparation(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, -s: D.State, +code: Source.JudgmentSyntactic,
  +branch: R.Branch, +before: List<&2, Q.Frame>, +later: List<&2, Q.Frame>, +origin: OriginPreparation, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  without_before: WithoutPreparation(before), without_later: WithoutPreparation(later), source_real: PreparationOfOrigin(source, c, m, s, code, branch, before, origin),
  query_result: {Q.query(Q.concatenate(before, Con{milestone_preparation(origin), later}), t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}) ->
  PreparationInTrace(source, c, m, s, code, branch, Q.concatenate(before, Con{milestone_preparation(origin), later}), t, r, bs):
  F.combined_pair(PreparationInTrace(source, c, m, s, code, branch, Q.concatenate(before, Con{milestone_preparation(origin), later}), t, r, bs),
    {t == Nat.add(Q.size(before), 0n) : Nat}, {Q.Prepared{r, bs} == milestone_preparation(origin) : Q.Frame},
    Five.marker_unique(before, milestone_preparation(origin), later, Q.Prepared{r, bs}, t, without_before(r, bs), without_later(r, bs), query_result),
    position => frame => return_value_preparation(source, c, m, s, code, branch, before, later, origin, t, r, bs, position, frame, source_real))

def preparation_by_equations(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, -s: D.State, +code: Source.JudgmentSyntactic,
  +branch: R.Branch, +qs: List<&2, Q.Frame>, +before: List<&2, Q.Frame>, +later: List<&2, Q.Frame>, +origin: OriginPreparation, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  trace: {qs == Q.concatenate(before, Con{milestone_preparation(origin), later}) : List<&2, Q.Frame>},
  position: {t == Nat.add(Q.size(before), 0n) : Nat}, +frame: {Q.Prepared{r, bs} == milestone_preparation(origin) : Q.Frame},
  source_real: PreparationOfOrigin(source, c, m, s, code, branch, before, origin)) -> PreparationInTrace(source, c, m, s, code, branch, qs, t, r, bs):
  (before, later, origin, L.Both{Equal.trans(List<&2, Q.Frame>, qs, Q.concatenate(before, Con{milestone_preparation(origin), later}), Q.concatenate(before, Con{Q.Prepared{r, bs}, later}),
    trace, Equal.cong(Q.Frame, List<&2, Q.Frame>, q => Q.concatenate(before, Con{q, later}), milestone_preparation(origin), Q.Prepared{r, bs}, Equal.sym(Q.Frame, Q.Prepared{r, bs}, milestone_preparation(origin), frame))),
    L.Both{position, L.Both{frame, source_real}}})

law size_summed:
  for xs: List<&2, Q.Frame>
  for -ys: List<&2, Q.Frame>
  for -n: Nat
  {Nat.add(Q.size(xs), Nat.add(Q.size(ys), n)) == Nat.add(Q.size(Q.concatenate(xs, ys)), n) : Nat}
def size_summed(xs, ys, n):
  match xs:
    case Nil{}: {==}
    case Con{h, +t}: Equal.cong(Nat, Nat, z => Succ{z}, Nat.add(Q.size(t), Nat.add(Q.size(ys), n)), Nat.add(Q.size(Q.concatenate(t, ys)), n), size_summed(t, ys, n))

def two_marks_by_part(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, -s: D.State, +code: Source.JudgmentSyntactic,
  +branch: R.Branch, +before: List<&2, Q.Frame>, +middle: List<&2, Q.Frame>, +later: List<&2, Q.Frame>,
  +native: OriginPreparation, +fixed: OriginPreparation, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  without_before: WithoutPreparation(before), without_middle: WithoutPreparation(middle), without_later: WithoutPreparation(later),
  origin_native: PreparationOfOrigin(source, c, m, s, code, branch, before, native),
  origin_fixed: PreparationOfOrigin(source, c, m, s, code, branch, Q.concatenate(Q.concatenate(before, [milestone_preparation(native)]), middle), fixed),
  part: Q.Part(Q.concatenate(before, [milestone_preparation(native)]), Q.concatenate(middle, Con{milestone_preparation(fixed), later}), t, Q.Prepared{r, bs})) ->
  PreparationInTrace(source, c, m, s, code, branch,
    Q.concatenate(Q.concatenate(before, [milestone_preparation(native)]), Q.concatenate(middle, Con{milestone_preparation(fixed), later})), t, r, bs):
  match part:
    case L.Left{(+i, L.Both{pos, query_result})}:
      F.combined_pair(PreparationInTrace(source, c, m, s, code, branch, Q.concatenate(Q.concatenate(before, [milestone_preparation(native)]), Q.concatenate(middle, Con{milestone_preparation(fixed), later})), t, r, bs),
        {i == Nat.add(Q.size(before), 0n) : Nat}, {Q.Prepared{r, bs} == milestone_preparation(native) : Q.Frame},
        Five.marker_unique(before, milestone_preparation(native), Nil{}, Q.Prepared{r, bs}, i, without_before(r, bs), Five.empty_without_frame(Q.Prepared{r, bs}), query_result), size => frame =>
          preparation_by_equations(source, c, m, s, code, branch,
            Q.concatenate(Q.concatenate(before, [milestone_preparation(native)]), Q.concatenate(middle, Con{milestone_preparation(fixed), later})), before, Q.concatenate(middle, Con{milestone_preparation(fixed), later}), native, t, r, bs,
            Q.concatenate_assoc(before, [milestone_preparation(native)], Q.concatenate(middle, Con{milestone_preparation(fixed), later})),
            Equal.trans(Nat, t, i, Nat.add(Q.size(before), 0n), pos, size), frame, origin_native))
    case L.Right{(+i, L.Both{pos, query_result})}:
      F.combined_pair(PreparationInTrace(source, c, m, s, code, branch, Q.concatenate(Q.concatenate(before, [milestone_preparation(native)]), Q.concatenate(middle, Con{milestone_preparation(fixed), later})), t, r, bs),
        {i == Nat.add(Q.size(middle), 0n) : Nat}, {Q.Prepared{r, bs} == milestone_preparation(fixed) : Q.Frame},
        Five.marker_unique(middle, milestone_preparation(fixed), later, Q.Prepared{r, bs}, i, without_middle(r, bs), without_later(r, bs), query_result), size => frame =>
          preparation_by_equations(source, c, m, s, code, branch,
            Q.concatenate(Q.concatenate(before, [milestone_preparation(native)]), Q.concatenate(middle, Con{milestone_preparation(fixed), later})), Q.concatenate(Q.concatenate(before, [milestone_preparation(native)]), middle), later, fixed, t, r, bs,
            Equal.sym(List<&2, Q.Frame>, Q.concatenate(Q.concatenate(Q.concatenate(before, [milestone_preparation(native)]), middle), Con{milestone_preparation(fixed), later}),
              Q.concatenate(Q.concatenate(before, [milestone_preparation(native)]), Q.concatenate(middle, Con{milestone_preparation(fixed), later})),
              Q.concatenate_assoc(Q.concatenate(before, [milestone_preparation(native)]), middle, Con{milestone_preparation(fixed), later})),
            Equal.trans(Nat, t, Nat.add(Q.size(Q.concatenate(before, [milestone_preparation(native)])), i), Nat.add(Q.size(Q.concatenate(Q.concatenate(before, [milestone_preparation(native)]), middle)), 0n), pos,
              Equal.trans(Nat, Nat.add(Q.size(Q.concatenate(before, [milestone_preparation(native)])), i), Nat.add(Q.size(Q.concatenate(before, [milestone_preparation(native)])), Nat.add(Q.size(middle), 0n)),
                Nat.add(Q.size(Q.concatenate(Q.concatenate(before, [milestone_preparation(native)]), middle)), 0n),
                Equal.cong(Nat, Nat, z => Nat.add(Q.size(Q.concatenate(before, [milestone_preparation(native)])), z), i, Nat.add(Q.size(middle), 0n), size),
                size_summed(Q.concatenate(before, [milestone_preparation(native)]), middle, 0n))), frame, origin_fixed))

def invert_two_marks(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, -s: D.State, +code: Source.JudgmentSyntactic,
  +branch: R.Branch, +before: List<&2, Q.Frame>, +middle: List<&2, Q.Frame>, +later: List<&2, Q.Frame>,
  +native: OriginPreparation, +fixed: OriginPreparation, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  without_before: WithoutPreparation(before), without_middle: WithoutPreparation(middle), without_later: WithoutPreparation(later),
  origin_native: PreparationOfOrigin(source, c, m, s, code, branch, before, native),
  origin_fixed: PreparationOfOrigin(source, c, m, s, code, branch, Q.concatenate(Q.concatenate(before, [milestone_preparation(native)]), middle), fixed),
  query_result: {Q.query(Q.concatenate(Q.concatenate(before, [milestone_preparation(native)]), Q.concatenate(middle, Con{milestone_preparation(fixed), later})), t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}) ->
  PreparationInTrace(source, c, m, s, code, branch, Q.concatenate(Q.concatenate(before, [milestone_preparation(native)]), Q.concatenate(middle, Con{milestone_preparation(fixed), later})), t, r, bs):
  two_marks_by_part(source, c, m, s, code, branch, before, middle, later, native, fixed, t, r, bs, without_before, without_middle, without_later, origin_native, origin_fixed,
    Q.divide_query(Q.concatenate(before, [milestone_preparation(native)]), Q.concatenate(middle, Con{milestone_preparation(fixed), later}), t, Q.Prepared{r, bs}, query_result))

def later_delivery_without_preparation(closes: Bool, +s: D.State, next: Bool) -> WithoutPreparation(R.later_delivery(closes, s, next)):
  match closes next:
    case True{} _: prefix_without_preparation(Q.Closed{}, Nil{}, {==}, without_preparation_empty())
    case False{} True{}: prefix_without_preparation(Q.Next{s, s}, Nil{}, {==}, without_preparation_empty())
    case False{} False{}: without_preparation_empty()

def delivery_without_preparation(+s: D.State, +bs: List<&2, U32>, +closes: Bool, delivery: R.Delivery) -> WithoutPreparation(R.render_delivery(s, bs, closes, delivery)):
  match delivery:
    case R.Complete{next}: prefix_without_preparation(Q.Delivered{bs}, R.later_delivery(closes, s, next), {==}, later_delivery_without_preparation(closes, s, next))
    case R.Broken{+prefix}: prefix_without_preparation(Q.Interrupted{prefix}, [Q.Closed{}], {==}, prefix_without_preparation(Q.Closed{}, Nil{}, {==}, without_preparation_empty()))
    case R.PendingDelivery{}: without_preparation_empty()

def publication_without_preparation(r: S.Response, +s: D.State) -> WithoutPreparation(R.render_publication(r, s)):
  match r:
    case S.Response{S.Success{}, v}: prefix_without_preparation(Q.Published{s}, Nil{}, {==}, without_preparation_empty())
    case S.Response{S.Refusal{}, v}: without_preparation_empty()
    case S.Response{S.Input{}, v}: without_preparation_empty()
    case S.Response{S.Authentication{}, v}: without_preparation_empty()
    case S.Response{S.Certificate{}, v}: without_preparation_empty()
    case S.Response{S.DataError{}, v}: without_preparation_empty()
    case S.Response{S.Limit{}, v}: without_preparation_empty()
    case S.Response{S.Failure{}, v}: without_preparation_empty()

def tail_of_conclusion(conclusion: N.Conclusion, +closes: Bool, delivery: R.Delivery) -> List<&2, Q.Frame>:
  match conclusion:
    case N.Conclusion{+s, +r, +bs}: Q.concatenate(R.render_publication(r, s), Con{Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, delivery)})

def tail_of_conclusion_without_preparation(conclusion: N.Conclusion, +closes: Bool, delivery: R.Delivery) -> WithoutPreparation(tail_of_conclusion(conclusion, closes, delivery)):
  match conclusion:
    case N.Conclusion{+s, +r, +bs}:
      concatenate_without_preparation(R.render_publication(r, s), Con{Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, delivery)}, publication_without_preparation(r, s),
        prefix_without_preparation(Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, delivery), {==}, delivery_without_preparation(s, bs, closes, delivery)))

def initial_without_preparation(q: Maybe<&2, List<&2, U32>>, +s: D.State) -> WithoutPreparation(R.render_initial(q, s)):
  match q:
    case None{}: prefix_without_preparation(Q.Encoded{D.state_value(s), None{}}, Nil{}, {==}, without_preparation_empty())
    case Some{+bs}: prefix_without_preparation(Q.Encoded{D.state_value(s), Some{bs}}, [Q.Stored{s, bs, s}, Q.Initialized{s}], {==},
      prefix_without_preparation(Q.Stored{s, bs, s}, [Q.Initialized{s}], {==}, prefix_without_preparation(Q.Initialized{s}, Nil{}, {==}, without_preparation_empty())))

def prefix_initial_without_preparation(+m: R.Micro, accepts: Bool) -> WithoutPreparation(R.prefix_initial(m, accepts)):
  match accepts:
    case True{}: prefix_without_preparation(Q.InitialAccepts{}, R.micro_output(m), {==}, output_without_preparation(m))
    case False{}: without_preparation_empty()

def phase_without_preparation_or_native(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, -s: D.State, +code: Source.JudgmentSyntactic,
  +phase: R.PhaseBefore, real: Five.PhaseReal(source, c, s, code, phase)) ->
  L.Disjunction<WithoutPreparation(R.render_phase(m, phase)),
    &r: P.Request -> &ctx: D.Context -> &xs: List<&2, Q.FrameExec> -> &p: N.Prepared ->
      L.E<{phase == R.AfterPrepare{r, ctx, xs, p} : R.PhaseBefore}, Source.FinalReal(source, c, s, r, ctx, code, xs, p)>>:
  match phase:
    case R.BeforeInput{}: L.Left{input_without_preparation(m)}
    case R.AfterReceive{r}: L.Left{received_without_preparation(m, r)}
    case R.AfterAuthenticate{r, ctx}: L.Left{authenticated_without_preparation(m, r, ctx)}
    case R.AfterVerify{r, ctx}: L.Left{verified_without_preparation(m, r, ctx)}
    case R.Executing{r, ctx, xs}: L.Left{execution_without_preparation(m, r, ctx, xs)}
    case R.AfterPrepare{r, ctx, xs, p}: L.Right{(r, ctx, xs, p, L.Both{{==}, real})}

def group_preparation_native(+m: R.Micro, +r: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>, +mark: Q.Frame, +later: List<&2, Q.Frame>) ->
  {Con{Q.Configured{}, Q.concatenate(R.render_execution(m, r, ctx, xs), Q.concatenate(R.micro_output(m), Con{mark, later}))} ==
    Q.concatenate(Con{Q.Configured{}, before_execution(m, r, ctx, xs)}, Con{mark, later}) : List<&2, Q.Frame>}:
  Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, qs => Con{Q.Configured{}, qs},
    Q.concatenate(R.render_execution(m, r, ctx, xs), Q.concatenate(R.micro_output(m), Con{mark, later})),
    Q.concatenate(before_execution(m, r, ctx, xs), Con{mark, later}),
    Equal.sym(List<&2, Q.Frame>, Q.concatenate(before_execution(m, r, ctx, xs), Con{mark, later}),
      Q.concatenate(R.render_execution(m, r, ctx, xs), Q.concatenate(R.micro_output(m), Con{mark, later})),
      Q.concatenate_assoc(R.render_execution(m, r, ctx, xs), R.micro_output(m), Con{mark, later})))

def reflect_inversion_preparation(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, -s: D.State, +code: Source.JudgmentSyntactic,
  +branch: R.Branch, +qs: List<&2, Q.Frame>, +normal: List<&2, Q.Frame>, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  +equal: {qs == normal : List<&2, Q.Frame>}, query_result: {Q.query(qs, t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>},
  resolve: {Q.query(normal, t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>} -> PreparationInTrace(source, c, m, s, code, branch, normal, t, r, bs)) ->
  PreparationInTrace(source, c, m, s, code, branch, qs, t, r, bs):
  %Equal.sym(List<&2, Q.Frame>, qs, normal, equal) : PreparationInTrace(source, c, m, s, code, branch, _, t, r, bs)
  resolve(%equal : {Q.query(_, t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>} query_result)
def invert_preparation_native(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, +s: D.State, +code: Source.JudgmentSyntactic,
  +branch: R.Branch, +qs: List<&2, Q.Frame>, +req: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>, +p: N.Prepared,
  +later: List<&2, Q.Frame>, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  real: Source.FinalReal(source, c, s, req, ctx, code, xs, p),
  equal: {qs == Q.concatenate(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, Con{R.frame_prepared(p), later}) : List<&2, Q.Frame>},
  without_later: WithoutPreparation(later), query_result: {Q.query(qs, t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}) ->
  PreparationInTrace(source, c, m, s, code, branch, qs, t, r, bs):
  reflect_inversion_preparation(source, c, m, s, code, branch, qs,
    Q.concatenate(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, Con{R.frame_prepared(p), later}), t, r, bs, equal, query_result,
    normal => invert_mark_of_preparation(source, c, m, s, code, branch, Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, later,
      Native{req, ctx, xs, p}, t, r, bs, before_execution_without_preparation(m, req, ctx, xs), without_later, L.Both{{==}, real}, normal))

def tail_of_error(+s: D.State, +e: Errors.Error, +closes: Bool, delivery: R.Delivery) -> List<&2, Q.Frame>:
  Con{Q.Completed{S.response_error(Errors.status(e)), s, closes}, R.render_delivery(s, Errors.bytes(e), closes, delivery)}

def tail_of_error_without_preparation(+s: D.State, +e: Errors.Error, +closes: Bool, delivery: R.Delivery) -> WithoutPreparation(tail_of_error(s, e, closes, delivery)):
  prefix_without_preparation(Q.Completed{S.response_error(Errors.status(e)), s, closes}, R.render_delivery(s, Errors.bytes(e), closes, delivery), {==}, delivery_without_preparation(s, Errors.bytes(e), closes, delivery))

def normalize_error_preparation(+before: List<&2, Q.Frame>, +s: D.State, +e: Errors.Error, +closes: Bool, +delivery: R.Delivery) ->
  {Q.concatenate(before, R.render_error(Errors.status(e), s, closes, delivery)) == Q.concatenate(before, Con{milestone_preparation(Fixed{e}), tail_of_error(s, e, closes, delivery)}) : List<&2, Q.Frame>}:
  Equal.cong(Maybe<&2, List<&2, U32>>, List<&2, Q.Frame>, q => Q.concatenate(before, R.render_error_framed(q, S.response_error(Errors.status(e)), s, closes, delivery)),
    P.frame(S.response_value(S.response_error(Errors.status(e)))), Some{Errors.bytes(e)}, Errors.all_os_errors_prepared_are_exactly_messages_original(e))

def invert_preparation_fixed(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, +s: D.State, +code: Source.JudgmentSyntactic,
  +branch: R.Branch, +qs: List<&2, Q.Frame>, +before: List<&2, Q.Frame>, +e: Errors.Error, +closes: Bool, +delivery: R.Delivery, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  cause: FixedOfBranch(e, branch), prefix: PrefixFixed(m, branch, before), without_before: WithoutPreparation(before),
  equal: {qs == Q.concatenate(before, R.render_error(Errors.status(e), s, closes, delivery)) : List<&2, Q.Frame>},
  query_result: {Q.query(qs, t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}) -> PreparationInTrace(source, c, m, s, code, branch, qs, t, r, bs):
  reflect_inversion_preparation(source, c, m, s, code, branch, qs, Q.concatenate(before, Con{milestone_preparation(Fixed{e}), tail_of_error(s, e, closes, delivery)}), t, r, bs,
    Equal.trans(List<&2, Q.Frame>, qs, Q.concatenate(before, R.render_error(Errors.status(e), s, closes, delivery)),
      Q.concatenate(before, Con{milestone_preparation(Fixed{e}), tail_of_error(s, e, closes, delivery)}), equal, normalize_error_preparation(before, s, e, closes, delivery)), query_result,
    normal => invert_mark_of_preparation(source, c, m, s, code, branch, before, tail_of_error(s, e, closes, delivery), Fixed{e}, t, r, bs,
      without_before, tail_of_error_without_preparation(s, e, closes, delivery), L.Both{cause, prefix}, normal))

def group_phase_prepared(+m: R.Micro, +req: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>, +p: N.Prepared, +later: List<&2, Q.Frame>) ->
  {Con{Q.Configured{}, Q.concatenate(R.render_phase(m, R.AfterPrepare{req, ctx, xs, p}), later)} ==
    Q.concatenate(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, Con{R.frame_prepared(p), later}) : List<&2, Q.Frame>}:
  Equal.trans(List<&2, Q.Frame>, Con{Q.Configured{}, Q.concatenate(R.render_phase(m, R.AfterPrepare{req, ctx, xs, p}), later)},
    Con{Q.Configured{}, Q.concatenate(R.render_execution(m, req, ctx, xs), Q.concatenate(R.micro_output(m), Con{R.frame_prepared(p), later}))},
    Q.concatenate(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, Con{R.frame_prepared(p), later}),
    Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, qs => Con{Q.Configured{}, qs},
      Q.concatenate(R.render_phase(m, R.AfterPrepare{req, ctx, xs, p}), later),
      Q.concatenate(R.render_execution(m, req, ctx, xs), Q.concatenate(R.micro_output(m), Con{R.frame_prepared(p), later})),
      group_three(R.render_execution(m, req, ctx, xs), R.micro_output(m), [R.frame_prepared(p)], later)),
    group_preparation_native(m, req, ctx, xs, R.frame_prepared(p), later))

def invert_phase_by_origin(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, +s: D.State, +code: Source.JudgmentSyntactic,
  +branch: R.Branch, +phase: R.PhaseBefore, +later: List<&2, Q.Frame>, +t: Nat, +r: S.Response, +bs: List<&2, U32>, without_later: WithoutPreparation(later),
  origin: L.Disjunction<WithoutPreparation(R.render_phase(m, phase)),
    &req: P.Request -> &ctx: D.Context -> &xs: List<&2, Q.FrameExec> -> &p: N.Prepared -> L.E<{phase == R.AfterPrepare{req, ctx, xs, p} : R.PhaseBefore}, Source.FinalReal(source, c, s, req, ctx, code, xs, p)>>,
  query_result: {Q.query(Con{Q.Configured{}, Q.concatenate(R.render_phase(m, phase), later)}, t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}) ->
  PreparationInTrace(source, c, m, s, code, branch, Con{Q.Configured{}, Q.concatenate(R.render_phase(m, phase), later)}, t, r, bs):
  match origin:
    case L.Left{without_phase}:
      L.ex_false(PreparationInTrace(source, c, m, s, code, branch, Con{Q.Configured{}, Q.concatenate(R.render_phase(m, phase), later)}, t, r, bs),
        prefix_without_preparation(Q.Configured{}, Q.concatenate(R.render_phase(m, phase), later), {==}, concatenate_without_preparation(R.render_phase(m, phase), later, without_phase, without_later))(r, bs, t, query_result))
    case L.Right{(+req, +ctx, +xs, +p, L.Both{equal, real})}:
      invert_preparation_native(source, c, m, s, code, branch, Con{Q.Configured{}, Q.concatenate(R.render_phase(m, phase), later)}, req, ctx, xs, p, later, t, r, bs, real,
        Equal.trans(List<&2, Q.Frame>, Con{Q.Configured{}, Q.concatenate(R.render_phase(m, phase), later)},
          Con{Q.Configured{}, Q.concatenate(R.render_phase(m, R.AfterPrepare{req, ctx, xs, p}), later)},
          Q.concatenate(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, Con{R.frame_prepared(p), later}),
          Equal.cong(R.PhaseBefore, List<&2, Q.Frame>, f => Con{Q.Configured{}, Q.concatenate(R.render_phase(m, f), later)}, phase, R.AfterPrepare{req, ctx, xs, p}, equal),
          group_phase_prepared(m, req, ctx, xs, p, later)), without_later, query_result)

def invert_preparation_of_phase(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, +s: D.State, +code: Source.JudgmentSyntactic,
  +branch: R.Branch, +phase: R.PhaseBefore, +later: List<&2, Q.Frame>, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  real: Five.PhaseReal(source, c, s, code, phase), without_later: WithoutPreparation(later),
  query_result: {Q.query(Con{Q.Configured{}, Q.concatenate(R.render_phase(m, phase), later)}, t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}) ->
  PreparationInTrace(source, c, m, s, code, branch, Con{Q.Configured{}, Q.concatenate(R.render_phase(m, phase), later)}, t, r, bs):
  invert_phase_by_origin(source, c, m, s, code, branch, phase, later, t, r, bs, without_later, phase_without_preparation_or_native(source, c, m, s, code, phase, real), query_result)

def before_auth_without_preparation(+m: R.Micro, +req: P.Request) -> WithoutPreparation(Con{Q.Configured{}, before_authentication(m, req)}):
  prefix_without_preparation(Q.Configured{}, before_authentication(m, req), {==},
    concatenate_without_preparation(R.render_received(m, req), Q.concatenate(R.micro_authentication(m), [Q.Authenticated{req, None{}}]), received_without_preparation(m, req),
      concatenate_without_preparation(R.micro_authentication(m), [Q.Authenticated{req, None{}}], authentication_without_preparation(m), prefix_without_preparation(Q.Authenticated{req, None{}}, Nil{}, {==}, without_preparation_empty()))))

def before_gate_without_preparation(+m: R.Micro, +req: P.Request, +ctx: D.Context) -> WithoutPreparation(Con{Q.Configured{}, before_gate(m, req, ctx)}):
  prefix_without_preparation(Q.Configured{}, before_gate(m, req, ctx), {==},
    concatenate_without_preparation(R.render_authenticated(m, req, ctx), [Q.Rejected{req, ctx}], authenticated_without_preparation(m, req, ctx), prefix_without_preparation(Q.Rejected{req, ctx}, Nil{}, {==}, without_preparation_empty())))

def invert_preparation_executed(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, +s: D.State, +code: Source.JudgmentSyntactic,
  +req: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>, p: N.Prepared, +delivery: R.Delivery, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  real: Source.FinalReal(source, c, s, req, ctx, code, xs, p),
  query_result: {Q.query(R.render(m, s, R.Executed{req, ctx, xs, p, delivery}), t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}) ->
  PreparationInTrace(source, c, m, s, code, R.Executed{req, ctx, xs, p, delivery}, R.render(m, s, R.Executed{req, ctx, xs, p, delivery}), t, r, bs):
  match p:
    case N.Prepared{+w, +ts, +resp, +bytes}:
      invert_preparation_native(source, c, m, s, code, R.Executed{req, ctx, xs, N.Prepared{w, ts, resp, bytes}, delivery},
        R.render(m, s, R.Executed{req, ctx, xs, N.Prepared{w, ts, resp, bytes}, delivery}), req, ctx, xs, N.Prepared{w, ts, resp, bytes},
        tail_of_conclusion(N.conclude(N.Prepared{w, ts, resp, bytes}, s), False{}, delivery), t, r, bs, real,
        group_preparation_native(m, req, ctx, xs, Q.Prepared{resp, bytes}, tail_of_conclusion(N.conclude(N.Prepared{w, ts, resp, bytes}, s), False{}, delivery)),
        tail_of_conclusion_without_preparation(N.conclude(N.Prepared{w, ts, resp, bytes}, s), False{}, delivery), query_result)

def tail_fatal(conclusion: N.Conclusion, +stage: X.Stage, +id: String) -> List<&2, Q.Frame>:
  match conclusion:
    case N.Conclusion{+s, r, bs}: Q.concatenate(R.render_publication(r, s), [Q.Failed{stage, id, True{}}, Q.Closed{}])

def tail_fatal_without_preparation(conclusion: N.Conclusion, +stage: X.Stage, +id: String) -> WithoutPreparation(tail_fatal(conclusion, stage, id)):
  match conclusion:
    case N.Conclusion{+s, +r, bs}:
      concatenate_without_preparation(R.render_publication(r, s), [Q.Failed{stage, id, True{}}, Q.Closed{}], publication_without_preparation(r, s),
        prefix_without_preparation(Q.Failed{stage, id, True{}}, [Q.Closed{}], {==}, prefix_without_preparation(Q.Closed{}, Nil{}, {==}, without_preparation_empty())))

def invert_preparation_fatal_published(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, +s: D.State, +code: Source.JudgmentSyntactic,
  +req: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>, p: N.Prepared, +stage: X.Stage, +id: String, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  real: Source.FinalReal(source, c, s, req, ctx, code, xs, p),
  query_result: {Q.query(R.render(m, s, R.FatalAfterPublication{req, ctx, xs, p, stage, id}), t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}) ->
  PreparationInTrace(source, c, m, s, code, R.FatalAfterPublication{req, ctx, xs, p, stage, id}, R.render(m, s, R.FatalAfterPublication{req, ctx, xs, p, stage, id}), t, r, bs):
  match p:
    case N.Prepared{+w, +ts, +resp, +bytes}:
      invert_preparation_native(source, c, m, s, code, R.FatalAfterPublication{req, ctx, xs, N.Prepared{w, ts, resp, bytes}, stage, id},
        R.render(m, s, R.FatalAfterPublication{req, ctx, xs, N.Prepared{w, ts, resp, bytes}, stage, id}), req, ctx, xs, N.Prepared{w, ts, resp, bytes},
        tail_fatal(N.conclude(N.Prepared{w, ts, resp, bytes}, s), stage, id), t, r, bs, real,
        group_preparation_native(m, req, ctx, xs, Q.Prepared{resp, bytes}, tail_fatal(N.conclude(N.Prepared{w, ts, resp, bytes}, s), stage, id)),
        tail_fatal_without_preparation(N.conclude(N.Prepared{w, ts, resp, bytes}, s), stage, id), query_result)

def status_error_of_input(e: R.ErrorInput) -> {R.status_input(e) == Errors.status(error_of_input(e)) : S.Status}:
  match e:
    case R.Input{}: {==}
    case R.Limit{}: {==}

def invert_preparation_input(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, +s: D.State, +code: Source.JudgmentSyntactic,
  +e: R.ErrorInput, +closes: Bool, +delivery: R.Delivery, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  query_result: {Q.query(R.render(m, s, R.InputRefusal{e, closes, delivery}), t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}) ->
  PreparationInTrace(source, c, m, s, code, R.InputRefusal{e, closes, delivery}, R.render(m, s, R.InputRefusal{e, closes, delivery}), t, r, bs):
  invert_preparation_fixed(source, c, m, s, code, R.InputRefusal{e, closes, delivery}, R.render(m, s, R.InputRefusal{e, closes, delivery}),
    Con{Q.Configured{}, R.micro_input(m)}, error_of_input(e), closes, delivery, t, r, bs, {==}, {==}, prefix_without_preparation(Q.Configured{}, R.micro_input(m), {==}, input_without_preparation(m)),
    Equal.cong(S.Status, List<&2, Q.Frame>, status => Con{Q.Configured{}, Q.concatenate(R.micro_input(m), R.render_error(status, s, closes, delivery))}, R.status_input(e), Errors.status(error_of_input(e)), status_error_of_input(e)), query_result)

def invert_preparation_aut(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, +s: D.State, +code: Source.JudgmentSyntactic,
  +req: P.Request, +delivery: R.Delivery, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  query_result: {Q.query(R.render(m, s, R.AutRefusal{req, delivery}), t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}) ->
  PreparationInTrace(source, c, m, s, code, R.AutRefusal{req, delivery}, R.render(m, s, R.AutRefusal{req, delivery}), t, r, bs):
  invert_preparation_fixed(source, c, m, s, code, R.AutRefusal{req, delivery}, R.render(m, s, R.AutRefusal{req, delivery}), Con{Q.Configured{}, before_authentication(m, req)},
    Errors.Authentication{}, False{}, delivery, t, r, bs, {==}, {==}, before_auth_without_preparation(m, req),
    Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, qs => Con{Q.Configured{}, qs},
      R.render_branch(m, s, R.AutRefusal{req, delivery}), Q.concatenate(before_authentication(m, req), R.render_error(S.Authentication{}, s, False{}, delivery)),
      Equal.sym(List<&2, Q.Frame>, Q.concatenate(before_authentication(m, req), R.render_error(S.Authentication{}, s, False{}, delivery)), R.render_branch(m, s, R.AutRefusal{req, delivery}),
        group_three(R.render_received(m, req), R.micro_authentication(m), [Q.Authenticated{req, None{}}], R.render_error(S.Authentication{}, s, False{}, delivery)))), query_result)

def invert_preparation_gate(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, +s: D.State, +code: Source.JudgmentSyntactic,
  +req: P.Request, +ctx: D.Context, +delivery: R.Delivery, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  query_result: {Q.query(R.render(m, s, R.GateRefusal{req, ctx, delivery}), t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}) ->
  PreparationInTrace(source, c, m, s, code, R.GateRefusal{req, ctx, delivery}, R.render(m, s, R.GateRefusal{req, ctx, delivery}), t, r, bs):
  invert_preparation_fixed(source, c, m, s, code, R.GateRefusal{req, ctx, delivery}, R.render(m, s, R.GateRefusal{req, ctx, delivery}), Con{Q.Configured{}, before_gate(m, req, ctx)},
    Errors.Certificate{}, False{}, delivery, t, r, bs, {==}, {==}, before_gate_without_preparation(m, req, ctx),
    Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, qs => Con{Q.Configured{}, qs},
      R.render_branch(m, s, R.GateRefusal{req, ctx, delivery}), Q.concatenate(before_gate(m, req, ctx), R.render_error(S.Certificate{}, s, False{}, delivery)),
      Equal.sym(List<&2, Q.Frame>, Q.concatenate(before_gate(m, req, ctx), R.render_error(S.Certificate{}, s, False{}, delivery)), R.render_branch(m, s, R.GateRefusal{req, ctx, delivery}),
        Q.concatenate_assoc(R.render_authenticated(m, req, ctx), [Q.Rejected{req, ctx}], R.render_error(S.Certificate{}, s, False{}, delivery)))), query_result)

def prefix_fixed_of_failure_pair(+m: R.Micro, +phase: R.PhaseBefore, +req: P.Request, +ctx: D.Context,
  +xs: List<&2, Q.FrameExec>, +p: N.Prepared, +stage: X.Stage, +id: String, +delivery: R.Delivery,
  phase_equal: {phase == R.AfterPrepare{req, ctx, xs, p} : R.PhaseBefore}) ->
  PrefixFixed(m, R.FailureBefore{phase, stage, id, False{}, delivery},
    Q.concatenate(Q.concatenate(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, [R.frame_prepared(p)]), [Q.Failed{stage, id, False{}}])):
  Equal.trans(List<&2, Q.Frame>,
    Q.concatenate(Q.concatenate(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, [R.frame_prepared(p)]), [Q.Failed{stage, id, False{}}]),
    Q.concatenate(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, [R.frame_prepared(p), Q.Failed{stage, id, False{}}]),
    Con{Q.Configured{}, before_failure(m, phase, stage, id, False{})},
    Q.concatenate_assoc(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, [R.frame_prepared(p)], [Q.Failed{stage, id, False{}}]),
    Equal.sym(List<&2, Q.Frame>, Con{Q.Configured{}, before_failure(m, phase, stage, id, False{})},
      Q.concatenate(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, [R.frame_prepared(p), Q.Failed{stage, id, False{}}]),
      Equal.trans(List<&2, Q.Frame>, Con{Q.Configured{}, before_failure(m, phase, stage, id, False{})},
        Con{Q.Configured{}, before_failure(m, R.AfterPrepare{req, ctx, xs, p}, stage, id, False{})},
        Q.concatenate(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, [R.frame_prepared(p), Q.Failed{stage, id, False{}}]),
        Equal.cong(R.PhaseBefore, List<&2, Q.Frame>, f => Con{Q.Configured{}, before_failure(m, f, stage, id, False{})}, phase, R.AfterPrepare{req, ctx, xs, p}, phase_equal),
        group_phase_prepared(m, req, ctx, xs, p, [Q.Failed{stage, id, False{}}]))))

def normalize_failure_pair(+m: R.Micro, +s: D.State, +req: P.Request, +ctx: D.Context,
  +xs: List<&2, Q.FrameExec>, +p: N.Prepared, +stage: X.Stage, +id: String, +delivery: R.Delivery) ->
  {R.render(m, s, R.FailureBefore{R.AfterPrepare{req, ctx, xs, p}, stage, id, False{}, delivery}) ==
    Q.concatenate(Q.concatenate(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, [R.frame_prepared(p)]),
      Con{Q.Failed{stage, id, False{}}, Con{milestone_preparation(Fixed{Errors.Failure{}}), tail_of_error(s, Errors.Failure{}, False{}, delivery)}}) : List<&2, Q.Frame>}:
  Equal.trans(List<&2, Q.Frame>, R.render(m, s, R.FailureBefore{R.AfterPrepare{req, ctx, xs, p}, stage, id, False{}, delivery}),
    Con{Q.Configured{}, Q.concatenate(R.render_phase(m, R.AfterPrepare{req, ctx, xs, p}),
      Con{Q.Failed{stage, id, False{}}, Con{milestone_preparation(Fixed{Errors.Failure{}}), tail_of_error(s, Errors.Failure{}, False{}, delivery)}})},
    Q.concatenate(Q.concatenate(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, [R.frame_prepared(p)]),
      Con{Q.Failed{stage, id, False{}}, Con{milestone_preparation(Fixed{Errors.Failure{}}), tail_of_error(s, Errors.Failure{}, False{}, delivery)}}),
    Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, tail => Con{Q.Configured{}, Q.concatenate(R.render_phase(m, R.AfterPrepare{req, ctx, xs, p}), Con{Q.Failed{stage, id, False{}}, tail})},
      R.render_error(S.Failure{}, s, False{}, delivery), Con{milestone_preparation(Fixed{Errors.Failure{}}), tail_of_error(s, Errors.Failure{}, False{}, delivery)}, normalize_error_preparation(Nil{}, s, Errors.Failure{}, False{}, delivery)),
    Equal.trans(List<&2, Q.Frame>, Con{Q.Configured{}, Q.concatenate(R.render_phase(m, R.AfterPrepare{req, ctx, xs, p}), Con{Q.Failed{stage, id, False{}}, Con{milestone_preparation(Fixed{Errors.Failure{}}), tail_of_error(s, Errors.Failure{}, False{}, delivery)}})},
      Q.concatenate(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, Con{R.frame_prepared(p), Con{Q.Failed{stage, id, False{}}, Con{milestone_preparation(Fixed{Errors.Failure{}}), tail_of_error(s, Errors.Failure{}, False{}, delivery)}}}),
      Q.concatenate(Q.concatenate(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, [R.frame_prepared(p)]), Con{Q.Failed{stage, id, False{}}, Con{milestone_preparation(Fixed{Errors.Failure{}}), tail_of_error(s, Errors.Failure{}, False{}, delivery)}}),
      group_phase_prepared(m, req, ctx, xs, p, Con{Q.Failed{stage, id, False{}}, Con{milestone_preparation(Fixed{Errors.Failure{}}), tail_of_error(s, Errors.Failure{}, False{}, delivery)}}),
      Equal.sym(List<&2, Q.Frame>, Q.concatenate(Q.concatenate(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, [R.frame_prepared(p)]), Con{Q.Failed{stage, id, False{}}, Con{milestone_preparation(Fixed{Errors.Failure{}}), tail_of_error(s, Errors.Failure{}, False{}, delivery)}}),
        Q.concatenate(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, Con{R.frame_prepared(p), Con{Q.Failed{stage, id, False{}}, Con{milestone_preparation(Fixed{Errors.Failure{}}), tail_of_error(s, Errors.Failure{}, False{}, delivery)}}}),
        Q.concatenate_assoc(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, [R.frame_prepared(p)], Con{Q.Failed{stage, id, False{}}, Con{milestone_preparation(Fixed{Errors.Failure{}}), tail_of_error(s, Errors.Failure{}, False{}, delivery)}}))))

def invert_failure_pair(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, +s: D.State, +code: Source.JudgmentSyntactic,
  +phase: R.PhaseBefore, +req: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>, +p: N.Prepared,
  +stage: X.Stage, +id: String, +delivery: R.Delivery, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  +phase_equal: {phase == R.AfterPrepare{req, ctx, xs, p} : R.PhaseBefore}, real: Source.FinalReal(source, c, s, req, ctx, code, xs, p),
  query_result: {Q.query(R.render(m, s, R.FailureBefore{phase, stage, id, False{}, delivery}), t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}) ->
  PreparationInTrace(source, c, m, s, code, R.FailureBefore{phase, stage, id, False{}, delivery}, R.render(m, s, R.FailureBefore{phase, stage, id, False{}, delivery}), t, r, bs):
  reflect_inversion_preparation(source, c, m, s, code, R.FailureBefore{phase, stage, id, False{}, delivery}, R.render(m, s, R.FailureBefore{phase, stage, id, False{}, delivery}),
    Q.concatenate(Q.concatenate(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, [R.frame_prepared(p)]),
      Con{Q.Failed{stage, id, False{}}, Con{milestone_preparation(Fixed{Errors.Failure{}}), tail_of_error(s, Errors.Failure{}, False{}, delivery)}}), t, r, bs,
    Equal.trans(List<&2, Q.Frame>, R.render(m, s, R.FailureBefore{phase, stage, id, False{}, delivery}),
      R.render(m, s, R.FailureBefore{R.AfterPrepare{req, ctx, xs, p}, stage, id, False{}, delivery}),
      Q.concatenate(Q.concatenate(Con{Q.Configured{}, before_execution(m, req, ctx, xs)}, [R.frame_prepared(p)]), Con{Q.Failed{stage, id, False{}}, Con{milestone_preparation(Fixed{Errors.Failure{}}), tail_of_error(s, Errors.Failure{}, False{}, delivery)}}),
      Equal.cong(R.PhaseBefore, List<&2, Q.Frame>, f => R.render(m, s, R.FailureBefore{f, stage, id, False{}, delivery}), phase, R.AfterPrepare{req, ctx, xs, p}, phase_equal),
      normalize_failure_pair(m, s, req, ctx, xs, p, stage, id, delivery)), query_result,
    normal => invert_two_marks(source, c, m, s, code, R.FailureBefore{phase, stage, id, False{}, delivery}, Con{Q.Configured{}, before_execution(m, req, ctx, xs)},
      [Q.Failed{stage, id, False{}}], tail_of_error(s, Errors.Failure{}, False{}, delivery), Native{req, ctx, xs, p}, Fixed{Errors.Failure{}}, t, r, bs,
      before_execution_without_preparation(m, req, ctx, xs), prefix_without_preparation(Q.Failed{stage, id, False{}}, Nil{}, {==}, without_preparation_empty()), tail_of_error_without_preparation(s, Errors.Failure{}, False{}, delivery),
      L.Both{{==}, real}, L.Both{L.Both{{==}, {==}}, prefix_fixed_of_failure_pair(m, phase, req, ctx, xs, p, stage, id, delivery, phase_equal)}, normal))

def invert_failure_by_origin(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, +s: D.State, +code: Source.JudgmentSyntactic,
  +phase: R.PhaseBefore, +stage: X.Stage, +id: String, +delivery: R.Delivery, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  origin: L.Disjunction<WithoutPreparation(R.render_phase(m, phase)), &req: P.Request -> &ctx: D.Context -> &xs: List<&2, Q.FrameExec> -> &p: N.Prepared ->
    L.E<{phase == R.AfterPrepare{req, ctx, xs, p} : R.PhaseBefore}, Source.FinalReal(source, c, s, req, ctx, code, xs, p)>>,
  query_result: {Q.query(R.render(m, s, R.FailureBefore{phase, stage, id, False{}, delivery}), t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}) ->
  PreparationInTrace(source, c, m, s, code, R.FailureBefore{phase, stage, id, False{}, delivery}, R.render(m, s, R.FailureBefore{phase, stage, id, False{}, delivery}), t, r, bs):
  match origin:
    case L.Left{without_phase}:
      invert_preparation_fixed(source, c, m, s, code, R.FailureBefore{phase, stage, id, False{}, delivery}, R.render(m, s, R.FailureBefore{phase, stage, id, False{}, delivery}),
        Con{Q.Configured{}, before_failure(m, phase, stage, id, False{})}, Errors.Failure{}, False{}, delivery, t, r, bs, L.Both{{==}, {==}}, {==},
        prefix_without_preparation(Q.Configured{}, before_failure(m, phase, stage, id, False{}), {==},
          concatenate_without_preparation(R.render_phase(m, phase), [Q.Failed{stage, id, False{}}], without_phase, prefix_without_preparation(Q.Failed{stage, id, False{}}, Nil{}, {==}, without_preparation_empty()))),
        Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, qs => Con{Q.Configured{}, qs},
          R.render_branch(m, s, R.FailureBefore{phase, stage, id, False{}, delivery}), Q.concatenate(before_failure(m, phase, stage, id, False{}), R.render_error(S.Failure{}, s, False{}, delivery)),
          Equal.sym(List<&2, Q.Frame>, Q.concatenate(before_failure(m, phase, stage, id, False{}), R.render_error(S.Failure{}, s, False{}, delivery)),
            R.render_branch(m, s, R.FailureBefore{phase, stage, id, False{}, delivery}), Q.concatenate_assoc(R.render_phase(m, phase), [Q.Failed{stage, id, False{}}], R.render_error(S.Failure{}, s, False{}, delivery)))), query_result)
    case L.Right{(+req, +ctx, +xs, +p, L.Both{phase_equal, real})}:
      invert_failure_pair(source, c, m, s, code, phase, req, ctx, xs, p, stage, id, delivery, t, r, bs, phase_equal, real, query_result)

def invert_preparation_failure(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, +s: D.State, +code: Source.JudgmentSyntactic,
  +phase: R.PhaseBefore, +stage: X.Stage, +id: String, fatal: Bool, +delivery: R.Delivery, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  real: Five.PhaseReal(source, c, s, code, phase),
  query_result: {Q.query(R.render(m, s, R.FailureBefore{phase, stage, id, fatal, delivery}), t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}) ->
  PreparationInTrace(source, c, m, s, code, R.FailureBefore{phase, stage, id, fatal, delivery}, R.render(m, s, R.FailureBefore{phase, stage, id, fatal, delivery}), t, r, bs):
  match fatal:
    case True{}:
      invert_preparation_of_phase(source, c, m, s, code, R.FailureBefore{phase, stage, id, True{}, delivery}, phase, [Q.Failed{stage, id, True{}}, Q.Closed{}], t, r, bs, real,
        prefix_without_preparation(Q.Failed{stage, id, True{}}, [Q.Closed{}], {==}, prefix_without_preparation(Q.Closed{}, Nil{}, {==}, without_preparation_empty())), query_result)
    case False{}:
      invert_failure_by_origin(source, c, m, s, code, phase, stage, id, delivery, t, r, bs, phase_without_preparation_or_native(source, c, m, s, code, phase, real), query_result)

def invert_preparation_pending(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, +s: D.State, +code: Source.JudgmentSyntactic,
  +phase: R.PhaseBefore, +t: Nat, +r: S.Response, +bs: List<&2, U32>, real: Five.PhaseReal(source, c, s, code, phase),
  query_result: {Q.query(R.render(m, s, R.Pending{phase}), t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}) ->
  PreparationInTrace(source, c, m, s, code, R.Pending{phase}, R.render(m, s, R.Pending{phase}), t, r, bs):
  reflect_inversion_preparation(source, c, m, s, code, R.Pending{phase}, R.render(m, s, R.Pending{phase}), Con{Q.Configured{}, Q.concatenate(R.render_phase(m, phase), Nil{})}, t, r, bs,
    Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, qs => Con{Q.Configured{}, qs}, R.render_phase(m, phase), Q.concatenate(R.render_phase(m, phase), Nil{}),
      Equal.sym(List<&2, Q.Frame>, Q.concatenate(R.render_phase(m, phase), Nil{}), R.render_phase(m, phase), Five.concatenate_empty_right(R.render_phase(m, phase)))), query_result,
    normal => invert_preparation_of_phase(source, c, m, s, code, R.Pending{phase}, phase, Nil{}, t, r, bs, real, without_preparation_empty(), normal))

def exclude_preparation_without_mark(~source: Source.Source, ~c: S.Configuration, +m: R.Micro, -s: D.State, +code: Source.JudgmentSyntactic,
  +branch: R.Branch, +qs: List<&2, Q.Frame>, +t: Nat, +r: S.Response, +bs: List<&2, U32>, without: WithoutPreparation(qs),
  query_result: {Q.query(qs, t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}) -> PreparationInTrace(source, c, m, s, code, branch, qs, t, r, bs):
  L.ex_false(PreparationInTrace(source, c, m, s, code, branch, qs, t, r, bs), without(r, bs, t, query_result))

# Initializations reuse the same exclusions as the invert below.
def initial_ok_without_preparation(+m: R.Micro, +s: D.State) -> WithoutPreparation(R.render(m, s, R.InitialOk{})):
  prefix_without_preparation(Q.Configured{}, R.render_branch(m, s, R.InitialOk{}), {==},
    prefix_without_preparation(Q.InitialAccepts{}, Q.concatenate(R.micro_output(m), R.render_initial(P.encode(D.state_value(s)), s)), {==},
      concatenate_without_preparation(R.micro_output(m), R.render_initial(P.encode(D.state_value(s)), s), output_without_preparation(m), initial_without_preparation(P.encode(D.state_value(s)), s))))

def initial_refusal_without_preparation(+m: R.Micro, +s: D.State, +status: S.Status) -> WithoutPreparation(R.render(m, s, R.InitialRefusal{status})):
  prefix_without_preparation(Q.Configured{}, [Q.InitialRefused{status}], {==}, prefix_without_preparation(Q.InitialRefused{status}, Nil{}, {==}, without_preparation_empty()))

def initial_failure_without_preparation(+m: R.Micro, +s: D.State, +accepts: Bool, +stage: X.Stage, +id: String, +fatal: Bool) ->
  WithoutPreparation(R.render(m, s, R.InitialFailure{accepts, stage, id, fatal})):
  prefix_without_preparation(Q.Configured{}, R.render_branch(m, s, R.InitialFailure{accepts, stage, id, fatal}), {==},
    concatenate_without_preparation(R.prefix_initial(m, accepts), [Q.Failed{stage, id, fatal}, Q.InitialRefused{S.Failure{}}], prefix_initial_without_preparation(m, accepts),
      prefix_without_preparation(Q.Failed{stage, id, fatal}, [Q.InitialRefused{S.Failure{}}], {==}, prefix_without_preparation(Q.InitialRefused{S.Failure{}}, Nil{}, {==}, without_preparation_empty()))))

def initial_pending_without_preparation(+m: R.Micro, +s: D.State, +accepts: Bool) -> WithoutPreparation(R.render(m, s, R.InitialPending{accepts})):
  prefix_without_preparation(Q.Configured{}, R.prefix_initial(m, accepts), {==}, prefix_initial_without_preparation(m, accepts))

# Every occurrence originates in the actual case, including native preparation
# before cleanup failure. Preparation is not assumed unique.
law invert_preparation:
  for ~source: Source.Source
  for ~c: S.Configuration
  for +m: R.Micro
  for +s: D.State
  for +code: Source.JudgmentSyntactic
  for +branch: R.Branch
  for +t: Nat
  for +r: S.Response
  for +bs: List<&2, U32>
  for real: Five.BranchReal(source, c, s, code, branch)
  for query_result: {Q.query(R.render(m, s, branch), t) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}
  PreparationInTrace(source, c, m, s, code, branch, R.render(m, s, branch), t, r, bs)
def invert_preparation(source, c, m, s, code, branch, t, r, bs, real, query_result):
  match branch:
    case R.InitialOk{}:
      exclude_preparation_without_mark(source, c, m, s, code, R.InitialOk{}, R.render(m, s, R.InitialOk{}), t, r, bs,
        initial_ok_without_preparation(m, s), query_result)
    case R.InitialRefusal{+status}:
      exclude_preparation_without_mark(source, c, m, s, code, R.InitialRefusal{status}, R.render(m, s, R.InitialRefusal{status}), t, r, bs,
        initial_refusal_without_preparation(m, s, status), query_result)
    case R.InitialFailure{+accepts, +stage, +id, +fatal}:
      exclude_preparation_without_mark(source, c, m, s, code, R.InitialFailure{accepts, stage, id, fatal}, R.render(m, s, R.InitialFailure{accepts, stage, id, fatal}), t, r, bs,
        initial_failure_without_preparation(m, s, accepts, stage, id, fatal), query_result)
    case R.WithoutResponse{}:
      exclude_preparation_without_mark(source, c, m, s, code, R.WithoutResponse{}, R.render(m, s, R.WithoutResponse{}), t, r, bs,
        prefix_without_preparation(Q.Configured{}, [Q.Closed{}], {==}, prefix_without_preparation(Q.Closed{}, Nil{}, {==}, without_preparation_empty())), query_result)
    case R.InputRefusal{e, closes, delivery}: invert_preparation_input(source, c, m, s, code, e, closes, delivery, t, r, bs, query_result)
    case R.AutRefusal{req, delivery}: invert_preparation_aut(source, c, m, s, code, req, delivery, t, r, bs, query_result)
    case R.GateRefusal{req, ctx, delivery}: invert_preparation_gate(source, c, m, s, code, req, ctx, delivery, t, r, bs, query_result)
    case R.Executed{req, ctx, xs, p, delivery}: invert_preparation_executed(source, c, m, s, code, req, ctx, xs, p, delivery, t, r, bs, real, query_result)
    case R.FailureBefore{phase, stage, id, fatal, delivery}: invert_preparation_failure(source, c, m, s, code, phase, stage, id, fatal, delivery, t, r, bs, real, query_result)
    case R.FatalAfterPublication{req, ctx, xs, p, stage, id}: invert_preparation_fatal_published(source, c, m, s, code, req, ctx, xs, p, stage, id, t, r, bs, real, query_result)
    case R.Pending{phase}: invert_preparation_pending(source, c, m, s, code, phase, t, r, bs, real, query_result)
    case R.InitialPending{+accepts}:
      exclude_preparation_without_mark(source, c, m, s, code, R.InitialPending{accepts}, R.render(m, s, R.InitialPending{accepts}), t, r, bs,
        initial_pending_without_preparation(m, s, accepts), query_result)

def result_initial_without_preparation(+m: R.Micro, +s: D.State, result: R.ResultInitial, is_valid: Bool) ->
  WithoutPreparation(R.render(m, s, R.decide_accepted_initial(result, is_valid))):
  match result:
    case R.InitializationFinished{}:
      match is_valid:
        case False{}: initial_refusal_without_preparation(m, s, S.DataError{})
        case True{}: initial_ok_without_preparation(m, s)
    case R.FailedInitial{accepts, stage, id, fatal}: initial_failure_without_preparation(m, s, accepts && is_valid, stage, id, fatal)
    case R.PendingInitial{accepts}: initial_pending_without_preparation(m, s, accepts && is_valid)

def initialization_without_preparation(+m: R.Micro, +s: D.State, judgment: R.Judgment, +result: R.ResultInitial, +is_valid: Bool) ->
  WithoutPreparation(R.render(m, s, R.decide_judgment_initial(judgment, result, is_valid))):
  match judgment:
    case R.Accepted{}: result_initial_without_preparation(m, s, result, is_valid)
    case R.Refused{}: initial_refusal_without_preparation(m, s, S.Certificate{})
    case R.ErrorJudgment{id, fatal}: initial_failure_without_preparation(m, s, False{}, X.Verify{}, id, fatal)
    case R.PendingJudgment{}: initial_pending_without_preparation(m, s, False{})

# Shared with Law6: initialization emits no transactional conclusion.
def result_initial_without_closure(+m: R.Micro, +s: D.State, result: R.ResultInitial, is_valid: Bool) ->
  {closure_of_branch(m, s, R.decide_accepted_initial(result, is_valid)) == None{} : Maybe<&2, Closure>}:
  match result:
    case R.InitializationFinished{}:
      match is_valid:
        case False{}: {==}
        case True{}: {==}
    case R.FailedInitial{accepts, stage, id, fatal}: {==}
    case R.PendingInitial{accepts}: {==}

def judgment_initial_without_closure(+m: R.Micro, +s: D.State, j: R.Judgment, +result: R.ResultInitial, +is_valid: Bool) ->
  {closure_of_branch(m, s, R.decide_judgment_initial(j, result, is_valid)) == None{} : Maybe<&2, Closure>}:
  match j:
    case R.Accepted{}: result_initial_without_closure(m, s, result, is_valid)
    case R.Refused{}: {==}
    case R.ErrorJudgment{id, fatal}: {==}
    case R.PendingJudgment{}: {==}

def exclusions_of_start(+m: R.Micro, +s: D.State, +j: R.Judgment, +result: R.ResultInitial, +is_valid: Bool) ->
  L.E<{Phases.absent(Phases.Conclusion{}, R.render(m, s, R.decide_judgment_initial(j, result, is_valid))) == True{} : Bool},
    WithoutNext(R.render(m, s, R.decide_judgment_initial(j, result, is_valid)))>:
  L.Both{
    (%judgment_initial_without_closure(m, s, j, result, is_valid) :
      Form(R.render(m, s, R.decide_judgment_initial(j, result, is_valid)), R.decide_judgment_initial(j, result, is_valid), _)
      form_of_route(m, s, R.decide_judgment_initial(j, result, is_valid))),
    absence_of_closure_excludes_next(m, s, R.decide_judgment_initial(j, result, is_valid),
      judgment_initial_without_closure(m, s, j, result, is_valid))}

def initialization_without_conclusion_delivery(+m: R.Micro, +s: D.State, +j: R.Judgment, +result: R.ResultInitial, +is_valid: Bool) ->
  L.E<{Phases.absent(Phases.Conclusion{}, R.render(m, s, R.decide_judgment_initial(j, result, is_valid))) == True{} : Bool},
    L.E<{Phases.absent(Phases.Complete{}, R.render(m, s, R.decide_judgment_initial(j, result, is_valid))) == True{} : Bool},
      {Phases.absent(Phases.Interrupted{}, R.render(m, s, R.decide_judgment_initial(j, result, is_valid))) == True{} : Bool}>>:
  L.Both{
    L.and_left({Phases.absent(Phases.Conclusion{}, R.render(m, s, R.decide_judgment_initial(j, result, is_valid))) == True{} : Bool},
      WithoutNext(R.render(m, s, R.decide_judgment_initial(j, result, is_valid))), exclusions_of_start(m, s, j, result, is_valid)),
    (%judgment_initial_without_closure(m, s, j, result, is_valid) :
      DeliveriesOfForm(R.render(m, s, R.decide_judgment_initial(j, result, is_valid)), _)
      deliveries_of_form(m, s, R.decide_judgment_initial(j, result, is_valid)))}
