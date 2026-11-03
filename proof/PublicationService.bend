# Publication derives from actual execution and certificate; valid post-state
# is a conclusion, not an origin field supplied by the environment.
import Base
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/LAWS.bend as K
import ../contract/Logic.bend as L
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as Req
import ../contract/Resources.bend as X
import ../contract/Semantics.bend as S
import ../src/Core.bend as N
import ../src/ConfigurationCheck.bend as Config
import ./SourceService.bend as Source
import ./ProtocolService.bend as Q
import ./RoutesService.bend as R
import ./PhasesService.bend as Phases
import ./ConclusionService.bend as Conclusion
import ./HistoryService.bend as History
import ./Foundations.bend as F
import ./Law5Service.bend as Five
import ./Law34Service.bend as Adm
import ./Preparation.bend as Preparation
import ./LinkageService.bend as Linkage
import ./VisibilityService.bend as Vis
import ./ExecutionService.bend as Exec
import ./ScenariosService.bend as Scenarios

# The suffix may be normal delivery OR fatal failure after the store.
def trace(+before: List<&2, Q.Frame>, +w: D.State, +v: D.Value, +bs: List<&2, U32>, later: List<&2, Q.Frame>) -> List<&2, Q.Frame>:
  Q.concatenate(before, Con{Q.Prepared{S.Response{S.Success{}, v}, bs}, Con{Q.Published{w}, later}})

def in_pair(+w: D.State, +v: D.Value, +bs: List<&2, U32>, u: Nat, +published: D.State,
  query_result: {Q.query([Q.Prepared{S.Response{S.Success{}, v}, bs}, Q.Published{w}], u) == Some{Q.Published{published}} : Maybe<&2, Q.Frame>}) -> L.E<{u == 1n : Nat}, {published == w : D.State}>:
  match u:
    case 0n: L.ex_false(L.E<{0n == 1n : Nat}, {published == w : D.State}>, Phases.absent_excludes_query(Phases.Publication{}, [Q.Prepared{S.Response{S.Success{}, v}, bs}], 0n, Q.Published{published}, {==}, {==}, query_result))
    case 1n: L.Both{{==}, Phases.published_equal(w, published, query_result)}
    case 2n+k: L.ex_false(L.E<{2n+k == 1n : Nat}, {published == w : D.State}>, F.none_negative_some(Q.Frame, Q.Published{published}, query_result))

def in_part(+before: List<&2, Q.Frame>, +w: D.State, +v: D.Value, +bs: List<&2, U32>, +later: List<&2, Q.Frame>, -t: Nat, +published: D.State,
  without_later: {Phases.absent(Phases.Publication{}, later) == True{} : Bool},
  part: &u: Nat -> L.E<{t == Nat.add(Q.size(before), u) : Nat}, {Q.query(Con{Q.Prepared{S.Response{S.Success{}, v}, bs}, Con{Q.Published{w}, later}}, u) == Some{Q.Published{published}} : Maybe<&2, Q.Frame>}>) ->
  L.E<{t == Nat.add(Q.size(before), 1n) : Nat}, {published == w : D.State}>:
  match part:
    case (+u, L.Both{position, query_result}):
      F.combined_pair(L.E<{t == Nat.add(Q.size(before), 1n) : Nat}, {published == w : D.State}>, {u == 1n : Nat}, {published == w : D.State},
        in_pair(w, v, bs, u, published, Five.remove_suffix_without_frame([Q.Prepared{S.Response{S.Success{}, v}, bs}, Q.Published{w}], later, u, Q.Published{published},
          i => other => Phases.absent_excludes_query(Phases.Publication{}, later, i, Q.Published{published}, without_later, {==}, other), query_result)),
        local => state => L.Both{Equal.trans(Nat, t, Nat.add(Q.size(before), u), Nat.add(Q.size(before), 1n), position, Equal.cong(Nat, Nat, x => Nat.add(Q.size(before), x), u, 1n, local)), state})

law publication_in_frame_and_unique:
  for +before: List<&2, Q.Frame>
  for +w: D.State
  for +v: D.Value
  for +bs: List<&2, U32>
  for +later: List<&2, Q.Frame>
  for +t: Nat
  for +published: D.State
  for without_before: {Phases.absent(Phases.Publication{}, before) == True{} : Bool}
  for without_later: {Phases.absent(Phases.Publication{}, later) == True{} : Bool}
  for query_result: {Q.query(trace(before, w, v, bs, later), t) == Some{Q.Published{published}} : Maybe<&2, Q.Frame>}
  L.E<{t == Nat.add(Q.size(before), 1n) : Nat}, {published == w : D.State}>
def publication_in_frame_and_unique(before, w, v, bs, later, t, published, without_before, without_later, query_result):
  in_part(before, w, v, bs, later, t, published, without_later,
    Phases.locate_in_suffix(Phases.Publication{}, before, Con{Q.Prepared{S.Response{S.Success{}, v}, bs}, Con{Q.Published{w}, later}}, t, Q.Published{published}, without_before, {==}, query_result))

# All ports below query/introduce the same route, as proved by
# LinkageService. They receive neither published validity nor Rule6.
def frame_canonical(~source: Source.Source, ~c: S.Configuration, -a: I.Environment, -k: String, -x: I.Scenario,
  +before: List<&2, Q.Frame>, +s: D.State, +req: P.Request, +ctx: D.Context, +origin: Source.JudgmentSyntactic,
  +n: Nat, +w: D.State, +ts: List<&2, S.OperationEvent>, +proposal: S.Response, +v: D.Value, +bs: List<&2, U32>, +later: List<&2, Q.Frame>,
  configuration: {I.configuration(x) == c : S.Configuration}, initial: {s == I.initial(x) : D.State}, valid: Req.Valid(c, I.initial(x)),
  verified: Conclusion.OriginOfSource(source, c, s, origin, History.Record{req, ctx, n, w, ts, proposal, N.Prepared{w, ts, S.Response{S.Success{}, v}, bs}}),
  finalized: {Req.finalize(proposal, I.configuration(x), w) == S.Response{S.Success{}, v} : S.Response},
  index: &i: Nat -> {Q.query(before, i) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>},
  without_before: {Phases.absent(Phases.Publication{}, before) == True{} : Bool}, without_later: {Phases.absent(Phases.Publication{}, later) == True{} : Bool},
  prepare: @u: Nat -> {Q.query(trace(before, w, v, bs, later), u) == Some{Q.Prepared{S.Response{S.Success{}, v}, bs}} : Maybe<&2, Q.Frame>} -> I.Happens(a, k, x, u, I.Prepared{S.Response{S.Success{}, v}, bs}),
  evaluate: @u: Nat -> {Q.query(trace(before, w, v, bs, later), u) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>} -> I.Happens(a, k, x, u, I.Evaluated{req, ctx, Source.program(source, origin), S.Final{w, ts, proposal}}),
  publish: @u: Nat -> @state: D.State -> I.Happens(a, k, x, u, I.Published{state}) -> {Q.query(trace(before, w, v, bs, later), u) == Some{Q.Published{state}} : Maybe<&2, Q.Frame>}) ->
  K.Rule6(I.Published{w}, a, k, x, Nat.add(Q.size(before), 1n)):
  L.Both{(%Equal.sym(S.Configuration, I.configuration(x), c, configuration) : Req.Valid(_, w)
      History.step_preserves_validity(c, s, History.Record{req, ctx, n, w, ts, proposal, N.Prepared{w, ts, S.Response{S.Success{}, v}, bs}},
        (%Equal.sym(D.State, s, I.initial(x), initial) : Req.Valid(c, _) valid), Conclusion.history_of_source(source, c, s, origin, History.Record{req, ctx, n, w, ts, proposal, N.Prepared{w, ts, S.Response{S.Success{}, v}, bs}}, verified))),
    L.Both{(v, bs, L.Both{(Nat.add(Q.size(before), 0n), L.Both{Q.order_shifted(Q.size(before), 0n, 1n, {==}), prepare(Nat.add(Q.size(before), 0n), Q.query_after_prefix(before, Con{Q.Prepared{S.Response{S.Success{}, v}, bs}, Con{Q.Published{w}, later}}, 0n))}),
      Conclusion.response_final_has_cause_in_evaluation_real(source, a, k, x, before, Con{Q.Prepared{S.Response{S.Success{}, v}, bs}, Con{Q.Published{w}, later}}, 1n, req, ctx, origin, w, ts, proposal, S.Response{S.Success{}, v}, finalized, index, evaluate)}),
      +u => +state => fact => publication_in_frame_and_unique(before, w, v, bs, later, u, state, without_before, without_later, publish(u, state, fact))}}

def frame_reflected(~source: Source.Source, ~c: S.Configuration, -a: I.Environment, -k: String, -x: I.Scenario,
  +before: List<&2, Q.Frame>, +s: D.State, +req: P.Request, +ctx: D.Context, +origin: Source.JudgmentSyntactic,
  +n: Nat, +w: D.State, +ts: List<&2, S.OperationEvent>, +proposal: S.Response, +v: D.Value, +bs: List<&2, U32>, +later: List<&2, Q.Frame>, +t: Nat, +published: D.State,
  configuration: {I.configuration(x) == c : S.Configuration}, initial: {s == I.initial(x) : D.State}, valid: Req.Valid(c, I.initial(x)),
  verified: Conclusion.OriginOfSource(source, c, s, origin, History.Record{req, ctx, n, w, ts, proposal, N.Prepared{w, ts, S.Response{S.Success{}, v}, bs}}),
  finalized: {Req.finalize(proposal, I.configuration(x), w) == S.Response{S.Success{}, v} : S.Response},
  index: &i: Nat -> {Q.query(before, i) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>},
  without_before: {Phases.absent(Phases.Publication{}, before) == True{} : Bool}, without_later: {Phases.absent(Phases.Publication{}, later) == True{} : Bool},
  prepare: @u: Nat -> {Q.query(trace(before, w, v, bs, later), u) == Some{Q.Prepared{S.Response{S.Success{}, v}, bs}} : Maybe<&2, Q.Frame>} -> I.Happens(a, k, x, u, I.Prepared{S.Response{S.Success{}, v}, bs}),
  evaluate: @u: Nat -> {Q.query(trace(before, w, v, bs, later), u) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>} -> I.Happens(a, k, x, u, I.Evaluated{req, ctx, Source.program(source, origin), S.Final{w, ts, proposal}}),
  publish: @u: Nat -> @state: D.State -> I.Happens(a, k, x, u, I.Published{state}) -> {Q.query(trace(before, w, v, bs, later), u) == Some{Q.Published{state}} : Maybe<&2, Q.Frame>},
  query_result: {Q.query(trace(before, w, v, bs, later), t) == Some{Q.Published{published}} : Maybe<&2, Q.Frame>}) -> K.Rule6(I.Published{published}, a, k, x, t):
  F.combined_pair(K.Rule6(I.Published{published}, a, k, x, t), {Phases.absent(Phases.Publication{}, before) == True{} : Bool}, {Phases.absent(Phases.Publication{}, before) == True{} : Bool},
    Q.equality_reopenable(Bool, Phases.absent(Phases.Publication{}, before), True{}, without_before), before_current => before_all =>
      F.combined_pair(K.Rule6(I.Published{published}, a, k, x, t), {Phases.absent(Phases.Publication{}, later) == True{} : Bool}, {Phases.absent(Phases.Publication{}, later) == True{} : Bool},
        Q.equality_reopenable(Bool, Phases.absent(Phases.Publication{}, later), True{}, without_later), later_current => later_all =>
          Conclusion.transport_publication6(a, k, x, before, w, t, published,
            publication_in_frame_and_unique(before, w, v, bs, later, t, published, before_current, later_current, query_result),
            frame_canonical(source, c, a, k, x, before, s, req, ctx, origin, n, w, ts, proposal, v, bs, later,
              configuration, initial, valid, verified, finalized, index, before_all, later_all, prepare, evaluate, publish))))

# Actual prefix common to success and failure after the store.
def before(+m: R.Micro, +req: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>) -> List<&2, Q.Frame>:
  Con{Q.Configured{}, Q.concatenate(R.render_execution(m, req, ctx, xs), R.micro_output(m))}

def before_without_publication(+m: R.Micro, +req: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>) -> {Phases.absent(Phases.Publication{}, before(m, req, ctx, xs)) == True{} : Bool}:
  Phases.concatenate_absence(Phases.Publication{}, R.render_execution(m, req, ctx, xs), R.micro_output(m), Phases.execution_host_without_macros(Phases.Publication{}, m, req, ctx, xs), Phases.micro_output_without_macros(Phases.Publication{}, m))

def index_in_prefix(+m: R.Micro, +req: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>, +w: D.State, +ts: List<&2, S.OperationEvent>, +proposal: S.Response,
  index: &i: Nat -> {Exec.query(xs, i) == Some{Q.Evaluation{S.Final{w, ts, proposal}}} : Maybe<&2, Q.FrameExec>}) ->
  &u: Nat -> {Q.query(before(m, req, ctx, xs), u) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>}:
  match index:
    case (+i, query_result): (Nat.add(Q.size(Con{Q.Configured{}, R.render_started(m, req, ctx)}), i),
      Adm.query_prefix(Con{Q.Configured{}, R.render_execution(m, req, ctx, xs)}, R.micro_output(m), Nat.add(Q.size(Con{Q.Configured{}, R.render_started(m, req, ctx)}), i), Q.Evaluated{req, ctx, S.Final{w, ts, proposal}},
        Equal.trans(Maybe<&2, Q.Frame>, Q.query(Con{Q.Configured{}, R.render_execution(m, req, ctx, xs)}, Nat.add(Q.size(Con{Q.Configured{}, R.render_started(m, req, ctx)}), i)), Q.query(Q.expand_exec(req, ctx, xs), i), Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}},
          Q.query_after_prefix(Con{Q.Configured{}, R.render_started(m, req, ctx)}, Q.expand_exec(req, ctx, xs), i), Exec.expand_preserves_query(req, ctx, xs, i, Q.Evaluation{S.Final{w, ts, proposal}}, query_result))))

# Extracts only the checked certificate; does not turn it into result Valid.
def certificate_of_source(~source: Source.Source, -c: S.Configuration, -req: P.Request, -ctx: D.Context, +origin: Source.JudgmentSyntactic,
  source_accepts: Source.JudgmentAccepted(source, c, req, ctx, origin)) -> Req.Certifies(c, I.code(req), Source.program(source, origin), ctx, I.arguments(req)):
  match source_accepts:
    case L.Both{elaborates, L.Both{derives, L.Both{certificate, rest}}}: certificate

# Query ports of the same trace. Constructed using list equality
# and LinkageService, not assumed controller behavior.
def Prepares(~source: Source.Source, ~c: S.Configuration, -world: Nat, -s: D.State, -rx: X.Reception, -qs: List<&2, Q.Frame>) -> Type:
  @u: Nat -> @r: S.Response -> @bs: List<&2, U32> -> {Q.query(qs, u) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>} -> I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, u, I.Prepared{r, bs})
def Evaluates(~source: Source.Source, ~c: S.Configuration, -world: Nat, -s: D.State, -rx: X.Reception, +origin: Source.JudgmentSyntactic, -req: P.Request, -ctx: D.Context, -qs: List<&2, Q.Frame>) -> Type:
  @u: Nat -> @p: S.Trace -> {Q.query(qs, u) == Some{Q.Evaluated{req, ctx, p}} : Maybe<&2, Q.Frame>} -> I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, u, I.Evaluated{req, ctx, Source.program(source, origin), p})
def Extracts(~source: Source.Source, ~c: S.Configuration, -world: Nat, -s: D.State, -rx: X.Reception, -qs: List<&2, Q.Frame>) -> Type:
  @u: Nat -> @w: D.State -> I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, u, I.Published{w}) -> {Q.query(qs, u) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}
def Ports(~source: Source.Source, ~c: S.Configuration, -world: Nat, -s: D.State, -rx: X.Reception, +origin: Source.JudgmentSyntactic, -req: P.Request, -ctx: D.Context, -qs: List<&2, Q.Frame>) -> Type:
  L.E<Prepares(source, c, world, s, rx, qs), L.E<Evaluates(source, c, world, s, rx, origin, req, ctx, qs), Extracts(source, c, world, s, rx, qs)>>

def prepare_in_source(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception, +qs: List<&2, Q.Frame>, +u: Nat, +r: S.Response, +bs: List<&2, U32>,
  canonical: {I.Serve{world, c, s, rx} == Source.scenario(source, world) : I.Scenario},
  trace: {Vis.frames_call(c, s, rx, Source.call(source, world)) == qs : List<&2, Q.Frame>}, query_result: {Q.query(qs, u) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}) ->
  I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, u, I.Prepared{r, bs}):
  Linkage.introduce_frame(source, c, world, s, rx, u, Q.Prepared{r, bs}, I.Prepared{r, bs}, canonical,
    (%Equal.sym(List<&2, Q.Frame>, Vis.frames_call(c, s, rx, Source.call(source, world)), qs, trace) : {Q.query(_, u) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>} query_result), {==}, Unit{})

def evaluate_in_source(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception, +origin: Source.JudgmentSyntactic, +req: P.Request, +ctx: D.Context,
  +qs: List<&2, Q.Frame>, +u: Nat, +execution_trace: S.Trace, canonical: {I.Serve{world, c, s, rx} == Source.scenario(source, world) : I.Scenario},
  trace: {Vis.frames_call(c, s, rx, Source.call(source, world)) == qs : List<&2, Q.Frame>}, root: {Source.program(source, origin) == Five.program_of_world(source, world) : S.Program},
  query_result: {Q.query(qs, u) == Some{Q.Evaluated{req, ctx, execution_trace}} : Maybe<&2, Q.Frame>}) -> I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, u, I.Evaluated{req, ctx, Source.program(source, origin), execution_trace}):
  Linkage.introduce_frame(source, c, world, s, rx, u, Q.Evaluated{req, ctx, execution_trace}, I.Evaluated{req, ctx, Source.program(source, origin), execution_trace}, canonical,
    (%Equal.sym(List<&2, Q.Frame>, Vis.frames_call(c, s, rx, Source.call(source, world)), qs, trace) : {Q.query(_, u) == Some{Q.Evaluated{req, ctx, execution_trace}} : Maybe<&2, Q.Frame>} query_result),
    (%root : Q.rel_fact(c, _, Q.Evaluated{req, ctx, execution_trace}, I.Evaluated{req, ctx, Source.program(source, origin), execution_trace}) {==}), Unit{})

def extract_of_source(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception, +qs: List<&2, Q.Frame>, +u: Nat, +w: D.State,
  trace: {Vis.frames_call(c, s, rx, Source.call(source, world)) == qs : List<&2, Q.Frame>}, fact: I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, u, I.Published{w})) -> {Q.query(qs, u) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}:
  %trace : {Q.query(_, u) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}
  Linkage.extract_frame(source, c, world, s, rx, u, I.Published{w}, Unit{}, fact)

def ports_of_source(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception, +origin: Source.JudgmentSyntactic, +req: P.Request, +ctx: D.Context, +qs: List<&2, Q.Frame>,
  canonical: {I.Serve{world, c, s, rx} == Source.scenario(source, world) : I.Scenario},
  trace: {Vis.frames_call(c, s, rx, Source.call(source, world)) == qs : List<&2, Q.Frame>}, root: {Source.program(source, origin) == Five.program_of_world(source, world) : S.Program}) -> Ports(source, c, world, s, rx, origin, req, ctx, qs):
  F.combined_pair(Ports(source, c, world, s, rx, origin, req, ctx, qs), {I.Serve{world, c, s, rx} == Source.scenario(source, world) : I.Scenario}, {I.Serve{world, c, s, rx} == Source.scenario(source, world) : I.Scenario},
    Q.equality_reopenable(I.Scenario, I.Serve{world, c, s, rx}, Source.scenario(source, world), canonical), c_pre => c_aval =>
      F.combined_pair(Ports(source, c, world, s, rx, origin, req, ctx, qs), {Vis.frames_call(c, s, rx, Source.call(source, world)) == qs : List<&2, Q.Frame>}, {Vis.frames_call(c, s, rx, Source.call(source, world)) == qs : List<&2, Q.Frame>},
        Q.equality_reopenable(List<&2, Q.Frame>, Vis.frames_call(c, s, rx, Source.call(source, world)), qs, trace), for_intros => for_extract =>
          F.combined_pair(Ports(source, c, world, s, rx, origin, req, ctx, qs), {Vis.frames_call(c, s, rx, Source.call(source, world)) == qs : List<&2, Q.Frame>}, {Vis.frames_call(c, s, rx, Source.call(source, world)) == qs : List<&2, Q.Frame>},
            Q.equality_reopenable(List<&2, Q.Frame>, Vis.frames_call(c, s, rx, Source.call(source, world)), qs, for_intros), for_preparation => for_evaluate =>
              L.Both{+u => +r => +bs => query_result => prepare_in_source(source, c, world, s, rx, qs, u, r, bs, c_pre, for_preparation, query_result),
                L.Both{+u => +execution_trace => query_result => evaluate_in_source(source, c, world, s, rx, origin, req, ctx, qs, u, execution_trace, c_aval, for_evaluate, root, query_result),
                  +u => +w => fact => extract_of_source(source, c, world, s, rx, qs, u, w, for_extract, fact)}})))

def end(conclusion: N.Conclusion, later: List<&2, Q.Frame>) -> List<&2, Q.Frame>:
  match conclusion:
    case N.Conclusion{+w, +r, bs}: Con{Q.Prepared{r, bs}, Q.concatenate(R.render_publication(r, w), later)}
def frame_final(+m: R.Micro, +req: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>, +p: N.Prepared, +s: D.State, later: List<&2, Q.Frame>) -> List<&2, Q.Frame>:
  Q.concatenate(before(m, req, ctx, xs), end(N.conclude(p, s), later))

def success_combined_ports(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +m: R.Micro, +req: P.Request, +ctx: D.Context, +origin: Source.JudgmentSyntactic, +xs: List<&2, Q.FrameExec>, +n: Nat,
  +w: D.State, +ts: List<&2, S.OperationEvent>, +proposal: S.Response, +v: D.Value, +bs: List<&2, U32>, +later: List<&2, Q.Frame>, +t: Nat, +published: D.State,
  valid: Req.Valid(c, s), verified: Conclusion.OriginOfSource(source, c, s, origin, History.Record{req, ctx, n, w, ts, proposal, N.Prepared{w, ts, S.Response{S.Success{}, v}, bs}}),
  finalized: {Req.finalize(proposal, c, w) == S.Response{S.Success{}, v} : S.Response},
  index: &i: Nat -> {Q.query(before(m, req, ctx, xs), i) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>},
  without_later: {Phases.absent(Phases.Publication{}, later) == True{} : Bool},
  ports: Ports(source, c, world, s, rx, origin, req, ctx, trace(before(m, req, ctx, xs), w, v, bs, later)),
  query_result: {Q.query(trace(before(m, req, ctx, xs), w, v, bs, later), t) == Some{Q.Published{published}} : Maybe<&2, Q.Frame>}) ->
  K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t):
  match ports:
    case L.Both{prepare, L.Both{evaluate, publish}}:
      frame_reflected(source, c, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, before(m, req, ctx, xs), s, req, ctx, origin, n, w, ts, proposal, v, bs, later, t, published,
        {==}, {==}, valid, verified, finalized, index, before_without_publication(m, req, ctx, xs), without_later,
        +u => h => prepare(u, S.Response{S.Success{}, v}, bs, h),
        +u => h => evaluate(u, S.Final{w, ts, proposal}, h), publish, query_result)

def response_of_result(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +m: R.Micro, +req: P.Request, +ctx: D.Context, +origin: Source.JudgmentSyntactic, +xs: List<&2, Q.FrameExec>, +n: Nat,
  +w: D.State, +ts: List<&2, S.OperationEvent>, +proposal: S.Response, r: S.Response, +bs: List<&2, U32>, +later: List<&2, Q.Frame>, +t: Nat, +published: D.State,
  valid: Req.Valid(c, s), verified: Conclusion.OriginOfSource(source, c, s, origin, History.Record{req, ctx, n, w, ts, proposal, N.Prepared{w, ts, r, bs}}),
  finalized: {Req.finalize(proposal, c, w) == r : S.Response},
  index: &i: Nat -> {Q.query(before(m, req, ctx, xs), i) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>},
  without_later: {Phases.absent(Phases.Publication{}, later) == True{} : Bool},
  ports: Ports(source, c, world, s, rx, origin, req, ctx, frame_final(m, req, ctx, xs, N.Prepared{w, ts, r, bs}, s, later)),
  query_result: {Q.query(frame_final(m, req, ctx, xs, N.Prepared{w, ts, r, bs}, s, later), t) == Some{Q.Published{published}} : Maybe<&2, Q.Frame>}) ->
  K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t):
  match r:
    case S.Response{S.Success{}, +v}: success_combined_ports(source, c, world, s, rx, m, req, ctx, origin, xs, n, w, ts, proposal, v, bs, later, t, published, valid, verified, finalized, index, without_later, ports, query_result)
    case S.Response{S.Refusal{}, +v}: L.ex_false(K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t),
      Phases.absent_excludes_query(Phases.Publication{}, Q.concatenate(before(m, req, ctx, xs), Con{Q.Prepared{S.Response{S.Refusal{}, v}, bs}, later}), t, Q.Published{published},
        Phases.concatenate_absence(Phases.Publication{}, before(m, req, ctx, xs), Con{Q.Prepared{S.Response{S.Refusal{}, v}, bs}, later}, before_without_publication(m, req, ctx, xs), without_later), {==}, query_result))
    case S.Response{S.Input{}, +v}: L.ex_false(K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t),
      Phases.absent_excludes_query(Phases.Publication{}, Q.concatenate(before(m, req, ctx, xs), Con{Q.Prepared{S.Response{S.Input{}, v}, bs}, later}), t, Q.Published{published},
        Phases.concatenate_absence(Phases.Publication{}, before(m, req, ctx, xs), Con{Q.Prepared{S.Response{S.Input{}, v}, bs}, later}, before_without_publication(m, req, ctx, xs), without_later), {==}, query_result))
    case S.Response{S.Authentication{}, +v}: L.ex_false(K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t),
      Phases.absent_excludes_query(Phases.Publication{}, Q.concatenate(before(m, req, ctx, xs), Con{Q.Prepared{S.Response{S.Authentication{}, v}, bs}, later}), t, Q.Published{published},
        Phases.concatenate_absence(Phases.Publication{}, before(m, req, ctx, xs), Con{Q.Prepared{S.Response{S.Authentication{}, v}, bs}, later}, before_without_publication(m, req, ctx, xs), without_later), {==}, query_result))
    case S.Response{S.Certificate{}, +v}: L.ex_false(K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t),
      Phases.absent_excludes_query(Phases.Publication{}, Q.concatenate(before(m, req, ctx, xs), Con{Q.Prepared{S.Response{S.Certificate{}, v}, bs}, later}), t, Q.Published{published},
        Phases.concatenate_absence(Phases.Publication{}, before(m, req, ctx, xs), Con{Q.Prepared{S.Response{S.Certificate{}, v}, bs}, later}, before_without_publication(m, req, ctx, xs), without_later), {==}, query_result))
    case S.Response{S.DataError{}, +v}: L.ex_false(K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t),
      Phases.absent_excludes_query(Phases.Publication{}, Q.concatenate(before(m, req, ctx, xs), Con{Q.Prepared{S.Response{S.DataError{}, v}, bs}, later}), t, Q.Published{published},
        Phases.concatenate_absence(Phases.Publication{}, before(m, req, ctx, xs), Con{Q.Prepared{S.Response{S.DataError{}, v}, bs}, later}, before_without_publication(m, req, ctx, xs), without_later), {==}, query_result))
    case S.Response{S.Limit{}, +v}: L.ex_false(K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t),
      Phases.absent_excludes_query(Phases.Publication{}, Q.concatenate(before(m, req, ctx, xs), Con{Q.Prepared{S.Response{S.Limit{}, v}, bs}, later}), t, Q.Published{published},
        Phases.concatenate_absence(Phases.Publication{}, before(m, req, ctx, xs), Con{Q.Prepared{S.Response{S.Limit{}, v}, bs}, later}, before_without_publication(m, req, ctx, xs), without_later), {==}, query_result))
    case S.Response{S.Failure{}, +v}: L.ex_false(K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t),
      Phases.absent_excludes_query(Phases.Publication{}, Q.concatenate(before(m, req, ctx, xs), Con{Q.Prepared{S.Response{S.Failure{}, v}, bs}, later}), t, Q.Published{published},
        Phases.concatenate_absence(Phases.Publication{}, before(m, req, ctx, xs), Con{Q.Prepared{S.Response{S.Failure{}, v}, bs}, later}, before_without_publication(m, req, ctx, xs), without_later), {==}, query_result))

# N.prepare equality transports the entire argument set,
# including observation ports of the result actually received.
def normalized(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +m: R.Micro, +req: P.Request, +ctx: D.Context, +origin: Source.JudgmentSyntactic, +xs: List<&2, Q.FrameExec>, +n: Nat,
  +w: D.State, +ts: List<&2, S.OperationEvent>, +proposal: S.Response, +p: N.Prepared, +bs: List<&2, U32>, +later: List<&2, Q.Frame>, +t: Nat, +published: D.State,
  valid: Req.Valid(c, s), index: &i: Nat -> {Q.query(before(m, req, ctx, xs), i) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>},
  without_later: {Phases.absent(Phases.Publication{}, later) == True{} : Bool}, normalization: {p == N.Prepared{w, ts, Req.finalize(proposal, c, w), bs} : N.Prepared}) ->
  Conclusion.OriginOfSource(source, c, s, origin, History.Record{req, ctx, n, w, ts, proposal, p}) ->
    Ports(source, c, world, s, rx, origin, req, ctx, frame_final(m, req, ctx, xs, p, s, later)) ->
      {Q.query(frame_final(m, req, ctx, xs, p, s, later), t) == Some{Q.Published{published}} : Maybe<&2, Q.Frame>} ->
        K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t):
  %Equal.sym(N.Prepared, p, N.Prepared{w, ts, Req.finalize(proposal, c, w), bs}, normalization) :
    (Conclusion.OriginOfSource(source, c, s, origin, History.Record{req, ctx, n, w, ts, proposal, _}) ->
      Ports(source, c, world, s, rx, origin, req, ctx, frame_final(m, req, ctx, xs, _, s, later)) ->
        {Q.query(frame_final(m, req, ctx, xs, _, s, later), t) == Some{Q.Published{published}} : Maybe<&2, Q.Frame>} ->
          K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t))
  verified => ports => query_result => response_of_result(source, c, world, s, rx, m, req, ctx, origin, xs, n, w, ts, proposal, Req.finalize(proposal, c, w), bs, later, t, published,
    valid, verified, {==}, index, without_later, ports, query_result)

def publication_final_real(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +m: R.Micro, +req: P.Request, +ctx: D.Context, +origin: Source.JudgmentSyntactic, +xs: List<&2, Q.FrameExec>, +p: N.Prepared, +later: List<&2, Q.Frame>, +t: Nat, +published: D.State,
  valid: Req.Valid(c, s), aut: {D.authenticate(s, I.credential(req)) == Some{ctx} : Maybe<&2, D.Context>}, judgment: Source.JudgmentAccepted(source, c, req, ctx, origin),
  real: Source.FinalReal(source, c, s, req, ctx, origin, xs, p), without_later: {Phases.absent(Phases.Publication{}, later) == True{} : Bool},
  ports: Ports(source, c, world, s, rx, origin, req, ctx, frame_final(m, req, ctx, xs, p, s, later)),
  query_result: {Q.query(frame_final(m, req, ctx, xs, p, s, later), t) == Some{Q.Published{published}} : Maybe<&2, Q.Frame>}) ->
  K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t):
  match real:
    case (+n, +w, +ts, +proposal, L.Both{sequence, L.Both{result, obtained}}):
      F.combined_pair(K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t),
        {N.traverse(n, N.start(Source.program(source, origin), ctx, I.arguments(req), s), S.schema(c)) == S.Final{w, ts, proposal} : S.Trace},
        {N.traverse(n, N.start(Source.program(source, origin), ctx, I.arguments(req), s), S.schema(c)) == S.Final{w, ts, proposal} : S.Trace},
        Q.equality_reopenable(S.Trace, N.traverse(n, N.start(Source.program(source, origin), ctx, I.arguments(req), s), S.schema(c)), S.Final{w, ts, proposal}, result), for_origin => for_index =>
          F.combined_pair(K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t),
            {N.prepare(N.Stopped{w, ts, proposal}, c) == Some{p} : Maybe<&2, N.Prepared>}, {N.prepare(N.Stopped{w, ts, proposal}, c) == Some{p} : Maybe<&2, N.Prepared>},
            Q.equality_reopenable(Maybe<&2, N.Prepared>, N.prepare(N.Stopped{w, ts, proposal}, c), Some{p}, obtained), for_origin_preparation => for_normalize =>
              normalized(source, c, world, s, rx, m, req, ctx, origin, xs, n, w, ts, proposal, p, Preparation.bytes_prepared(p), later, t, published, valid,
                index_in_prefix(m, req, ctx, xs, w, ts, proposal, Conclusion.last_evaluation_of_result_real(source, c, s, req, ctx, origin, n, w, ts, proposal, xs, sequence, for_index)), without_later,
                L.and_left({p == N.Prepared{w, ts, Req.finalize(proposal, c, w), Preparation.bytes_prepared(p)} : N.Prepared},
                  P.Message(S.response_value(Req.finalize(proposal, c, w)), Preparation.bytes_prepared(p)), Conclusion.normalize_prepared_real(c, w, ts, proposal, p, for_normalize)))(L.Both{certificate_of_source(source, c, req, ctx, origin, judgment), L.Both{aut, L.Both{for_origin, for_origin_preparation}}}, ports, query_result)))

def later_normal(conclusion: N.Conclusion, delivery: R.Delivery) -> List<&2, Q.Frame>:
  match conclusion:
    case N.Conclusion{+w, +r, +bs}: Con{Q.Completed{r, w, False{}}, R.render_delivery(w, bs, False{}, delivery)}
def later_normal_without_publication(conclusion: N.Conclusion, delivery: R.Delivery) -> {Phases.absent(Phases.Publication{}, later_normal(conclusion, delivery)) == True{} : Bool}:
  match conclusion:
    case N.Conclusion{w, r, bs}: Phases.delivery_without_publication(w, bs, False{}, delivery)

def form_normal(+conclusion: N.Conclusion, +delivery: R.Delivery) -> {R.render_conclusion(conclusion, False{}, delivery) == end(conclusion, later_normal(conclusion, delivery)) : List<&2, Q.Frame>}:
  match conclusion:
    case N.Conclusion{w, r, bs}: {==}
def form_fatal(+conclusion: N.Conclusion, +stage: X.Stage, +id: String) -> {R.render_fatal_published(conclusion, stage, id) == end(conclusion, [Q.Failed{stage, id, True{}}, Q.Closed{}]) : List<&2, Q.Frame>}:
  match conclusion:
    case N.Conclusion{w, r, bs}: {==}

def associate_before(+m: R.Micro, +req: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>, +end: List<&2, Q.Frame>) ->
  {Con{Q.Configured{}, Q.concatenate(R.render_execution(m, req, ctx, xs), Q.concatenate(R.micro_output(m), end))} == Q.concatenate(before(m, req, ctx, xs), end) : List<&2, Q.Frame>}:
  Equal.sym(List<&2, Q.Frame>, Q.concatenate(before(m, req, ctx, xs), end),
    Con{Q.Configured{}, Q.concatenate(R.render_execution(m, req, ctx, xs), Q.concatenate(R.micro_output(m), end))},
    Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, qs => Con{Q.Configured{}, qs},
      Q.concatenate(Q.concatenate(R.render_execution(m, req, ctx, xs), R.micro_output(m)), end),
      Q.concatenate(R.render_execution(m, req, ctx, xs), Q.concatenate(R.micro_output(m), end)), Q.concatenate_assoc(R.render_execution(m, req, ctx, xs), R.micro_output(m), end)))

def error_framed_without_publication(q: Maybe<&2, List<&2, U32>>, -r: S.Response, +s: D.State, +closes: Bool, delivery: R.Delivery) -> {Phases.absent(Phases.Publication{}, R.render_error_framed(q, r, s, closes, delivery)) == True{} : Bool}:
  match q:
    case None{}: {==}
    case Some{bs}: Phases.delivery_without_publication(s, bs, closes, delivery)
def error_without_publication(+status: S.Status, +s: D.State, +closes: Bool, delivery: R.Delivery) -> {Phases.absent(Phases.Publication{}, R.render_error(status, s, closes, delivery)) == True{} : Bool}:
  error_framed_without_publication(P.frame(S.response_value(S.response_error(status))), S.response_error(status), s, closes, delivery)
def failure_without_publication(+s: D.State, -stage: X.Stage, -id: String, fatal: Bool, delivery: R.Delivery) -> {Phases.absent(Phases.Publication{}, R.render_failure(s, stage, id, fatal, delivery)) == True{} : Bool}:
  match fatal:
    case True{}: {==}
    case False{}: error_without_publication(S.Failure{}, s, False{}, delivery)

def OutsideFinal(-m: R.Micro, -s: D.State, branch: R.Branch) -> Type:
  match branch:
    case R.Executed{r, ctx, xs, p, delivery}: Unit
    case R.FatalAfterPublication{r, ctx, xs, p, stage, id}: Unit
    case _: {Phases.absent(Phases.Publication{}, R.render(m, s, branch)) == True{} : Bool}

def outside_final_negative_publish(+m: R.Micro, +s: D.State, branch: R.Branch) -> OutsideFinal(m, s, branch):
  match branch:
    case R.InitialOk{}: Phases.initialization_without_publication(m, s)
    case R.InitialRefusal{status}: {==}
    case R.InitialFailure{+accepts, +stage, +id, +fatal}:
      Phases.concatenate_absence(Phases.Publication{}, R.prefix_initial(m, accepts), [Q.Failed{stage, id, fatal}, Q.InitialRefused{S.Failure{}}],
        L.and_left({Phases.absent(Phases.Publication{}, R.prefix_initial(m, accepts)) == True{} : Bool}, {Phases.absent(Phases.Initialization{}, R.prefix_initial(m, accepts)) == True{} : Bool}, Phases.prefix_initial_without_store(m, accepts)), {==})
    case R.WithoutResponse{}: {==}
    case R.InputRefusal{+error, +closes, +delivery}:
      Phases.concatenate_absence(Phases.Publication{}, R.micro_input(m), R.render_error(R.status_input(error), s, closes, delivery), Phases.micro_input_without_macros(Phases.Publication{}, m), error_without_publication(R.status_input(error), s, closes, delivery))
    case R.AutRefusal{+r, +delivery}:
      Phases.concatenate_absence(Phases.Publication{}, R.render_received(m, r), Q.concatenate(R.micro_authentication(m), Con{Q.Authenticated{r, None{}}, R.render_error(S.Authentication{}, s, False{}, delivery)}), Phases.received_without_macros(Phases.Publication{}, m, r),
        Phases.concatenate_absence(Phases.Publication{}, R.micro_authentication(m), Con{Q.Authenticated{r, None{}}, R.render_error(S.Authentication{}, s, False{}, delivery)}, Phases.micro_authentication_without_macros(Phases.Publication{}, m), error_without_publication(S.Authentication{}, s, False{}, delivery)))
    case R.GateRefusal{+r, +ctx, +delivery}:
      Phases.concatenate_absence(Phases.Publication{}, R.render_authenticated(m, r, ctx), Con{Q.Rejected{r, ctx}, R.render_error(S.Certificate{}, s, False{}, delivery)}, Phases.authenticated_without_macros(Phases.Publication{}, m, r, ctx), error_without_publication(S.Certificate{}, s, False{}, delivery))
    case R.Executed{r, ctx, xs, p, delivery}: Unit{}
    case R.FailureBefore{+phase, +stage, +id, +fatal, +delivery}:
      Phases.concatenate_absence(Phases.Publication{}, R.render_phase(m, phase), R.render_failure(s, stage, id, fatal, delivery), Phases.phase_previous_without_macros(Phases.Publication{}, m, phase), failure_without_publication(s, stage, id, fatal, delivery))
    case R.FatalAfterPublication{r, ctx, xs, p, stage, id}: Unit{}
    case R.Pending{phase}: Phases.phase_previous_without_macros(Phases.Publication{}, m, phase)
    case R.InitialPending{+accepts}: L.and_left({Phases.absent(Phases.Publication{}, R.prefix_initial(m, accepts)) == True{} : Bool}, {Phases.absent(Phases.Initialization{}, R.prefix_initial(m, accepts)) == True{} : Bool}, Phases.prefix_initial_without_store(m, accepts))

def final_linked(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +m: R.Micro, +req: P.Request, +ctx: D.Context, +origin: Source.JudgmentSyntactic, +xs: List<&2, Q.FrameExec>, +p: N.Prepared, +later: List<&2, Q.Frame>, +t: Nat, +published: D.State,
  valid: Req.Valid(c, s), aut: {D.authenticate(s, I.credential(req)) == Some{ctx} : Maybe<&2, D.Context>}, judgment: Source.JudgmentAccepted(source, c, req, ctx, origin), real: Source.FinalReal(source, c, s, req, ctx, origin, xs, p),
  without_later: {Phases.absent(Phases.Publication{}, later) == True{} : Bool}, canonical: {I.Serve{world, c, s, rx} == Source.scenario(source, world) : I.Scenario},
  root: {Source.program(source, origin) == Five.program_of_world(source, world) : S.Program},
  trace: {Vis.frames_call(c, s, rx, Source.call(source, world)) == frame_final(m, req, ctx, xs, p, s, later) : List<&2, Q.Frame>},
  query_result: {Q.query(Vis.frames_call(c, s, rx, Source.call(source, world)), t) == Some{Q.Published{published}} : Maybe<&2, Q.Frame>}) ->
  K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t):
  F.combined_pair(K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t),
    {Vis.frames_call(c, s, rx, Source.call(source, world)) == frame_final(m, req, ctx, xs, p, s, later) : List<&2, Q.Frame>}, {Vis.frames_call(c, s, rx, Source.call(source, world)) == frame_final(m, req, ctx, xs, p, s, later) : List<&2, Q.Frame>},
    Q.equality_reopenable(List<&2, Q.Frame>, Vis.frames_call(c, s, rx, Source.call(source, world)), frame_final(m, req, ctx, xs, p, s, later), trace), for_ports => for_query =>
      publication_final_real(source, c, world, s, rx, m, req, ctx, origin, xs, p, later, t, published, valid, aut, judgment, real, without_later,
        ports_of_source(source, c, world, s, rx, origin, req, ctx, frame_final(m, req, ctx, xs, p, s, later), canonical, for_ports, root),
        (%for_query : {Q.query(_, t) == Some{Q.Published{published}} : Maybe<&2, Q.Frame>} query_result)))

def branch_impossible(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +m: R.Micro, +branch: R.Branch, +t: Nat, +published: D.State,
  without: {Phases.absent(Phases.Publication{}, R.render(m, s, branch)) == True{} : Bool},
  trace: {Vis.frames_call(c, s, rx, Source.call(source, world)) == R.render(m, s, branch) : List<&2, Q.Frame>},
  query_result: {Q.query(Vis.frames_call(c, s, rx, Source.call(source, world)), t) == Some{Q.Published{published}} : Maybe<&2, Q.Frame>}) ->
  K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t):
  L.ex_false(K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t), Phases.absent_excludes_query(Phases.Publication{}, R.render(m, s, branch), t, Q.Published{published}, without, {==},
    (%trace : {Q.query(_, t) == Some{Q.Published{published}} : Maybe<&2, Q.Frame>} query_result)))

def publication_of_branch(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +m: R.Micro, +origin: Source.JudgmentSyntactic, branch: R.Branch, +t: Nat, +published: D.State,
  valid: Req.Valid(c, s), real: Five.BranchReal(source, c, s, origin, branch), aut: Five.AuthOfBranch(s, branch), judgment: Source.JudgmentOfBranch(source, c, origin, branch),
  canonical: {I.Serve{world, c, s, rx} == Source.scenario(source, world) : I.Scenario}, root: {Source.program(source, origin) == Five.program_of_world(source, world) : S.Program},
  trace: {Vis.frames_call(c, s, rx, Source.call(source, world)) == R.render(m, s, branch) : List<&2, Q.Frame>},
  query_result: {Q.query(Vis.frames_call(c, s, rx, Source.call(source, world)), t) == Some{Q.Published{published}} : Maybe<&2, Q.Frame>}) ->
  K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t):
  match branch:
    case R.Executed{+req, +ctx, +xs, +p, +delivery}:
      final_linked(source, c, world, s, rx, m, req, ctx, origin, xs, p, later_normal(N.conclude(p, s), delivery), t, published,
        valid, aut, judgment, real, later_normal_without_publication(N.conclude(p, s), delivery), canonical, root,
        Equal.trans(List<&2, Q.Frame>, Vis.frames_call(c, s, rx, Source.call(source, world)), R.render(m, s, R.Executed{req, ctx, xs, p, delivery}), frame_final(m, req, ctx, xs, p, s, later_normal(N.conclude(p, s), delivery)), trace,
          Equal.trans(List<&2, Q.Frame>, R.render(m, s, R.Executed{req, ctx, xs, p, delivery}), Q.concatenate(before(m, req, ctx, xs), R.render_final(p, s, False{}, delivery)), frame_final(m, req, ctx, xs, p, s, later_normal(N.conclude(p, s), delivery)),
            associate_before(m, req, ctx, xs, R.render_final(p, s, False{}, delivery)),
            Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, rest => Q.concatenate(before(m, req, ctx, xs), rest), R.render_final(p, s, False{}, delivery), end(N.conclude(p, s), later_normal(N.conclude(p, s), delivery)), form_normal(N.conclude(p, s), delivery)))), query_result)
    case R.FatalAfterPublication{+req, +ctx, +xs, +p, +stage, +id}:
      final_linked(source, c, world, s, rx, m, req, ctx, origin, xs, p, [Q.Failed{stage, id, True{}}, Q.Closed{}], t, published,
        valid, aut, judgment, real, {==}, canonical, root,
        Equal.trans(List<&2, Q.Frame>, Vis.frames_call(c, s, rx, Source.call(source, world)), R.render(m, s, R.FatalAfterPublication{req, ctx, xs, p, stage, id}), frame_final(m, req, ctx, xs, p, s, [Q.Failed{stage, id, True{}}, Q.Closed{}]), trace,
          Equal.trans(List<&2, Q.Frame>, R.render(m, s, R.FatalAfterPublication{req, ctx, xs, p, stage, id}), Q.concatenate(before(m, req, ctx, xs), R.render_fatal_published(N.conclude(p, s), stage, id)), frame_final(m, req, ctx, xs, p, s, [Q.Failed{stage, id, True{}}, Q.Closed{}]),
            associate_before(m, req, ctx, xs, R.render_fatal_published(N.conclude(p, s), stage, id)),
            Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, rest => Q.concatenate(before(m, req, ctx, xs), rest), R.render_fatal_published(N.conclude(p, s), stage, id), end(N.conclude(p, s), [Q.Failed{stage, id, True{}}, Q.Closed{}]), form_fatal(N.conclude(p, s), stage, id)))), query_result)
    case R.InitialOk{}: branch_impossible(source, c, world, s, rx, m, R.InitialOk{}, t, published, outside_final_negative_publish(m, s, R.InitialOk{}), trace, query_result)
    case R.InitialRefusal{+a0}: branch_impossible(source, c, world, s, rx, m, R.InitialRefusal{a0}, t, published, outside_final_negative_publish(m, s, R.InitialRefusal{a0}), trace, query_result)
    case R.InitialFailure{+a0, +a1, +a2, +a3}: branch_impossible(source, c, world, s, rx, m, R.InitialFailure{a0, a1, a2, a3}, t, published, outside_final_negative_publish(m, s, R.InitialFailure{a0, a1, a2, a3}), trace, query_result)
    case R.WithoutResponse{}: branch_impossible(source, c, world, s, rx, m, R.WithoutResponse{}, t, published, outside_final_negative_publish(m, s, R.WithoutResponse{}), trace, query_result)
    case R.InputRefusal{+a0, +a1, +a2}: branch_impossible(source, c, world, s, rx, m, R.InputRefusal{a0, a1, a2}, t, published, outside_final_negative_publish(m, s, R.InputRefusal{a0, a1, a2}), trace, query_result)
    case R.AutRefusal{+a0, +a1}: branch_impossible(source, c, world, s, rx, m, R.AutRefusal{a0, a1}, t, published, outside_final_negative_publish(m, s, R.AutRefusal{a0, a1}), trace, query_result)
    case R.GateRefusal{+a0, +a1, +a2}: branch_impossible(source, c, world, s, rx, m, R.GateRefusal{a0, a1, a2}, t, published, outside_final_negative_publish(m, s, R.GateRefusal{a0, a1, a2}), trace, query_result)
    case R.FailureBefore{+a0, +a1, +a2, +a3, +a4}: branch_impossible(source, c, world, s, rx, m, R.FailureBefore{a0, a1, a2, a3, a4}, t, published, outside_final_negative_publish(m, s, R.FailureBefore{a0, a1, a2, a3, a4}), trace, query_result)
    case R.Pending{+a0}: branch_impossible(source, c, world, s, rx, m, R.Pending{a0}, t, published, outside_final_negative_publish(m, s, R.Pending{a0}), trace, query_result)
    case R.InitialPending{+a0}: branch_impossible(source, c, world, s, rx, m, R.InitialPending{a0}, t, published, outside_final_negative_publish(m, s, R.InitialPending{a0}), trace, query_result)

def JudgmentOfCall(~source: Source.Source, ~c: S.Configuration, +rx: X.Reception, data: Source.CallData) -> Type:
  match data:
    case Source.CallData{cf, +origin, pf, tf, +state, +tools, micro}:
      Source.JudgmentOfBranch(source, c, origin, R.decide(c, rx, state, tools))

def publication_data(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception, data: Source.CallData, +t: Nat, +published: D.State,
  valid: Req.Valid(c, s), canonical: {I.Serve{world, c, s, rx} == Source.scenario(source, world) : I.Scenario},
  metadata: {Source.call(source, world) == data : Source.CallData}, real: Five.CallReal(source, c, s, rx, data), judgment: JudgmentOfCall(source, c, rx, data),
  query_result: {Q.query(Vis.frames_call(c, s, rx, Source.call(source, world)), t) == Some{Q.Published{published}} : Maybe<&2, Q.Frame>}) ->
  K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t):
  match data:
    case Source.CallData{+cf, +origin, +pf, +tf, +state, +tools, +micro}:
      F.combined_pair(K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t),
        {Source.call(source, world) == Source.CallData{cf, origin, pf, tf, state, tools, micro} : Source.CallData}, {Source.call(source, world) == Source.CallData{cf, origin, pf, tf, state, tools, micro} : Source.CallData},
        Q.equality_reopenable(Source.CallData, Source.call(source, world), Source.CallData{cf, origin, pf, tf, state, tools, micro}, metadata), for_root => for_trace =>
          F.combined_pair(K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t),
            Five.BranchReal(source, c, s, origin, R.decide(c, rx, state, tools)), L.E<Five.AuthOfBranch(s, R.decide(c, rx, state, tools)), Five.GateOfBranch(R.judgment_of(tools), R.decide(c, rx, state, tools))>,
            Five.route_real_decided(source, c, s, origin, state, tools, rx, real), origin_final => admission =>
              F.combined_pair(K.Rule6(I.Published{published}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t), Five.AuthOfBranch(s, R.decide(c, rx, state, tools)), Five.GateOfBranch(R.judgment_of(tools), R.decide(c, rx, state, tools)), admission,
                aut => gate => publication_of_branch(source, c, world, s, rx, micro, origin, R.decide(c, rx, state, tools), t, published, valid, origin_final, aut, judgment, canonical,
                  Five.same_root_of_call(source, world, Source.CallData{cf, origin, pf, tf, state, tools, micro}, Equal.sym(Source.CallData, Source.call(source, world), Source.CallData{cf, origin, pf, tf, state, tools, micro}, for_root)),
                  Equal.cong(Source.CallData, List<&2, Q.Frame>, d => Vis.frames_call(c, s, rx, d), Source.call(source, world), Source.CallData{cf, origin, pf, tf, state, tools, micro}, for_trace), query_result))))

law publication_of_call:
  for ~source: Source.Source
  for ~c: S.Configuration
  for +world: Nat
  for +s: D.State
  for +rx: X.Reception
  for +t: Nat
  for +w: D.State
  for valid: Req.Valid(c, s)
  for real: Five.CallReal(source, c, s, rx, Source.call(source, world))
  for judgment: JudgmentOfCall(source, c, rx, Source.call(source, world))
  for fact: I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t, I.Published{w})
  K.Rule6(I.Published{w}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t)
def publication_of_call(source, c, world, s, rx, t, w, valid, real, judgment, fact):
  F.combined_pair(K.Rule6(I.Published{w}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t), {Source.artifact(source) == Source.artifact(source) : String},
    L.E<{I.Serve{world, c, s, rx} == Source.scenario(source, world) : I.Scenario}, Source.of_route(source, I.Serve{world, c, s, rx}, t, I.Published{w})>,
    Source.eliminate_fact_literal(source, Source.artifact(source), I.Serve{world, c, s, rx}, t, I.Published{w}, fact), name => literal =>
      F.combined_pair(K.Rule6(I.Published{w}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t), {I.Serve{world, c, s, rx} == Source.scenario(source, world) : I.Scenario}, Source.of_route(source, I.Serve{world, c, s, rx}, t, I.Published{w}), literal,
        canonical => obs => publication_data(source, c, world, s, rx, Source.call(source, world), t, w, valid, canonical, {==}, real, judgment,
          Linkage.frame_of_observation(source, c, s, rx, Source.call(source, world), t, I.Published{w}, Unit{}, obs))))

# Initialization does not perform a transaction/publication.
def initial_without_publication(+m: R.Micro, +s: D.State, j: R.Judgment, result: R.ResultInitial, +is_valid: Bool) -> {Phases.absent(Phases.Publication{}, R.render(m, s, R.decide_judgment_initial(j, result, is_valid))) == True{} : Bool}:
  match j:
    case R.Accepted{}:
      match result:
        case R.InitializationFinished{}:
          match is_valid:
            case False{}: {==}
            case True{}: Phases.initialization_without_publication(m, s)
        case R.FailedInitial{+accepts, +stage, +id, +fatal}: outside_final_negative_publish(m, s, R.InitialFailure{accepts && is_valid, stage, id, fatal})
        case R.PendingInitial{accepts}: outside_final_negative_publish(m, s, R.InitialPending{accepts && is_valid})
    case R.Refused{}: {==}
    case R.ErrorJudgment{id, fatal}: {==}
    case R.PendingJudgment{}: {==}

def initial_data_without_publication(~source: Source.Source, ~c: S.Configuration, +s: D.State, data: Source.InitialData) -> {Phases.absent(Phases.Publication{}, Vis.frames_initial(source, c, s, data)) == True{} : Bool}:
  match data:
    case Source.InitialData{cf, sf, pf, +j, +result, +micro}: initial_without_publication(micro, s, j, result, Config.is_valid(c, Source.identity(source)))

law publication_initial_impossible:
  for ~source: Source.Source
  for ~c: S.Configuration
  for +world: Nat
  for +s: D.State
  for +pi: String
  for +t: Nat
  for +w: D.State
  for fact: I.Happens(Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t, I.Published{w})
  Empty
def publication_initial_impossible(source, c, world, s, pi, t, w, fact):
  Phases.absent_excludes_query(Phases.Publication{}, Vis.frames_initial(source, c, s, Source.initial(source, world)), t, Q.Published{w}, initial_data_without_publication(source, c, s, Source.initial(source, world)), {==},
    Vis.eliminate_publication_source_initial(source, c, world, s, pi, t, w, fact))

def OriginOfMoment(~source: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, +world: Nat, moment: Scenarios.Moment) -> Type:
  match moment:
    case Scenarios.Initialization{}: Unit
    case Scenarios.Service{+rx}: L.E<Five.OriginOfMoment(source, c, seed, history, world, Scenarios.Service{rx}),
      JudgmentOfCall(source, c, rx, Source.call(source, world))>

law publication_by_moment:
  for ~source: Source.Source
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~history: Nat -> List<&2, History.Record>
  for ~pi: String
  for +world: Nat
  for moment: Scenarios.Moment
  for +t: Nat
  for +w: D.State
  for origin: OriginOfMoment(source, c, seed, history, world, moment)
  for fact: I.Happens(Source.environment(source), Source.artifact(source), Scenarios.of_moment(c, seed, history, pi, moment, world), t, I.Published{w})
  K.Rule6(I.Published{w}, Source.environment(source), Source.artifact(source), Scenarios.of_moment(c, seed, history, pi, moment, world), t)
def publication_by_moment(source, c, seed, history, pi, world, moment, t, w, origin, fact):
  match moment:
    case Scenarios.Initialization{}: L.ex_false(K.Rule6(I.Published{w}, Source.environment(source), Source.artifact(source), I.Initialize{world, c, seed(Unit{}), pi}, t), publication_initial_impossible(source, c, world, seed(Unit{}), pi, t, w, fact))
    case Scenarios.Service{+rx}:
      match origin:
        case L.Both{L.Both{cfg, L.Both{seed_valid, L.Both{sources, real}}}, judgment}:
          publication_of_call(source, c, world, History.state(history(world), seed(Unit{})), rx, t, w,
            History.history_preserves_validity(c, history(world), seed(Unit{}), seed_valid, sources), real, judgment, fact)
