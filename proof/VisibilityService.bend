# Visibility of the generated real environment: consumes Law6, without new store semantics.
import Base
import ../src/ConfigurationCheck.bend as Config
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Interface.bend as I
import ../contract/Resources.bend as X
import ../contract/Logic.bend as L
import ../contract/LAWS.bend as K
import ./ProtocolService.bend as Q
import ./RoutesService.bend as H
import ./SourceService.bend as Source
import ./PhasesService.bend as Phases
import ./Foundations.bend as F

# Only J substitution of equality with the canonical scenario.
def observe_literal(~source: Source.Source, -x: I.Scenario, -t: Nat, -f: I.Fact) -> Type:
  L.E<{x == Source.scenario(source, Source.world(x)) : I.Scenario}, Source.of_route(source, x, t, f)>

def frames_call(~c: S.Configuration, +s: D.State, reception: X.Reception, data: Source.CallData) -> List<&2, Q.Frame>:
  match data:
    case Source.CallData{cf, pf, cert, terminates, state, tools, micro}:
      H.generate(c, reception, state, s, tools, micro)

def visible_equal(+m: Maybe<&2, D.State>, +s: D.State, h: Q.visible(m, s)) ->
  {m == Some{s} : Maybe<&2, D.State>}:
  match m:
    case None{}: L.ex_false({None{} == Some{s} : Maybe<&2, D.State>}, h)
    case Some{+w}: Equal.cong(D.State, Maybe<&2, D.State>, x => Some{x}, w, s, Equal.sym(D.State, s, w, h))

def visible_in_point(+initial: Maybe<&2, D.State>, +xs: List<&2, Q.Frame>, +t: Nat, +s: D.State,
  h: L.E<{Q.position_observable(xs, t) == True{} : Bool}, Q.visible(Q.state_in(xs, t, initial), s)>) ->
  {Q.state_in(xs, t, initial) == Some{s} : Maybe<&2, D.State>}:
  match h:
    case L.Both{position, content}: visible_equal(Q.state_in(xs, t, initial), s, content)

def origin_of_call(~source: Source.Source, ~c: S.Configuration,
  +s: D.State, +reception: X.Reception, +data: Source.CallData, +t: Nat, +w: D.State,
  h: Source.of_observation(source, c, Source.construct_call(c, s, reception, data), t, I.StateVisible{w})) ->
  Phases.Origin(frames_call(c, s, reception, data), t, s, w):
  match data:
    case Source.CallData{cf, pf, cert, terminates, +state, +tools, +micro}:
      Phases.origin_of_state_visible(t, H.generate(c, reception, state, s, tools, micro), s, w,
        Phases.service_without_start(c, reception, state, s, tools, micro),
        visible_in_point(Some{s}, H.generate(c, reception, state, s, tools, micro), t, w, h))

def introduce_publication_call(~source: Source.Source, ~c: S.Configuration,
  +s: D.State, +reception: X.Reception, +data: Source.CallData, +t: Nat, +w: D.State,
  h: {Q.query(frames_call(c, s, reception, data), t) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}) ->
  Source.of_observation(source, c, Source.construct_call(c, s, reception, data), t, I.Published{w}):
  match data:
    case Source.CallData{cf, pf, cert, terminates, state, tools, micro}:
      Q.query_establishes_observation(c, Source.program(source, pf), H.generate(c, reception, state, s, tools, micro), t, Q.Published{w}, I.Published{w}, h, {==})

def extract_publication_call(~source: Source.Source, ~c: S.Configuration,
  +s: D.State, +reception: X.Reception, +data: Source.CallData, +t: Nat, +w: D.State,
  h: Source.of_observation(source, c, Source.construct_call(c, s, reception, data), t, I.Published{w})) ->
  {Q.query(frames_call(c, s, reception, data), t) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}:
  match data:
    case Source.CallData{cf, pf, cert, terminates, state, tools, micro}:
      Q.observation_frame(c, Source.program(source, pf), H.generate(c, reception, state, s, tools, micro), t, I.Published{w}, h)

def eliminate_publication_source(~source: Source.Source, ~c: S.Configuration, +world: Nat,
  +s: D.State, +reception: X.Reception, +t: Nat, +w: D.State,
  h: I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t, I.Published{w})) ->
  {Q.query(frames_call(c, s, reception, Source.call(source, world)), t) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}:
  F.combined_pair({Q.query(frames_call(c, s, reception, Source.call(source, world)), t) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>},
    {Source.artifact(source) == Source.artifact(source) : String},
    observe_literal(source, I.Serve{world, c, s, reception}, t, I.Published{w}),
    Source.eliminate_fact_literal(source, Source.artifact(source), I.Serve{world, c, s, reception}, t, I.Published{w}, h),
    name => observed =>
      F.combined_pair({Q.query(frames_call(c, s, reception, Source.call(source, world)), t) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>},
        {I.Serve{world, c, s, reception} == Source.scenario(source, world) : I.Scenario},
        Source.of_observation(source, c,
          Source.construct_call(c, s, reception, Source.call(source, world)), t, I.Published{w}), observed,
        scenario => content => extract_publication_call(source, c, s, reception, Source.call(source, world), t, w, content)))

def visible_combined_scenario(~source: Source.Source, ~c: S.Configuration, +world: Nat,
  +s: D.State, +reception: X.Reception, +t: Nat, +w: D.State,
  origin: L.E<{I.Serve{world, c, s, reception} == Source.scenario(source, world) : I.Scenario},
    Source.of_observation(source, c,
      Source.construct_call(c, s, reception, Source.call(source, world)), t, I.StateVisible{w})>) ->
  K.Rule6(I.StateVisible{w}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t):
  match origin:
    case L.Both{scenario, content}:
      Phases.origin_for_rule6(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t,
        frames_call(c, s, reception, Source.call(source, world)), w,
        origin_of_call(source, c, s, reception, Source.call(source, world), t, w, content),
        +u => +v => query_result => Source.introduce_fact(source, Source.artifact(source), I.Serve{world, c, s, reception}, u, I.Published{v}, {==},
          Source.origin_canonical(source, I.Serve{world, c, s, reception}, Source.scenario(source, world), u, I.Published{v}, scenario,
            introduce_publication_call(source, c, s, reception, Source.call(source, world), u, v, query_result))),
        +u => +v => fact => eliminate_publication_source(source, c, world, s, reception, u, v, fact))

law visibility_service_source_obeys_rule6:
  for ~source: Source.Source
  for ~c: S.Configuration
  for +world: Nat
  for +s: D.State
  for +reception: X.Reception
  for +t: Nat
  for +w: D.State
  for fact: I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t, I.StateVisible{w})
  K.Rule6(I.StateVisible{w}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t)
def visibility_service_source_obeys_rule6(source, c, world, s, reception, t, w, fact):
  F.combined_pair(K.Rule6(I.StateVisible{w}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t),
    {Source.artifact(source) == Source.artifact(source) : String},
    observe_literal(source, I.Serve{world, c, s, reception}, t, I.StateVisible{w}),
    Source.eliminate_fact_literal(source, Source.artifact(source), I.Serve{world, c, s, reception}, t, I.StateVisible{w}, fact),
    name => observation => visible_combined_scenario(source, c, world, s, reception, t, w, observation))

def frames_initial(~source: Source.Source, ~c: S.Configuration, +s: D.State, data: Source.InitialData) -> List<&2, Q.Frame>:
  match data:
    case Source.InitialData{cf, sf, pf, judgment, result, micro}: H.generate_result_initial(c, Source.identity(source), s, judgment, result, micro)

def origin_of_initialization(~source: Source.Source, ~c: S.Configuration, +s: D.State,
  +data: Source.InitialData, +t: Nat, +w: D.State,
  h: Source.of_observation(source, c, Source.construct_initial(Source.identity(source), c, s, data), t, I.StateVisible{w})) ->
  Phases.Origin(frames_initial(source, c, s, data), t, s, w):
  match data:
    case Source.InitialData{cf, sf, pf, +judgment, +result, +micro}:
      Phases.origin_of_result_initial_cases(micro, s, judgment, result, Config.is_valid(c, Source.identity(source)), t, w,
        visible_in_point(None{}, H.generate_result_initial(c, Source.identity(source), s, judgment, result, micro), t, w, h))

def introduce_publication_initial(~source: Source.Source, ~c: S.Configuration, +s: D.State,
  +data: Source.InitialData, +t: Nat, +w: D.State,
  h: {Q.query(frames_initial(source, c, s, data), t) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}) ->
  Source.of_observation(source, c, Source.construct_initial(Source.identity(source), c, s, data), t, I.Published{w}):
  match data:
    case Source.InitialData{cf, sf, pf, judgment, result, micro}:
      Q.query_establishes_observation(c, Source.without_program(), H.generate_result_initial(c, Source.identity(source), s, judgment, result, micro), t, Q.Published{w}, I.Published{w}, h, {==})

def extract_publication_initial(~source: Source.Source, ~c: S.Configuration, +s: D.State,
  +data: Source.InitialData, +t: Nat, +w: D.State,
  h: Source.of_observation(source, c, Source.construct_initial(Source.identity(source), c, s, data), t, I.Published{w})) ->
  {Q.query(frames_initial(source, c, s, data), t) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}:
  match data:
    case Source.InitialData{cf, sf, pf, judgment, result, micro}:
      Q.observation_frame(c, Source.without_program(), H.generate_result_initial(c, Source.identity(source), s, judgment, result, micro), t, I.Published{w}, h)

def eliminate_publication_source_initial(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State,
  +pi: String, +t: Nat, +w: D.State,
  h: I.Happens(Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t, I.Published{w})) ->
  {Q.query(frames_initial(source, c, s, Source.initial(source, world)), t) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}:
  F.combined_pair({Q.query(frames_initial(source, c, s, Source.initial(source, world)), t) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>},
    {Source.artifact(source) == Source.artifact(source) : String},
    observe_literal(source, I.Initialize{world, c, s, pi}, t, I.Published{w}),
    Source.eliminate_fact_literal(source, Source.artifact(source), I.Initialize{world, c, s, pi}, t, I.Published{w}, h), name => observed =>
      F.combined_pair({Q.query(frames_initial(source, c, s, Source.initial(source, world)), t) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>},
        {I.Initialize{world, c, s, pi} == Source.scenario(source, world) : I.Scenario},
        Source.of_observation(source, c, Source.construct_initial(Source.identity(source), c, s, Source.initial(source, world)), t, I.Published{w}), observed,
        scenario => content => extract_publication_initial(source, c, s, Source.initial(source, world), t, w, content)))

def initial_visible_combined_scenario(~source: Source.Source, ~c: S.Configuration, +world: Nat,
  +s: D.State, +pi: String, +t: Nat, +w: D.State,
  origin: L.E<{I.Initialize{world, c, s, pi} == Source.scenario(source, world) : I.Scenario},
    Source.of_observation(source, c, Source.construct_initial(Source.identity(source), c, s, Source.initial(source, world)), t, I.StateVisible{w})>) ->
  K.Rule6(I.StateVisible{w}, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t):
  match origin:
    case L.Both{scenario, content}:
      Phases.origin_for_rule6(Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t,
        frames_initial(source, c, s, Source.initial(source, world)), w,
        origin_of_initialization(source, c, s, Source.initial(source, world), t, w, content),
        +u => +v => query_result => Source.introduce_fact(source, Source.artifact(source), I.Initialize{world, c, s, pi}, u, I.Published{v}, {==},
          Source.origin_canonical(source, I.Initialize{world, c, s, pi}, Source.scenario(source, world), u, I.Published{v}, scenario,
            introduce_publication_initial(source, c, s, Source.initial(source, world), u, v, query_result))),
        +u => +v => fact => eliminate_publication_source_initial(source, c, world, s, pi, u, v, fact))

law visibility_initial_source_obeys_rule6:
  for ~source: Source.Source
  for ~c: S.Configuration
  for +world: Nat
  for +s: D.State
  for +pi: String
  for +t: Nat
  for +w: D.State
  for fact: I.Happens(Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t, I.StateVisible{w})
  K.Rule6(I.StateVisible{w}, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t)
def visibility_initial_source_obeys_rule6(source, c, world, s, pi, t, w, fact):
  F.combined_pair(K.Rule6(I.StateVisible{w}, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t),
    {Source.artifact(source) == Source.artifact(source) : String},
    observe_literal(source, I.Initialize{world, c, s, pi}, t, I.StateVisible{w}),
    Source.eliminate_fact_literal(source, Source.artifact(source), I.Initialize{world, c, s, pi}, t, I.StateVisible{w}, fact),
    name => observation => initial_visible_combined_scenario(source, c, world, s, pi, t, w, observation))
