# Links milestones of the unique route to observation, shared by the laws.
import Base
import ../contract/Logic.bend as L
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/Resources.bend as X
import ../contract/Semantics.bend as S
import ./SourceService.bend as Source
import ./ProtocolService.bend as Q
import ./RoutesService.bend as R
import ./Law5Service.bend as Five
import ./VisibilityService.bend as Vis

def Milestone(f: I.Fact) -> Type:
  match f:
    case I.ConfigurationInUse{c}: Empty
    case I.StateVisible{s}: Empty
    case _: Unit

def kind_of_milestone(-c: S.Configuration, -p: S.Program, -ini: Maybe<&2, D.State>,
  -xs: List<&2, Q.Frame>, -t: Nat, f: I.Fact, milestone: Milestone(f)) ->
  {Q.observes_service(c, p, ini, xs, t, f) == Q.observes(c, p, xs, t, f) : Type}:
  match f:
    case I.ConfigurationInUse{c0}: L.ex_false({Q.observes_service(c, p, ini, xs, t, I.ConfigurationInUse{c0}) == Q.observes(c, p, xs, t, I.ConfigurationInUse{c0}) : Type}, milestone)
    case I.StateVisible{s}: L.ex_false({Q.observes_service(c, p, ini, xs, t, I.StateVisible{s}) == Q.observes(c, p, xs, t, I.StateVisible{s}) : Type}, milestone)
    case I.InspectionNotModeled{a0}: {==}
    case I.EffectNotModeled{a0}: {==}
    case I.InstanceStarted{a0}: {==}
    case I.InitializationRefused{a0}: {==}
    case I.ProofInitialAccepts{}: {==}
    case I.Encoded{a0, a1}: {==}
    case I.Decoded{a0, a1}: {==}
    case I.Stored{a0, a1, a2}: {==}
    case I.Operated{a0, a1, a2, a3}: {==}
    case I.CheckedLength{a0, a1}: {==}
    case I.AllocatedField{a0, a1}: {==}
    case I.ReadBody{a0, a1, a2}: {==}
    case I.ReceivedRequest{a0}: {==}
    case I.Authenticated{a0, a1}: {==}
    case I.CertificateAccepted{a0, a1, a2}: {==}
    case I.CertificateRejected{a0, a1}: {==}
    case I.ProgramStarted{a0, a1, a2}: {==}
    case I.Evaluated{a0, a1, a2, a3}: {==}
    case I.Prepared{a0, a1}: {==}
    case I.Published{a0}: {==}
    case I.FailedEnvironment{a0, a1, a2}: {==}
    case I.Concluded{a0, a1, a2}: {==}
    case I.DeliveredEverything{a0}: {==}
    case I.DeliveryInterrupted{a0}: {==}
    case I.ClosedChannel{}: {==}
    case I.NextCall{a0, a1}: {==}

def observe_milestone(-c: S.Configuration, -p: S.Program, -ini: Maybe<&2, D.State>,
  -xs: List<&2, Q.Frame>, -t: Nat, f: I.Fact, milestone: Milestone(f), obs: Q.observes(c, p, xs, t, f)) ->
  Q.observes_service(c, p, ini, xs, t, f):
  %Equal.sym(Type, Q.observes_service(c, p, ini, xs, t, f), Q.observes(c, p, xs, t, f),
    kind_of_milestone(c, p, ini, xs, t, f, milestone)) : _
  obs

def select_milestone(-c: S.Configuration, -p: S.Program, -ini: Maybe<&2, D.State>,
  -xs: List<&2, Q.Frame>, -t: Nat, f: I.Fact, milestone: Milestone(f), obs: Q.observes_service(c, p, ini, xs, t, f)) ->
  Q.observes(c, p, xs, t, f):
  %kind_of_milestone(c, p, ini, xs, t, f, milestone) : _
  obs

def frame_of_call(~source: Source.Source, ~c: S.Configuration,
  +s: D.State, +reception: X.Reception, +data: Source.CallData,
  +world: Nat, +t: Nat, +q: Q.Frame, f: I.Fact,
  same: {data == Source.call(source, world) : Source.CallData},
  query_result: {Q.query(Vis.frames_call(c, s, reception, data), t) == Some{q} : Maybe<&2, Q.Frame>},
  relation: Q.rel_fact(c, Five.program_of_world(source, world), q, f), milestone: Milestone(f)) ->
  Source.of_observation(source, c, Source.construct_call(c, s, reception, data), t, f):
  match data:
    case Source.CallData{cf, +pf, cert, terminates, +state, +tools, +micro}:
      observe_milestone(c, Source.program(source, pf), Some{s},
        R.generate(c, reception, state, s, tools, micro), t, f, milestone,
        Q.query_establishes_observation(c, Source.program(source, pf),
        R.generate(c, reception, state, s, tools, micro), t, q, f, query_result,
        (%Equal.sym(S.Program, Source.program(source, pf), Five.program_of_world(source, world),
            Five.same_root_of_call(source, world,
              Source.CallData{cf, pf, cert, terminates, state, tools, micro}, same)) :
          Q.rel_fact(c, _, q, f) relation)))

# The same fact producer, with the scenario guard opened once.
def introduce_frame(~source: Source.Source, ~c: S.Configuration, +world: Nat,
  +s: D.State, +reception: X.Reception, +t: Nat, +q: Q.Frame, f: I.Fact,
  canonical: {I.Serve{world, c, s, reception} == Source.scenario(source, world) : I.Scenario},
  query_result: {Q.query(Vis.frames_call(c, s, reception, Source.call(source, world)), t) == Some{q} : Maybe<&2, Q.Frame>},
  relation: Q.rel_fact(c, Five.program_of_world(source, world), q, f), milestone: Milestone(f)) ->
  I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t, f):
  Source.introduce_fact(source, Source.artifact(source), I.Serve{world, c, s, reception}, t, f, {==},
    Source.origin_canonical(source, I.Serve{world, c, s, reception}, Source.scenario(source, world), t, f, canonical,
      frame_of_call(source, c, s, reception, Source.call(source, world), world, t, q, f, {==}, query_result, relation, milestone)))


def frame_of_observation(~source: Source.Source, ~c: S.Configuration,
  +s: D.State, +reception: X.Reception, +data: Source.CallData, +t: Nat,
  f: I.Fact, milestone: Milestone(f),
  obs: Source.of_observation(source, c, Source.construct_call(c, s, reception, data), t, f)) ->
  {Q.query(Vis.frames_call(c, s, reception, data), t) == Some{Q.frame_of_fact(f)} : Maybe<&2, Q.Frame>}:
  match data:
    case Source.CallData{cf, pf, cert, terminates, +state, +tools, +micro}:
      Q.observation_frame(c, Source.program(source, pf), R.generate(c, reception, state, s, tools, micro), t, f,
        select_milestone(c, Source.program(source, pf), Some{s}, R.generate(c, reception, state, s, tools, micro), t, f, milestone, obs))

def frame_by_guards(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +s: D.State, +reception: X.Reception, +t: Nat, f: I.Fact, milestone: Milestone(f),
  input: L.E<{Source.artifact(source) == Source.artifact(source) : String},
    L.E<{I.Serve{world, c, s, reception} == Source.scenario(source, world) : I.Scenario},
      Source.of_route(source, I.Serve{world, c, s, reception}, t, f)>>) ->
  {Q.query(Vis.frames_call(c, s, reception, Source.call(source, world)), t) ==
    Some{Q.frame_of_fact(f)} : Maybe<&2, Q.Frame>}:
  match input:
    case L.Both{name, L.Both{canonical, obs}}:
      frame_of_observation(source, c, s, reception, Source.call(source, world), t, f, milestone, obs)

def extract_frame(~source: Source.Source, ~c: S.Configuration, +world: Nat,
  +s: D.State, +reception: X.Reception, +t: Nat, f: I.Fact, milestone: Milestone(f),
  obs: I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t, f)) ->
  {Q.query(Vis.frames_call(c, s, reception, Source.call(source, world)), t) ==
    Some{Q.frame_of_fact(f)} : Maybe<&2, Q.Frame>}:
  frame_by_guards(source, c, world, s, reception, t, f, milestone,
    Source.eliminate_fact_literal(source, Source.artifact(source), I.Serve{world, c, s, reception}, t, f, obs))

# Associativity of the same list leaves facts unchanged; no host function is assumed here.
def introduce_in_list(~source: Source.Source, ~c: S.Configuration, +world: Nat,
  +s: D.State, +reception: X.Reception, +xs: List<&2, Q.Frame>, +t: Nat, +q: Q.Frame,
  f: I.Fact, canonical: {I.Serve{world, c, s, reception} == Source.scenario(source, world) : I.Scenario},
  same: {Vis.frames_call(c, s, reception, Source.call(source, world)) == xs : List<&2, Q.Frame>},
  query_result: {Q.query(xs, t) == Some{q} : Maybe<&2, Q.Frame>},
  relation: Q.rel_fact(c, Five.program_of_world(source, world), q, f), milestone: Milestone(f)) ->
  I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t, f):
  introduce_frame(source, c, world, s, reception, t, q, f, canonical,
    (%Equal.sym(List<&2, Q.Frame>, Vis.frames_call(c, s, reception, Source.call(source, world)), xs, same) :
      {Q.query(_, t) == Some{q} : Maybe<&2, Q.Frame>} query_result), relation, milestone)

def extract_in_list(~source: Source.Source, ~c: S.Configuration, +world: Nat,
  +s: D.State, +reception: X.Reception, +xs: List<&2, Q.Frame>, +t: Nat, f: I.Fact,
  same: {Vis.frames_call(c, s, reception, Source.call(source, world)) == xs : List<&2, Q.Frame>},
  milestone: Milestone(f), obs: I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t, f)) ->
  {Q.query(xs, t) == Some{Q.frame_of_fact(f)} : Maybe<&2, Q.Frame>}:
  %same : {Q.query(_, t) == Some{Q.frame_of_fact(f)} : Maybe<&2, Q.Frame>}
  extract_frame(source, c, world, s, reception, t, f, milestone, obs)

# Data projections; the route is exactly the one already observed by Source.
def micro_of_data(data: Source.CallData) -> R.Micro:
  match data:
    case Source.CallData{cf, pf, cert, terminates, be, tools, micro}: micro

def branch_of_data(~c: S.Configuration, reception: X.Reception, data: Source.CallData) -> R.Branch:
  match data:
    case Source.CallData{cf, pf, cert, terminates, be, tools, micro}: R.decide(c, reception, be, tools)

law frames_follow_o_branch:
  for ~c: S.Configuration
  for +s: D.State
  for +reception: X.Reception
  for +data: Source.CallData
  {Vis.frames_call(c, s, reception, data) ==
    R.render(micro_of_data(data), s, branch_of_data(c, reception, data)) : List<&2, Q.Frame>}
def frames_follow_o_branch(c, s, reception, data):
  match data:
    case Source.CallData{cf, pf, cert, terminates, be, tools, micro}: {==}
