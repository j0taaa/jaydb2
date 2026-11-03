# Observed-field bindings; the check follows from the actual Codec generator.
import Base
import ./SourceService.bend as Source
import ./RoutesService.bend as Route
import ../contract/Resources.bend as X
import ../contract/Bytes.bend as B
import ../contract/Protocol.bend as P
import ../src/Codec.bend as Codec
import ./PrimitivesService.bend as M
import ./CodecLaw2.bend as CodecLaw2
import ./CodecRefusals.bend as Refusals
import ./Representation.bend as Representation
import ./Foundations.bend as Foundations
import ../src/State.bend as State
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/LAWS.bend as K
import ../contract/Logic.bend as L
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as Requirements
import ./FieldsService.bend as C
import ./ProtocolService.bend as Q
import ./ExecutionService.bend as E
import ./Law5Service.bend as Five
import ./ReceptionLimits.bend as Reading
import ./ModelService.bend as Model
import ./ScenariosService.bend as Scenarios
import ./HistoryService.bend as History
import ./Call.bend as Call
import ../src/Core.bend as N
import ../src/Input.bend as Input
import ../src/Transport.bend as Transport
import ../src/ConfigurationCheck.bend as Configuration

# Local order witnesses, then lifted into the source environment.
def Before(-ob: Nat -> I.Fact -> Type, -t: Nat, -f: I.Fact) -> Type:
  &b: Nat -> L.E<{Nat.is_lt(b, t) == True{} : Bool}, ob(b, f)>

# Pure fact content. Reads and order are treated separately.
def Content(~c: S.Configuration, +x: Source.Context, q: Q.Frame) -> Type:
  match q:
    case Q.Encoded{v, bs}: {bs == P.encode(v) : Maybe<&2, List<&2, U32>>}
    case Q.Decoded{bs, v}: I.DecodingCorrect(bs, v)
    case Q.Stored{s, bs, abstr}: {abstr == s : D.State}
    case Q.Operated{e, s, o, r}: {r == D.operate(e, s, o) : D.ResultOp}
    case Q.Received{r}: I.RequestReceived(Source.scenario_context(c, x), r)
    case Q.Read{before, n, declared}: K.ReadBounded(Source.scenario_context(c, x), before, n, declared)
    case _: Unit

def Contents(~c: S.Configuration, +x: Source.Context, qs: List<&2, Q.Frame>) -> Type:
  match qs:
    case Nil{}: Unit
    case Con{h, t}: L.E<Content(c, x, h), Contents(c, x, t)>

def concatenate_contents(~c: S.Configuration, +x: Source.Context, xs: List<&2, Q.Frame>, -ys: List<&2, Q.Frame>, a: Contents(c, x, xs), b: Contents(c, x, ys)) ->
  Contents(c, x, Q.concatenate(xs, ys)):
  match xs a:
    case Nil{} _: b
    case Con{h, t} L.Both{head, tail}: L.Both{head, concatenate_contents(c, x, t, ys, tail, b)}

def construct_content(~c: S.Configuration, +x: Source.Context, check: Codec.Check, -pos: Nat, -n: Nat) -> Contents(c, x, M.construct(check, pos, n)):
  match check:
    case Codec.Fits{}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}
    case Codec.Short{}: Unit{}
    case Codec.Large{}: Unit{}

def opening_content(~c: S.Configuration, +x: Source.Context, check: Codec.Check, ready: Bool, -pos: Nat, -n: Nat) ->
  Contents(c, x, M.open_field(check, ready, pos, n)):
  match check ready:
    case Codec.Fits{} True{}: construct_content(c, x, Codec.Fits{}, pos, n)
    case Codec.Fits{} False{}: L.Both{Unit{}, Unit{}}
    case Codec.Short{} _: Unit{}
    case Codec.Large{} _: Unit{}

def field_content(~c: S.Configuration, +x: Source.Context, +pos: Nat, +f: Codec.Purpose, +high: U32, +low: U32,
  +stack: Codec.Stack, +body: B.Number64, +ceiling: B.Number64) ->
  Contents(c, x, M.frame_field(pos, f, high, low, stack, body, ceiling)):
  opening_content(c, x, M.check(f, high, low, stack, body, ceiling), M.open_name_valid(f, high, low), pos, M.count(high, low))

def tag_content(~c: S.Configuration, +x: Source.Context, tag: Nat, -pos: Nat) -> Contents(c, x, M.frame_tag(tag, pos)):
  match tag:
    case 0n: construct_content(c, x, Codec.Fits{}, pos, 1n)
    case 1n: construct_content(c, x, Codec.Fits{}, pos, 1n)
    case 2n: construct_content(c, x, Codec.Fits{}, pos, 1n)
    case 3n+k: Unit{}

def word_content(~c: S.Configuration, +x: Source.Context, f: Codec.Purpose, +high: U32, +low: U32, +stack: Codec.Stack,
  +body: B.Number64, +ceiling: B.Number64, +pos: Nat) -> Contents(c, x, M.frame_word(f, high, low, stack, body, ceiling, pos)):
  match f:
    case Codec.Integer{}: construct_content(c, x, Codec.Fits{}, pos, 8n)
    case Codec.TextValue{}: field_content(c, x, pos, Codec.TextValue{}, high, low, stack, body, ceiling)
    case Codec.NameText{}: field_content(c, x, pos, Codec.NameText{}, high, low, stack, body, ceiling)
    case Codec.CountsList{}: field_content(c, x, pos, Codec.CountsList{}, high, low, stack, body, ceiling)
    case Codec.CountsRecord{}: field_content(c, x, pos, Codec.CountsRecord{}, high, low, stack, body, ceiling)

def step_content(~c: S.Configuration, +x: Source.Context, m: Codec.Machine, +b: U32, +body: B.Number64, +ceiling: B.Number64, +pos: Nat) ->
  Contents(c, x, M.frame_step(m, b, body, ceiling, pos)):
  match m:
    case Codec.Tag{stack}: tag_content(c, x, U32.to_nat(b), pos)
    case Codec.WordInput{f, 0n, high, +low, stack}:
      word_content(c, x, f, (high * 256 + U32.shrn(low, 24n) : U32), (low * 256 + b : U32), stack, body, ceiling, pos)
    case Codec.WordInput{f, 1n+k, high, low, stack}: Unit{}
    case Codec.TagName{stack}: Unit{}
    case Codec.Content{name, last, q, u, text, stack}: Unit{}
    case Codec.DecodedReady{v}: Unit{}
    case Codec.Invalid{}: Unit{}
    case Codec.Above{}: Unit{}

law content_of_parser_comes_of_functions_real:
  for ~c: S.Configuration
  for +x: Source.Context
  for bs: List<&2, U32>
  for +m: Codec.Machine
  for +body: B.Number64
  for +ceiling: B.Number64
  for +pos: Nat
  Contents(c, x, M.frames_codec(bs, m, body, ceiling, pos))
def content_of_parser_comes_of_functions_real(c, x, bs, m, body, ceiling, pos):
  match bs:
    case Nil{}: Unit{}
    case Con{+b, +t}:
      concatenate_contents(c, x, M.frame_step(m, b, Codec.decrease64(body), Codec.decrease64(ceiling), pos),
        M.frames_codec(t, Codec.step(m, b, Codec.decrease64(body), Codec.decrease64(ceiling)), Codec.decrease64(body), Codec.decrease64(ceiling), Succ{pos}),
        step_content(c, x, m, b, Codec.decrease64(body), Codec.decrease64(ceiling), pos),
        content_of_parser_comes_of_functions_real(c, x, t, Codec.step(m, b, Codec.decrease64(body), Codec.decrease64(ceiling)), Codec.decrease64(body), Codec.decrease64(ceiling), Succ{pos}))

def decoding_admitted_content(~c: S.Configuration, +x: Source.Context, ok: Bool, +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64,
  measured: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>},
  decision: {Codec.less_equal64(body, ceiling) && B.octets_all_valid(bs) == ok : Bool}) ->
  Contents(c, x, M.decoding_admitted(ok, bs, body, ceiling)):
  match ok:
    case False{}: Unit{}
    case True{}:
      concatenate_contents(c, x, M.frames_codec(bs, Codec.Tag{Codec.Root{}}, body, ceiling, 0n),
        [Q.Decoded{bs, Refusals.optional(Codec.decode(bs, ceiling))}],
        content_of_parser_comes_of_functions_real(c, x, bs, Codec.Tag{Codec.Root{}}, body, ceiling, 0n),
        L.Both{CodecLaw2.decode_satisfies_relation_original(bs, body, ceiling, measured,
          Foundations.and_boolean_left(Codec.less_equal64(body, ceiling), B.octets_all_valid(bs), decision)), Unit{}})

def decoding_measure_content(~c: S.Configuration, +x: Source.Context, q: Maybe<&2, B.Number64>, +bs: List<&2, U32>, +ceiling: B.Number64,
  measure: {B.nat64(B.length(bs)) == q : Maybe<&2, B.Number64>}) -> Contents(c, x, M.decoding_measure(q, bs, ceiling)):
  match q:
    case None{}: Unit{}
    case Some{+body}:
      decoding_admitted_content(c, x, Codec.less_equal64(body, ceiling) && B.octets_all_valid(bs), bs, body, ceiling, measure, {==})

def storage_abstract_content(~c: S.Configuration, +x: Source.Context, q: Maybe<&2, D.State>, +s: D.State, -bs: List<&2, U32>,
  exact: {q == Some{s} : Maybe<&2, D.State>}) -> Contents(c, x, M.store_abstraction(q, s, bs)):
  match q:
    case None{}: Unit{}
    case Some{a}:
      L.Both{Foundations.some_injective(D.State, a, s, exact), Unit{}}

def storage_content(~c: S.Configuration, +x: Source.Context, q: Maybe<&2, List<&2, U32>>, +e: D.Schema, +s: D.State,
  structure: {D.structure(e, s) == True{} : Bool}) -> Contents(c, x, M.store_bytes(q, e, s)):
  match q:
    case None{}: Unit{}
    case Some{bs}: storage_abstract_content(c, x, State.decode(D.state_value(s), e), s, bs,
      Representation.transport_private_preserves_state(e, s, structure))

def first_contents(~c: S.Configuration, +x: Source.Context, n: Nat, qs: List<&2, Q.Frame>, contents: Contents(c, x, qs)) -> Contents(c, x, Q.first(n, qs)):
  match n qs:
    case 0n _: Unit{}
    case 1n+k Nil{}: Unit{}
    case 1n+k Con{h, t}:
      match contents:
        case L.Both{head, tail}: L.Both{head, first_contents(c, x, k, t, tail)}

def HeaderMeasured(input: X.Reception, -declared: Nat) -> Type:
  match input:
    case X.BodyTruncated{high, low, body}: {B.nat64(declared) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
    case X.BodyReceived{high, low, body}: {B.nat64(declared) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
    case _: Empty

def ReadReal(~c: S.Configuration, +x: Source.Context, -before: Nat, -cap: Nat, -received: Nat, -declared: Nat) -> Type:
  match x:
    case Source.Initial{world, s, pi}: Empty
    case Source.Service{world, s, input}:
      L.E<HeaderMeasured(input, declared),
        L.E<{Nat.is_le(before, declared) == True{} : Bool},
          L.E<{Nat.is_le(received, Nat.min(cap, Nat.sub(declared, before))) == True{} : Bool},
            {Nat.is_le(declared, Requirements.limit_message(S.limits(c))) == True{} : Bool}>>>

def declaration_measure(~c: S.Configuration, input: X.Reception, +declared: Nat, measure: HeaderMeasured(input, declared)) ->
  K.LengthDeclared(input, declared):
  match input:
    case X.BodyTruncated{+high, +low, body}: Reading.header_measured_establishes_declaration_original(high, low, declared, measure)
    case X.BodyReceived{+high, +low, body}: Reading.header_measured_establishes_declaration_original(high, low, declared, measure)
    case X.EOFBetweenMessages{}: measure
    case X.StoppedOperator{}: measure
    case X.HeaderTruncated{bs}: measure

def reading_has_content(~c: S.Configuration, +x: Source.Context, +before: Nat, +cap: Nat, +received: Nat, +declared: Nat,
  real: ReadReal(c, x, before, cap, received, declared)) -> K.ReadBounded(Source.scenario_context(c, x), before, received, declared):
  match x:
    case Source.Initial{world, s, pi}: L.ex_false(K.ReadBounded(I.Initialize{world, c, s, pi}, before, received, declared), real)
    case Source.Service{world, s, +input}:
      match real:
        case L.Both{measure, L.Both{existing, L.Both{real, admitted}}}:
          L.Both{declaration_measure(c, input, declared, measure),
            Reading.consumption_confirmed_respects_declared_and_limit(declared, before, cap, received,
              Requirements.limit_message(S.limits(c)), existing, real, admitted)}

# Requires only the storage decoder's concrete prerequisite.
# Published validity derives from history and certificate, not this type.
# Store is not a test on every private mutation; working states with
# empty/duplicate credentials do not pass through this snapshot decoder.
def OriginPrimitive(~c: S.Configuration, +x: Source.Context, q: M.Primitive) -> Type:
  match q:
    case M.Prefix{n, p}: OriginPrimitive(c, x, p)
    case M.Store{e, s}: {D.structure(e, s) == True{} : Bool}
    case M.Read{before, cap, received, declared}: ReadReal(c, x, before, cap, received, declared)
    case _: Unit

law primitives_produce_content_exact:
  for ~c: S.Configuration
  for +x: Source.Context
  for q: M.Primitive
  for origin: OriginPrimitive(c, x, q)
  Contents(c, x, M.expand(q))
def primitives_produce_content_exact(c, x, q, origin):
  match q:
    case M.Prefix{n, +p}: first_contents(c, x, n, M.expand(p), primitives_produce_content_exact(c, x, p, origin))
    case M.Encode{v}: L.Both{{==}, Unit{}}
    case M.Decode{+bs, +ceiling}: decoding_measure_content(c, x, B.nat64(B.length(bs)), bs, ceiling, {==})
    case M.Store{e, +s}: storage_content(c, x, P.encode(D.state_value(s)), e, s, origin)
    case M.Read{+before, +cap, +received, +declared}:
      L.Both{reading_has_content(c, x, before, cap, received, declared, origin), Unit{}}

def OriginsPrimitives(~c: S.Configuration, +x: Source.Context, ps: List<&2, M.Primitive>) -> Type:
  match ps:
    case Nil{}: Unit
    case Con{h, t}: L.E<OriginPrimitive(c, x, h), OriginsPrimitives(c, x, t)>

law content_of_all_primitives_and_exact:
  for ~c: S.Configuration
  for +x: Source.Context
  for ps: List<&2, M.Primitive>
  for origin: OriginsPrimitives(c, x, ps)
  Contents(c, x, M.expand_primitives(ps))
def content_of_all_primitives_and_exact(c, x, ps, origin):
  match ps origin:
    case Nil{} _: Unit{}
    case Con{+h, +t} L.Both{head, tail}:
      concatenate_contents(c, x, M.expand(h), M.expand_primitives(t),
        primitives_produce_content_exact(c, x, h, head), content_of_all_primitives_and_exact(c, x, t, tail))

law content_of_query:
  for ~c: S.Configuration
  for +x: Source.Context
  for qs: List<&2, Q.Frame>
  for t: Nat
  for -q: Q.Frame
  for contents: Contents(c, x, qs)
  for query_result: {Q.query(qs, t) == Some{q} : Maybe<&2, Q.Frame>}
  Content(c, x, q)
def content_of_query(c, x, qs, t, q, contents, query_result):
  match qs t:
    case Nil{} _: L.ex_false(Content(c, x, q), Foundations.none_negative_some(Q.Frame, q, query_result))
    case Con{+h, rest} 0n:
      match contents:
        case L.Both{head, tail}:
          %Foundations.some_injective(Q.Frame, h, q, query_result) : Content(c, x, _)
          head
    case Con{h, rest} 1n+n:
      match contents:
        case L.Both{head, tail}: content_of_query(c, x, rest, n, q, tail, query_result)

# Check observed on the same route; not a Rule2 hypothesis.
def record_pure(-c: S.Configuration, -p: S.Program, +ini: Maybe<&2, D.State>,
  +qs: List<&2, Q.Frame>, -t: Nat, +pos: Nat, +n: Nat, before: C.BeforeOfField(qs, t, pos, n)) ->
  Before(E.observation_model(c, p, ini, qs), t, I.CheckedLength{pos, n}):
  match before:
    case (+b, L.Both{order, query_result}):
      (b, L.Both{order, Q.query_establishes_observation(c, p, qs, b, Q.Checked{pos, n}, I.CheckedLength{pos, n}, query_result, {==})})

def field_pure(-c: S.Configuration, -p: S.Program, +ini: Maybe<&2, D.State>,
  +qs: List<&2, Q.Frame>, +t: Nat, +pos: Nat, +n: Nat, safe: C.FieldsSafe(qs),
  fact: Q.observes_service(c, p, ini, qs, t, I.AllocatedField{pos, n})) ->
  Before(E.observation_model(c, p, ini, qs), t, I.CheckedLength{pos, n}):
  record_pure(c, p, ini, qs, t, pos, n, safe(t, pos, n,
    Q.observation_frame(c, p, qs, t, I.AllocatedField{pos, n}, fact)))

def BeforeOrigin(~source: Source.Source, -c: S.Configuration, -ini: Maybe<&2, D.State>,
  -qs: List<&2, Q.Frame>, -origin: Maybe<&2, Source.JudgmentSyntactic>, -t: Nat, -pos: Nat, -n: Nat) -> Type:
  &b: Nat -> L.E<{Nat.is_lt(b, t) == True{} : Bool}, Source.of_origin(source, c, ini, qs, origin, b, I.CheckedLength{pos, n})>

def field_of_origin(~source: Source.Source, -c: S.Configuration, +ini: Maybe<&2, D.State>,
  +qs: List<&2, Q.Frame>, origin: Maybe<&2, Source.JudgmentSyntactic>, +t: Nat, +pos: Nat, +n: Nat,
  safe: C.FieldsSafe(qs), fact: Source.of_origin(source, c, ini, qs, origin, t, I.AllocatedField{pos, n})) ->
  BeforeOrigin(source, c, ini, qs, origin, t, pos, n):
  match origin:
    case None{}: field_pure(c, Source.without_program(), ini, qs, t, pos, n, safe, fact)
    case Some{origin}: field_pure(c, Source.program(source, origin), ini, qs, t, pos, n, safe, fact)

def BeforeObservation(~source: Source.Source, -c: S.Configuration, -d: Source.ObservationData, -t: Nat, -pos: Nat, -n: Nat) -> Type:
  &b: Nat -> L.E<{Nat.is_lt(b, t) == True{} : Bool}, Source.of_observation(source, c, d, b, I.CheckedLength{pos, n})>

def FieldsOfObservation(d: Source.ObservationData) -> Type:
  match d:
    case Source.ObservationData{ini, qs, origin}: C.FieldsSafe(qs)

def field_of_observation(~source: Source.Source, -c: S.Configuration, d: Source.ObservationData,
  +t: Nat, +pos: Nat, +n: Nat, safe: FieldsOfObservation(d),
  fact: Source.of_observation(source, c, d, t, I.AllocatedField{pos, n})) -> BeforeObservation(source, c, d, t, pos, n):
  match d:
    case Source.ObservationData{ini, qs, origin}: field_of_origin(source, c, ini, qs, origin, t, pos, n, safe, fact)

def fields_of_call(~c: S.Configuration, +s: D.State, +reception: X.Reception, data: Source.CallData) ->
  FieldsOfObservation(Source.construct_call(c, s, reception, data)):
  match data:
    case Source.CallData{cf, pf, cert, terminates, state, tools, +micro}:
      C.protocol_checks_fields_before_of_construct(micro, s, Route.decide(c, reception, state, tools))

def fields_of_start(~source: Source.Source, ~c: S.Configuration, +s: D.State, data: Source.InitialData) ->
  FieldsOfObservation(Source.construct_initial(Source.identity(source), c, s, data)):
  match data:
    case Source.InitialData{cf, sf, pf, judgment, result, +micro}:
      C.protocol_checks_fields_before_of_construct(micro, s, Route.decide_result_initial(c, Source.identity(source), judgment, result))

# One renderer content proof: Codec, reads, requests and operations.
def OriginsMicro(~c: S.Configuration, +x: Source.Context, m: Route.Micro) -> Type:
  match m:
    case Route.Micro{a, b, d, e}:
      L.E<OriginsPrimitives(c, x, a), L.E<OriginsPrimitives(c, x, b),
        L.E<OriginsPrimitives(c, x, d), OriginsPrimitives(c, x, e)>>>

def execution_generated_content(~c: S.Configuration, +x: Source.Context, +r: P.Request, +ctx: D.Context,
  n: Nat, m: N.Machine, +e: D.Schema) -> Contents(c, x, Q.expand_exec(r, ctx, E.generate(n, m, e))):
  match n m:
    case _ N.Stopped{w, ts, response}: L.Both{Unit{}, Unit{}}
    case 0n N.Running{w, a, ts}: L.Both{Unit{}, Unit{}}
    case 1n+j N.Running{+w, a, +ts}:
      match a:
        case S.Finish{v}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}
        case S.Refuse{v}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}
        case S.Access{+o, k}:
          L.Both{Unit{}, L.Both{{==}, execution_generated_content(c, x, r, ctx, j,
            N.step_machine(S.apply(D.operate(e, w, o), w, o, k), ts), e)}}

def execution_real_content(~source: Source.Source, ~c: S.Configuration, +x: Source.Context,
  +s: D.State, +origin: Source.JudgmentSyntactic, +r: P.Request, +ctx: D.Context,
  +xs: List<&2, Q.FrameExec>, real: Source.PrefixReal(source, c, s, r, ctx, origin, xs)) ->
  Contents(c, x, Q.expand_exec(r, ctx, xs)):
  match real:
    case (+n, equal):
      %Equal.sym(List<&2, Q.FrameExec>, xs, E.generate(n, N.start(Source.program(source, origin), ctx, I.arguments(r), s), S.schema(c)), equal) :
        Contents(c, x, Q.expand_exec(r, ctx, _))
      execution_generated_content(c, x, r, ctx, n, N.start(Source.program(source, origin), ctx, I.arguments(r), s), S.schema(c))

def received_content(~c: S.Configuration, +x: Source.Context, +m: Route.Micro, +r: P.Request,
  a: Contents(c, x, Route.micro_input(m)), command: I.RequestReceived(Source.scenario_context(c, x), r)) ->
  Contents(c, x, Route.render_received(m, r)):
  concatenate_contents(c, x, Route.micro_input(m), [Q.Received{r}], a, L.Both{command, Unit{}})

def authenticated_content(~c: S.Configuration, +x: Source.Context, +m: Route.Micro, +r: P.Request, +ctx: D.Context,
  a: Contents(c, x, Route.micro_input(m)), b: Contents(c, x, Route.micro_authentication(m)),
  command: I.RequestReceived(Source.scenario_context(c, x), r)) -> Contents(c, x, Route.render_authenticated(m, r, ctx)):
  concatenate_contents(c, x, Route.render_received(m, r), Q.concatenate(Route.micro_authentication(m), [Q.Authenticated{r, Some{ctx}}]),
    received_content(c, x, m, r, a, command), concatenate_contents(c, x, Route.micro_authentication(m), [Q.Authenticated{r, Some{ctx}}], b, L.Both{Unit{}, Unit{}}))

def verified_content(~c: S.Configuration, +x: Source.Context, +m: Route.Micro, +r: P.Request, +ctx: D.Context,
  a: Contents(c, x, Route.micro_input(m)), b: Contents(c, x, Route.micro_authentication(m)),
  command: I.RequestReceived(Source.scenario_context(c, x), r)) -> Contents(c, x, Route.render_verified(m, r, ctx)):
  concatenate_contents(c, x, Route.render_authenticated(m, r, ctx), [Q.Accepts{r, ctx}],
    authenticated_content(c, x, m, r, ctx, a, b, command), L.Both{Unit{}, Unit{}})

def started_content(~c: S.Configuration, +x: Source.Context, +m: Route.Micro, +r: P.Request, +ctx: D.Context,
  a: Contents(c, x, Route.micro_input(m)), b: Contents(c, x, Route.micro_authentication(m)),
  d: Contents(c, x, Route.micro_execution(m)), command: I.RequestReceived(Source.scenario_context(c, x), r)) ->
  Contents(c, x, Route.render_started(m, r, ctx)):
  concatenate_contents(c, x, Route.render_verified(m, r, ctx), Q.concatenate(Route.micro_execution(m), [Q.Started{r, ctx}]),
    verified_content(c, x, m, r, ctx, a, b, command), concatenate_contents(c, x, Route.micro_execution(m), [Q.Started{r, ctx}], d, L.Both{Unit{}, Unit{}}))

def executed_content(~source: Source.Source, ~c: S.Configuration, +x: Source.Context, +m: Route.Micro,
  +s: D.State, +origin: Source.JudgmentSyntactic, +r: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>,
  real: Source.PrefixReal(source, c, s, r, ctx, origin, xs), command: I.RequestReceived(Source.scenario_context(c, x), r),
  a: Contents(c, x, Route.micro_input(m)), b: Contents(c, x, Route.micro_authentication(m)), d: Contents(c, x, Route.micro_execution(m))) ->
  Contents(c, x, Route.render_execution(m, r, ctx, xs)):
  concatenate_contents(c, x, Route.render_started(m, r, ctx), Q.expand_exec(r, ctx, xs),
    started_content(c, x, m, r, ctx, a, b, d, command), execution_real_content(source, c, x, s, origin, r, ctx, xs, real))

def later_delivery_content(~c: S.Configuration, +x: Source.Context, closes: Bool, -s: D.State, next: Bool) ->
  Contents(c, x, Route.later_delivery(closes, s, next)):
  match closes next:
    case True{} _: L.Both{Unit{}, Unit{}}
    case False{} True{}: L.Both{Unit{}, Unit{}}
    case False{} False{}: Unit{}

def delivery_content(~c: S.Configuration, +x: Source.Context, +s: D.State, +bs: List<&2, U32>, +closes: Bool, delivery: Route.Delivery) ->
  Contents(c, x, Route.render_delivery(s, bs, closes, delivery)):
  match delivery:
    case Route.Complete{next}: L.Both{Unit{}, later_delivery_content(c, x, closes, s, next)}
    case Route.Broken{prefix}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}
    case Route.PendingDelivery{}: Unit{}

def publication_content(~c: S.Configuration, +x: Source.Context, r: S.Response, -s: D.State) ->
  Contents(c, x, Route.render_publication(r, s)):
  match r:
    case S.Response{S.Success{}, v}: L.Both{Unit{}, Unit{}}
    case S.Response{S.Refusal{}, v}: Unit{}
    case S.Response{S.Input{}, v}: Unit{}
    case S.Response{S.Authentication{}, v}: Unit{}
    case S.Response{S.Certificate{}, v}: Unit{}
    case S.Response{S.DataError{}, v}: Unit{}
    case S.Response{S.Limit{}, v}: Unit{}
    case S.Response{S.Failure{}, v}: Unit{}

def conclusion_content(~c: S.Configuration, +x: Source.Context, conclusion: N.Conclusion, +closes: Bool, delivery: Route.Delivery) ->
  Contents(c, x, Route.render_conclusion(conclusion, closes, delivery)):
  match conclusion:
    case N.Conclusion{+s, +r, +bs}:
      L.Both{Unit{}, concatenate_contents(c, x, Route.render_publication(r, s), Con{Q.Completed{r, s, closes}, Route.render_delivery(s, bs, closes, delivery)},
        publication_content(c, x, r, s), L.Both{Unit{}, delivery_content(c, x, s, bs, closes, delivery)})}

def error_framed_content(~c: S.Configuration, +x: Source.Context, q: Maybe<&2, List<&2, U32>>, +r: S.Response,
  +s: D.State, +closes: Bool, delivery: Route.Delivery) -> Contents(c, x, Route.render_error_framed(q, r, s, closes, delivery)):
  match q:
    case None{}: Unit{}
    case Some{+bs}: L.Both{Unit{}, L.Both{Unit{}, delivery_content(c, x, s, bs, closes, delivery)}}

def error_content(~c: S.Configuration, +x: Source.Context, +status: S.Status, +s: D.State, +closes: Bool, delivery: Route.Delivery) ->
  Contents(c, x, Route.render_error(status, s, closes, delivery)):
  error_framed_content(c, x, P.frame(S.response_value(S.response_error(status))), S.response_error(status), s, closes, delivery)

def failure_content(~c: S.Configuration, +x: Source.Context, +s: D.State, +stage: X.Stage, +id: String, fatal: Bool, +delivery: Route.Delivery) ->
  Contents(c, x, Route.render_failure(s, stage, id, fatal, delivery)):
  match fatal:
    case True{}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}
    case False{}: L.Both{Unit{}, error_content(c, x, S.Failure{}, s, False{}, delivery)}

def fatal_published_content(~c: S.Configuration, +x: Source.Context, conclusion: N.Conclusion, +stage: X.Stage, +id: String) ->
  Contents(c, x, Route.render_fatal_published(conclusion, stage, id)):
  match conclusion:
    case N.Conclusion{+s, +r, bs}:
      L.Both{Unit{}, concatenate_contents(c, x, Route.render_publication(r, s), [Q.Failed{stage, id, True{}}, Q.Closed{}],
        publication_content(c, x, r, s), L.Both{Unit{}, L.Both{Unit{}, Unit{}}})}

def initial_content(~c: S.Configuration, +x: Source.Context, q: Maybe<&2, List<&2, U32>>, +s: D.State,
  exact: {q == P.encode(D.state_value(s)) : Maybe<&2, List<&2, U32>>}) -> Contents(c, x, Route.render_initial(q, s)):
  match q:
    case None{}: L.Both{exact, Unit{}}
    case Some{bs}: L.Both{exact, L.Both{{==}, L.Both{Unit{}, Unit{}}}}

def prepared_content(~c: S.Configuration, +x: Source.Context, p: N.Prepared) -> Contents(c, x, [Route.frame_prepared(p)]):
  match p:
    case N.Prepared{w, ts, r, bs}: L.Both{Unit{}, Unit{}}

def phase_content(~source: Source.Source, ~c: S.Configuration, +x: Source.Context, +m: Route.Micro,
  +s: D.State, +origin: Source.JudgmentSyntactic, phase: Route.PhaseBefore,
  real: Five.PhaseReal(source, c, s, origin, phase), command: Source.RequestOfPhase(c, x, phase),
  a: Contents(c, x, Route.micro_input(m)), b: Contents(c, x, Route.micro_authentication(m)),
  d: Contents(c, x, Route.micro_execution(m)), e: Contents(c, x, Route.micro_output(m))) -> Contents(c, x, Route.render_phase(m, phase)):
  match phase:
    case Route.BeforeInput{}: a
    case Route.AfterReceive{r}: received_content(c, x, m, r, a, command)
    case Route.AfterAuthenticate{r, ctx}: authenticated_content(c, x, m, r, ctx, a, b, command)
    case Route.AfterVerify{r, ctx}: verified_content(c, x, m, r, ctx, a, b, command)
    case Route.Executing{r, ctx, xs}: executed_content(source, c, x, m, s, origin, r, ctx, xs, real, command, a, b, d)
    case Route.AfterPrepare{+r, +ctx, +xs, +p}:
      concatenate_contents(c, x, Route.render_execution(m, r, ctx, xs), Q.concatenate(Route.micro_output(m), [Route.frame_prepared(p)]),
        executed_content(source, c, x, m, s, origin, r, ctx, xs, Five.prefix_of_final(source, c, s, r, ctx, origin, xs, p, real), command, a, b, d),
        concatenate_contents(c, x, Route.micro_output(m), [Route.frame_prepared(p)], e, prepared_content(c, x, p)))

def prefix_initial_content(~c: S.Configuration, +x: Source.Context, +m: Route.Micro, accepts: Bool,
  e: Contents(c, x, Route.micro_output(m))) -> Contents(c, x, Route.prefix_initial(m, accepts)):
  match accepts:
    case True{}: L.Both{Unit{}, e}
    case False{}: Unit{}

def branch_content(~source: Source.Source, ~c: S.Configuration, +x: Source.Context, +m: Route.Micro,
  +s: D.State, +origin: Source.JudgmentSyntactic, branch: Route.Branch,
  real: Five.BranchReal(source, c, s, origin, branch), command: Source.RequestOfBranch(c, x, branch),
  a: Contents(c, x, Route.micro_input(m)), b: Contents(c, x, Route.micro_authentication(m)),
  d: Contents(c, x, Route.micro_execution(m)), e: Contents(c, x, Route.micro_output(m))) -> Contents(c, x, Route.render_branch(m, s, branch)):
  match branch:
    case Route.InitialOk{}:
      L.Both{Unit{}, concatenate_contents(c, x, Route.micro_output(m), Route.render_initial(P.encode(D.state_value(s)), s), e,
        initial_content(c, x, P.encode(D.state_value(s)), s, {==}))}
    case Route.InitialRefusal{status}: L.Both{Unit{}, Unit{}}
    case Route.InitialFailure{+accepts, +stage, +id, +fatal}:
      concatenate_contents(c, x, Route.prefix_initial(m, accepts), [Q.Failed{stage, id, fatal}, Q.InitialRefused{S.Failure{}}],
        prefix_initial_content(c, x, m, accepts, e), L.Both{Unit{}, L.Both{Unit{}, Unit{}}})
    case Route.WithoutResponse{}: L.Both{Unit{}, Unit{}}
    case Route.InputRefusal{+error, +closes, +delivery}:
      concatenate_contents(c, x, Route.micro_input(m), Route.render_error(Route.status_input(error), s, closes, delivery), a,
        error_content(c, x, Route.status_input(error), s, closes, delivery))
    case Route.AutRefusal{+r, +delivery}:
      concatenate_contents(c, x, Route.render_received(m, r), Q.concatenate(Route.micro_authentication(m), Con{Q.Authenticated{r, None{}}, Route.render_error(S.Authentication{}, s, False{}, delivery)}),
        received_content(c, x, m, r, a, command), concatenate_contents(c, x, Route.micro_authentication(m), Con{Q.Authenticated{r, None{}}, Route.render_error(S.Authentication{}, s, False{}, delivery)},
          b, L.Both{Unit{}, error_content(c, x, S.Authentication{}, s, False{}, delivery)}))
    case Route.GateRefusal{+r, +ctx, +delivery}:
      concatenate_contents(c, x, Route.render_authenticated(m, r, ctx), Con{Q.Rejected{r, ctx}, Route.render_error(S.Certificate{}, s, False{}, delivery)},
        authenticated_content(c, x, m, r, ctx, a, b, command), L.Both{Unit{}, error_content(c, x, S.Certificate{}, s, False{}, delivery)})
    case Route.Executed{+r, +ctx, +xs, +p, +delivery}:
      concatenate_contents(c, x, Route.render_execution(m, r, ctx, xs), Q.concatenate(Route.micro_output(m), Route.render_final(p, s, False{}, delivery)),
        executed_content(source, c, x, m, s, origin, r, ctx, xs, Five.prefix_of_final(source, c, s, r, ctx, origin, xs, p, real), command, a, b, d),
        concatenate_contents(c, x, Route.micro_output(m), Route.render_final(p, s, False{}, delivery), e, conclusion_content(c, x, N.conclude(p, s), False{}, delivery)))
    case Route.FailureBefore{+phase, +stage, +id, +fatal, +delivery}:
      concatenate_contents(c, x, Route.render_phase(m, phase), Route.render_failure(s, stage, id, fatal, delivery),
        phase_content(source, c, x, m, s, origin, phase, real, command, a, b, d, e), failure_content(c, x, s, stage, id, fatal, delivery))
    case Route.FatalAfterPublication{+r, +ctx, +xs, +p, +stage, +id}:
      concatenate_contents(c, x, Route.render_execution(m, r, ctx, xs), Q.concatenate(Route.micro_output(m), Route.render_fatal_published(N.conclude(p, s), stage, id)),
        executed_content(source, c, x, m, s, origin, r, ctx, xs, Five.prefix_of_final(source, c, s, r, ctx, origin, xs, p, real), command, a, b, d),
        concatenate_contents(c, x, Route.micro_output(m), Route.render_fatal_published(N.conclude(p, s), stage, id), e, fatal_published_content(c, x, N.conclude(p, s), stage, id)))
    case Route.Pending{phase}: phase_content(source, c, x, m, s, origin, phase, real, command, a, b, d, e)
    case Route.InitialPending{accepts}: prefix_initial_content(c, x, m, accepts, e)

# All local premises are concrete primitive results, not Rule2.
def protocol_content(~source: Source.Source, ~c: S.Configuration, +x: Source.Context, +m: Route.Micro,
  +s: D.State, +origin: Source.JudgmentSyntactic, +branch: Route.Branch,
  real: Five.BranchReal(source, c, s, origin, branch), command: Source.RequestOfBranch(c, x, branch), origins: OriginsMicro(c, x, m)) ->
  Contents(c, x, Route.render(m, s, branch)):
  match m origins:
    case Route.Micro{+a, +b, +d, +e} L.Both{oa, L.Both{ob, L.Both{od, oe}}}:
      L.Both{Unit{}, branch_content(source, c, x, Route.Micro{a, b, d, e}, s, origin, branch, real, command,
        content_of_all_primitives_and_exact(c, x, a, oa), content_of_all_primitives_and_exact(c, x, b, ob),
        content_of_all_primitives_and_exact(c, x, d, od), content_of_all_primitives_and_exact(c, x, e, oe))}

def data_of_route(~source: Source.Source, ~c: S.Configuration, x: Source.Context) -> Source.ObservationData:
  match x:
    case Source.Initial{+m, +s, pi}: Source.construct_initial(Source.identity(source), c, s, Source.initial(source, m))
    case Source.Service{+m, +s, +r}: Source.construct_call(c, s, r, Source.call(source, m))

def origin_observed(~source: Source.Source, ~c: S.Configuration, +x: Source.Context, -t: Nat, -f: I.Fact,
  observed: Source.of_route(source, Source.scenario_context(c, x), t, f)) -> Source.of_observation(source, c, data_of_route(source, c, x), t, f):
  match x:
    case Source.Initial{m, s, pi}: observed
    case Source.Service{m, s, r}: observed

def fields_of_route(~source: Source.Source, ~c: S.Configuration, +x: Source.Context) -> FieldsOfObservation(data_of_route(source, c, x)):
  match x:
    case Source.Initial{+m, +s, pi}: fields_of_start(source, c, s, Source.initial(source, m))
    case Source.Service{+m, +s, +r}: fields_of_call(c, s, r, Source.call(source, m))

def ContentOfObservation(~c: S.Configuration, +x: Source.Context, d: Source.ObservationData) -> Type:
  match d:
    case Source.ObservationData{ini, qs, origin}: Contents(c, x, qs)

def content_of_fact(~c: S.Configuration, +x: Source.Context, -p: S.Program,
  +ini: Maybe<&2, D.State>, +qs: List<&2, Q.Frame>, +t: Nat, f: I.Fact,
  contents: Contents(c, x, qs), observed: Q.observes_service(c, p, ini, qs, t, f)) -> Content(c, x, Q.frame_of_fact(f)):
  match f:
    case I.ConfigurationInUse{c}: Unit{}
    case I.ProofInitialAccepts{}: Unit{}
    case I.InstanceStarted{s}: Unit{}
    case I.InitializationRefused{s}: Unit{}
    case I.Encoded{+v, +bs}: content_of_query(c, x, qs, t, Q.Encoded{v, bs}, contents, Q.observation_frame(c, p, qs, t, I.Encoded{v, bs}, observed))
    case I.Decoded{+bs, +v}: content_of_query(c, x, qs, t, Q.Decoded{bs, v}, contents, Q.observation_frame(c, p, qs, t, I.Decoded{bs, v}, observed))
    case I.Stored{+s, +bs, +abstr}: content_of_query(c, x, qs, t, Q.Stored{s, bs, abstr}, contents, Q.observation_frame(c, p, qs, t, I.Stored{s, bs, abstr}, observed))
    case I.CheckedLength{pos, n}: Unit{}
    case I.AllocatedField{pos, n}: Unit{}
    case I.ReadBody{+before, +n, +declared}: content_of_query(c, x, qs, t, Q.Read{before, n, declared}, contents, Q.observation_frame(c, p, qs, t, I.ReadBody{before, n, declared}, observed))
    case I.ReceivedRequest{+r}: content_of_query(c, x, qs, t, Q.Received{r}, contents, Q.observation_frame(c, p, qs, t, I.ReceivedRequest{r}, observed))
    case I.Authenticated{r, ctx}: Unit{}
    case I.CertificateAccepted{r, ctx, p}: Unit{}
    case I.CertificateRejected{r, ctx}: Unit{}
    case I.ProgramStarted{r, ctx, p}: Unit{}
    case I.Evaluated{r, ctx, p, execution_trace}: Unit{}
    case I.Operated{+e, +s, +o, +r}: content_of_query(c, x, qs, t, Q.Operated{e, s, o, r}, contents, Q.observation_frame(c, p, qs, t, I.Operated{e, s, o, r}, observed))
    case I.Prepared{r, bs}: Unit{}
    case I.Published{s}: Unit{}
    case I.StateVisible{s}: Unit{}
    case I.FailedEnvironment{stage, id, fatal}: Unit{}
    case I.Concluded{r, s, closes}: Unit{}
    case I.DeliveredEverything{bs}: Unit{}
    case I.DeliveryInterrupted{bs}: Unit{}
    case I.ClosedChannel{}: Unit{}
    case I.NextCall{before, after}: Unit{}
    case I.InspectionNotModeled{description}: Unit{}
    case I.EffectNotModeled{description}: Unit{}

def content_in_origin(~source: Source.Source, ~c: S.Configuration, +x: Source.Context,
  +ini: Maybe<&2, D.State>, +qs: List<&2, Q.Frame>, origin: Maybe<&2, Source.JudgmentSyntactic>, +t: Nat, f: I.Fact,
  contents: Contents(c, x, qs), observed: Source.of_origin(source, c, ini, qs, origin, t, f)) ->
  Content(c, x, Q.frame_of_fact(f)):
  match origin:
    case None{}:
      content_of_fact(c, x, Source.without_program(), ini, qs, t, f, contents, observed)
    case Some{origin}:
      content_of_fact(c, x, Source.program(source, origin), ini, qs, t, f, contents, observed)

def content_in_observation(~source: Source.Source, ~c: S.Configuration, +x: Source.Context, data: Source.ObservationData,
  +t: Nat, f: I.Fact, contents: ContentOfObservation(c, x, data),
  observed: Source.of_observation(source, c, data, t, f)) -> Content(c, x, Q.frame_of_fact(f)):
  match data:
    case Source.ObservationData{ini, qs, origin}: content_in_origin(source, c, x, ini, qs, origin, t, f, contents, observed)

def observation_became_route(~source: Source.Source, ~c: S.Configuration, +x: Source.Context, -t: Nat, -f: I.Fact,
  observed: Source.of_observation(source, c, data_of_route(source, c, x), t, f)) -> Source.of_route(source, Source.scenario_context(c, x), t, f):
  match x:
    case Source.Initial{m, s, pi}: observed
    case Source.Service{m, s, r}: observed

def introduce_check(~source: Source.Source, ~c: S.Configuration, +x: Source.Context, -t: Nat, -pos: Nat, -n: Nat,
  name: {Source.artifact(source) == Source.artifact(source) : String},
  canonical: {Source.scenario_context(c, x) == Source.scenario(source, Source.world(Source.scenario_context(c, x))) : I.Scenario},
  before: BeforeObservation(source, c, data_of_route(source, c, x), t, pos, n)) ->
  I.Before(Source.environment(source), Source.artifact(source), Source.scenario_context(c, x), t, I.CheckedLength{pos, n}):
  match before:
    case (+b, L.Both{order, observed}):
      (b, L.Both{order, Source.introduce_fact_literal(source, Source.artifact(source), Source.scenario_context(c, x), b, I.CheckedLength{pos, n},
        L.Both{name, L.Both{canonical, observation_became_route(source, c, x, b, I.CheckedLength{pos, n}, observed)}})})

# Exact composition: the sole order-constrained fact uses FieldsService.
def rule2_components(~source: Source.Source, ~c: S.Configuration, +x: Source.Context, +t: Nat, f: I.Fact,
  contents: ContentOfObservation(c, x, data_of_route(source, c, x)),
  name: {Source.artifact(source) == Source.artifact(source) : String},
  canonical: {Source.scenario_context(c, x) == Source.scenario(source, Source.world(Source.scenario_context(c, x))) : I.Scenario},
  observed: Source.of_route(source, Source.scenario_context(c, x), t, f)) ->
  K.Rule2(f, Source.environment(source), Source.artifact(source), Source.scenario_context(c, x), t):
  match f:
    case I.ConfigurationInUse{c}: Unit{}
    case I.ProofInitialAccepts{}: Unit{}
    case I.InstanceStarted{s}: Unit{}
    case I.InitializationRefused{s}: Unit{}
    case I.Encoded{+v, +bs}: content_in_observation(source, c, x, data_of_route(source, c, x), t, I.Encoded{v, bs}, contents, origin_observed(source, c, x, t, I.Encoded{v, bs}, observed))
    case I.Decoded{+bs, +v}: content_in_observation(source, c, x, data_of_route(source, c, x), t, I.Decoded{bs, v}, contents, origin_observed(source, c, x, t, I.Decoded{bs, v}, observed))
    case I.Stored{+s, +bs, +abstr}: content_in_observation(source, c, x, data_of_route(source, c, x), t, I.Stored{s, bs, abstr}, contents, origin_observed(source, c, x, t, I.Stored{s, bs, abstr}, observed))
    case I.CheckedLength{pos, n}: Unit{}
    case I.AllocatedField{+pos, +n}: introduce_check(source, c, x, t, pos, n, name, canonical, field_of_observation(source, c, data_of_route(source, c, x), t, pos, n, fields_of_route(source, c, x), origin_observed(source, c, x, t, I.AllocatedField{pos, n}, observed)))
    case I.ReadBody{+before, +n, +declared}: content_in_observation(source, c, x, data_of_route(source, c, x), t, I.ReadBody{before, n, declared}, contents, origin_observed(source, c, x, t, I.ReadBody{before, n, declared}, observed))
    case I.ReceivedRequest{+r}: content_in_observation(source, c, x, data_of_route(source, c, x), t, I.ReceivedRequest{r}, contents, origin_observed(source, c, x, t, I.ReceivedRequest{r}, observed))
    case I.Authenticated{r, ctx}: Unit{}
    case I.CertificateAccepted{r, ctx, p}: Unit{}
    case I.CertificateRejected{r, ctx}: Unit{}
    case I.ProgramStarted{r, ctx, p}: Unit{}
    case I.Evaluated{r, ctx, p, execution_trace}: Unit{}
    case I.Operated{+e, +s, +o, +r}: content_in_observation(source, c, x, data_of_route(source, c, x), t, I.Operated{e, s, o, r}, contents, origin_observed(source, c, x, t, I.Operated{e, s, o, r}, observed))
    case I.Prepared{r, bs}: Unit{}
    case I.Published{s}: Unit{}
    case I.StateVisible{s}: Unit{}
    case I.FailedEnvironment{stage, id, fatal}: Unit{}
    case I.Concluded{r, s, closes}: Unit{}
    case I.DeliveredEverything{bs}: Unit{}
    case I.DeliveryInterrupted{bs}: Unit{}
    case I.ClosedChannel{}: Unit{}
    case I.NextCall{before, after}: Unit{}
    case I.InspectionNotModeled{description}: Unit{}
    case I.EffectNotModeled{description}: Unit{}

# Request provenance through the same decision, without another parser or renderer.
def requests_in_point(~c: S.Configuration, +x: Source.Context, +r: P.Request, +ctx: D.Context,
  point: Route.PointExec, command: I.RequestReceived(Source.scenario_context(c, x), r)) ->
  Source.RequestOfPhase(c, x, Route.phase_of_error(point, r, ctx)):
  match point:
    case Route.BeforeOfStart{}: command
    case Route.During{xs}: command
    case Route.Prepared{xs, p}: command

def requests_in_cleanup(~c: S.Configuration, +x: Source.Context, +r: P.Request, +ctx: D.Context,
  +xs: List<&2, Q.FrameExec>, +p: N.Prepared, cleanup: Route.Cleanup, +delivery: Route.Delivery,
  command: I.RequestReceived(Source.scenario_context(c, x), r)) ->
  Source.RequestOfBranch(c, x, Route.decide_cleanup(r, ctx, xs, p, cleanup, delivery)):
  match cleanup:
    case Route.Clears{}: command
    case Route.ErrorCleanup{id, fatal}: command
    case Route.FatalAfterStore{stage, id}: command
    case Route.PendingCleanup{}: command

def requests_in_execution(~c: S.Configuration, +x: Source.Context, +r: P.Request, +ctx: D.Context,
  output: Route.OutputExecution, +cleanup: Route.Cleanup, +delivery: Route.Delivery,
  command: I.RequestReceived(Source.scenario_context(c, x), r)) ->
  Source.RequestOfBranch(c, x, Route.decide_execution(r, ctx, output, cleanup, delivery)):
  match output:
    case Route.Finalized{xs, p}: requests_in_cleanup(c, x, r, ctx, xs, p, cleanup, delivery, command)
    case Route.ErrorExecution{point, stage, id, fatal}: requests_in_point(c, x, r, ctx, point, command)
    case Route.PendingExecution{point}: requests_in_point(c, x, r, ctx, point, command)

def requests_in_judgment(~c: S.Configuration, +x: Source.Context, +r: P.Request, +ctx: D.Context,
  data: Route.DataTools, command: I.RequestReceived(Source.scenario_context(c, x), r)) ->
  Source.RequestOfBranch(c, x, Route.decide_judgment(r, ctx, data)):
  match data:
    case Route.DataTools{j, +output, +cleanup, +delivery, pre}:
      match j:
        case Route.Accepted{}: requests_in_execution(c, x, r, ctx, output, cleanup, delivery, command)
        case Route.Refused{}: command
        case Route.ErrorJudgment{id, fatal}: command
        case Route.PendingJudgment{}: command

def requests_in_identity(~c: S.Configuration, +x: Source.Context, identity: Maybe<&2, D.Context>, +r: P.Request,
  +data: Route.DataTools, command: I.RequestReceived(Source.scenario_context(c, x), r)) ->
  Source.RequestOfBranch(c, x, Route.decide_identity(identity, r, data)):
  match identity:
    case None{}:
      match data:
        case Route.DataTools{j, output, cleanup, delivery, pre}: command
    case Some{ctx}: requests_in_judgment(c, x, r, ctx, data, command)

def requests_in_authentication(~c: S.Configuration, +x: Source.Context, +s: D.State, +r: P.Request,
  pre: Route.Preprocessing, +data: Route.DataTools, command: I.RequestReceived(Source.scenario_context(c, x), r)) ->
  Source.RequestOfBranch(c, x, Route.decide_authentication(pre, s, r, data)):
  match pre:
    case Route.FailureAuth{id, fatal}: command
    case Route.PendingAuth{}: command
    case Route.Normal{}: requests_in_identity(c, x, D.authenticate(s, I.credential(r)), r, data, command)
    case Route.FailureFraming{id, fatal}: requests_in_identity(c, x, D.authenticate(s, I.credential(r)), r, data, command)
    case Route.FailureDecode{id, fatal}: requests_in_identity(c, x, D.authenticate(s, I.credential(r)), r, data, command)
    case Route.PendingFraming{}: requests_in_identity(c, x, D.authenticate(s, I.credential(r)), r, data, command)
    case Route.PendingDecode{}: requests_in_identity(c, x, D.authenticate(s, I.credential(r)), r, data, command)

def requests_in_input(~c: S.Configuration, +world: Nat, +s: D.State, +input: X.Reception,
  +be: List<&2, U32>, +br: List<&2, U32>, +bs: List<&2, U32>, pre: Input.PreAuthentication, +data: Route.DataTools,
  assembly: {Transport.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
  octets_and: {B.octets_all_valid(be) == True{} : Bool}, octets_r: {B.octets_all_valid(br) == True{} : Bool},
  received: {X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition},
  ready: {Input.decode(bs, S.schema(c), S.limits(c)) == pre : Input.PreAuthentication}) ->
  Source.RequestOfBranch(c, Source.Service{world, s, input}, Route.decide_pre(pre, data)):
  match pre:
    case Input.InputReady{+decoded, +r}:
      requests_in_authentication(c, Source.Service{world, s, input}, decoded, r, Route.preprocessing(data), data,
        Source.request_ready_came_of_body(be, br, bs, S.schema(c), S.limits(c), decoded, r, world, c, input,
          assembly, octets_and, octets_r, received, ready))
    case Input.ErrorMessage{status}:
      match data:
        case Route.DataTools{j, output, cleanup, delivery, pre}: Unit{}
    case Input.ErrorTransport{}:
      match data:
        case Route.DataTools{j, output, cleanup, delivery, pre}: Unit{}

def requests_in_decode(~c: S.Configuration, +world: Nat, +s: D.State, +input: X.Reception,
  +be: List<&2, U32>, +br: List<&2, U32>, +bs: List<&2, U32>, pre: Route.Preprocessing, +data: Route.DataTools,
  assembly: {Transport.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
  octets_and: {B.octets_all_valid(be) == True{} : Bool}, octets_r: {B.octets_all_valid(br) == True{} : Bool},
  received: {X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition}) ->
  Source.RequestOfBranch(c, Source.Service{world, s, input}, Route.decide_decode(pre, bs, S.schema(c), S.limits(c), data)):
  match pre:
    case Route.FailureDecode{id, fatal}: Unit{}
    case Route.PendingDecode{}: Unit{}
    case Route.Normal{}: requests_in_input(c, world, s, input, be, br, bs, Input.decode(bs, S.schema(c), S.limits(c)), data, assembly, octets_and, octets_r, received, {==})
    case Route.FailureFraming{id, fatal}: requests_in_input(c, world, s, input, be, br, bs, Input.decode(bs, S.schema(c), S.limits(c)), data, assembly, octets_and, octets_r, received, {==})
    case Route.FailureAuth{id, fatal}: requests_in_input(c, world, s, input, be, br, bs, Input.decode(bs, S.schema(c), S.limits(c)), data, assembly, octets_and, octets_r, received, {==})
    case Route.PendingFraming{}: requests_in_input(c, world, s, input, be, br, bs, Input.decode(bs, S.schema(c), S.limits(c)), data, assembly, octets_and, octets_r, received, {==})
    case Route.PendingAuth{}: requests_in_input(c, world, s, input, be, br, bs, Input.decode(bs, S.schema(c), S.limits(c)), data, assembly, octets_and, octets_r, received, {==})

def requests_in_packet(~c: S.Configuration, +world: Nat, +s: D.State, +input: X.Reception,
  +be: List<&2, U32>, +br: List<&2, U32>, packet: Maybe<&2, List<&2, U32>>, +data: Route.DataTools,
  assembly: {Transport.join(be, br) == packet : Maybe<&2, List<&2, U32>>},
  octets_and: {B.octets_all_valid(be) == True{} : Bool}, octets_r: {B.octets_all_valid(br) == True{} : Bool},
  received: {X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition}) ->
  Source.RequestOfBranch(c, Source.Service{world, s, input}, Route.decide_packet(packet, S.schema(c), S.limits(c), data)):
  match packet:
    case None{}:
      match data:
        case Route.DataTools{j, output, cleanup, delivery, pre}: Unit{}
    case Some{+bs}: requests_in_decode(c, world, s, input, be, br, bs, Route.preprocessing(data), data, assembly, octets_and, octets_r, received)

def OctetsReceived(d: X.Disposition) -> Type:
  match d:
    case X.ProcessBody{br}: {B.octets_all_valid(br) == True{} : Bool}
    case _: Unit

def requests_in_disposition(~c: S.Configuration, +world: Nat, +s: D.State, +input: X.Reception,
  +be: List<&2, U32>, disposition: X.Disposition, +data: Route.DataTools,
  octets_and: {B.octets_all_valid(be) == True{} : Bool}, octets_r: OctetsReceived(disposition),
  received: {X.decide_reception(c, input) == disposition : X.Disposition}) ->
  Source.RequestOfBranch(c, Source.Service{world, s, input}, Route.decide_disposition(disposition, be, S.schema(c), S.limits(c), data)):
  match disposition:
    case X.CloseWithoutResponse{}: Unit{}
    case X.RefuseClose{status}:
      match data:
        case Route.DataTools{j, output, cleanup, delivery, pre}: Unit{}
    case X.RefuseContinue{status}:
      match data:
        case Route.DataTools{j, output, cleanup, delivery, pre}: Unit{}
    case X.ProcessBody{+br}: requests_in_packet(c, world, s, input, be, br, Transport.join(be, br), data, {==}, octets_and, octets_r, received)

def requests_in_framing(~c: S.Configuration, +world: Nat, +s: D.State, +input: X.Reception,
  +be: List<&2, U32>, pre: Route.Preprocessing, +disposition: X.Disposition, +data: Route.DataTools,
  octets_and: {B.octets_all_valid(be) == True{} : Bool}, octets_r: OctetsReceived(disposition),
  received: {X.decide_reception(c, input) == disposition : X.Disposition}) ->
  Source.RequestOfBranch(c, Source.Service{world, s, input}, Route.decide_framing(pre, disposition, be, S.schema(c), S.limits(c), data)):
  match pre:
    case Route.FailureFraming{id, fatal}: Unit{}
    case Route.PendingFraming{}: Unit{}
    case Route.Normal{}: requests_in_disposition(c, world, s, input, be, disposition, data, octets_and, octets_r, received)
    case Route.FailureDecode{id, fatal}: requests_in_disposition(c, world, s, input, be, disposition, data, octets_and, octets_r, received)
    case Route.FailureAuth{id, fatal}: requests_in_disposition(c, world, s, input, be, disposition, data, octets_and, octets_r, received)
    case Route.PendingDecode{}: requests_in_disposition(c, world, s, input, be, disposition, data, octets_and, octets_r, received)
    case Route.PendingAuth{}: requests_in_disposition(c, world, s, input, be, disposition, data, octets_and, octets_r, received)

law decide_by_reception:
  for c: S.Configuration
  for -r: X.Reception
  for -be: List<&2, U32>
  for -data: Route.DataTools
  {Route.decide(c, r, be, data) ==
    Route.decide_framing(Route.preprocessing(data), X.decide_reception(c, r), be, S.schema(c), S.limits(c), data) : Route.Branch}
def decide_by_reception(c, r, be, data):
  match c:
    case S.Configuration{e, laws, lim, environment}: {==}

def requests_of_decision(~c: S.Configuration, +world: Nat, +s: D.State, +input: X.Reception,
  +be: List<&2, U32>, +data: Route.DataTools,
  octets_and: {B.octets_all_valid(be) == True{} : Bool}, octets_r: OctetsReceived(X.decide_reception(c, input))) ->
  Source.RequestOfBranch(c, Source.Service{world, s, input}, Route.decide(c, input, be, data)):
  %Equal.sym(Route.Branch, Route.decide(c, input, be, data),
    Route.decide_framing(Route.preprocessing(data), X.decide_reception(c, input), be, S.schema(c), S.limits(c), data),
    decide_by_reception(c, input, be, data)) : Source.RequestOfBranch(c, Source.Service{world, s, input}, _)
  requests_in_framing(c, world, s, input, be, Route.preprocessing(data), X.decide_reception(c, input), data, octets_and, octets_r, {==})

# Low-level contracts of primitives actually recorded for this call.
def OriginOfCall(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State,
  +input: X.Reception, data: Source.CallData) -> Type:
  match data:
    case Source.CallData{cf, origin, pf, tf, be, tools, micro}:
      L.E<Five.CallReal(source, c, s, input, Source.CallData{cf, origin, pf, tf, be, tools, micro}),
        L.E<OriginsMicro(c, Source.Service{world, s, input}, micro),
          L.E<{B.octets_all_valid(be) == True{} : Bool}, OctetsReceived(X.decide_reception(c, input))>>>

def contents_of_call(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State,
  +input: X.Reception, data: Source.CallData, origin_real: OriginOfCall(source, c, world, s, input, data)) ->
  ContentOfObservation(c, Source.Service{world, s, input}, Source.construct_call(c, s, input, data)):
  match data origin_real:
    case Source.CallData{cf, +origin, pf, tf, +be, +tools, +micro} L.Both{real, L.Both{origins, L.Both{octets_and, octets_r}}}:
      protocol_content(source, c, Source.Service{world, s, input}, micro, s, origin, Route.decide(c, input, be, tools),
        Five.execution_of_decision(source, c, s, origin, be, tools, input, real),
        requests_of_decision(c, world, s, input, be, tools, octets_and, octets_r), origins)

def initial_accepted_without_program(~source: Source.Source, ~c: S.Configuration, +x: Source.Context,
  -s: D.State, -origin: Source.JudgmentSyntactic, result: Route.ResultInitial, is_valid: Bool) ->
  L.E<Five.BranchReal(source, c, s, origin, Route.decide_accepted_initial(result, is_valid)),
    Source.RequestOfBranch(c, x, Route.decide_accepted_initial(result, is_valid))>:
  match result:
    case Route.InitializationFinished{}:
      match is_valid:
        case False{}: L.Both{Unit{}, Unit{}}
        case True{}: L.Both{Unit{}, Unit{}}
    case Route.FailedInitial{accepts, stage, id, fatal}: L.Both{Unit{}, Unit{}}
    case Route.PendingInitial{accepts}: L.Both{Unit{}, Unit{}}

def initial_without_program(~source: Source.Source, ~c: S.Configuration, +x: Source.Context,
  -s: D.State, -origin: Source.JudgmentSyntactic, judgment: Route.Judgment, +result: Route.ResultInitial, +is_valid: Bool) ->
  L.E<Five.BranchReal(source, c, s, origin, Route.decide_judgment_initial(judgment, result, is_valid)),
    Source.RequestOfBranch(c, x, Route.decide_judgment_initial(judgment, result, is_valid))>:
  match judgment:
    case Route.Accepted{}: initial_accepted_without_program(source, c, x, s, origin, result, is_valid)
    case Route.Refused{}: L.Both{Unit{}, Unit{}}
    case Route.ErrorJudgment{id, fatal}: L.Both{Unit{}, Unit{}}
    case Route.PendingJudgment{}: L.Both{Unit{}, Unit{}}

def OriginOfInitial(~c: S.Configuration, +world: Nat, +s: D.State, +pi: String, data: Source.InitialData) -> Type:
  match data:
    case Source.InitialData{cf, sf, pf, j, result, micro}: OriginsMicro(c, Source.Initial{world, s, pi}, micro)

def contents_of_initial(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +pi: String,
  data: Source.InitialData, origins: OriginOfInitial(c, world, s, pi, data)) ->
  ContentOfObservation(c, Source.Initial{world, s, pi}, Source.construct_initial(Source.identity(source), c, s, data)):
  match data:
    case Source.InitialData{cf, sf, +pf, +j, +result, +micro}:
      Foundations.combined_pair(Contents(c, Source.Initial{world, s, pi}, Route.generate_result_initial(c, Source.identity(source), s, j, result, micro)),
        Five.BranchReal(source, c, s, pf, Route.decide_result_initial(c, Source.identity(source), j, result)),
        Source.RequestOfBranch(c, Source.Initial{world, s, pi}, Route.decide_result_initial(c, Source.identity(source), j, result)),
        initial_without_program(source, c, Source.Initial{world, s, pi}, s, pf, j, result, Configuration.is_valid(c, Source.identity(source))),
        real => command => protocol_content(source, c, Source.Initial{world, s, pi}, micro, s, pf,
          Route.decide_result_initial(c, Source.identity(source), j, result), real, command, origins))

def OriginOfRoute(~source: Source.Source, ~c: S.Configuration, x: Source.Context) -> Type:
  match x:
    case Source.Initial{+m, +s, +pi}: OriginOfInitial(c, m, s, pi, Source.initial(source, m))
    case Source.Service{+m, +s, +r}: OriginOfCall(source, c, m, s, r, Source.call(source, m))

def contents_of_route(~source: Source.Source, ~c: S.Configuration, +x: Source.Context,
  origins: OriginOfRoute(source, c, x)) -> ContentOfObservation(c, x, data_of_route(source, c, x)):
  match x:
    case Source.Initial{+m, +s, +pi}: contents_of_initial(source, c, m, s, pi, Source.initial(source, m), origins)
    case Source.Service{+m, +s, +r}: contents_of_call(source, c, m, s, r, Source.call(source, m), origins)

def rule2_literal(~source: Source.Source, ~c: S.Configuration, +x: Source.Context, +t: Nat, f: I.Fact,
  origins: OriginOfRoute(source, c, x),
  input: L.E<{Source.artifact(source) == Source.artifact(source) : String},
    L.E<{Source.scenario_context(c, x) == Source.scenario(source, Source.world(Source.scenario_context(c, x))) : I.Scenario},
      Source.of_route(source, Source.scenario_context(c, x), t, f)>>) ->
  K.Rule2(f, Source.environment(source), Source.artifact(source), Source.scenario_context(c, x), t):
  match input:
    case L.Both{name, L.Both{canonical, observed}}:
      rule2_components(source, c, x, t, f, contents_of_route(source, c, x, origins), name, canonical, observed)

# The world uses the same configuration and snapshot computed from history.
def context_of_moment(~seed: Unit -> D.State, ~history: Nat -> List<&2, History.Record>, ~pi: String,
  +world: Nat, moment: Scenarios.Moment) -> Source.Context:
  match moment:
    case Scenarios.Initialization{}: Source.Initial{world, seed(Unit{}), pi}
    case Scenarios.Service{r}: Source.Service{world, History.state(history(world), seed(Unit{})), r}

def context_represents_scenario(~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~pi: String, +world: Nat, +moment: Scenarios.Moment) ->
  {Source.scenario_context(c, context_of_moment(seed, history, pi, world, moment)) ==
    Scenarios.of_moment(c, seed, history, pi, moment, world) : I.Scenario}:
  match moment:
    case Scenarios.Initialization{}: {==}
    case Scenarios.Service{r}: {==}

def same_world_of_context(~source: Source.Source, ~c: S.Configuration, +world: Nat, +x: Source.Context,
  world_equal: {Source.world(Source.scenario_context(c, x)) == world : Nat},
  equal: {Source.scenario_context(c, x) == Source.scenario(source, world) : I.Scenario}) ->
  {Source.scenario_context(c, x) == Source.scenario(source, Source.world(Source.scenario_context(c, x))) : I.Scenario}:
  %Equal.sym(Nat, Source.world(Source.scenario_context(c, x)), world, world_equal) :
    {Source.scenario_context(c, x) == Source.scenario(source, _) : I.Scenario}
  equal

def rule2_in_canonical(~source: Source.Source, ~c: S.Configuration, +world: Nat, +x: Source.Context,
  world_equal: {Source.world(Source.scenario_context(c, x)) == world : Nat},
  equal: {Source.scenario_context(c, x) == Source.scenario(source, world) : I.Scenario}, origins: OriginOfRoute(source, c, x),
  +t: Nat, f: I.Fact, name: {Source.artifact(source) == Source.artifact(source) : String},
  observed: Source.of_route(source, Source.scenario(source, world), t, f)) ->
  K.Rule2(f, Source.environment(source), Source.artifact(source), Source.scenario(source, world), t):
  Five.combined_four({Source.scenario_context(c, x) == Source.scenario(source, world) : I.Scenario},
    K.Rule2(f, Source.environment(source), Source.artifact(source), Source.scenario(source, world), t),
    Five.four_equalities(I.Scenario, Source.scenario_context(c, x), Source.scenario(source, world), equal),
    i1 => i2 => i3 => i4 =>
      %i1 : K.Rule2(f, Source.environment(source), Source.artifact(source), _, t)
      rule2_literal(source, c, x, t, f, origins, L.Both{name, L.Both{
        same_world_of_context(source, c, world, x, world_equal, i2),
        (%Equal.sym(I.Scenario, Source.scenario_context(c, x), Source.scenario(source, world), i3) :
          Source.of_route(source, _, t, f) observed)}}))

def context_preserves_world(~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~pi: String, +world: Nat, moment: Scenarios.Moment) ->
  {Source.world(Source.scenario_context(c, context_of_moment(seed, history, pi, world, moment))) == world : Nat}:
  match moment:
    case Scenarios.Initialization{}: {==}
    case Scenarios.Service{r}: {==}

def OriginOfModel(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String, +world: Nat) -> Type:
  OriginOfRoute(Model.source(base, c, seed, history, moment, pi), c,
    context_of_moment(seed, history, pi, world, moment(world)))

def rule2_of_origin(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  -x: I.Scenario, +world: Nat, origins: OriginOfModel(base, c, seed, history, moment, pi, world),
  +t: Nat, f: I.Fact,
  input: L.E<{Source.artifact(Model.source(base, c, seed, history, moment, pi)) ==
      Source.artifact(Model.source(base, c, seed, history, moment, pi)) : String},
    L.E<{x == Source.scenario(Model.source(base, c, seed, history, moment, pi), world) : I.Scenario},
      Source.of_route(Model.source(base, c, seed, history, moment, pi),
        Source.scenario(Model.source(base, c, seed, history, moment, pi), world), t, f)>>) ->
  K.Rule2(f, Source.environment(Model.source(base, c, seed, history, moment, pi)),
    Source.artifact(Model.source(base, c, seed, history, moment, pi)), x, t):
  match input:
    case L.Both{name, L.Both{equal, observed}}:
      %Equal.sym(I.Scenario, x, Source.scenario(Model.source(base, c, seed, history, moment, pi), world), equal) :
        K.Rule2(f, Source.environment(Model.source(base, c, seed, history, moment, pi)),
          Source.artifact(Model.source(base, c, seed, history, moment, pi)), _, t)
      rule2_in_canonical(Model.source(base, c, seed, history, moment, pi), c, world,
        context_of_moment(seed, history, pi, world, moment(world)),
        context_preserves_world(c, seed, history, pi, world, moment(world)),
        Equal.trans(I.Scenario,
          Source.scenario_context(c, context_of_moment(seed, history, pi, world, moment(world))),
          Scenarios.canonical(c, seed, history, moment, pi, world),
          Source.scenario(Model.source(base, c, seed, history, moment, pi), world),
          context_represents_scenario(c, seed, history, pi, world, moment(world)),
          Equal.sym(I.Scenario, Source.scenario(Model.source(base, c, seed, history, moment, pi), world),
            Scenarios.canonical(c, seed, history, moment, pi, world), Model.scenario_of_model(base, c, seed, history, moment, pi, world))),
        origins, t, f, name, observed)

def law2_of_scenario(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  origins: @world: Nat -> OriginOfModel(base, c, seed, history, moment, pi, world),
  x: I.Scenario, +t: Nat, f: I.Fact,
  observed: I.Happens(Source.environment(Model.source(base, c, seed, history, moment, pi)),
    Source.artifact(Model.source(base, c, seed, history, moment, pi)), x, t, f)) ->
  K.Rule2(f, Source.environment(Model.source(base, c, seed, history, moment, pi)),
    Source.artifact(Model.source(base, c, seed, history, moment, pi)), x, t):
  match x:
    case I.Initialize{+m, original, +s, +proof}:
      rule2_of_origin(base, c, seed, history, moment, pi, I.Initialize{m, original, s, proof}, m, origins(m), t, f,
        Source.eliminate_fact(Model.source(base, c, seed, history, moment, pi),
          Source.artifact(Model.source(base, c, seed, history, moment, pi)), I.Initialize{m, original, s, proof}, t, f, observed))
    case I.Serve{+m, original, +s, +input}:
      rule2_of_origin(base, c, seed, history, moment, pi, I.Serve{m, original, s, input}, m, origins(m), t, f,
        Source.eliminate_fact(Model.source(base, c, seed, history, moment, pi),
          Source.artifact(Model.source(base, c, seed, history, moment, pi)), I.Serve{m, original, s, input}, t, f, observed))

def law2_of_model(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  origins: @world: Nat -> OriginOfModel(base, c, seed, history, moment, pi, world)) ->
  K.Law2(Source.environment(Model.source(base, c, seed, history, moment, pi)),
    Source.artifact(Model.source(base, c, seed, history, moment, pi))):
  x => +t => f => observed => law2_of_scenario(base, c, seed, history, moment, pi, origins, x, t, f, observed)
