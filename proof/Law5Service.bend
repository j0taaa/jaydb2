# Links observed execution. Guards are eliminated/introduced without
# identifying a conjunction with its second field by Type equality.
import Base
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/LAWS.bend as Laws
import ../contract/Logic.bend as L
import ../contract/Protocol.bend as P
import ../contract/Resources.bend as X
import ../contract/Requirements.bend as Requirements
import ../contract/Semantics.bend as S
import ../contract/Links.bend as V
import ./ExecutionService.bend as E
import ./ProtocolService.bend as Q
import ./Foundations.bend as F
import ./CodecCanonical.bend as Sum
import ./Call.bend as Call
import ./PrimitivesService.bend as M
import ./RoutesService.bend as R
import ./PhasesService.bend as Phases
import ./RefinementService.bend as Ref
import ./SourceService.bend as Source
import ../src/Input.bend as Input
import ../src/Transport.bend as Transport
import ../src/ConfigurationCheck.bend as Configuration
import ./ScenariosService.bend as Scenarios
import ./HistoryService.bend as History
import ./ModelService.bend as Model
import ../src/Core.bend as N

law linkage_preserves_guards:
  for -G: Type
  for -H: Type
  for -ob: Nat -> I.Fact -> Type
  for -x: I.Scenario
  for -t: Nat
  for -e: D.Schema
  for -s: D.State
  for -o: D.Operation
  for -result: D.ResultOp
  for guards: L.E<L.E<G, H>, L.E<G, H>>
  for linkage: E.Linkage(ob, x, t, e, s, o, result)
  E.Linkage(Ref.observation_stored(G, H, ob), x, t, e, s, o, result)
def linkage_preserves_guards(G, H, ob, x, t, e, s, o, result, guards, linkage):
  match guards:
    case L.Both{before_guards, later_guards}:
      match linkage:
        case (req, (ctx, (p, (ts, (before, (later, (after,
          L.Both{schema, L.Both{window, L.Both{first, L.Both{second,
            L.Both{effect, unique}}}}}))))))):
          (req, ctx, p, ts, before, later, after,
            L.Both{schema, L.Both{window,
              L.Both{Ref.combined_guards(G, H, ob(before, I.Evaluated{req, ctx, p, S.Prefix{s, ts}}), before_guards, first),
                L.Both{Ref.combined_guards(G, H, ob(later, I.Evaluated{req, ctx, p, after}), later_guards, second),
                  L.Both{effect, u => e2 => s2 => o2 => r2 => left => right => observed =>
                    unique(u, e2, s2, o2, r2, left, right,
                      Ref.remove_guards(G, H, ob(u, I.Operated{e2, s2, o2, r2}), observed))}}}}})

law operation_bound_stored:
  for ~program: Nat -> S.Program
  for -G: Type
  for -H: Type
  for +world: Nat
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for -c: S.Configuration
  for +initial: Maybe<&2, D.State>
  for +xs: List<&2, Q.Frame>
  for +r: P.Request
  for +ctx: D.Context
  for +e: D.Schema
  for +s: D.State
  for +o: D.Operation
  for +ts: List<&2, S.OperationEvent>
  for +b: Nat
  for guards: L.E<L.E<G, H>, L.E<G, H>>
  for schema: {e == S.schema(I.configuration(x)) : D.Schema}
  for before: {Q.query(xs, b) == Some{Q.Evaluated{r, ctx, S.Prefix{s, ts}}} : Maybe<&2, Q.Frame>}
  for operation: {Q.query(xs, Succ{b}) == Some{Q.Operated{e, s, o, D.operate(e, s, o)}} : Maybe<&2, Q.Frame>}
  for later: {Q.query(xs, Succ{Succ{b}}) == Some{Q.Evaluated{r, ctx, E.after(D.operate(e, s, o), s, o, ts)}} : Maybe<&2, Q.Frame>}
  for refinement: {E.observation_real(a, k, x) ==
    Ref.observation_stored(G, H, E.observation_model(c, program(world), initial, xs)) : Nat -> I.Fact -> Type}
  V.OperationBound(a, k, x, Succ{b}, e, s, o, D.operate(e, s, o))
def operation_bound_stored(program, G, H, world, a, k, x, c, initial, xs,
  r, ctx, e, s, o, ts, b, guards, schema, before, operation, later, refinement):
  %Equal.sym((Nat -> I.Fact -> Type), E.observation_real(a, k, x),
    Ref.observation_stored(G, H, E.observation_model(c, program(world), initial, xs)), refinement) :
      E.Linkage(_, x, Succ{b}, e, s, o, D.operate(e, s, o))
  linkage_preserves_guards(G, H, E.observation_model(c, program(world), initial, xs),
    x, Succ{b}, e, s, o, D.operate(e, s, o), guards,
    E.bind_queries(program, world, x, c, initial, xs, r, ctx, e, s, o, ts, b,
      schema, before, operation, later))

def subtrace(+before: List<&2, Q.Frame>, +body: List<&2, Q.Frame>,
  +later: List<&2, Q.Frame>) -> List<&2, Q.Frame>:
  Q.concatenate(before, Q.concatenate(body, later))

law query_of_subtrace:
  for +before: List<&2, Q.Frame>
  for +body: List<&2, Q.Frame>
  for +later: List<&2, Q.Frame>
  for +t: Nat
  for -q: Q.Frame
  for present: {Q.query(body, t) == Some{q} : Maybe<&2, Q.Frame>}
  {Q.query(subtrace(before, body, later), Nat.add(Q.size(before), t)) == Some{q} : Maybe<&2, Q.Frame>}
def query_of_subtrace(before, body, later, t, q, present):
  Equal.trans(Maybe<&2, Q.Frame>,
    Q.query(subtrace(before, body, later), Nat.add(Q.size(before), t)),
    Q.query(Q.concatenate(body, later), t), Some{q},
    Q.query_after_prefix(before, Q.concatenate(body, later), t),
    Q.query_prefix(body, later, t, q, present))

law query_expanded_in_subtrace:
  for +before: List<&2, Q.Frame>
  for +later: List<&2, Q.Frame>
  for +r: P.Request
  for +ctx: D.Context
  for +xs: List<&2, Q.FrameExec>
  for +t: Nat
  for +q: Q.FrameExec
  for present: {E.query(xs, t) == Some{q} : Maybe<&2, Q.FrameExec>}
  {Q.query(subtrace(before, Q.expand_exec(r, ctx, xs), later), Nat.add(Q.size(before), t)) ==
    Some{E.expand_frame(r, ctx, q)} : Maybe<&2, Q.Frame>}
def query_expanded_in_subtrace(before, later, r, ctx, xs, t, q, present):
  query_of_subtrace(before, Q.expand_exec(r, ctx, xs), later, t,
    E.expand_frame(r, ctx, q), E.expand_preserves_query(r, ctx, xs, t, q, present))

def sum_two_successors(+a: Nat, +b: Nat) ->
  {Nat.add(a, Succ{Succ{b}}) == Succ{Succ{Nat.add(a, b)}} : Nat}:
  Equal.trans(Nat, Nat.add(a, Succ{Succ{b}}), Succ{Nat.add(a, Succ{b})},
    Succ{Succ{Nat.add(a, b)}}, Sum.sum_successor_right(a, Succ{b}),
    Equal.cong(Nat, Nat, n => Succ{n}, Nat.add(a, Succ{b}), Succ{Nat.add(a, b)},
      Sum.sum_successor_right(a, b)))

# Shifting does not change the actual window of three consecutive frames.
def bind_step_inserted(~program: Nat -> S.Program, +world: Nat,
  -x: I.Scenario, -c: S.Configuration, +initial: Maybe<&2, D.State>,
  +before: List<&2, Q.Frame>, +later: List<&2, Q.Frame>,
  +r: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>,
  +e: D.Schema, +s: D.State, +o: D.Operation, +ts: List<&2, S.OperationEvent>, +b: Nat,
  schema: {e == S.schema(I.configuration(x)) : D.Schema},
  first: {E.query(xs, b) == Some{Q.Evaluation{S.Prefix{s, ts}}} : Maybe<&2, Q.FrameExec>},
  operation: {E.query(xs, Succ{b}) == Some{Q.Operation{e, s, o, D.operate(e, s, o)}} : Maybe<&2, Q.FrameExec>},
  second: {E.query(xs, Succ{Succ{b}}) == Some{Q.Evaluation{E.after(D.operate(e, s, o), s, o, ts)}} : Maybe<&2, Q.FrameExec>}) ->
  E.Linkage(E.observation_model(c, program(world), initial, subtrace(before, Q.expand_exec(r, ctx, xs), later)),
    x, Succ{Nat.add(Q.size(before), b)}, e, s, o, D.operate(e, s, o)):
  E.bind_queries(program, world, x, c, initial,
    subtrace(before, Q.expand_exec(r, ctx, xs), later), r, ctx, e, s, o, ts,
    Nat.add(Q.size(before), b), schema,
    query_expanded_in_subtrace(before, later, r, ctx, xs, b, Q.Evaluation{S.Prefix{s, ts}}, first),
    (%Sum.sum_successor_right(Q.size(before), b) :
      {Q.query(subtrace(before, Q.expand_exec(r, ctx, xs), later), _) ==
        Some{Q.Operated{e, s, o, D.operate(e, s, o)}} : Maybe<&2, Q.Frame>}
      query_expanded_in_subtrace(before, later, r, ctx, xs, Succ{b},
        Q.Operation{e, s, o, D.operate(e, s, o)}, operation)),
    (%sum_two_successors(Q.size(before), b) :
      {Q.query(subtrace(before, Q.expand_exec(r, ctx, xs), later), _) ==
        Some{Q.Evaluated{r, ctx, E.after(D.operate(e, s, o), s, o, ts)}} : Maybe<&2, Q.Frame>}
      query_expanded_in_subtrace(before, later, r, ctx, xs, Succ{Succ{b}},
        Q.Evaluation{E.after(D.operate(e, s, o), s, o, ts)}, second)))

def apply(-A: Type, -B: Type, function: A -> B, argument: A) -> B:
  function(argument)

def bind_operation_local(~program: Nat -> S.Program, +world: Nat,
  -x: I.Scenario, -c: S.Configuration, +initial: Maybe<&2, D.State>,
  +before: List<&2, Q.Frame>, +later: List<&2, Q.Frame>,
  +r: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>,
  +t: Nat, +e: D.Schema, +s: D.State, +o: D.Operation, +result: D.ResultOp,
  schema: {e == S.schema(I.configuration(x)) : D.Schema},
  present: {E.query(xs, t) == Some{Q.Operation{e, s, o, result}} : Maybe<&2, Q.FrameExec>},
  correct: E.OperationCorrect(xs, t, Q.Operation{e, s, o, result}, e)) ->
  E.Linkage(E.observation_model(c, program(world), initial,
    subtrace(before, Q.expand_exec(r, ctx, xs), later)),
    x, Nat.add(Q.size(before), t), e, s, o, result):
  match correct:
    case L.Both{same_schema, L.Both{calculated, (+b, +ts,
      L.Both{position, L.Both{first, second}})}}:
      apply({E.query(xs, t) == Some{Q.Operation{e, s, o, result}} : Maybe<&2, Q.FrameExec>},
        E.Linkage(E.observation_model(c, program(world), initial,
          subtrace(before, Q.expand_exec(r, ctx, xs), later)),
          x, Nat.add(Q.size(before), t), e, s, o, result),
        (%Equal.sym(Nat, t, Succ{b}, position) :
          {E.query(xs, _) == Some{Q.Operation{e, s, o, result}} : Maybe<&2, Q.FrameExec>} ->
          E.Linkage(E.observation_model(c, program(world), initial,
            subtrace(before, Q.expand_exec(r, ctx, xs), later)),
            x, Nat.add(Q.size(before), _), e, s, o, result)
          in_middle => apply(
            L.E<{E.query(xs, Succ{b}) == Some{Q.Operation{e, s, o, result}} : Maybe<&2, Q.FrameExec>},
              {E.query(xs, Succ{Succ{b}}) == Some{Q.Evaluation{E.after(result, s, o, ts)}} : Maybe<&2, Q.FrameExec>}>,
            E.Linkage(E.observation_model(c, program(world), initial,
              subtrace(before, Q.expand_exec(r, ctx, xs), later)),
              x, Nat.add(Q.size(before), Succ{b}), e, s, o, result),
            (%Equal.sym(D.ResultOp, result, D.operate(e, s, o), calculated) :
              L.E<{E.query(xs, Succ{b}) == Some{Q.Operation{e, s, o, _}} : Maybe<&2, Q.FrameExec>},
                {E.query(xs, Succ{Succ{b}}) == Some{Q.Evaluation{E.after(_, s, o, ts)}} : Maybe<&2, Q.FrameExec>}> ->
              E.Linkage(E.observation_model(c, program(world), initial,
                subtrace(before, Q.expand_exec(r, ctx, xs), later)),
                x, Nat.add(Q.size(before), Succ{b}), e, s, o, _)
              pair => F.combined_pair(
                E.Linkage(E.observation_model(c, program(world), initial,
                  subtrace(before, Q.expand_exec(r, ctx, xs), later)),
                  x, Nat.add(Q.size(before), Succ{b}), e, s, o, D.operate(e, s, o)),
                {E.query(xs, Succ{b}) == Some{Q.Operation{e, s, o, D.operate(e, s, o)}} : Maybe<&2, Q.FrameExec>},
                {E.query(xs, Succ{Succ{b}}) == Some{Q.Evaluation{E.after(D.operate(e, s, o), s, o, ts)}} : Maybe<&2, Q.FrameExec>},
                pair, operation => next =>
                  %Equal.sym(Nat, Nat.add(Q.size(before), Succ{b}), Succ{Nat.add(Q.size(before), b)},
                    Sum.sum_successor_right(Q.size(before), b)) :
                    E.Linkage(E.observation_model(c, program(world), initial,
                      subtrace(before, Q.expand_exec(r, ctx, xs), later)),
                      x, _, e, s, o, D.operate(e, s, o))
                  bind_step_inserted(program, world, x, c, initial, before, later, r, ctx, xs,
                    e, s, o, ts, b, schema, first, operation, next))),
            L.Both{in_middle, second})), present)

def bind_schema_generated(~program: Nat -> S.Program, +world: Nat,
  -x: I.Scenario, -c: S.Configuration, +initial: Maybe<&2, D.State>,
  +before: List<&2, Q.Frame>, +later: List<&2, Q.Frame>,
  +r: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>,
  +t: Nat, +e: D.Schema, +e2: D.Schema, +s: D.State, +o: D.Operation, +result: D.ResultOp,
  schema: {e == S.schema(I.configuration(x)) : D.Schema},
  present: {E.query(xs, t) == Some{Q.Operation{e2, s, o, result}} : Maybe<&2, Q.FrameExec>},
  correct: E.OperationCorrect(xs, t, Q.Operation{e2, s, o, result}, e)) ->
  E.Linkage(E.observation_model(c, program(world), initial,
    subtrace(before, Q.expand_exec(r, ctx, xs), later)),
    x, Nat.add(Q.size(before), t), e2, s, o, result):
  match correct:
    case L.Both{same_schema, rest}:
      apply({E.query(xs, t) == Some{Q.Operation{e2, s, o, result}} : Maybe<&2, Q.FrameExec>},
        E.Linkage(E.observation_model(c, program(world), initial,
          subtrace(before, Q.expand_exec(r, ctx, xs), later)),
          x, Nat.add(Q.size(before), t), e2, s, o, result),
        (%Equal.sym(D.Schema, e2, e, same_schema) :
          {E.query(xs, t) == Some{Q.Operation{_, s, o, result}} : Maybe<&2, Q.FrameExec>} ->
          E.Linkage(E.observation_model(c, program(world), initial,
            subtrace(before, Q.expand_exec(r, ctx, xs), later)),
            x, Nat.add(Q.size(before), t), _, s, o, result)
          fact => bind_operation_local(program, world, x, c, initial, before, later, r, ctx, xs,
            t, e, s, o, result, schema, fact, L.Both{{==}, rest})), present)

law all_operation_generated_has_binding_global:
  for ~program: Nat -> S.Program
  for +world: Nat
  for -x: I.Scenario
  for -c: S.Configuration
  for +initial: Maybe<&2, D.State>
  for +before: List<&2, Q.Frame>
  for +later: List<&2, Q.Frame>
  for +r: P.Request
  for +ctx: D.Context
  for +s0: D.State
  for +n: Nat
  for +t: Nat
  for +e: D.Schema
  for +e2: D.Schema
  for +s: D.State
  for +o: D.Operation
  for +result: D.ResultOp
  for schema: {e == S.schema(I.configuration(x)) : D.Schema}
  for present: {E.query(E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e), t) ==
    Some{Q.Operation{e2, s, o, result}} : Maybe<&2, Q.FrameExec>}
  E.Linkage(E.observation_model(c, program(world), initial,
    subtrace(before, Q.expand_exec(r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e)), later)),
    x, Nat.add(Q.size(before), t), e2, s, o, result)
def all_operation_generated_has_binding_global(program, world, x, c, initial, before, later, r, ctx,
  s0, n, t, e, e2, s, o, result, schema, present):
  F.combined_pair(
    E.Linkage(E.observation_model(c, program(world), initial,
      subtrace(before, Q.expand_exec(r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e)), later)),
      x, Nat.add(Q.size(before), t), e2, s, o, result),
    {E.query(E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e), t) ==
      Some{Q.Operation{e2, s, o, result}} : Maybe<&2, Q.FrameExec>},
    {E.query(E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e), t) ==
      Some{Q.Operation{e2, s, o, result}} : Maybe<&2, Q.FrameExec>},
    Call.duplicate_equality(Maybe<&2, Q.FrameExec>,
      E.query(E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e), t),
      Some{Q.Operation{e2, s, o, result}}, present),
    for_binding => for_generator =>
      bind_schema_generated(program, world, x, c, initial, before, later, r, ctx,
        E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e), t, e, e2, s, o, result, schema,
        for_binding,
        E.all_operations_generated_are_real(n, N.start(program(world), ctx, I.arguments(r), s0), e,
          t, Q.Operation{e2, s, o, result}, for_generator)))

def WithoutFrame(-xs: List<&2, Q.Frame>, -q: Q.Frame) -> Type:
  @t: Nat -> {Q.query(xs, t) == Some{q} : Maybe<&2, Q.Frame>} -> Empty

def lift_origin(-h: Q.Frame, +prefix: List<&2, Q.Frame>, -rest: List<&2, Q.Frame>,
  -t: Nat, -q: Q.Frame,
  origin: &i: Nat -> L.E<{t == Nat.add(Q.size(prefix), i) : Nat},
    {Q.query(rest, i) == Some{q} : Maybe<&2, Q.Frame>}>) ->
  &i: Nat -> L.E<{Succ{t} == Nat.add(Q.size(Con{h, prefix}), i) : Nat},
    {Q.query(rest, i) == Some{q} : Maybe<&2, Q.Frame>}>:
  match origin:
    case (+i, L.Both{position, present}):
      (i, L.Both{Equal.cong(Nat, Nat, n => Succ{n}, t,
        Nat.add(Q.size(prefix), i), position), present})

law remove_prefix_without_frame:
  for +prefix: List<&2, Q.Frame>
  for +rest: List<&2, Q.Frame>
  for +t: Nat
  for -q: Q.Frame
  for absent: WithoutFrame(prefix, q)
  for present: {Q.query(Q.concatenate(prefix, rest), t) == Some{q} : Maybe<&2, Q.Frame>}
  exs i: Nat
  L.E<{t == Nat.add(Q.size(prefix), i) : Nat},
    {Q.query(rest, i) == Some{q} : Maybe<&2, Q.Frame>}>
def remove_prefix_without_frame(prefix, rest, t, q, absent, present):
  match prefix t:
    case Nil{} _: (t, L.Both{{==}, present})
    case Con{h, tail} 0n:
      L.ex_false((&i: Nat -> L.E<{0n == Nat.add(Q.size(Con{h, tail}), i) : Nat},
        {Q.query(rest, i) == Some{q} : Maybe<&2, Q.Frame>}>), absent(0n, present))
    case Con{h, +tail} 1n+j:
      lift_origin(h, tail, rest, j, q,
        remove_prefix_without_frame(tail, rest, j, q, u => proof => absent(Succ{u}, proof), present))

law remove_suffix_without_frame:
  for +body: List<&2, Q.Frame>
  for -suffix: List<&2, Q.Frame>
  for +t: Nat
  for -q: Q.Frame
  for absent: WithoutFrame(suffix, q)
  for present: {Q.query(Q.concatenate(body, suffix), t) == Some{q} : Maybe<&2, Q.Frame>}
  {Q.query(body, t) == Some{q} : Maybe<&2, Q.Frame>}
def remove_suffix_without_frame(body, suffix, t, q, absent, present):
  match body t:
    case Nil{} _: L.ex_false({Q.query(Nil{}, t) == Some{q} : Maybe<&2, Q.Frame>}, absent(t, present))
    case Con{h, tail} 0n: present
    case Con{h, +tail} 1n+j: remove_suffix_without_frame(tail, suffix, j, q, absent, present)

law query_internal:
  for xs: List<&2, Q.Frame>
  for t: Nat
  for -q: Q.Frame
  for internal: M.Internal(xs)
  for present: {Q.query(xs, t) == Some{q} : Maybe<&2, Q.Frame>}
  {M.internal(q) == True{} : Bool}
def query_internal(xs, t, q, internal, present):
  match xs t:
    case Nil{} _:
      L.ex_false({M.internal(q) == True{} : Bool}, F.none_negative_some(Q.Frame, q, present))
    case Con{+h, tail} 0n:
      F.combined_pair({M.internal(q) == True{} : Bool}, {M.internal(h) == True{} : Bool}, M.Internal(tail), internal,
        head => rest =>
          %F.some_injective(Q.Frame, h, q, present) : {M.internal(_) == True{} : Bool}
          head)
    case Con{h, tail} 1n+j:
      F.combined_pair({M.internal(q) == True{} : Bool}, {M.internal(h) == True{} : Bool}, M.Internal(tail), internal,
        head => rest => query_internal(tail, j, q, rest, present))

def internal_negative_contains(+xs: List<&2, Q.Frame>, -q: Q.Frame,
  internal: M.Internal(xs), external: {M.internal(q) == False{} : Bool}) -> WithoutFrame(xs, q):
  t => present => F.false_negative_true(Equal.trans(Bool, False{}, M.internal(q), True{},
    Equal.sym(Bool, M.internal(q), False{}, external), query_internal(xs, t, q, internal, present)))

def concatenate_without_frame(+xs: List<&2, Q.Frame>, -ys: List<&2, Q.Frame>, -q: Q.Frame,
  first: WithoutFrame(xs, q), second: WithoutFrame(ys, q), t: Nat,
  present: {Q.query(Q.concatenate(xs, ys), t) == Some{q} : Maybe<&2, Q.Frame>}) -> Empty:
  match xs t:
    case Nil{} _: second(t, present)
    case Con{h, tail} 0n: first(0n, present)
    case Con{h, +tail} 1n+j:
      concatenate_without_frame(tail, ys, q, u => proof => first(Succ{u}, proof), second, j, present)

def of_execution(q: Q.Frame) -> Bool:
  match q:
    case Q.Started{r, ctx}: True{}
    case Q.Evaluated{r, ctx, p}: True{}
    case Q.Operated{e, s, o, result}: True{}
    case Q.Inspection{d}: True{}
    case Q.Effect{d}: True{}
    case _: False{}

def head_by_tag(~tag: Q.Frame -> Bool, +h: Q.Frame, -q: Q.Frame, -xs: List<&2, Q.Frame>,
  neutral: {tag(h) == False{} : Bool}, target: {tag(q) == True{} : Bool},
  rest: WithoutFrame(xs, q), t: Nat,
  present: {Q.query(Con{h, xs}, t) == Some{q} : Maybe<&2, Q.Frame>}) -> Empty:
  match t:
    case 0n:
      F.false_negative_true(Equal.trans(Bool, False{}, tag(h), True{},
        Equal.sym(Bool, tag(h), False{}, neutral),
        Equal.trans(Bool, tag(h), tag(q), True{},
          Equal.cong(Q.Frame, Bool, tag, h, q, F.some_injective(Q.Frame, h, q, present)), target)))
    case 1n+j: rest(j, present)

def head_without_execution(+h: Q.Frame, -q: Q.Frame, -xs: List<&2, Q.Frame>,
  neutral: {of_execution(h) == False{} : Bool}, target: {of_execution(q) == True{} : Bool},
  rest: WithoutFrame(xs, q)) -> WithoutFrame(Con{h, xs}, q):
  head_by_tag(of_execution, h, q, xs, neutral, target, rest)

# Subtype of the only frames relevant to Rule5; no program is copied.
type Interest is Data:
  Start{request: P.Request, context: D.Context}
  Evaluation{request: P.Request, context: D.Context, execution_trace: S.Trace}
  Operation{schema: D.Schema, state: D.State, operation: D.Operation, result: D.ResultOp}
  Inspection{description: String}
  Effect{description: String}

def frame_interest(i: Interest) -> Q.Frame:
  match i:
    case Start{r, ctx}: Q.Started{r, ctx}
    case Evaluation{r, ctx, p}: Q.Evaluated{r, ctx, p}
    case Operation{e, s, o, result}: Q.Operated{e, s, o, result}
    case Inspection{d}: Q.Inspection{d}
    case Effect{d}: Q.Effect{d}

def interest_and_execution(i: Interest) -> {of_execution(frame_interest(i)) == True{} : Bool}:
  match i:
    case Start{r, ctx}: {==}
    case Evaluation{r, ctx, p}: {==}
    case Operation{e, s, o, result}: {==}
    case Inspection{d}: {==}
    case Effect{d}: {==}

def interest_negative_internal(i: Interest) -> {M.internal(frame_interest(i)) == False{} : Bool}:
  match i:
    case Start{r, ctx}: {==}
    case Evaluation{r, ctx, p}: {==}
    case Operation{e, s, o, result}: {==}
    case Inspection{d}: {==}
    case Effect{d}: {==}

def OutsideStart(i: Interest) -> Type:
  match i:
    case Start{r, ctx}: Empty
    case _: Unit

def is_start(q: Q.Frame) -> Bool:
  match q:
    case Q.Started{r, ctx}: True{}
    case _: False{}

def interest_outside_start(i: Interest, outside: OutsideStart(i)) ->
  {Bool.not(is_start(frame_interest(i))) == True{} : Bool}:
  match i:
    case Start{r, ctx}: L.ex_false({Bool.not(is_start(Q.Started{r, ctx})) == True{} : Bool}, outside)
    case Evaluation{r, ctx, p}: {==}
    case Operation{e, s, o, result}: {==}
    case Inspection{d}: {==}
    case Effect{d}: {==}

def empty_without_frame(-q: Q.Frame) -> WithoutFrame(Nil{}, q):
  t => present => F.none_negative_some(Q.Frame, q, present)

def primitives_without_interest(+ps: List<&2, M.Primitive>, +i: Interest) ->
  WithoutFrame(M.expand_primitives(ps), frame_interest(i)):
  internal_negative_contains(M.expand_primitives(ps), frame_interest(i),
    M.primitives_only_generate_internal(ps), interest_negative_internal(i))

def received_without_interest(m: R.Micro, +r: P.Request, +i: Interest) ->
  WithoutFrame(R.render_received(m, r), frame_interest(i)):
  match m:
    case R.Micro{+a, b, c, d}:
      concatenate_without_frame(M.expand_primitives(a), [Q.Received{r}], frame_interest(i),
        primitives_without_interest(a, i),
        head_without_execution(Q.Received{r}, frame_interest(i), Nil{}, {==},
          interest_and_execution(i), empty_without_frame(frame_interest(i))))

def authenticated_without_interest(+m: R.Micro, +r: P.Request, +ctx: D.Context,
  +i: Interest) -> WithoutFrame(R.render_authenticated(m, r, ctx), frame_interest(i)):
  match m:
    case R.Micro{+a, +b, +c, +d}:
      concatenate_without_frame(R.render_received(R.Micro{a, b, c, d}, r),
        Q.concatenate(M.expand_primitives(b), [Q.Authenticated{r, Some{ctx}}]), frame_interest(i),
        received_without_interest(R.Micro{a, b, c, d}, r, i),
        concatenate_without_frame(M.expand_primitives(b), [Q.Authenticated{r, Some{ctx}}], frame_interest(i),
          primitives_without_interest(b, i),
          head_without_execution(Q.Authenticated{r, Some{ctx}}, frame_interest(i), Nil{}, {==},
            interest_and_execution(i), empty_without_frame(frame_interest(i)))))

def verified_without_interest(+m: R.Micro, +r: P.Request, +ctx: D.Context,
  +i: Interest) -> WithoutFrame(R.render_verified(m, r, ctx), frame_interest(i)):
  concatenate_without_frame(R.render_authenticated(m, r, ctx), [Q.Accepts{r, ctx}], frame_interest(i),
    authenticated_without_interest(m, r, ctx, i),
    head_without_execution(Q.Accepts{r, ctx}, frame_interest(i), Nil{}, {==},
      interest_and_execution(i), empty_without_frame(frame_interest(i))))

def started_without_other_interest(+m: R.Micro, +r: P.Request, +ctx: D.Context,
  +i: Interest, outside: OutsideStart(i)) -> WithoutFrame(R.render_started(m, r, ctx), frame_interest(i)):
  match m:
    case R.Micro{+a, +b, +c, +d}:
      concatenate_without_frame(R.render_verified(R.Micro{a, b, c, d}, r, ctx),
        Q.concatenate(M.expand_primitives(c), [Q.Started{r, ctx}]), frame_interest(i),
        verified_without_interest(R.Micro{a, b, c, d}, r, ctx, i),
        concatenate_without_frame(M.expand_primitives(c), [Q.Started{r, ctx}], frame_interest(i),
          primitives_without_interest(c, i),
          head_by_tag(q => Bool.not(is_start(q)), Q.Started{r, ctx}, frame_interest(i), Nil{},
            {==}, interest_outside_start(i, outside), empty_without_frame(frame_interest(i)))))

def neutral_in_front(+h: Q.Frame, -rest: List<&2, Q.Frame>, +i: Interest,
  neutral: {of_execution(h) == False{} : Bool}, without: WithoutFrame(rest, frame_interest(i))) ->
  WithoutFrame(Con{h, rest}, frame_interest(i)):
  head_without_execution(h, frame_interest(i), rest, neutral, interest_and_execution(i), without)

def prefix_executed(m: R.Micro, +r: P.Request, +ctx: D.Context) -> List<&2, Q.Frame>:
  Con{Q.Configured{}, R.render_started(m, r, ctx)}

def prefix_without_other_interest(+m: R.Micro, +r: P.Request, +ctx: D.Context,
  +i: Interest, outside: OutsideStart(i)) -> WithoutFrame(prefix_executed(m, r, ctx), frame_interest(i)):
  neutral_in_front(Q.Configured{}, R.render_started(m, r, ctx), i, {==},
    started_without_other_interest(m, r, ctx, i, outside))

def prefix_without_conclusion(+m: R.Micro, +r: P.Request, +ctx: D.Context) ->
  {Phases.absent(Phases.Conclusion{}, prefix_executed(m, r, ctx)) == True{} : Bool}:
  Phases.started_without_macros(Phases.Conclusion{}, m, r, ctx)

law start_of_prefix:
  for +m: R.Micro
  for +r: P.Request
  for +ctx: D.Context
  exs b: Nat
  {Q.query(prefix_executed(m, r, ctx), b) == Some{Q.Started{r, ctx}} : Maybe<&2, Q.Frame>}
def start_of_prefix(m, r, ctx):
  match m:
    case R.Micro{+a, +b, +c, +d}:
      (Succ{Nat.add(Q.size(R.render_verified(R.Micro{a, b, c, d}, r, ctx)),
        Nat.add(Q.size(M.expand_primitives(c)), 0n))},
        Equal.trans(Maybe<&2, Q.Frame>,
          Q.query(R.render_started(R.Micro{a, b, c, d}, r, ctx),
            Nat.add(Q.size(R.render_verified(R.Micro{a, b, c, d}, r, ctx)),
              Nat.add(Q.size(M.expand_primitives(c)), 0n))),
          Q.query(Q.concatenate(M.expand_primitives(c), [Q.Started{r, ctx}]),
            Nat.add(Q.size(M.expand_primitives(c)), 0n)), Some{Q.Started{r, ctx}},
          Q.query_after_prefix(R.render_verified(R.Micro{a, b, c, d}, r, ctx),
            Q.concatenate(M.expand_primitives(c), [Q.Started{r, ctx}]), Nat.add(Q.size(M.expand_primitives(c)), 0n)),
          Q.query_after_prefix(M.expand_primitives(c), [Q.Started{r, ctx}], 0n)))

def later_delivery_without_interest(closes: Bool, +s: D.State, next: Bool, +i: Interest) ->
  WithoutFrame(R.later_delivery(closes, s, next), frame_interest(i)):
  match closes next:
    case True{} _:
      neutral_in_front(Q.Closed{}, Nil{}, i, {==}, empty_without_frame(frame_interest(i)))
    case False{} True{}:
      neutral_in_front(Q.Next{s, s}, Nil{}, i, {==}, empty_without_frame(frame_interest(i)))
    case False{} False{}: empty_without_frame(frame_interest(i))

def delivery_without_interest(+s: D.State, +bs: List<&2, U32>, +closes: Bool,
  delivery: R.Delivery, +i: Interest) -> WithoutFrame(R.render_delivery(s, bs, closes, delivery), frame_interest(i)):
  match delivery:
    case R.Complete{+next}:
      neutral_in_front(Q.Delivered{bs}, R.later_delivery(closes, s, next), i, {==},
        later_delivery_without_interest(closes, s, next, i))
    case R.Broken{+prefix}:
      neutral_in_front(Q.Interrupted{prefix}, [Q.Closed{}], i, {==},
        neutral_in_front(Q.Closed{}, Nil{}, i, {==}, empty_without_frame(frame_interest(i))))
    case R.PendingDelivery{}: empty_without_frame(frame_interest(i))

def publication_without_interest(r: S.Response, +s: D.State, +i: Interest) ->
  WithoutFrame(R.render_publication(r, s), frame_interest(i)):
  match r:
    case S.Response{S.Success{}, v}:
      neutral_in_front(Q.Published{s}, Nil{}, i, {==}, empty_without_frame(frame_interest(i)))
    case S.Response{S.Refusal{}, v}: empty_without_frame(frame_interest(i))
    case S.Response{S.Input{}, v}: empty_without_frame(frame_interest(i))
    case S.Response{S.Authentication{}, v}: empty_without_frame(frame_interest(i))
    case S.Response{S.Certificate{}, v}: empty_without_frame(frame_interest(i))
    case S.Response{S.DataError{}, v}: empty_without_frame(frame_interest(i))
    case S.Response{S.Limit{}, v}: empty_without_frame(frame_interest(i))
    case S.Response{S.Failure{}, v}: empty_without_frame(frame_interest(i))

def conclusion_without_interest(conclusion: N.Conclusion, +closes: Bool, +delivery: R.Delivery,
  +i: Interest) -> WithoutFrame(R.render_conclusion(conclusion, closes, delivery), frame_interest(i)):
  match conclusion:
    case N.Conclusion{+s, +r, +bs}:
      neutral_in_front(Q.Prepared{r, bs},
        Q.concatenate(R.render_publication(r, s), Con{Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, delivery)}),
        i, {==}, concatenate_without_frame(R.render_publication(r, s),
          Con{Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, delivery)}, frame_interest(i),
          publication_without_interest(r, s, i),
          neutral_in_front(Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, delivery), i, {==},
            delivery_without_interest(s, bs, closes, delivery, i))))

def error_framed_without_interest(q: Maybe<&2, List<&2, U32>>, +response: S.Response,
  +initial: D.State, +closes: Bool, +delivery: R.Delivery, +i: Interest) ->
  WithoutFrame(R.render_error_framed(q, response, initial, closes, delivery), frame_interest(i)):
  match q:
    case None{}: empty_without_frame(frame_interest(i))
    case Some{+bs}:
      neutral_in_front(Q.Prepared{response, bs}, Con{Q.Completed{response, initial, closes},
        R.render_delivery(initial, bs, closes, delivery)}, i, {==},
        neutral_in_front(Q.Completed{response, initial, closes}, R.render_delivery(initial, bs, closes, delivery),
          i, {==}, delivery_without_interest(initial, bs, closes, delivery, i)))

def error_without_interest(+status: S.Status, +initial: D.State, +closes: Bool,
  +delivery: R.Delivery, +i: Interest) -> WithoutFrame(R.render_error(status, initial, closes, delivery), frame_interest(i)):
  error_framed_without_interest(P.frame(S.response_value(S.response_error(status))),
    S.response_error(status), initial, closes, delivery, i)

def failure_end_without_interest(+s: D.State, fatal: Bool, +delivery: R.Delivery, +i: Interest) ->
  WithoutFrame(R.render_failure_end(s, fatal, delivery), frame_interest(i)):
  match fatal:
    case True{}: neutral_in_front(Q.Closed{}, Nil{}, i, {==}, empty_without_frame(frame_interest(i)))
    case False{}: error_without_interest(S.Failure{}, s, False{}, delivery, i)

def failure_without_interest(+s: D.State, +stage: X.Stage, +id: String, +fatal: Bool,
  +delivery: R.Delivery, +i: Interest) -> WithoutFrame(R.render_failure(s, stage, id, fatal, delivery), frame_interest(i)):
  neutral_in_front(Q.Failed{stage, id, fatal}, R.render_failure_end(s, fatal, delivery), i, {==},
    failure_end_without_interest(s, fatal, delivery, i))

def conclusion_negative_precedes_prefix(+before: List<&2, Q.Frame>, +later: List<&2, Q.Frame>,
  +t: Nat, -q: Q.Frame, present: {Q.query(before, t) == Some{q} : Maybe<&2, Q.Frame>},
  without: {Phases.absent(Phases.Conclusion{}, before) == True{} : Bool},
  +u: Nat, +r: S.Response, +s: D.State, +closes: Bool,
  order: {Nat.is_lt(u, t) == True{} : Bool},
  completed: {Q.query(Q.concatenate(before, later), u) == Some{Q.Completed{r, s, closes}} : Maybe<&2, Q.Frame>}) -> Empty:
  Phases.absent_excludes_query(Phases.Conclusion{}, before, u, Q.Completed{r, s, closes},
      without, {==}, Equal.trans(Maybe<&2, Q.Frame>, Q.query(before, u),
        Q.query(Q.concatenate(before, later), u), Some{Q.Completed{r, s, closes}},
        Equal.sym(Maybe<&2, Q.Frame>, Q.query(Q.concatenate(before, later), u), Q.query(before, u),
          Q.query_inside_prefix(before, later, u,
            Q.less_transitive(u, t, Q.size(before), order,
              Q.position_present_inside(before, t, q, present)))), completed))

def origin_frame_extracted(+r: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>,
  +suffix: List<&2, Q.Frame>, -t: Nat, +base: Nat, -q: Q.Frame,
  later_without: WithoutFrame(suffix, q),
  origin: &i: Nat -> L.E<{t == Nat.add(base, i) : Nat},
    {Q.query(Q.concatenate(Q.expand_exec(r, ctx, xs), suffix), i) == Some{q} : Maybe<&2, Q.Frame>}>) ->
  &i: Nat -> L.E<{t == Nat.add(base, i) : Nat},
    E.Reflection(r, ctx, E.query(xs, i), q)>:
  match origin:
    case (+i, L.Both{position, query_result}):
      (i, L.Both{position,
        E.expand_reflects_query(r, ctx, xs, i, q,
          remove_suffix_without_frame(Q.expand_exec(r, ctx, xs), suffix, i,
            q, later_without, query_result))})

def origin_frame_in_subtrace(+prefix: List<&2, Q.Frame>, +suffix: List<&2, Q.Frame>,
  +r: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>, +t: Nat, -q: Q.Frame,
  before_without: WithoutFrame(prefix, q), later_without: WithoutFrame(suffix, q),
  present: {Q.query(subtrace(prefix, Q.expand_exec(r, ctx, xs), suffix), t) ==
    Some{q} : Maybe<&2, Q.Frame>}) ->
  &i: Nat -> L.E<{t == Nat.add(Q.size(prefix), i) : Nat},
    E.Reflection(r, ctx, E.query(xs, i), q)>:
  origin_frame_extracted(r, ctx, xs, suffix, t, Q.size(prefix), q, later_without,
    remove_prefix_without_frame(prefix, Q.concatenate(Q.expand_exec(r, ctx, xs), suffix), t,
      q, before_without, present))

def extract_conclusion(-G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  -c: S.Configuration, -p: S.Program, +initial: Maybe<&2, D.State>, +xs: List<&2, Q.Frame>,
  +u: Nat, +response: S.Response, +s: D.State, +closes: Bool,
  refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H, E.observation_model(c, p, initial, xs)) : Nat -> I.Fact -> Type},
  observed: I.Happens(a, k, x, u, I.Concluded{response, s, closes})) ->
  {Q.query(xs, u) == Some{Q.Completed{response, s, closes}} : Maybe<&2, Q.Frame>}:
  Q.observation_frame(c, p, xs, u, I.Concluded{response, s, closes},
    Ref.remove_guards(G, H, Q.observes(c, p, xs, u, I.Concluded{response, s, closes}),
      (%refinement : _(u, I.Concluded{response, s, closes}) observed)))

def extract_evaluation(-G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  -c: S.Configuration, -program: S.Program, +initial: Maybe<&2, D.State>, +xs: List<&2, Q.Frame>,
  +u: Nat, +r: P.Request, +ctx: D.Context, -p: S.Program, +execution_trace: S.Trace,
  refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H, E.observation_model(c, program, initial, xs)) : Nat -> I.Fact -> Type},
  observed: I.Happens(a, k, x, u, I.Evaluated{r, ctx, p, execution_trace})) ->
  {Q.query(xs, u) == Some{Q.Evaluated{r, ctx, execution_trace}} : Maybe<&2, Q.Frame>}:
  Q.observation_frame(c, program, xs, u, I.Evaluated{r, ctx, p, execution_trace},
    Ref.remove_guards(G, H, Q.observes(c, program, xs, u, I.Evaluated{r, ctx, p, execution_trace}),
      (%refinement : _(u, I.Evaluated{r, ctx, p, execution_trace}) observed)))

law query_without_suffix:
  for +prefix: List<&2, Q.Frame>
  for +body: List<&2, Q.Frame>
  for +t: Nat
  for -q: Q.Frame
  for present: {Q.query(body, t) == Some{q} : Maybe<&2, Q.Frame>}
  {Q.query(Q.concatenate(prefix, body), Nat.add(Q.size(prefix), t)) == Some{q} : Maybe<&2, Q.Frame>}
def query_without_suffix(prefix, body, t, q, present):
  Equal.trans(Maybe<&2, Q.Frame>, Q.query(Q.concatenate(prefix, body), Nat.add(Q.size(prefix), t)),
    Q.query(body, t), Some{q}, Q.query_after_prefix(prefix, body, t), present)

def without_conclusion_in_block_in(-G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  -c: S.Configuration, -p: S.Program, +initial: Maybe<&2, D.State>,
  +prefix: List<&2, Q.Frame>, +body: List<&2, Q.Frame>, +suffix: List<&2, Q.Frame>,
  +t: Nat, -q: Q.Frame,
  refinement: {E.observation_real(a, k, x) ==
    Ref.observation_stored(G, H, E.observation_model(c, p, initial, subtrace(prefix, body, suffix))) : Nat -> I.Fact -> Type},
  present: {Q.query(body, t) == Some{q} : Maybe<&2, Q.Frame>},
  without_prefix: {Phases.absent(Phases.Conclusion{}, prefix) == True{} : Bool},
  without_body: {Phases.absent(Phases.Conclusion{}, body) == True{} : Bool},
  +response: S.Response, +published: D.State, +closes: Bool,
  previous: I.Before(a, k, x, Nat.add(Q.size(prefix), t), I.Concluded{response, published, closes})) -> Empty:
  match previous:
    case (+u, L.Both{order, observed}):
      conclusion_negative_precedes_prefix(Q.concatenate(prefix, body), suffix,
        Nat.add(Q.size(prefix), t), q, query_without_suffix(prefix, body, t, q, present),
        Phases.concatenate_absence(Phases.Conclusion{}, prefix, body, without_prefix, without_body),
        u, response, published, closes, order,
        (%Equal.sym(List<&2, Q.Frame>, Q.concatenate(Q.concatenate(prefix, body), suffix),
          subtrace(prefix, body, suffix), Q.concatenate_assoc(prefix, body, suffix)) :
          {Q.query(_, u) == Some{Q.Completed{response, published, closes}} : Maybe<&2, Q.Frame>}
          extract_conclusion(G, H, a, k, x, c, p, initial, subtrace(prefix, body, suffix),
            u, response, published, closes, refinement, observed)))
def without_conclusion_in_block(-G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  -c: S.Configuration, -p: S.Program, +initial: Maybe<&2, D.State>,
  +prefix: List<&2, Q.Frame>, +body: List<&2, Q.Frame>, +suffix: List<&2, Q.Frame>,
  +t: Nat, -q: Q.Frame,
  refinement: {E.observation_real(a, k, x) ==
    Ref.observation_stored(G, H, E.observation_model(c, p, initial, subtrace(prefix, body, suffix))) : Nat -> I.Fact -> Type},
  present: {Q.query(body, t) == Some{q} : Maybe<&2, Q.Frame>},
  without_prefix: {Phases.absent(Phases.Conclusion{}, prefix) == True{} : Bool},
  without_body: {Phases.absent(Phases.Conclusion{}, body) == True{} : Bool}) ->
  V.WithoutConclusionPrevious(a, k, x, Nat.add(Q.size(prefix), t)):
  response => published => closes => previous =>
    without_conclusion_in_block_in(G, H, a, k, x, c, p, initial, prefix, body, suffix, t, q,
      refinement, present, without_prefix, without_body, response, published, closes, previous)

law shift_reflects_before:
  for base: Nat
  for +a: Nat
  for +b: Nat
  for order: {Nat.is_lt(Nat.add(base, a), Nat.add(base, b)) == True{} : Bool}
  {Nat.is_lt(a, b) == True{} : Bool}
def shift_reflects_before(base, a, b, order):
  match base:
    case 0n: order
    case 1n+j: shift_reflects_before(j, a, b, order)

def final_negative_precedes_origin(+base: Nat, +xs: List<&2, Q.FrameExec>,
  +u: Nat, +t: Nat, -q: Q.FrameExec, +r: P.Request, +ctx: D.Context,
  +rq: P.Request, +cx: D.Context, +w: D.State, +ts: List<&2, S.OperationEvent>, +response: S.Response,
  order: {Nat.is_lt(u, Nat.add(base, t)) == True{} : Bool},
  query_result: {E.query(xs, t) == Some{q} : Maybe<&2, Q.FrameExec>},
  terminates: E.TerminatesInFirst(xs),
  origin: &i: Nat -> L.E<{u == Nat.add(base, i) : Nat},
    E.Reflection(r, ctx, E.query(xs, i), Q.Evaluated{rq, cx, S.Final{w, ts, response}})>) -> Empty:
  match origin:
    case (+i, L.Both{position, L.Both{same_req, L.Both{same_ctx, final}}}):
      E.final_prevents_query_subsequent(xs, i, t, w, ts, response, q,
        shift_reflects_before(base, i, t,
          (%position : {Nat.is_lt(_, Nat.add(base, t)) == True{} : Bool} order)),
        final, query_result, terminates)

def final_negative_precedes_generator_in(~program: Nat -> S.Program, +world: Nat,
  -G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  -c: S.Configuration, +initial: Maybe<&2, D.State>,
  +prefix: List<&2, Q.Frame>, +suffix: List<&2, Q.Frame>,
  +r: P.Request, +ctx: D.Context, +s0: D.State, +e: D.Schema, +n: Nat,
  +t: Nat, +q: Q.FrameExec,
  before_without: @rq: P.Request -> @cx: D.Context -> @execution_trace: S.Trace ->
    WithoutFrame(prefix, Q.Evaluated{rq, cx, execution_trace}),
  later_without: @rq: P.Request -> @cx: D.Context -> @execution_trace: S.Trace ->
    WithoutFrame(suffix, Q.Evaluated{rq, cx, execution_trace}),
  refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
    E.observation_model(c, program(world), initial,
      subtrace(prefix, Q.expand_exec(r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e)), suffix))) : Nat -> I.Fact -> Type},
  present: {E.query(E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e), t) == Some{q} : Maybe<&2, Q.FrameExec>},
  +rq: P.Request, +cx: D.Context, -p: S.Program, +w: D.State, +ts: List<&2, S.OperationEvent>, +response: S.Response,
  previous: I.Before(a, k, x, Nat.add(Q.size(prefix), t), I.Evaluated{rq, cx, p, S.Final{w, ts, response}})) -> Empty:
  match previous:
    case (+u, L.Both{order, observed}):
      final_negative_precedes_origin(Q.size(prefix),
        E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e), u, t, q, r, ctx, rq, cx, w, ts, response,
        order, present, E.generator_for_in_first_final(n, N.start(program(world), ctx, I.arguments(r), s0), e),
        origin_frame_in_subtrace(prefix, suffix, r, ctx,
          E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e), u,
          Q.Evaluated{rq, cx, S.Final{w, ts, response}},
          before_without(rq, cx, S.Final{w, ts, response}), later_without(rq, cx, S.Final{w, ts, response}),
          extract_evaluation(G, H, a, k, x, c, program(world), initial,
            subtrace(prefix, Q.expand_exec(r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e)), suffix),
            u, rq, cx, p, S.Final{w, ts, response}, refinement, observed)))

law none_final_precedes_query_generated:
  for ~program: Nat -> S.Program
  for +world: Nat
  for -G: Type
  for -H: Type
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for -c: S.Configuration
  for +initial: Maybe<&2, D.State>
  for +prefix: List<&2, Q.Frame>
  for +suffix: List<&2, Q.Frame>
  for +r: P.Request
  for +ctx: D.Context
  for +s0: D.State
  for +e: D.Schema
  for +n: Nat
  for +t: Nat
  for +q: Q.FrameExec
  for before_without: @rq: P.Request -> @cx: D.Context -> @execution_trace: S.Trace ->
    WithoutFrame(prefix, Q.Evaluated{rq, cx, execution_trace})
  for later_without: @rq: P.Request -> @cx: D.Context -> @execution_trace: S.Trace ->
    WithoutFrame(suffix, Q.Evaluated{rq, cx, execution_trace})
  for refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
    E.observation_model(c, program(world), initial,
      subtrace(prefix, Q.expand_exec(r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e)), suffix))) : Nat -> I.Fact -> Type}
  for present: {E.query(E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e), t) == Some{q} : Maybe<&2, Q.FrameExec>}
  V.PrefixesNotTerminated(a, k, x, Nat.add(Q.size(prefix), t))
def none_final_precedes_query_generated(program, world, G, H, a, k, x, c, initial, prefix, suffix,
  r, ctx, s0, e, n, t, q, before_without, later_without, refinement, present):
  rq => cx => p => w => ts => response => previous =>
    final_negative_precedes_generator_in(program, world, G, H, a, k, x, c, initial, prefix, suffix,
      r, ctx, s0, e, n, t, q, before_without, later_without, refinement, present, rq, cx, p, w, ts, response, previous)

def prefixes_in_order_of_origin(~program: Nat -> S.Program, +world: Nat,
  +base: Nat, +r: P.Request, +ctx: D.Context, +s0: D.State, +e: D.Schema, +n: Nat,
  +u: Nat, +t: Nat, +before: S.Trace, +current: S.Trace,
  order: {Nat.is_lt(u, Nat.add(base, t)) == True{} : Bool},
  query_result: {E.query(E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e), t) ==
    Some{Q.Evaluation{current}} : Maybe<&2, Q.FrameExec>},
  origin: &i: Nat -> L.E<{u == Nat.add(base, i) : Nat},
    E.Reflection(r, ctx,
      E.query(E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e), i), Q.Evaluated{r, ctx, before})>) ->
  L.Prefix(S.OperationEvent, S.events_execution_trace(before), S.events_execution_trace(current)):
  match origin:
    case (+i, L.Both{position, L.Both{same_req, L.Both{same_ctx, previous}}}):
      E.prefixes_of_evaluations_in_order(i, t, N.start(program(world), ctx, I.arguments(r), s0), e, before, current,
        shift_reflects_before(base, i, t,
          (%position : {Nat.is_lt(_, Nat.add(base, t)) == True{} : Bool} order)),
        E.evaluations_real(n, N.start(program(world), ctx, I.arguments(r), s0), e, i, before, previous),
        E.evaluations_real(n, N.start(program(world), ctx, I.arguments(r), s0), e, t, current, query_result))

law evaluations_generated_in_order:
  for ~program: Nat -> S.Program
  for +world: Nat
  for -G: Type
  for -H: Type
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for -c: S.Configuration
  for +initial: Maybe<&2, D.State>
  for +prefix: List<&2, Q.Frame>
  for +suffix: List<&2, Q.Frame>
  for +r: P.Request
  for +ctx: D.Context
  for +s0: D.State
  for +e: D.Schema
  for +n: Nat
  for +t: Nat
  for +execution_trace: S.Trace
  for before_without: @rq: P.Request -> @cx: D.Context -> @p: S.Trace ->
    WithoutFrame(prefix, Q.Evaluated{rq, cx, p})
  for later_without: @rq: P.Request -> @cx: D.Context -> @p: S.Trace ->
    WithoutFrame(suffix, Q.Evaluated{rq, cx, p})
  for refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
    E.observation_model(c, program(world), initial,
      subtrace(prefix, Q.expand_exec(r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e)), suffix))) : Nat -> I.Fact -> Type}
  for present: {E.query(E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e), t) ==
    Some{Q.Evaluation{execution_trace}} : Maybe<&2, Q.FrameExec>}
  Laws.PrefixesInOrder(a, k, x, Nat.add(Q.size(prefix), t), r, ctx, program(world), execution_trace)
def evaluations_generated_in_order(program, world, G, H, a, k, x, c, initial, prefix, suffix,
  r, ctx, s0, e, n, t, execution_trace, before_without, later_without, refinement, present):
  +u => +previous => order => observed =>
    prefixes_in_order_of_origin(program, world, Q.size(prefix), r, ctx, s0, e, n,
      u, t, previous, execution_trace, order, present,
      origin_frame_in_subtrace(prefix, suffix, r, ctx,
        E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e), u, Q.Evaluated{r, ctx, previous},
        before_without(r, ctx, previous), later_without(r, ctx, previous),
        extract_evaluation(G, H, a, k, x, c, program(world), initial,
          subtrace(prefix, Q.expand_exec(r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), e)), suffix),
          u, r, ctx, program(world), previous, refinement, observed)))

law less_remains_combined_addition:
  for a: Nat
  for b: Nat
  for +n: Nat
  for less: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(a, Nat.add(b, n)) == True{} : Bool}
def less_remains_combined_addition(a, b, n, less):
  match a b:
    case 0n 0n: F.absurd_boolean({Nat.is_lt(0n, Nat.add(0n, n)) == True{} : Bool}, less)
    case 0n 1n+j: {==}
    case 1n+i 0n: F.absurd_boolean({Nat.is_lt(1n+i, Nat.add(0n, n)) == True{} : Bool}, less)
    case 1n+i 1n+j: less_remains_combined_addition(i, j, n, less)

def start_observed_before(-G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  -c: S.Configuration, -p: S.Program, +initial: Maybe<&2, D.State>,
  +prefix: List<&2, Q.Frame>, +body: List<&2, Q.Frame>, +suffix: List<&2, Q.Frame>,
  +r: P.Request, +ctx: D.Context, +t: Nat, +b: Nat,
  refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
    E.observation_model(c, p, initial, subtrace(prefix, body, suffix))) : Nat -> I.Fact -> Type},
  guards: L.E<G, H>,
  present: {Q.query(prefix, b) == Some{Q.Started{r, ctx}} : Maybe<&2, Q.Frame>}) ->
  I.Before(a, k, x, Nat.add(Q.size(prefix), t), I.ProgramStarted{r, ctx, p}):
  F.combined_pair(I.Before(a, k, x, Nat.add(Q.size(prefix), t), I.ProgramStarted{r, ctx, p}),
    {Q.query(prefix, b) == Some{Q.Started{r, ctx}} : Maybe<&2, Q.Frame>},
    {Q.query(prefix, b) == Some{Q.Started{r, ctx}} : Maybe<&2, Q.Frame>},
    Call.duplicate_equality(Maybe<&2, Q.Frame>, Q.query(prefix, b), Some{Q.Started{r, ctx}}, present),
    limit => observed =>
      (b, L.Both{less_remains_combined_addition(b, Q.size(prefix), t,
          Q.position_present_inside(prefix, b, Q.Started{r, ctx}, limit)),
        (%Equal.sym((Nat -> I.Fact -> Type), E.observation_real(a, k, x),
          Ref.observation_stored(G, H, E.observation_model(c, p, initial, subtrace(prefix, body, suffix))), refinement) :
          _(b, I.ProgramStarted{r, ctx, p})
          Ref.combined_guards(G, H, Q.observes(c, p, subtrace(prefix, body, suffix), b, I.ProgramStarted{r, ctx, p}), guards,
            Q.query_establishes_observation(c, p, subtrace(prefix, body, suffix), b, Q.Started{r, ctx},
              I.ProgramStarted{r, ctx, p},
              query_of_subtrace(Nil{}, prefix, Q.concatenate(body, suffix), b, Q.Started{r, ctx}, observed), {==})))}))

type Four<-P: Type> is Type:
  Four{a: P, b: P, c: P, d: P}

def four_equalities(-A: Type, -x: A, -y: A, proof: {x == y : A}) -> Four<{x == y : A}>:
  %proof : Four<{x == _ : A}>
  Four{{==}, {==}, {==}, {==}}

def combined_four(-P: Type, -T: Type, proofs: Four<P>, resume: P -> P -> P -> P -> T) -> T:
  match proofs:
    case Four{a, b, c, d}: resume(a, b, c, d)

def start_observed_combined_index(-G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  -c: S.Configuration, -p: S.Program, +initial: Maybe<&2, D.State>,
  +prefix: List<&2, Q.Frame>, +body: List<&2, Q.Frame>, +suffix: List<&2, Q.Frame>,
  +r: P.Request, +ctx: D.Context, +t: Nat,
  refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
    E.observation_model(c, p, initial, subtrace(prefix, body, suffix))) : Nat -> I.Fact -> Type},
  guards: L.E<G, H>,
  start: &b: Nat -> {Q.query(prefix, b) == Some{Q.Started{r, ctx}} : Maybe<&2, Q.Frame>}) ->
  I.Before(a, k, x, Nat.add(Q.size(prefix), t), I.ProgramStarted{r, ctx, p}):
  match start:
    case (+b, present):
      start_observed_before(G, H, a, k, x, c, p, initial, prefix, body, suffix, r, ctx, t, b,
        refinement, guards, present)

def evaluation_satisfies_rule5(~program: Nat -> S.Program, ~c: S.Configuration,
  +world: Nat, -G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  +m: R.Micro, +suffix: List<&2, Q.Frame>, +r: P.Request, +ctx: D.Context,
  +s0: D.State, +n: Nat, +t: Nat, +execution_trace: S.Trace,
  configuration: {c == I.configuration(x) : S.Configuration}, state: {s0 == I.initial(x) : D.State},
  guards: L.E<G, H>,
  suffixes: L.E<(@rq: P.Request -> @cx: D.Context -> @p: S.Trace -> WithoutFrame(suffix, Q.Evaluated{rq, cx, p})),
    (@rq: P.Request -> @cx: D.Context -> @p: S.Trace -> WithoutFrame(suffix, Q.Evaluated{rq, cx, p}))>,
  refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
    E.observation_model(c, program(world), Some{s0},
      subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx,
        E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix))) : Nat -> I.Fact -> Type},
  present: {E.query(E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)), t) ==
    Some{Q.Evaluation{execution_trace}} : Maybe<&2, Q.FrameExec>}) ->
  Laws.Rule5(I.Evaluated{r, ctx, program(world), execution_trace}, a, k, x,
    Nat.add(Q.size(prefix_executed(m, r, ctx)), t)):
  combined_four(
    {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
      E.observation_model(c, program(world), Some{s0}, subtrace(prefix_executed(m, r, ctx),
        Q.expand_exec(r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix))) : Nat -> I.Fact -> Type},
    Laws.Rule5(I.Evaluated{r, ctx, program(world), execution_trace}, a, k, x,
      Nat.add(Q.size(prefix_executed(m, r, ctx)), t)),
    four_equalities((Nat -> I.Fact -> Type), E.observation_real(a, k, x),
      Ref.observation_stored(G, H, E.observation_model(c, program(world), Some{s0}, subtrace(prefix_executed(m, r, ctx),
        Q.expand_exec(r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix))), refinement),
    ref1 => ref2 => ref3 => ref4 =>
      combined_four(
        {E.query(E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)), t) ==
          Some{Q.Evaluation{execution_trace}} : Maybe<&2, Q.FrameExec>},
        Laws.Rule5(I.Evaluated{r, ctx, program(world), execution_trace}, a, k, x,
          Nat.add(Q.size(prefix_executed(m, r, ctx)), t)),
        four_equalities(Maybe<&2, Q.FrameExec>,
          E.query(E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)), t),
          Some{Q.Evaluation{execution_trace}}, present),
        h1 => h2 => h3 => h4 =>
          F.combined_pair(Laws.Rule5(I.Evaluated{r, ctx, program(world), execution_trace}, a, k, x,
              Nat.add(Q.size(prefix_executed(m, r, ctx)), t)),
            (@rq: P.Request -> @cx: D.Context -> @p: S.Trace -> WithoutFrame(suffix, Q.Evaluated{rq, cx, p})),
            (@rq: P.Request -> @cx: D.Context -> @p: S.Trace -> WithoutFrame(suffix, Q.Evaluated{rq, cx, p})),
            suffixes, suf1 => suf2 =>
              L.Both{L.Both{
                without_conclusion_in_block(G, H, a, k, x, c, program(world), Some{s0}, prefix_executed(m, r, ctx),
                  Q.expand_exec(r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))),
                  suffix, t, Q.Evaluated{r, ctx, execution_trace}, ref1,
                  E.expand_preserves_query(r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)), t, Q.Evaluation{execution_trace}, h1),
                  prefix_without_conclusion(m, r, ctx), Phases.execution_without_macros(Phases.Conclusion{}, r, ctx,
                    E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)))),
                none_final_precedes_query_generated(program, world, G, H, a, k, x, c, Some{s0}, prefix_executed(m, r, ctx),
                  suffix, r, ctx, s0, S.schema(c), n, t, Q.Evaluation{execution_trace},
                  +rq => +cx => +p => prefix_without_other_interest(m, r, ctx, Evaluation{rq, cx, p}, Unit{}),
                  suf1, ref2, h2)},
                L.Both{start_observed_combined_index(G, H, a, k, x, c, program(world), Some{s0}, prefix_executed(m, r, ctx),
                    Q.expand_exec(r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))),
                    suffix, r, ctx, t, ref3, guards, start_of_prefix(m, r, ctx)),
                  L.Both{
                    (%configuration : I.ExecutionCorrect(_, I.initial(x), r, ctx, program(world), execution_trace)
                      %state : I.ExecutionCorrect(c, _, r, ctx, program(world), execution_trace)
                      E.evaluation_exact_of_program(program, world, c, S.schema(c), s0, r, ctx, n, t, execution_trace, {==}, h3)),
                    evaluations_generated_in_order(program, world, G, H, a, k, x, c, Some{s0}, prefix_executed(m, r, ctx),
                      suffix, r, ctx, s0, S.schema(c), n, t, execution_trace,
                      +rq => +cx => +p => prefix_without_other_interest(m, r, ctx, Evaluation{rq, cx, p}, Unit{}), suf2, ref4, h4)}}})))

def operation_satisfies_rule5(~program: Nat -> S.Program, ~c: S.Configuration,
  +world: Nat, -G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  +m: R.Micro, +suffix: List<&2, Q.Frame>, +r: P.Request, +ctx: D.Context,
  +s0: D.State, +n: Nat, +t: Nat, +e: D.Schema, +s: D.State, +o: D.Operation, +result: D.ResultOp,
  configuration: {c == I.configuration(x) : S.Configuration},
  guards: L.E<L.E<G, H>, L.E<G, H>>,
  suffix_without: @rq: P.Request -> @cx: D.Context -> @p: S.Trace -> WithoutFrame(suffix, Q.Evaluated{rq, cx, p}),
  refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
    E.observation_model(c, program(world), Some{s0},
      subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx,
        E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix))) : Nat -> I.Fact -> Type},
  present: {E.query(E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)), t) ==
    Some{Q.Operation{e, s, o, result}} : Maybe<&2, Q.FrameExec>}) ->
  Laws.Rule5(I.Operated{e, s, o, result}, a, k, x, Nat.add(Q.size(prefix_executed(m, r, ctx)), t)):
  combined_four(
    {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
      E.observation_model(c, program(world), Some{s0}, subtrace(prefix_executed(m, r, ctx),
        Q.expand_exec(r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix))) : Nat -> I.Fact -> Type},
    Laws.Rule5(I.Operated{e, s, o, result}, a, k, x, Nat.add(Q.size(prefix_executed(m, r, ctx)), t)),
    four_equalities((Nat -> I.Fact -> Type), E.observation_real(a, k, x),
      Ref.observation_stored(G, H, E.observation_model(c, program(world), Some{s0}, subtrace(prefix_executed(m, r, ctx),
        Q.expand_exec(r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix))), refinement),
    ref1 => ref2 => ref3 => ref4 =>
      combined_four(
        {E.query(E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)), t) ==
          Some{Q.Operation{e, s, o, result}} : Maybe<&2, Q.FrameExec>},
        Laws.Rule5(I.Operated{e, s, o, result}, a, k, x, Nat.add(Q.size(prefix_executed(m, r, ctx)), t)),
        four_equalities(Maybe<&2, Q.FrameExec>,
          E.query(E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)), t),
          Some{Q.Operation{e, s, o, result}}, present),
        h1 => h2 => h3 => h4 =>
          L.Both{
            without_conclusion_in_block(G, H, a, k, x, c, program(world), Some{s0}, prefix_executed(m, r, ctx),
              Q.expand_exec(r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))),
              suffix, t, Q.Operated{e, s, o, result}, ref1,
              E.expand_preserves_query(r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)),
                t, Q.Operation{e, s, o, result}, h1),
              prefix_without_conclusion(m, r, ctx), Phases.execution_without_macros(Phases.Conclusion{}, r, ctx,
                E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)))),
            L.Both{none_final_precedes_query_generated(program, world, G, H, a, k, x, c, Some{s0}, prefix_executed(m, r, ctx),
                suffix, r, ctx, s0, S.schema(c), n, t, Q.Operation{e, s, o, result},
                +rq => +cx => +p => prefix_without_other_interest(m, r, ctx, Evaluation{rq, cx, p}, Unit{}), suffix_without, ref2, h2),
              (%Equal.sym((Nat -> I.Fact -> Type), E.observation_real(a, k, x),
                Ref.observation_stored(G, H, E.observation_model(c, program(world), Some{s0}, subtrace(prefix_executed(m, r, ctx),
                  Q.expand_exec(r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix))), ref3) :
                E.Linkage(_, x, Nat.add(Q.size(prefix_executed(m, r, ctx)), t), e, s, o, result)
                linkage_preserves_guards(G, H, E.observation_model(c, program(world), Some{s0}, subtrace(prefix_executed(m, r, ctx),
                    Q.expand_exec(r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix)),
                  x, Nat.add(Q.size(prefix_executed(m, r, ctx)), t), e, s, o, result, guards,
                  all_operation_generated_has_binding_global(program, world, x, c, Some{s0}, prefix_executed(m, r, ctx),
                    suffix, r, ctx, s0, n, t, S.schema(c), e, s, o, result,
                    Equal.cong(S.Configuration, D.Schema, S.schema, c, I.configuration(x), configuration), h3)))}}))

# DERIVED classification of actual process results. The only execution
# premises are generate/traverse/prepare equations in Source.OutputReal.
def PhaseReal(~source: Source.Source, -c: S.Configuration, -s: D.State,
  +origin: Source.JudgmentSyntactic, phase: R.PhaseBefore) -> Type:
  match phase:
    case R.Executing{r, ctx, frames}: Source.PrefixReal(source, c, s, r, ctx, origin, frames)
    case R.AfterPrepare{r, ctx, frames, prepared}: Source.FinalReal(source, c, s, r, ctx, origin, frames, prepared)
    case _: Unit

def BranchReal(~source: Source.Source, -c: S.Configuration, -s: D.State,
  +origin: Source.JudgmentSyntactic, branch: R.Branch) -> Type:
  match branch:
    case R.Executed{r, ctx, frames, prepared, delivery}: Source.FinalReal(source, c, s, r, ctx, origin, frames, prepared)
    case R.FatalAfterPublication{r, ctx, frames, prepared, stage, id}: Source.FinalReal(source, c, s, r, ctx, origin, frames, prepared)
    case R.FailureBefore{phase, stage, id, fatal, delivery}: PhaseReal(source, c, s, origin, phase)
    case R.Pending{phase}: PhaseReal(source, c, s, origin, phase)
    case _: Unit

# Identity origin, derived by the same selectors of the executed case.
def AuthOfPhase(-s: D.State, phase: R.PhaseBefore) -> Type:
  match phase:
    case R.AfterAuthenticate{r, ctx}: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}
    case R.AfterVerify{r, ctx}: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}
    case R.Executing{r, ctx, frames}: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}
    case R.AfterPrepare{r, ctx, frames, prepared}: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}
    case _: Unit

def AuthOfBranch(-s: D.State, branch: R.Branch) -> Type:
  match branch:
    case R.AutRefusal{r, delivery}: {D.authenticate(s, I.credential(r)) == None{} : Maybe<&2, D.Context>}
    case R.GateRefusal{r, ctx, delivery}: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}
    case R.Executed{r, ctx, frames, prepared, delivery}: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}
    case R.FatalAfterPublication{r, ctx, frames, prepared, stage, id}: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}
    case R.FailureBefore{phase, stage, id, fatal, delivery}: AuthOfPhase(s, phase)
    case R.Pending{phase}: AuthOfPhase(s, phase)
    case _: Unit

# Tool-result classification: only branches emitting admission facts
# require Accepted/Refused. Denotations are not stored here.
def GateOfPhase(-j: R.Judgment, phase: R.PhaseBefore) -> Type:
  match phase:
    case R.AfterVerify{r, ctx}: {j == R.Accepted{} : R.Judgment}
    case R.Executing{r, ctx, frames}: {j == R.Accepted{} : R.Judgment}
    case R.AfterPrepare{r, ctx, frames, prepared}: {j == R.Accepted{} : R.Judgment}
    case _: Unit

def GateOfBranch(-j: R.Judgment, branch: R.Branch) -> Type:
  match branch:
    case R.GateRefusal{r, ctx, delivery}: {j == R.Refused{} : R.Judgment}
    case R.Executed{r, ctx, frames, prepared, delivery}: {j == R.Accepted{} : R.Judgment}
    case R.FatalAfterPublication{r, ctx, frames, prepared, stage, id}: {j == R.Accepted{} : R.Judgment}
    case R.FailureBefore{phase, stage, id, fatal, delivery}: GateOfPhase(j, phase)
    case R.Pending{phase}: GateOfPhase(j, phase)
    case _: Unit

def clear_final_real(~source: Source.Source, -c: S.Configuration, -s: D.State,
  +origin: Source.JudgmentSyntactic, +r: P.Request, +ctx: D.Context,
  +frames: List<&2, Q.FrameExec>, +prepared: N.Prepared, cleanup: R.Cleanup,
  +delivery: R.Delivery, real: Source.FinalReal(source, c, s, r, ctx, origin, frames, prepared),
  aut: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}) ->
  L.E<BranchReal(source, c, s, origin, R.decide_cleanup(r, ctx, frames, prepared, cleanup, delivery)),
    L.E<AuthOfBranch(s, R.decide_cleanup(r, ctx, frames, prepared, cleanup, delivery)),
      GateOfBranch(R.Accepted{}, R.decide_cleanup(r, ctx, frames, prepared, cleanup, delivery))>>:
  match cleanup:
    case R.Clears{}: L.Both{real, L.Both{aut, {==}}}
    case R.ErrorCleanup{id, fatal}: L.Both{real, L.Both{aut, {==}}}
    case R.FatalAfterStore{stage, id}: L.Both{real, L.Both{aut, {==}}}
    case R.PendingCleanup{}: L.Both{real, L.Both{aut, {==}}}

def point_real_in_phase(~source: Source.Source, -c: S.Configuration, -s: D.State,
  +origin: Source.JudgmentSyntactic, +r: P.Request, +ctx: D.Context,
  point: R.PointExec, real: Source.PointReal(source, c, s, r, ctx, origin, point),
  aut: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}) ->
  L.E<PhaseReal(source, c, s, origin, R.phase_of_error(point, r, ctx)),
    L.E<AuthOfPhase(s, R.phase_of_error(point, r, ctx)),
      GateOfPhase(R.Accepted{}, R.phase_of_error(point, r, ctx))>>:
  match point:
    case R.BeforeOfStart{}: L.Both{Unit{}, L.Both{aut, {==}}}
    case R.During{frames}: L.Both{real, L.Both{aut, {==}}}
    case R.Prepared{frames, prepared}: L.Both{real, L.Both{aut, {==}}}

def decide_execution_real(~source: Source.Source, -c: S.Configuration, -s: D.State,
  +origin: Source.JudgmentSyntactic, +r: P.Request, +ctx: D.Context,
  output: R.OutputExecution, +cleanup: R.Cleanup, +delivery: R.Delivery,
  real: Source.OutputReal(source, c, s, r, ctx, origin, output),
  aut: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}) ->
  L.E<BranchReal(source, c, s, origin, R.decide_execution(r, ctx, output, cleanup, delivery)),
    L.E<AuthOfBranch(s, R.decide_execution(r, ctx, output, cleanup, delivery)),
      GateOfBranch(R.Accepted{}, R.decide_execution(r, ctx, output, cleanup, delivery))>>:
  match output:
    case R.Finalized{+frames, +prepared}:
      clear_final_real(source, c, s, origin, r, ctx, frames, prepared, cleanup, delivery, real, aut)
    case R.ErrorExecution{point, stage, id, fatal}:
      point_real_in_phase(source, c, s, origin, r, ctx, point, real, aut)
    case R.PendingExecution{point}:
      point_real_in_phase(source, c, s, origin, r, ctx, point, real, aut)

def JudgmentReal(~source: Source.Source, -c: S.Configuration, -s: D.State,
  +origin: Source.JudgmentSyntactic, -r: P.Request, -ctx: D.Context, data: R.DataTools) -> Type:
  match data:
    case R.DataTools{judgment, output, cleanup, delivery, _pre}:
      match judgment:
        case R.Accepted{}: Source.OutputReal(source, c, s, r, ctx, origin, output)
        case _: Unit

def decide_judgment_real(~source: Source.Source, -c: S.Configuration, -s: D.State,
  +origin: Source.JudgmentSyntactic, +r: P.Request, +ctx: D.Context,
  data: R.DataTools, real: JudgmentReal(source, c, s, origin, r, ctx, data),
  aut: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}) ->
  L.E<BranchReal(source, c, s, origin, R.decide_judgment(r, ctx, data)),
    L.E<AuthOfBranch(s, R.decide_judgment(r, ctx, data)), GateOfBranch(R.judgment_of(data), R.decide_judgment(r, ctx, data))>>:
  match data:
    case R.DataTools{judgment, +output, +cleanup, +delivery, _pre}:
      match judgment:
        case R.Accepted{}: decide_execution_real(source, c, s, origin, r, ctx, output, cleanup, delivery, real, aut)
        case R.Refused{}: L.Both{Unit{}, L.Both{aut, {==}}}
        case R.ErrorJudgment{id, fatal}: L.Both{Unit{}, L.Both{aut, Unit{}}}
        case R.PendingJudgment{}: L.Both{Unit{}, L.Both{aut, Unit{}}}

def decide_identity_real(~source: Source.Source, -c: S.Configuration, -s: D.State,
  +origin: Source.JudgmentSyntactic, +r: P.Request, identity: Maybe<&2, D.Context>, +data: R.DataTools,
  real: @ctx: D.Context -> {identity == Some{ctx} : Maybe<&2, D.Context>} ->
    JudgmentReal(source, c, s, origin, r, ctx, data),
  exact: {identity == D.authenticate(s, I.credential(r)) : Maybe<&2, D.Context>}) ->
  L.E<BranchReal(source, c, s, origin, R.decide_identity(identity, r, data)),
    L.E<AuthOfBranch(s, R.decide_identity(identity, r, data)),
      GateOfBranch(R.judgment_of(data), R.decide_identity(identity, r, data))>>:
  match identity:
    case None{}:
      match data:
        case R.DataTools{judgment, output, cleanup, delivery, _pre}:
          L.Both{Unit{}, L.Both{Equal.sym(Maybe<&2, D.Context>, None{}, D.authenticate(s, I.credential(r)), exact), Unit{}}}
    case Some{+ctx}: decide_judgment_real(source, c, s, origin, r, ctx, data, real(ctx, {==}),
      Equal.sym(Maybe<&2, D.Context>, Some{ctx}, D.authenticate(s, I.credential(r)), exact))

def AuthenticationReal(~source: Source.Source, -c: S.Configuration, +s: D.State,
  +origin: Source.JudgmentSyntactic, +decoded: D.State, +r: P.Request,
  +data: R.DataTools, pre: R.Preprocessing) -> Type:
  match pre:
    case R.FailureAuth{id, fatal}: Unit
    case R.PendingAuth{}: Unit
    case _:
      L.E<{decoded == s : D.State},
        @ctx: D.Context -> {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>} ->
          JudgmentReal(source, c, s, origin, r, ctx, data)>

def authentication_normal_real(~source: Source.Source, -c: S.Configuration, +s: D.State,
  +origin: Source.JudgmentSyntactic, +decoded: D.State, +r: P.Request, +data: R.DataTools,
  real: L.E<{decoded == s : D.State},
    @ctx: D.Context -> {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>} ->
      JudgmentReal(source, c, s, origin, r, ctx, data)>) ->
  L.E<BranchReal(source, c, s, origin, R.decide_identity(D.authenticate(decoded, I.credential(r)), r, data)),
    L.E<AuthOfBranch(s, R.decide_identity(D.authenticate(decoded, I.credential(r)), r, data)),
      GateOfBranch(R.judgment_of(data), R.decide_identity(D.authenticate(decoded, I.credential(r)), r, data))>>:
  F.combined_pair(L.E<BranchReal(source, c, s, origin, R.decide_identity(D.authenticate(decoded, I.credential(r)), r, data)),
      L.E<AuthOfBranch(s, R.decide_identity(D.authenticate(decoded, I.credential(r)), r, data)),
        GateOfBranch(R.judgment_of(data), R.decide_identity(D.authenticate(decoded, I.credential(r)), r, data))>>,
    {decoded == s : D.State},
    (@ctx: D.Context -> {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>} ->
      JudgmentReal(source, c, s, origin, r, ctx, data)), real,
    same => derived =>
      %Equal.sym(D.State, decoded, s, same) :
        L.E<BranchReal(source, c, s, origin, R.decide_identity(D.authenticate(_, I.credential(r)), r, data)),
          L.E<AuthOfBranch(s, R.decide_identity(D.authenticate(_, I.credential(r)), r, data)),
            GateOfBranch(R.judgment_of(data), R.decide_identity(D.authenticate(_, I.credential(r)), r, data))>>
      decide_identity_real(source, c, s, origin, r, D.authenticate(s, I.credential(r)), data, derived, {==}))

def decide_authentication_real(~source: Source.Source, -c: S.Configuration, +s: D.State,
  +origin: Source.JudgmentSyntactic, +decoded: D.State, +r: P.Request,
  pre: R.Preprocessing, +data: R.DataTools,
  real: AuthenticationReal(source, c, s, origin, decoded, r, data, pre)) ->
  L.E<BranchReal(source, c, s, origin, R.decide_authentication(pre, decoded, r, data)),
    L.E<AuthOfBranch(s, R.decide_authentication(pre, decoded, r, data)),
      GateOfBranch(R.judgment_of(data), R.decide_authentication(pre, decoded, r, data))>>:
  match pre:
    case R.FailureAuth{id, fatal}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}
    case R.PendingAuth{}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}
    case R.Normal{}: authentication_normal_real(source, c, s, origin, decoded, r, data, real)
    case R.FailureDecode{id, fatal}: authentication_normal_real(source, c, s, origin, decoded, r, data, real)
    case R.FailureFraming{id, fatal}: authentication_normal_real(source, c, s, origin, decoded, r, data, real)
    case R.PendingFraming{}: authentication_normal_real(source, c, s, origin, decoded, r, data, real)
    case R.PendingDecode{}: authentication_normal_real(source, c, s, origin, decoded, r, data, real)

def InputReal(~source: Source.Source, -c: S.Configuration, +s: D.State,
  +origin: Source.JudgmentSyntactic, +data: R.DataTools, input: Input.PreAuthentication) -> Type:
  match input:
    case Input.InputReady{decoded, r}: AuthenticationReal(source, c, s, origin, decoded, r, data, R.preprocessing(data))
    case _: Unit

def decide_input_real(~source: Source.Source, -c: S.Configuration, +s: D.State,
  +origin: Source.JudgmentSyntactic, input: Input.PreAuthentication, +data: R.DataTools,
  real: InputReal(source, c, s, origin, data, input)) ->
  L.E<BranchReal(source, c, s, origin, R.decide_pre(input, data)),
    L.E<AuthOfBranch(s, R.decide_pre(input, data)), GateOfBranch(R.judgment_of(data), R.decide_pre(input, data))>>:
  match input:
    case Input.InputReady{+decoded, +r}:
      decide_authentication_real(source, c, s, origin, decoded, r, R.preprocessing(data), data, real)
    case Input.ErrorMessage{status}:
      match data:
        case R.DataTools{judgment, output, cleanup, delivery, _pre}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}
    case Input.ErrorTransport{}:
      match data:
        case R.DataTools{judgment, output, cleanup, delivery, _pre}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}

def DecodeReal(~source: Source.Source, -c: S.Configuration, +s: D.State,
  +origin: Source.JudgmentSyntactic, +bytes: List<&2, U32>, +e: D.Schema, +lim: S.Limits,
  +data: R.DataTools, pre: R.Preprocessing) -> Type:
  match pre:
    case R.FailureDecode{id, fatal}: Unit
    case R.PendingDecode{}: Unit
    case _: InputReal(source, c, s, origin, data, Input.decode(bytes, e, lim))

def decide_decode_real(~source: Source.Source, -c: S.Configuration, +s: D.State,
  +origin: Source.JudgmentSyntactic, +bytes: List<&2, U32>, +e: D.Schema, +lim: S.Limits,
  pre: R.Preprocessing, +data: R.DataTools, real: DecodeReal(source, c, s, origin, bytes, e, lim, data, pre)) ->
  L.E<BranchReal(source, c, s, origin, R.decide_decode(pre, bytes, e, lim, data)),
    L.E<AuthOfBranch(s, R.decide_decode(pre, bytes, e, lim, data)),
      GateOfBranch(R.judgment_of(data), R.decide_decode(pre, bytes, e, lim, data))>>:
  match pre:
    case R.FailureDecode{id, fatal}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}
    case R.PendingDecode{}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}
    case R.Normal{}: decide_input_real(source, c, s, origin, Input.decode(bytes, e, lim), data, real)
    case R.FailureAuth{id, fatal}: decide_input_real(source, c, s, origin, Input.decode(bytes, e, lim), data, real)
    case R.FailureFraming{id, fatal}: decide_input_real(source, c, s, origin, Input.decode(bytes, e, lim), data, real)
    case R.PendingFraming{}: decide_input_real(source, c, s, origin, Input.decode(bytes, e, lim), data, real)
    case R.PendingAuth{}: decide_input_real(source, c, s, origin, Input.decode(bytes, e, lim), data, real)

def PacketReal(~source: Source.Source, -c: S.Configuration, +s: D.State,
  +origin: Source.JudgmentSyntactic, +e: D.Schema, +lim: S.Limits, +data: R.DataTools,
  packet: Maybe<&2, List<&2, U32>>) -> Type:
  match packet:
    case None{}: Unit
    case Some{bs}: DecodeReal(source, c, s, origin, bs, e, lim, data, R.preprocessing(data))

def decide_packet_real(~source: Source.Source, -c: S.Configuration, +s: D.State,
  +origin: Source.JudgmentSyntactic, +e: D.Schema, +lim: S.Limits,
  packet: Maybe<&2, List<&2, U32>>, +data: R.DataTools,
  real: PacketReal(source, c, s, origin, e, lim, data, packet)) ->
  L.E<BranchReal(source, c, s, origin, R.decide_packet(packet, e, lim, data)),
    L.E<AuthOfBranch(s, R.decide_packet(packet, e, lim, data)), GateOfBranch(R.judgment_of(data), R.decide_packet(packet, e, lim, data))>>:
  match packet:
    case None{}:
      match data:
        case R.DataTools{judgment, output, cleanup, delivery, _pre}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}
    case Some{+bs}: decide_decode_real(source, c, s, origin, bs, e, lim, R.preprocessing(data), data, real)

def DispositionReal(~source: Source.Source, -c: S.Configuration, +s: D.State,
  +origin: Source.JudgmentSyntactic, +state: List<&2, U32>, +e: D.Schema, +lim: S.Limits,
  +data: R.DataTools, disposition: X.Disposition) -> Type:
  match disposition:
    case X.ProcessBody{body}: PacketReal(source, c, s, origin, e, lim, data, Transport.join(state, body))
    case _: Unit

def decide_disposition_real(~source: Source.Source, -c: S.Configuration, +s: D.State,
  +origin: Source.JudgmentSyntactic, +state: List<&2, U32>, +e: D.Schema, +lim: S.Limits,
  disposition: X.Disposition, +data: R.DataTools,
  real: DispositionReal(source, c, s, origin, state, e, lim, data, disposition)) ->
  L.E<BranchReal(source, c, s, origin, R.decide_disposition(disposition, state, e, lim, data)),
    L.E<AuthOfBranch(s, R.decide_disposition(disposition, state, e, lim, data)),
      GateOfBranch(R.judgment_of(data), R.decide_disposition(disposition, state, e, lim, data))>>:
  match disposition:
    case X.CloseWithoutResponse{}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}
    case X.RefuseClose{status}:
      match data:
        case R.DataTools{judgment, output, cleanup, delivery, _pre}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}
    case X.RefuseContinue{status}:
      match data:
        case R.DataTools{judgment, output, cleanup, delivery, _pre}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}
    case X.ProcessBody{+body}:
      decide_packet_real(source, c, s, origin, e, lim, Transport.join(state, body), data, real)

def FramingReal(~source: Source.Source, -c: S.Configuration, +s: D.State,
  +origin: Source.JudgmentSyntactic, +state: List<&2, U32>, +e: D.Schema, +lim: S.Limits,
  +data: R.DataTools, +disposition: X.Disposition, pre: R.Preprocessing) -> Type:
  match pre:
    case R.FailureFraming{id, fatal}: Unit
    case R.PendingFraming{}: Unit
    case _: DispositionReal(source, c, s, origin, state, e, lim, data, disposition)

def decide_framing_real(~source: Source.Source, -c: S.Configuration, +s: D.State,
  +origin: Source.JudgmentSyntactic, +state: List<&2, U32>, +e: D.Schema, +lim: S.Limits,
  pre: R.Preprocessing, +disposition: X.Disposition, +data: R.DataTools,
  real: FramingReal(source, c, s, origin, state, e, lim, data, disposition, pre)) ->
  L.E<BranchReal(source, c, s, origin, R.decide_framing(pre, disposition, state, e, lim, data)),
    L.E<AuthOfBranch(s, R.decide_framing(pre, disposition, state, e, lim, data)),
      GateOfBranch(R.judgment_of(data), R.decide_framing(pre, disposition, state, e, lim, data))>>:
  match pre:
    case R.FailureFraming{id, fatal}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}
    case R.PendingFraming{}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}
    case R.Normal{}: decide_disposition_real(source, c, s, origin, state, e, lim, disposition, data, real)
    case R.FailureAuth{id, fatal}: decide_disposition_real(source, c, s, origin, state, e, lim, disposition, data, real)
    case R.FailureDecode{id, fatal}: decide_disposition_real(source, c, s, origin, state, e, lim, disposition, data, real)
    case R.PendingDecode{}: decide_disposition_real(source, c, s, origin, state, e, lim, disposition, data, real)
    case R.PendingAuth{}: decide_disposition_real(source, c, s, origin, state, e, lim, disposition, data, real)

law decide_by_projections:
  for c: S.Configuration
  for -r: X.Reception
  for -state: List<&2, U32>
  for -data: R.DataTools
  {R.decide(c, r, state, data) ==
    R.decide_framing(R.preprocessing(data), X.decide_reception_in(S.limits(c), r), state, S.schema(c), S.limits(c), data) : R.Branch}
def decide_by_projections(c, r, state, data):
  match c:
    case S.Configuration{e, laws, lim, environment}: {==}

def route_real_decided(~source: Source.Source, ~c: S.Configuration, +s: D.State,
  +origin: Source.JudgmentSyntactic, +state: List<&2, U32>, +data: R.DataTools, +reception: X.Reception,
  real: FramingReal(source, c, s, origin, state, S.schema(c), S.limits(c), data,
    X.decide_reception_in(S.limits(c), reception), R.preprocessing(data))) ->
  L.E<BranchReal(source, c, s, origin, R.decide(c, reception, state, data)),
    L.E<AuthOfBranch(s, R.decide(c, reception, state, data)), GateOfBranch(R.judgment_of(data), R.decide(c, reception, state, data))>>:
  %Equal.sym(R.Branch, R.decide(c, reception, state, data),
    R.decide_framing(R.preprocessing(data), X.decide_reception_in(S.limits(c), reception), state, S.schema(c), S.limits(c), data),
    decide_by_projections(c, reception, state, data)) :
      L.E<BranchReal(source, c, s, origin, _), L.E<AuthOfBranch(s, _), GateOfBranch(R.judgment_of(data), _)>>
  decide_framing_real(source, c, s, origin, state, S.schema(c), S.limits(c),
    R.preprocessing(data), X.decide_reception_in(S.limits(c), reception), data, real)

def marker_extracted(+base: Nat, +mark: Q.Frame, +q: Q.Frame,
  +suffix: List<&2, Q.Frame>, -t: Nat, without: WithoutFrame(suffix, q),
  origin: &i: Nat -> L.E<{t == Nat.add(base, i) : Nat},
    {Q.query(Con{mark, suffix}, i) == Some{q} : Maybe<&2, Q.Frame>}>) ->
  L.E<{t == Nat.add(base, 0n) : Nat}, {q == mark : Q.Frame}>:
  match origin:
    case (i, rest):
      match i:
        case 0n:
          match rest:
            case L.Both{position, query_result}:
              L.Both{position, Equal.sym(Q.Frame, mark, q, F.some_injective(Q.Frame, mark, q, query_result))}
        case 1n+j:
          match rest:
            case L.Both{position, query_result}:
              L.ex_false(L.E<{t == Nat.add(base, 0n) : Nat}, {q == mark : Q.Frame}>, without(j, query_result))

law marker_unique:
  for +prefix: List<&2, Q.Frame>
  for +mark: Q.Frame
  for +suffix: List<&2, Q.Frame>
  for +q: Q.Frame
  for +t: Nat
  for before: WithoutFrame(prefix, q)
  for later: WithoutFrame(suffix, q)
  for present: {Q.query(Q.concatenate(prefix, Con{mark, suffix}), t) == Some{q} : Maybe<&2, Q.Frame>}
  L.E<{t == Nat.add(Q.size(prefix), 0n) : Nat}, {q == mark : Q.Frame}>
def marker_unique(prefix, mark, suffix, q, t, before, later, present):
  marker_extracted(Q.size(prefix), mark, q, suffix, t, later,
    remove_prefix_without_frame(prefix, Con{mark, suffix}, t, q, before, present))

def before_of_start(+m: R.Micro, +r: P.Request, +ctx: D.Context) -> List<&2, Q.Frame>:
  Con{Q.Configured{}, Q.concatenate(R.render_verified(m, r, ctx), R.micro_execution(m))}

def before_of_start_without_interest(m: R.Micro, +r: P.Request, +ctx: D.Context, +i: Interest) ->
  WithoutFrame(before_of_start(m, r, ctx), frame_interest(i)):
  match m:
    case R.Micro{+a, +b, +c, +d}:
      neutral_in_front(Q.Configured{},
        Q.concatenate(R.render_verified(R.Micro{a, b, c, d}, r, ctx), M.expand_primitives(c)), i, {==},
        concatenate_without_frame(R.render_verified(R.Micro{a, b, c, d}, r, ctx), M.expand_primitives(c), frame_interest(i),
          verified_without_interest(R.Micro{a, b, c, d}, r, ctx, i), primitives_without_interest(c, i)))

law start_and_last_of_prefix:
  for m: R.Micro
  for +r: P.Request
  for +ctx: D.Context
  {prefix_executed(m, r, ctx) == Q.concatenate(before_of_start(m, r, ctx), [Q.Started{r, ctx}]) : List<&2, Q.Frame>}
def start_and_last_of_prefix(m, r, ctx):
  match m:
    case R.Micro{+a, +b, +c, +d}:
      Equal.sym(List<&2, Q.Frame>,
        Q.concatenate(before_of_start(R.Micro{a, b, c, d}, r, ctx), [Q.Started{r, ctx}]),
        prefix_executed(R.Micro{a, b, c, d}, r, ctx),
        Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, xs => Con{Q.Configured{}, xs},
          Q.concatenate(Q.concatenate(R.render_verified(R.Micro{a, b, c, d}, r, ctx), M.expand_primitives(c)), [Q.Started{r, ctx}]),
          Q.concatenate(R.render_verified(R.Micro{a, b, c, d}, r, ctx), Q.concatenate(M.expand_primitives(c), [Q.Started{r, ctx}])),
          Q.concatenate_assoc(R.render_verified(R.Micro{a, b, c, d}, r, ctx), M.expand_primitives(c), [Q.Started{r, ctx}])))

def expansion_negative_starts(+r: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>,
  -rq: P.Request, -cx: D.Context) -> WithoutFrame(Q.expand_exec(r, ctx, xs), Q.Started{rq, cx}):
  t => present => E.expand_reflects_query(r, ctx, xs, t, Q.Started{rq, cx}, present)

def query_combined_relation(-c: S.Configuration, -p: S.Program, +xs: List<&2, Q.Frame>, +t: Nat,
  +q: Q.Frame, -f: I.Fact, correspondence: {Q.frame_of_fact(f) == q : Q.Frame},
  observed: Q.observes(c, p, xs, t, f)) ->
  L.E<{Q.query(xs, t) == Some{q} : Maybe<&2, Q.Frame>}, Q.rel_fact(c, p, q, f)>:
  F.combined_pair(L.E<{Q.query(xs, t) == Some{q} : Maybe<&2, Q.Frame>}, Q.rel_fact(c, p, q, f)>,
    Q.observes(c, p, xs, t, f), Q.observes(c, p, xs, t, f), Q.duplicate_observation(c, p, xs, t, f, observed),
    for_query => for_relation =>
      F.combined_pair(L.E<{Q.query(xs, t) == Some{q} : Maybe<&2, Q.Frame>}, Q.rel_fact(c, p, q, f)>,
        {Q.query(xs, t) == Some{q} : Maybe<&2, Q.Frame>},
        {Q.query(xs, t) == Some{q} : Maybe<&2, Q.Frame>},
        Call.duplicate_equality(Maybe<&2, Q.Frame>, Q.query(xs, t), Some{q},
          (%correspondence : {Q.query(xs, t) == Some{_} : Maybe<&2, Q.Frame>}
            Q.observation_frame(c, p, xs, t, f, for_query))),
        copy => query_result => L.Both{copy,
          (%query_result : Q.selected(c, p, _, f) for_relation)}))

def since_start(+m: R.Micro, +r: P.Request, +ctx: D.Context,
  +xs: List<&2, Q.FrameExec>, +suffix: List<&2, Q.Frame>) -> List<&2, Q.Frame>:
  Q.concatenate(before_of_start(m, r, ctx), Con{Q.Started{r, ctx}, Q.concatenate(Q.expand_exec(r, ctx, xs), suffix)})

law trace_preserves_start:
  for +m: R.Micro
  for +r: P.Request
  for +ctx: D.Context
  for +xs: List<&2, Q.FrameExec>
  for +suffix: List<&2, Q.Frame>
  {subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx, xs), suffix) ==
    since_start(m, r, ctx, xs, suffix) : List<&2, Q.Frame>}
def trace_preserves_start(m, r, ctx, xs, suffix):
  Equal.trans(List<&2, Q.Frame>, subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx, xs), suffix),
    Q.concatenate(Q.concatenate(before_of_start(m, r, ctx), [Q.Started{r, ctx}]), Q.concatenate(Q.expand_exec(r, ctx, xs), suffix)),
    since_start(m, r, ctx, xs, suffix),
    Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, pre => subtrace(pre, Q.expand_exec(r, ctx, xs), suffix),
      prefix_executed(m, r, ctx), Q.concatenate(before_of_start(m, r, ctx), [Q.Started{r, ctx}]), start_and_last_of_prefix(m, r, ctx)),
    Q.concatenate_assoc(before_of_start(m, r, ctx), [Q.Started{r, ctx}], Q.concatenate(Q.expand_exec(r, ctx, xs), suffix)))

def start_unique_by_relation(-c: S.Configuration, -p: S.Program,
  -r: P.Request, -ctx: D.Context, -rq: P.Request, -cx: D.Context, -p2: S.Program,
  -u: Nat, -b: Nat,
  marker: L.E<{u == b : Nat}, {Q.Started{rq, cx} == Q.Started{r, ctx} : Q.Frame}>,
  relation: Q.rel_fact(c, p, Q.Started{rq, cx}, I.ProgramStarted{rq, cx, p2})) ->
  L.E<{u == b : Nat}, {I.ProgramStarted{rq, cx, p2} == I.ProgramStarted{r, ctx, p} : I.Fact}>:
  match marker:
    case L.Both{position, frame}:
      L.Both{position, (%frame : Q.rel_fact(c, p, _, I.ProgramStarted{rq, cx, p2}) relation)}

def start_unique_in_list(-c: S.Configuration, -p: S.Program,
  +m: R.Micro, +r: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>, +suffix: List<&2, Q.Frame>,
  +u: Nat, +rq: P.Request, +cx: D.Context, -p2: S.Program,
  later_without: @r2: P.Request -> @c2: D.Context -> WithoutFrame(suffix, Q.Started{r2, c2}),
  observed: Q.observes(c, p, since_start(m, r, ctx, xs, suffix), u, I.ProgramStarted{rq, cx, p2})) ->
  L.E<{u == Nat.add(Q.size(before_of_start(m, r, ctx)), 0n) : Nat},
    {I.ProgramStarted{rq, cx, p2} == I.ProgramStarted{r, ctx, p} : I.Fact}>:
  F.combined_pair(L.E<{u == Nat.add(Q.size(before_of_start(m, r, ctx)), 0n) : Nat},
      {I.ProgramStarted{rq, cx, p2} == I.ProgramStarted{r, ctx, p} : I.Fact}>,
    {Q.query(since_start(m, r, ctx, xs, suffix), u) == Some{Q.Started{rq, cx}} : Maybe<&2, Q.Frame>},
    Q.rel_fact(c, p, Q.Started{rq, cx}, I.ProgramStarted{rq, cx, p2}),
    query_combined_relation(c, p, since_start(m, r, ctx, xs, suffix), u, Q.Started{rq, cx},
      I.ProgramStarted{rq, cx, p2}, {==},
      observed),
    query_result => relation => start_unique_by_relation(c, p, r, ctx, rq, cx, p2, u,
      Nat.add(Q.size(before_of_start(m, r, ctx)), 0n),
      marker_unique(before_of_start(m, r, ctx), Q.Started{r, ctx},
        Q.concatenate(Q.expand_exec(r, ctx, xs), suffix), Q.Started{rq, cx}, u,
        before_of_start_without_interest(m, r, ctx, Start{rq, cx}),
        concatenate_without_frame(Q.expand_exec(r, ctx, xs), suffix, Q.Started{rq, cx},
          expansion_negative_starts(r, ctx, xs, rq, cx), later_without(rq, cx)), query_result), relation))

def start_unique_observed(-G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  -c: S.Configuration, -p: S.Program, +initial: Maybe<&2, D.State>,
  +m: R.Micro, +r: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>, +suffix: List<&2, Q.Frame>,
  +u: Nat, +rq: P.Request, +cx: D.Context, -p2: S.Program,
  later_without: @r2: P.Request -> @c2: D.Context -> WithoutFrame(suffix, Q.Started{r2, c2}),
  refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
    E.observation_model(c, p, initial, since_start(m, r, ctx, xs, suffix))) : Nat -> I.Fact -> Type},
  observed: I.Happens(a, k, x, u, I.ProgramStarted{rq, cx, p2})) ->
  L.E<{u == Nat.add(Q.size(before_of_start(m, r, ctx)), 0n) : Nat},
    {I.ProgramStarted{rq, cx, p2} == I.ProgramStarted{r, ctx, p} : I.Fact}>:
  start_unique_in_list(c, p, m, r, ctx, xs, suffix, u, rq, cx, p2, later_without,
    Ref.remove_guards(G, H, Q.observes(c, p, since_start(m, r, ctx, xs, suffix), u, I.ProgramStarted{rq, cx, p2}),
      (%refinement : _(u, I.ProgramStarted{rq, cx, p2}) observed)))

def FieldsOfStart(-r: P.Request, -ctx: D.Context, -p: S.Program, f: I.Fact) -> Type:
  match f:
    case I.ProgramStarted{rq, cx, other}:
      L.E<{rq == r : P.Request}, L.E<{cx == ctx : D.Context}, {other == p : S.Program}>>
    case _: Unit

def fields_of_start_equal(-r: P.Request, -ctx: D.Context, -p: S.Program,
  -rq: P.Request, -cx: D.Context, -p2: S.Program,
  equal: {I.ProgramStarted{rq, cx, p2} == I.ProgramStarted{r, ctx, p} : I.Fact}) ->
  L.E<{rq == r : P.Request}, L.E<{cx == ctx : D.Context}, {p2 == p : S.Program}>>:
  %Equal.sym(I.Fact, I.ProgramStarted{rq, cx, p2}, I.ProgramStarted{r, ctx, p}, equal) : FieldsOfStart(r, ctx, p, _)
  L.Both{{==}, L.Both{{==}, {==}}}

def before_of_start_without_conclusion(+m: R.Micro, +r: P.Request, +ctx: D.Context) ->
  {Phases.absent(Phases.Conclusion{}, before_of_start(m, r, ctx)) == True{} : Bool}:
  Phases.concatenate_absence(Phases.Conclusion{}, R.render_verified(m, r, ctx), R.micro_execution(m),
    Phases.verified_without_macros(Phases.Conclusion{}, m, r, ctx), Phases.micro_execution_without_macros(Phases.Conclusion{}, m))

def uniqueness_of_start_in_fields(-r: P.Request, -ctx: D.Context, -p: S.Program,
  -rq: P.Request, -cx: D.Context, -p2: S.Program, -u: Nat, -b: Nat,
  unique: L.E<{u == b : Nat}, {I.ProgramStarted{rq, cx, p2} == I.ProgramStarted{r, ctx, p} : I.Fact}>) ->
  L.E<{u == b : Nat}, L.E<{rq == r : P.Request}, L.E<{cx == ctx : D.Context}, {p2 == p : S.Program}>>>:
  match unique:
    case L.Both{time, fact}: L.Both{time, fields_of_start_equal(r, ctx, p, rq, cx, p2, fact)}

def start_satisfies_rule5(~program: Nat -> S.Program, ~c: S.Configuration,
  +world: Nat, -G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  +m: R.Micro, +r: P.Request, +ctx: D.Context, +s0: D.State,
  +xs: List<&2, Q.FrameExec>, +suffix: List<&2, Q.Frame>,
  configuration: {c == I.configuration(x) : S.Configuration}, state: {s0 == I.initial(x) : D.State},
  configuration_is_valid: I.ConfigurationValid(a, c), state_valid: Requirements.Valid(c, s0),
  later_without: @rq: P.Request -> @cx: D.Context -> WithoutFrame(suffix, Q.Started{rq, cx}),
  refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
    E.observation_model(c, program(world), Some{s0}, since_start(m, r, ctx, xs, suffix))) : Nat -> I.Fact -> Type}) ->
  Laws.Rule5(I.ProgramStarted{r, ctx, program(world)}, a, k, x,
    Nat.add(Q.size(before_of_start(m, r, ctx)), 0n)):
  F.combined_pair(Laws.Rule5(I.ProgramStarted{r, ctx, program(world)}, a, k, x,
      Nat.add(Q.size(before_of_start(m, r, ctx)), 0n)),
    {c == I.configuration(x) : S.Configuration}, {c == I.configuration(x) : S.Configuration},
    Call.duplicate_equality(S.Configuration, c, I.configuration(x), configuration), cfg1 => cfg2 =>
      F.combined_pair(Laws.Rule5(I.ProgramStarted{r, ctx, program(world)}, a, k, x,
          Nat.add(Q.size(before_of_start(m, r, ctx)), 0n)),
        {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
          E.observation_model(c, program(world), Some{s0}, since_start(m, r, ctx, xs, suffix))) : Nat -> I.Fact -> Type},
        {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
          E.observation_model(c, program(world), Some{s0}, since_start(m, r, ctx, xs, suffix))) : Nat -> I.Fact -> Type},
        Call.duplicate_equality((Nat -> I.Fact -> Type), E.observation_real(a, k, x),
          Ref.observation_stored(G, H, E.observation_model(c, program(world), Some{s0}, since_start(m, r, ctx, xs, suffix))), refinement),
        ref1 => ref2 => L.Both{
          L.Both{(%cfg1 : I.ConfigurationValid(a, _) configuration_is_valid),
            L.Both{(%cfg2 : Requirements.Valid(_, I.initial(x)) %state : Requirements.Valid(c, _) state_valid),
              without_conclusion_in_block(G, H, a, k, x, c, program(world), Some{s0}, before_of_start(m, r, ctx),
                [Q.Started{r, ctx}], Q.concatenate(Q.expand_exec(r, ctx, xs), suffix), 0n, Q.Started{r, ctx},
                ref1, {==}, before_of_start_without_conclusion(m, r, ctx), {==})}},
          +u => +rq => +cx => p2 => observed =>
            uniqueness_of_start_in_fields(r, ctx, program(world), rq, cx, p2, u,
              Nat.add(Q.size(before_of_start(m, r, ctx)), 0n),
              start_unique_observed(G, H, a, k, x, c, program(world), Some{s0}, m, r, ctx, xs, suffix,
                u, rq, cx, p2, later_without, ref2, observed))}))

def output_without_interest(m: R.Micro, +i: Interest) -> WithoutFrame(R.micro_output(m), frame_interest(i)):
  match m:
    case R.Micro{a, b, c, +d}: primitives_without_interest(d, i)

def micro_authentication_without_interest(m: R.Micro, +i: Interest) ->
  WithoutFrame(R.micro_authentication(m), frame_interest(i)):
  match m:
    case R.Micro{a, +b, c, d}: primitives_without_interest(b, i)

def initial_without_interest(q: Maybe<&2, List<&2, U32>>, +s: D.State, +i: Interest) ->
  WithoutFrame(R.render_initial(q, s), frame_interest(i)):
  match q:
    case None{}: neutral_in_front(Q.Encoded{D.state_value(s), None{}}, Nil{}, i, {==}, empty_without_frame(frame_interest(i)))
    case Some{+bs}:
      neutral_in_front(Q.Encoded{D.state_value(s), Some{bs}}, [Q.Stored{s, bs, s}, Q.Initialized{s}], i, {==},
        neutral_in_front(Q.Stored{s, bs, s}, [Q.Initialized{s}], i, {==},
          neutral_in_front(Q.Initialized{s}, Nil{}, i, {==}, empty_without_frame(frame_interest(i)))))

def fatal_published_without_interest(conclusion: N.Conclusion, +stage: X.Stage, +id: String, +i: Interest) ->
  WithoutFrame(R.render_fatal_published(conclusion, stage, id), frame_interest(i)):
  match conclusion:
    case N.Conclusion{+s, +r, +bs}:
      neutral_in_front(Q.Prepared{r, bs}, Q.concatenate(R.render_publication(r, s), [Q.Failed{stage, id, True{}}, Q.Closed{}]), i, {==},
        concatenate_without_frame(R.render_publication(r, s), [Q.Failed{stage, id, True{}}, Q.Closed{}], frame_interest(i),
          publication_without_interest(r, s, i),
          neutral_in_front(Q.Failed{stage, id, True{}}, [Q.Closed{}], i, {==},
            neutral_in_front(Q.Closed{}, Nil{}, i, {==}, empty_without_frame(frame_interest(i))))))

# Decomposes the existing renderer without executing another program or state.
type Block is Data:
  Block{request: P.Request, context: D.Context,
    steps: List<&2, Q.FrameExec>, suffix: List<&2, Q.Frame>}

def block_phase(+m: R.Micro, phase: R.PhaseBefore, +tail: List<&2, Q.Frame>) -> Maybe<&2, Block>:
  match phase:
    case R.Executing{r, ctx, xs}: Some{Block{r, ctx, xs, tail}}
    case R.AfterPrepare{r, ctx, xs, p}:
      Some{Block{r, ctx, xs, Q.concatenate(R.micro_output(m), Con{R.frame_prepared(p), tail})}}
    case _: None{}

def block_branch(+m: R.Micro, +s: D.State, branch: R.Branch) -> Maybe<&2, Block>:
  match branch:
    case R.Executed{r, ctx, xs, p, delivery}: Some{Block{r, ctx, xs, Q.concatenate(R.micro_output(m), R.render_final(p, s, False{}, delivery))}}
    case R.FatalAfterPublication{r, ctx, xs, p, stage, id}:
      Some{Block{r, ctx, xs, Q.concatenate(R.micro_output(m), R.render_fatal_published(N.conclude(p, s), stage, id))}}
    case R.FailureBefore{phase, stage, id, fatal, delivery}: block_phase(m, phase, R.render_failure(s, stage, id, fatal, delivery))
    case R.Pending{phase}: block_phase(m, phase, Nil{})
    case _: None{}

def render_block(+m: R.Micro, b: Block) -> List<&2, Q.Frame>:
  match b:
    case Block{+r, +ctx, xs, suffix}: subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx, xs), suffix)

def WithoutInterest(-xs: List<&2, Q.Frame>) -> Type:
  @i: Interest -> WithoutFrame(xs, frame_interest(i))

def suffix_block(b: Block) -> List<&2, Q.Frame>:
  match b:
    case Block{r, ctx, xs, suffix}: suffix

def Structure(-m: R.Micro, -original: List<&2, Q.Frame>, b: Maybe<&2, Block>) -> Type:
  match b:
    case None{}: WithoutInterest(original)
    case Some{+block}:
      L.E<{original == render_block(m, block) : List<&2, Q.Frame>}, WithoutInterest(suffix_block(block))>

def micro_input_without_interest(m: R.Micro, +i: Interest) ->
  WithoutFrame(R.micro_input(m), frame_interest(i)):
  match m:
    case R.Micro{+a, b, c, d}: primitives_without_interest(a, i)

def preparation_and_neutral(p: N.Prepared) -> {of_execution(R.frame_prepared(p)) == False{} : Bool}:
  match p:
    case N.Prepared{w, ts, r, bs}: {==}

def raise_execution_for_config(+m: R.Micro, +r: P.Request, +ctx: D.Context,
  +xs: List<&2, Q.FrameExec>, +tail: List<&2, Q.Frame>) ->
  {Con{Q.Configured{}, Q.concatenate(R.render_execution(m, r, ctx, xs), tail)} ==
    render_block(m, Block{r, ctx, xs, tail}) : List<&2, Q.Frame>}:
  Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, qs => Con{Q.Configured{}, qs},
    Q.concatenate(Q.concatenate(R.render_started(m, r, ctx), Q.expand_exec(r, ctx, xs)), tail),
    Q.concatenate(R.render_started(m, r, ctx), Q.concatenate(Q.expand_exec(r, ctx, xs), tail)),
    Q.concatenate_assoc(R.render_started(m, r, ctx), Q.expand_exec(r, ctx, xs), tail))

def without_execution_of_prefix(+prefix: List<&2, Q.Frame>, +tail: List<&2, Q.Frame>,
  without_prefix: WithoutInterest(prefix), without_tail: WithoutInterest(tail)) ->
  WithoutInterest(Con{Q.Configured{}, Q.concatenate(prefix, tail)}):
  +i => neutral_in_front(Q.Configured{}, Q.concatenate(prefix, tail), i, {==},
    concatenate_without_frame(prefix, tail, frame_interest(i), without_prefix(i), without_tail(i)))

def phase_prepared_preserves_block(+m: R.Micro, +r: P.Request, +ctx: D.Context,
  +xs: List<&2, Q.FrameExec>, +p: N.Prepared, +tail: List<&2, Q.Frame>) ->
  {Con{Q.Configured{}, Q.concatenate(R.render_phase(m, R.AfterPrepare{r, ctx, xs, p}), tail)} ==
    render_block(m, Block{r, ctx, xs, Q.concatenate(R.micro_output(m), Con{R.frame_prepared(p), tail})}) : List<&2, Q.Frame>}:
  Equal.trans(List<&2, Q.Frame>,
    Con{Q.Configured{}, Q.concatenate(R.render_phase(m, R.AfterPrepare{r, ctx, xs, p}), tail)},
    Con{Q.Configured{}, Q.concatenate(R.render_execution(m, r, ctx, xs),
      Q.concatenate(R.micro_output(m), Con{R.frame_prepared(p), tail}))},
    render_block(m, Block{r, ctx, xs, Q.concatenate(R.micro_output(m), Con{R.frame_prepared(p), tail})}),
    Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, qs => Con{Q.Configured{}, qs},
      Q.concatenate(R.render_phase(m, R.AfterPrepare{r, ctx, xs, p}), tail),
      Q.concatenate(R.render_execution(m, r, ctx, xs), Q.concatenate(R.micro_output(m), Con{R.frame_prepared(p), tail})),
      Equal.trans(List<&2, Q.Frame>, Q.concatenate(R.render_phase(m, R.AfterPrepare{r, ctx, xs, p}), tail),
        Q.concatenate(R.render_execution(m, r, ctx, xs), Q.concatenate(Q.concatenate(R.micro_output(m), [R.frame_prepared(p)]), tail)),
        Q.concatenate(R.render_execution(m, r, ctx, xs), Q.concatenate(R.micro_output(m), Con{R.frame_prepared(p), tail})),
        Q.concatenate_assoc(R.render_execution(m, r, ctx, xs), Q.concatenate(R.micro_output(m), [R.frame_prepared(p)]), tail),
        Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, rest => Q.concatenate(R.render_execution(m, r, ctx, xs), rest),
          Q.concatenate(Q.concatenate(R.micro_output(m), [R.frame_prepared(p)]), tail),
          Q.concatenate(R.micro_output(m), Con{R.frame_prepared(p), tail}),
          Q.concatenate_assoc(R.micro_output(m), [R.frame_prepared(p)], tail)))),
    raise_execution_for_config(m, r, ctx, xs, Q.concatenate(R.micro_output(m), Con{R.frame_prepared(p), tail})))

def structure_of_phase(+m: R.Micro, phase: R.PhaseBefore, +tail: List<&2, Q.Frame>, without_tail: WithoutInterest(tail)) ->
  Structure(m, Con{Q.Configured{}, Q.concatenate(R.render_phase(m, phase), tail)}, block_phase(m, phase, tail)):
  match phase:
    case R.BeforeInput{}:
      without_execution_of_prefix(R.micro_input(m), tail, +i => micro_input_without_interest(m, i), without_tail)
    case R.AfterReceive{+r}:
      without_execution_of_prefix(R.render_received(m, r), tail, +i => received_without_interest(m, r, i), without_tail)
    case R.AfterAuthenticate{+r, +ctx}:
      without_execution_of_prefix(R.render_authenticated(m, r, ctx), tail, +i => authenticated_without_interest(m, r, ctx, i), without_tail)
    case R.AfterVerify{+r, +ctx}:
      without_execution_of_prefix(R.render_verified(m, r, ctx), tail, +i => verified_without_interest(m, r, ctx, i), without_tail)
    case R.Executing{+r, +ctx, +xs}:
      L.Both{raise_execution_for_config(m, r, ctx, xs, tail), without_tail}
    case R.AfterPrepare{+r, +ctx, +xs, +p}:
      L.Both{phase_prepared_preserves_block(m, r, ctx, xs, p, tail),
        +i => concatenate_without_frame(R.micro_output(m), Con{R.frame_prepared(p), tail}, frame_interest(i),
          output_without_interest(m, i), neutral_in_front(R.frame_prepared(p), tail, i, preparation_and_neutral(p), without_tail(i)))}

law concatenate_empty_right:
  for xs: List<&2, Q.Frame>
  {Q.concatenate(xs, Nil{}) == xs : List<&2, Q.Frame>}
def concatenate_empty_right(xs):
  match xs:
    case Nil{}: {==}
    case Con{+h, +t}:
      Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, rest => Con{h, rest},
        Q.concatenate(t, Nil{}), t, concatenate_empty_right(t))

def configured_without_interest(+frames: List<&2, Q.Frame>, without: WithoutInterest(frames)) ->
  WithoutInterest(Con{Q.Configured{}, frames}):
  +i => neutral_in_front(Q.Configured{}, frames, i, {==}, without(i))

def prefix_initial_without_interest(+m: R.Micro, accepts: Bool, +i: Interest) ->
  WithoutFrame(R.prefix_initial(m, accepts), frame_interest(i)):
  match accepts:
    case True{}:
      neutral_in_front(Q.InitialAccepts{}, R.micro_output(m), i, {==}, output_without_interest(m, i))
    case False{}: empty_without_frame(frame_interest(i))

def structure_of_route(+m: R.Micro, +s: D.State, branch: R.Branch) ->
  Structure(m, R.render(m, s, branch), block_branch(m, s, branch)):
  match branch:
    case R.InitialOk{}:
      configured_without_interest(Con{Q.InitialAccepts{}, Q.concatenate(R.micro_output(m), R.render_initial(P.encode(D.state_value(s)), s))},
        +i => neutral_in_front(Q.InitialAccepts{}, Q.concatenate(R.micro_output(m), R.render_initial(P.encode(D.state_value(s)), s)), i, {==},
          concatenate_without_frame(R.micro_output(m), R.render_initial(P.encode(D.state_value(s)), s), frame_interest(i),
            output_without_interest(m, i), initial_without_interest(P.encode(D.state_value(s)), s, i))))
    case R.InitialRefusal{+status}:
      configured_without_interest([Q.InitialRefused{status}],
        +i => neutral_in_front(Q.InitialRefused{status}, Nil{}, i, {==}, empty_without_frame(frame_interest(i))))
    case R.InitialFailure{+accepts, +stage, +id, +fatal}:
      configured_without_interest(Q.concatenate(R.prefix_initial(m, accepts), [Q.Failed{stage, id, fatal}, Q.InitialRefused{S.Failure{}}]),
        +i => concatenate_without_frame(R.prefix_initial(m, accepts), [Q.Failed{stage, id, fatal}, Q.InitialRefused{S.Failure{}}], frame_interest(i),
          prefix_initial_without_interest(m, accepts, i),
          neutral_in_front(Q.Failed{stage, id, fatal}, [Q.InitialRefused{S.Failure{}}], i, {==},
            neutral_in_front(Q.InitialRefused{S.Failure{}}, Nil{}, i, {==}, empty_without_frame(frame_interest(i))))))
    case R.WithoutResponse{}:
      configured_without_interest([Q.Closed{}],
        +i => neutral_in_front(Q.Closed{}, Nil{}, i, {==}, empty_without_frame(frame_interest(i))))
    case R.InputRefusal{+error, +closes, +delivery}:
      without_execution_of_prefix(R.micro_input(m), R.render_error(R.status_input(error), s, closes, delivery),
        +i => micro_input_without_interest(m, i), +i => error_without_interest(R.status_input(error), s, closes, delivery, i))
    case R.AutRefusal{+r, +delivery}:
      structure_of_phase(m, R.AfterReceive{r},
        Q.concatenate(R.micro_authentication(m), Con{Q.Authenticated{r, None{}}, R.render_error(S.Authentication{}, s, False{}, delivery)}),
        +i => concatenate_without_frame(R.micro_authentication(m), Con{Q.Authenticated{r, None{}}, R.render_error(S.Authentication{}, s, False{}, delivery)},
          frame_interest(i), micro_authentication_without_interest(m, i),
          neutral_in_front(Q.Authenticated{r, None{}}, R.render_error(S.Authentication{}, s, False{}, delivery), i, {==},
            error_without_interest(S.Authentication{}, s, False{}, delivery, i))))
    case R.GateRefusal{+r, +ctx, +delivery}:
      structure_of_phase(m, R.AfterAuthenticate{r, ctx}, Con{Q.Rejected{r, ctx}, R.render_error(S.Certificate{}, s, False{}, delivery)},
        +i => neutral_in_front(Q.Rejected{r, ctx}, R.render_error(S.Certificate{}, s, False{}, delivery), i, {==},
          error_without_interest(S.Certificate{}, s, False{}, delivery, i)))
    case R.Executed{+r, +ctx, +xs, +p, +delivery}:
      L.Both{raise_execution_for_config(m, r, ctx, xs, Q.concatenate(R.micro_output(m), R.render_final(p, s, False{}, delivery))),
        +i => concatenate_without_frame(R.micro_output(m), R.render_final(p, s, False{}, delivery), frame_interest(i),
          output_without_interest(m, i), conclusion_without_interest(N.conclude(p, s), False{}, delivery, i))}
    case R.FailureBefore{+phase, +stage, +id, +fatal, +delivery}:
      structure_of_phase(m, phase, R.render_failure(s, stage, id, fatal, delivery),
        +i => failure_without_interest(s, stage, id, fatal, delivery, i))
    case R.FatalAfterPublication{+r, +ctx, +xs, +p, +stage, +id}:
      L.Both{raise_execution_for_config(m, r, ctx, xs, Q.concatenate(R.micro_output(m), R.render_fatal_published(N.conclude(p, s), stage, id))),
        +i => concatenate_without_frame(R.micro_output(m), R.render_fatal_published(N.conclude(p, s), stage, id), frame_interest(i),
          output_without_interest(m, i), fatal_published_without_interest(N.conclude(p, s), stage, id, i))}
    case R.Pending{+phase}:
      %Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, qs => Con{Q.Configured{}, qs},
        Q.concatenate(R.render_phase(m, phase), Nil{}), R.render_phase(m, phase), concatenate_empty_right(R.render_phase(m, phase))) :
        Structure(m, _, block_phase(m, phase, Nil{}))
      structure_of_phase(m, phase, Nil{}, +i => empty_without_frame(frame_interest(i)))
    case R.InitialPending{+accepts}:
      configured_without_interest(R.prefix_initial(m, accepts), +i => prefix_initial_without_interest(m, accepts, i))

def PrefixOfRoot(-p: S.Program, -c: S.Configuration, -s: D.State,
  -r: P.Request, -ctx: D.Context, -xs: List<&2, Q.FrameExec>) -> Type:
  &n: Nat -> {xs == E.generate(n, N.start(p, ctx, I.arguments(r), s), S.schema(c)) : List<&2, Q.FrameExec>}

def BlockReal(~source: Source.Source, -c: S.Configuration, -s: D.State,
  +origin: Source.JudgmentSyntactic, block: Maybe<&2, Block>) -> Type:
  match block:
    case None{}: Unit
    case Some{Block{r, ctx, xs, suffix}}: Source.PrefixReal(source, c, s, r, ctx, origin, xs)

def prefix_of_final(~source: Source.Source, -c: S.Configuration, -s: D.State, -r: P.Request, -ctx: D.Context,
  +origin: Source.JudgmentSyntactic, -xs: List<&2, Q.FrameExec>, -p: N.Prepared,
  real: Source.FinalReal(source, c, s, r, ctx, origin, xs, p)) -> Source.PrefixReal(source, c, s, r, ctx, origin, xs):
  match real:
    case (+n, w, ts, proposal, L.Both{frames, rest}): (n, frames)

def block_real_of_phase(~source: Source.Source, -c: S.Configuration, -s: D.State,
  +origin: Source.JudgmentSyntactic, +m: R.Micro, phase: R.PhaseBefore, +tail: List<&2, Q.Frame>,
  real: PhaseReal(source, c, s, origin, phase)) -> BlockReal(source, c, s, origin, block_phase(m, phase, tail)):
  match phase:
    case R.BeforeInput{}: Unit{}
    case R.AfterReceive{r}: Unit{}
    case R.AfterAuthenticate{r, ctx}: Unit{}
    case R.AfterVerify{r, ctx}: Unit{}
    case R.Executing{r, ctx, xs}: real
    case R.AfterPrepare{r, ctx, xs, p}: prefix_of_final(source, c, s, r, ctx, origin, xs, p, real)

def block_real_of_route(~source: Source.Source, -c: S.Configuration, +s: D.State,
  +origin: Source.JudgmentSyntactic, +m: R.Micro, branch: R.Branch, real: BranchReal(source, c, s, origin, branch)) ->
  BlockReal(source, c, s, origin, block_branch(m, s, branch)):
  match branch:
    case R.Executed{r, ctx, xs, p, delivery}: prefix_of_final(source, c, s, r, ctx, origin, xs, p, real)
    case R.FatalAfterPublication{r, ctx, xs, p, stage, id}: prefix_of_final(source, c, s, r, ctx, origin, xs, p, real)
    case R.FailureBefore{phase, +stage, +id, +fatal, +delivery}:
      block_real_of_phase(source, c, s, origin, m, phase, R.render_failure(s, stage, id, fatal, delivery), real)
    case R.Pending{phase}: block_real_of_phase(source, c, s, origin, m, phase, Nil{}, real)
    case R.InitialOk{}: Unit{}
    case R.InitialRefusal{status}: Unit{}
    case R.InitialFailure{accepts, stage, id, fatal}: Unit{}
    case R.WithoutResponse{}: Unit{}
    case R.InputRefusal{error, closes, delivery}: Unit{}
    case R.AutRefusal{r, delivery}: Unit{}
    case R.GateRefusal{r, ctx, delivery}: Unit{}
    case R.InitialPending{accepts}: Unit{}

def origin_of_call(data: Source.CallData) -> Source.JudgmentSyntactic:
  match data:
    case Source.CallData{cf, program, certificate, terminates, state, tools, micro}: program

def program_of_world(~source: Source.Source, world: Nat) -> S.Program:
  Source.program(source, origin_of_call(Source.call(source, world)))

def same_root_of_call(~source: Source.Source, +world: Nat, +data: Source.CallData,
  same_call: {data == Source.call(source, world) : Source.CallData}) ->
  {Source.program(source, origin_of_call(data)) == program_of_world(source, world) : S.Program}:
  Equal.cong(Source.CallData, S.Program, d => Source.program(source, origin_of_call(d)),
    data, Source.call(source, world), same_call)

def transport_prefix_of_root(-p: S.Program, -q: S.Program,
  -c: S.Configuration, -s: D.State, -r: P.Request, -ctx: D.Context, -xs: List<&2, Q.FrameExec>,
  same_root: {p == q : S.Program}, real: PrefixOfRoot(p, c, s, r, ctx, xs)) -> PrefixOfRoot(q, c, s, r, ctx, xs):
  %same_root : PrefixOfRoot(_, c, s, r, ctx, xs)
  real

def fact_without_execution(-a: I.Environment, -k: String, -x: I.Scenario, -c: S.Configuration,
  -p: S.Program, +original: List<&2, Q.Frame>, +t: Nat, f: I.Fact,
  without: WithoutInterest(original), observed: Q.observes(c, p, original, t, f)) -> Laws.Rule5(f, a, k, x, t):
  match f:
    case I.ProgramStarted{+r, +ctx, prog}:
      L.ex_false(Laws.Rule5(I.ProgramStarted{r, ctx, prog}, a, k, x, t),
        without(Start{r, ctx})(t, Q.observation_frame(c, p, original, t, I.ProgramStarted{r, ctx, prog}, observed)))
    case I.Evaluated{+r, +ctx, prog, +execution_trace}:
      L.ex_false(Laws.Rule5(I.Evaluated{r, ctx, prog, execution_trace}, a, k, x, t),
        without(Evaluation{r, ctx, execution_trace})(t, Q.observation_frame(c, p, original, t, I.Evaluated{r, ctx, prog, execution_trace}, observed)))
    case I.Operated{+e, +s, +o, +result}:
      L.ex_false(Laws.Rule5(I.Operated{e, s, o, result}, a, k, x, t),
        without(Operation{e, s, o, result})(t, Q.observation_frame(c, p, original, t, I.Operated{e, s, o, result}, observed)))
    case I.InspectionNotModeled{+d}:
      without(Inspection{d})(t, Q.observation_frame(c, p, original, t, I.InspectionNotModeled{d}, observed))
    case I.EffectNotModeled{+d}:
      without(Effect{d})(t, Q.observation_frame(c, p, original, t, I.EffectNotModeled{d}, observed))
    case I.ConfigurationInUse{configuration}: Unit{}
    case I.InstanceStarted{s}: Unit{}
    case I.InitializationRefused{status}: Unit{}
    case I.ProofInitialAccepts{}: Unit{}
    case I.Encoded{v, result}: Unit{}
    case I.Decoded{bs, result}: Unit{}
    case I.Stored{s, bytes, abstraction}: Unit{}
    case I.CheckedLength{pos, n}: Unit{}
    case I.AllocatedField{pos, n}: Unit{}
    case I.ReadBody{before, n, declared}: Unit{}
    case I.ReceivedRequest{r}: Unit{}
    case I.Authenticated{r, ctx}: Unit{}
    case I.CertificateAccepted{r, ctx, program}: Unit{}
    case I.CertificateRejected{r, ctx}: Unit{}
    case I.Prepared{r, bs}: Unit{}
    case I.Published{s}: Unit{}
    case I.StateVisible{s}: Unit{}
    case I.FailedEnvironment{stage, id, fatal}: Unit{}
    case I.Concluded{r, s, closes}: Unit{}
    case I.DeliveredEverything{bs}: Unit{}
    case I.DeliveryInterrupted{prefix}: Unit{}
    case I.ClosedChannel{}: Unit{}
    case I.NextCall{previous, next}: Unit{}

def evaluation_by_origin(~program: Nat -> S.Program, ~c: S.Configuration,
  +world: Nat, -G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  +m: R.Micro, +suffix: List<&2, Q.Frame>, +r: P.Request, +ctx: D.Context,
  +s0: D.State, +n: Nat, +u: Nat, +rq: P.Request, +cx: D.Context, -p2: S.Program, +execution_trace: S.Trace,
  configuration: {c == I.configuration(x) : S.Configuration}, state: {s0 == I.initial(x) : D.State},
  guards: L.E<G, H>,
  suffixes: L.E<(@r2: P.Request -> @c2: D.Context -> @p: S.Trace -> WithoutFrame(suffix, Q.Evaluated{r2, c2, p})),
    (@r2: P.Request -> @c2: D.Context -> @p: S.Trace -> WithoutFrame(suffix, Q.Evaluated{r2, c2, p}))>,
  refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
    E.observation_model(c, program(world), Some{s0},
      subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx,
        E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix))) : Nat -> I.Fact -> Type},
  relation: Q.rel_fact(c, program(world), Q.Evaluated{rq, cx, execution_trace}, I.Evaluated{rq, cx, p2, execution_trace}),
  origin: &i: Nat -> L.E<{u == Nat.add(Q.size(prefix_executed(m, r, ctx)), i) : Nat},
    E.Reflection(r, ctx, E.query(E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)), i),
      Q.Evaluated{rq, cx, execution_trace})>) ->
  Laws.Rule5(I.Evaluated{rq, cx, p2, execution_trace}, a, k, x, u):
  match origin:
    case (+i, L.Both{position, L.Both{same_req, L.Both{same_ctx, query_result}}}):
      %Equal.sym(Nat, u, Nat.add(Q.size(prefix_executed(m, r, ctx)), i), position) :
        Laws.Rule5(I.Evaluated{rq, cx, p2, execution_trace}, a, k, x, _)
      %Equal.sym(I.Fact, I.Evaluated{rq, cx, p2, execution_trace}, I.Evaluated{rq, cx, program(world), execution_trace}, relation) :
        Laws.Rule5(_, a, k, x, Nat.add(Q.size(prefix_executed(m, r, ctx)), i))
      %Equal.sym(P.Request, rq, r, same_req) :
        Laws.Rule5(I.Evaluated{_, cx, program(world), execution_trace}, a, k, x, Nat.add(Q.size(prefix_executed(m, r, ctx)), i))
      %Equal.sym(D.Context, cx, ctx, same_ctx) :
        Laws.Rule5(I.Evaluated{r, _, program(world), execution_trace}, a, k, x, Nat.add(Q.size(prefix_executed(m, r, ctx)), i))
      evaluation_satisfies_rule5(program, c, world, G, H, a, k, x, m, suffix, r, ctx, s0, n, i, execution_trace,
        configuration, state, guards, suffixes, refinement, query_result)

def operation_by_origin(~program: Nat -> S.Program, ~c: S.Configuration,
  +world: Nat, -G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  +m: R.Micro, +suffix: List<&2, Q.Frame>, +r: P.Request, +ctx: D.Context,
  +s0: D.State, +n: Nat, +u: Nat, +e: D.Schema, +s: D.State, +o: D.Operation, +result: D.ResultOp,
  configuration: {c == I.configuration(x) : S.Configuration}, guards: L.E<L.E<G, H>, L.E<G, H>>,
  suffix_without: @rq: P.Request -> @cx: D.Context -> @p: S.Trace -> WithoutFrame(suffix, Q.Evaluated{rq, cx, p}),
  refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
    E.observation_model(c, program(world), Some{s0},
      subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx,
        E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix))) : Nat -> I.Fact -> Type},
  origin: &i: Nat -> L.E<{u == Nat.add(Q.size(prefix_executed(m, r, ctx)), i) : Nat},
    E.Reflection(r, ctx, E.query(E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)), i),
      Q.Operated{e, s, o, result})>) -> Laws.Rule5(I.Operated{e, s, o, result}, a, k, x, u):
  match origin:
    case (+i, L.Both{position, query_result}):
      %Equal.sym(Nat, u, Nat.add(Q.size(prefix_executed(m, r, ctx)), i), position) :
        Laws.Rule5(I.Operated{e, s, o, result}, a, k, x, _)
      operation_satisfies_rule5(program, c, world, G, H, a, k, x, m, suffix, r, ctx, s0, n, i, e, s, o, result,
        configuration, guards, suffix_without, refinement, query_result)

def refinement_of_trace(-G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  -c: S.Configuration, -p: S.Program, +initial: Maybe<&2, D.State>,
  +before: List<&2, Q.Frame>, +later: List<&2, Q.Frame>,
  same: {before == later : List<&2, Q.Frame>},
  refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
    E.observation_model(c, p, initial, before)) : Nat -> I.Fact -> Type}) ->
  {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
    E.observation_model(c, p, initial, later)) : Nat -> I.Fact -> Type}:
  Equal.trans((Nat -> I.Fact -> Type), E.observation_real(a, k, x),
    Ref.observation_stored(G, H, E.observation_model(c, p, initial, before)),
    Ref.observation_stored(G, H, E.observation_model(c, p, initial, later)), refinement,
    Equal.cong(List<&2, Q.Frame>, (Nat -> I.Fact -> Type),
      qs => Ref.observation_stored(G, H, E.observation_model(c, p, initial, qs)), before, later, same))

def transport_rule5(-a: I.Environment, -k: String, -x: I.Scenario,
  -f: I.Fact, -g: I.Fact, -u: Nat, -t: Nat, time: {u == t : Nat}, fact: {f == g : I.Fact},
  proof: Laws.Rule5(g, a, k, x, t)) -> Laws.Rule5(f, a, k, x, u):
  %Equal.sym(Nat, u, t, time) : Laws.Rule5(f, a, k, x, _)
  %Equal.sym(I.Fact, f, g, fact) : Laws.Rule5(_, a, k, x, t)
  proof

def start_of_origin_satisfies_rule5(-a: I.Environment, -k: String, -x: I.Scenario,
  -r: P.Request, -ctx: D.Context, -p: S.Program,
  -rq: P.Request, -cx: D.Context, -p2: S.Program, -u: Nat, -t: Nat,
  proof: Laws.Rule5(I.ProgramStarted{r, ctx, p}, a, k, x, t),
  origin: L.E<{u == t : Nat}, {I.ProgramStarted{rq, cx, p2} == I.ProgramStarted{r, ctx, p} : I.Fact}>) ->
  Laws.Rule5(I.ProgramStarted{rq, cx, p2}, a, k, x, u):
  match origin:
    case L.Both{time, fact}:
      transport_rule5(a, k, x, I.ProgramStarted{rq, cx, p2}, I.ProgramStarted{r, ctx, p}, u, t, time, fact, proof)

def origin_impossible(-base: Nat, -u: Nat,
  origin: &i: Nat -> L.E<{u == Nat.add(base, i) : Nat}, Empty>) -> Empty:
  match origin:
    case (i, L.Both{position, impossible}): impossible

def rule5_of_frames(~program: Nat -> S.Program, ~c: S.Configuration,
  +world: Nat, -G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  +m: R.Micro, +r: P.Request, +ctx: D.Context, +s0: D.State, +n: Nat, +suffix: List<&2, Q.Frame>,
  configuration: {c == I.configuration(x) : S.Configuration}, state: {s0 == I.initial(x) : D.State},
  configuration_is_valid: I.ConfigurationValid(a, c), state_valid: Requirements.Valid(c, s0),
  guards: Four<L.E<G, H>>, suffixes: Four<WithoutInterest(suffix)>,
  refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
    E.observation_model(c, program(world), Some{s0},
      subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx,
        E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix))) : Nat -> I.Fact -> Type},
  +u: Nat, f: I.Fact,
  observed: Q.observes(c, program(world), subtrace(prefix_executed(m, r, ctx),
    Q.expand_exec(r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix), u, f)) ->
  Laws.Rule5(f, a, k, x, u):
  match f:
    case I.Evaluated{+rq, +cx, p2, +execution_trace}:
      combined_four(L.E<G, H>, Laws.Rule5(I.Evaluated{rq, cx, p2, execution_trace}, a, k, x, u), guards, g1 => g2 => g3 => g4 =>
        combined_four(WithoutInterest(suffix), Laws.Rule5(I.Evaluated{rq, cx, p2, execution_trace}, a, k, x, u), suffixes, s1 => s2 => s3 => s4 =>
          F.combined_pair(Laws.Rule5(I.Evaluated{rq, cx, p2, execution_trace}, a, k, x, u),
            {Q.query(subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx,
              E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix), u) ==
                Some{Q.Evaluated{rq, cx, execution_trace}} : Maybe<&2, Q.Frame>},
            Q.rel_fact(c, program(world), Q.Evaluated{rq, cx, execution_trace}, I.Evaluated{rq, cx, p2, execution_trace}),
            query_combined_relation(c, program(world), subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx,
              E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix), u,
              Q.Evaluated{rq, cx, execution_trace}, I.Evaluated{rq, cx, p2, execution_trace}, {==}, observed),
            query_result => relation => evaluation_by_origin(program, c, world, G, H, a, k, x, m, suffix, r, ctx, s0, n, u, rq, cx, p2, execution_trace,
              configuration, state, g1,
              L.Both{+r2 => +c2 => +p => s2(Evaluation{r2, c2, p}), +r2 => +c2 => +p => s3(Evaluation{r2, c2, p})}, refinement, relation,
              origin_frame_in_subtrace(prefix_executed(m, r, ctx), suffix, r, ctx,
                E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)), u, Q.Evaluated{rq, cx, execution_trace},
                prefix_without_other_interest(m, r, ctx, Evaluation{rq, cx, execution_trace}, Unit{}), s1(Evaluation{rq, cx, execution_trace}), query_result)))))
    case I.Operated{+e, +s, +o, +result}:
      combined_four(L.E<G, H>, Laws.Rule5(I.Operated{e, s, o, result}, a, k, x, u), guards, g1 => g2 => g3 => g4 =>
        combined_four(WithoutInterest(suffix), Laws.Rule5(I.Operated{e, s, o, result}, a, k, x, u), suffixes, s1 => s2 => s3 => s4 =>
          operation_by_origin(program, c, world, G, H, a, k, x, m, suffix, r, ctx, s0, n, u, e, s, o, result,
            configuration, L.Both{g1, g2}, +rq => +cx => +p => s2(Evaluation{rq, cx, p}), refinement,
            origin_frame_in_subtrace(prefix_executed(m, r, ctx), suffix, r, ctx,
              E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)), u, Q.Operated{e, s, o, result},
              prefix_without_other_interest(m, r, ctx, Operation{e, s, o, result}, Unit{}), s1(Operation{e, s, o, result}),
              Q.observation_frame(c, program(world), subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx,
                E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix), u,
                I.Operated{e, s, o, result}, observed)))))
    case I.ProgramStarted{+rq, +cx, p2}:
      combined_four(WithoutInterest(suffix), Laws.Rule5(I.ProgramStarted{rq, cx, p2}, a, k, x, u), suffixes, s1 => s2 => s3 => s4 =>
        start_of_origin_satisfies_rule5(a, k, x, r, ctx, program(world), rq, cx, p2, u,
          Nat.add(Q.size(before_of_start(m, r, ctx)), 0n),
          start_satisfies_rule5(program, c, world, G, H, a, k, x, m, r, ctx, s0,
            E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)), suffix,
            configuration, state, configuration_is_valid, state_valid, +r2 => +c2 => s2(Start{r2, c2}),
            refinement_of_trace(G, H, a, k, x, c, program(world), Some{s0},
              subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx,
                E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix),
              since_start(m, r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)), suffix),
              trace_preserves_start(m, r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)), suffix), refinement)),
          start_unique_in_list(c, program(world), m, r, ctx,
            E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)), suffix, u, rq, cx, p2,
            +r2 => +c2 => s1(Start{r2, c2}),
            (%trace_preserves_start(m, r, ctx, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)), suffix) :
              Q.observes(c, program(world), _, u, I.ProgramStarted{rq, cx, p2}) observed))))
    case I.InspectionNotModeled{+d}:
      combined_four(WithoutInterest(suffix), Empty, suffixes, s1 => s2 => s3 => s4 =>
        origin_impossible(Q.size(prefix_executed(m, r, ctx)), u,
          origin_frame_in_subtrace(prefix_executed(m, r, ctx), suffix, r, ctx,
            E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)), u, Q.Inspection{d},
            prefix_without_other_interest(m, r, ctx, Inspection{d}, Unit{}), s1(Inspection{d}),
            Q.observation_frame(c, program(world), subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx,
              E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix), u,
              I.InspectionNotModeled{d}, observed))))
    case I.EffectNotModeled{+d}:
      combined_four(WithoutInterest(suffix), Empty, suffixes, s1 => s2 => s3 => s4 =>
        origin_impossible(Q.size(prefix_executed(m, r, ctx)), u,
          origin_frame_in_subtrace(prefix_executed(m, r, ctx), suffix, r, ctx,
            E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)), u, Q.Effect{d},
            prefix_without_other_interest(m, r, ctx, Effect{d}, Unit{}), s1(Effect{d}),
            Q.observation_frame(c, program(world), subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx,
              E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix), u,
              I.EffectNotModeled{d}, observed))))
    case I.ConfigurationInUse{configuration}: Unit{}
    case I.InstanceStarted{s}: Unit{}
    case I.InitializationRefused{status}: Unit{}
    case I.ProofInitialAccepts{}: Unit{}
    case I.Encoded{v, result}: Unit{}
    case I.Decoded{bs, result}: Unit{}
    case I.Stored{s, bytes, abstraction}: Unit{}
    case I.CheckedLength{pos, n}: Unit{}
    case I.AllocatedField{pos, n}: Unit{}
    case I.ReadBody{before, n, declared}: Unit{}
    case I.ReceivedRequest{r}: Unit{}
    case I.Authenticated{r, ctx}: Unit{}
    case I.CertificateAccepted{r, ctx, program}: Unit{}
    case I.CertificateRejected{r, ctx}: Unit{}
    case I.Prepared{r, bs}: Unit{}
    case I.Published{s}: Unit{}
    case I.StateVisible{s}: Unit{}
    case I.FailedEnvironment{stage, id, fatal}: Unit{}
    case I.Concluded{r, s, closes}: Unit{}
    case I.DeliveredEverything{bs}: Unit{}
    case I.DeliveryInterrupted{prefix}: Unit{}
    case I.ClosedChannel{}: Unit{}
    case I.NextCall{previous, next}: Unit{}

def RootOfBlock(-p: S.Program, -c: S.Configuration, -s: D.State, block: Maybe<&2, Block>) -> Type:
  match block:
    case None{}: Unit
    case Some{Block{r, ctx, xs, suffix}}: PrefixOfRoot(p, c, s, r, ctx, xs)

def link_block_of_source(~source: Source.Source, -c: S.Configuration, -s: D.State,
  +origin: Source.JudgmentSyntactic, -p: S.Program, block: Maybe<&2, Block>,
  same_root: {Source.program(source, origin) == p : S.Program},
  real: BlockReal(source, c, s, origin, block)) -> RootOfBlock(p, c, s, block):
  match block:
    case None{}: Unit{}
    case Some{Block{r, ctx, xs, suffix}}:
      transport_prefix_of_root(Source.program(source, origin), p, c, s, r, ctx, xs, same_root, real)

def suffix_of_structure(-m: R.Micro, -original: List<&2, Q.Frame>, +b: Block,
  structure: Structure(m, original, Some{b})) -> WithoutInterest(suffix_block(b)):
  match structure:
    case L.Both{same, suffix}: suffix

def rule5_combined_trace_equal(~program: Nat -> S.Program, ~c: S.Configuration,
  +world: Nat, -G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  +m: R.Micro, +r: P.Request, +ctx: D.Context, +s0: D.State, +n: Nat,
  +suffix: List<&2, Q.Frame>, +original: List<&2, Q.Frame>,
  configuration: {c == I.configuration(x) : S.Configuration}, state: {s0 == I.initial(x) : D.State},
  configuration_is_valid: I.ConfigurationValid(a, c), state_valid: Requirements.Valid(c, s0),
  guards: Four<L.E<G, H>>, suffixes: Four<WithoutInterest(suffix)>,
  same_trace: {original == subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx,
    E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix) : List<&2, Q.Frame>},
  refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
    E.observation_model(c, program(world), Some{s0}, original)) : Nat -> I.Fact -> Type},
  +u: Nat, f: I.Fact, observed: Q.observes(c, program(world), original, u, f)) -> Laws.Rule5(f, a, k, x, u):
  F.combined_pair(Laws.Rule5(f, a, k, x, u),
    {original == subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx,
      E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix) : List<&2, Q.Frame>},
    {original == subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx,
      E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix) : List<&2, Q.Frame>},
    Call.duplicate_equality(List<&2, Q.Frame>, original, subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx,
      E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix), same_trace),
    for_refinement => for_query => rule5_of_frames(program, c, world, G, H, a, k, x, m, r, ctx, s0, n, suffix,
      configuration, state, configuration_is_valid, state_valid, guards, suffixes,
      refinement_of_trace(G, H, a, k, x, c, program(world), Some{s0}, original,
        subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx,
          E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix), for_refinement, refinement), u, f,
      (%for_query : Q.observes(c, program(world), _, u, f) observed)))

def rule5_of_block_concrete(~program: Nat -> S.Program, ~c: S.Configuration,
  +world: Nat, -G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  +m: R.Micro, +s0: D.State, +original: List<&2, Q.Frame>, block: Block,
  configuration: {c == I.configuration(x) : S.Configuration}, state: {s0 == I.initial(x) : D.State},
  configuration_is_valid: I.ConfigurationValid(a, c), state_valid: Requirements.Valid(c, s0),
  guards: Four<L.E<G, H>>, structures: Four<Structure(m, original, Some{block})>,
  real: RootOfBlock(program(world), c, s0, Some{block}),
  refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
    E.observation_model(c, program(world), Some{s0}, original)) : Nat -> I.Fact -> Type},
  +u: Nat, f: I.Fact, observed: Q.observes(c, program(world), original, u, f)) -> Laws.Rule5(f, a, k, x, u):
  match block:
    case Block{+r, +ctx, +xs, +suffix}:
      match real:
        case (+n, steps):
          combined_four(Structure(m, original, Some{Block{r, ctx, xs, suffix}}), Laws.Rule5(f, a, k, x, u), structures,
            e1 => e2 => e3 => e4 =>
              F.combined_pair(Laws.Rule5(f, a, k, x, u),
                {original == render_block(m, Block{r, ctx, xs, suffix}) : List<&2, Q.Frame>}, WithoutInterest(suffix), e1,
                rendered => without1 => rule5_combined_trace_equal(program, c, world, G, H, a, k, x, m, r, ctx, s0, n, suffix, original,
                  configuration, state, configuration_is_valid, state_valid, guards,
                  Four{without1, suffix_of_structure(m, original, Block{r, ctx, xs, suffix}, e2),
                    suffix_of_structure(m, original, Block{r, ctx, xs, suffix}, e3), suffix_of_structure(m, original, Block{r, ctx, xs, suffix}, e4)},
                  Equal.trans(List<&2, Q.Frame>, original, render_block(m, Block{r, ctx, xs, suffix}),
                    subtrace(prefix_executed(m, r, ctx), Q.expand_exec(r, ctx,
                      E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c))), suffix), rendered,
                    Equal.cong(List<&2, Q.FrameExec>, List<&2, Q.Frame>, qs => render_block(m, Block{r, ctx, qs, suffix}),
                      xs, E.generate(n, N.start(program(world), ctx, I.arguments(r), s0), S.schema(c)), steps)), refinement, u, f, observed)))

def rule5_of_block_optional(~program: Nat -> S.Program, ~c: S.Configuration,
  +world: Nat, -G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  +m: R.Micro, +s0: D.State, +original: List<&2, Q.Frame>, block: Maybe<&2, Block>,
  configuration: {c == I.configuration(x) : S.Configuration}, state: {s0 == I.initial(x) : D.State},
  configuration_is_valid: I.ConfigurationValid(a, c), state_valid: Requirements.Valid(c, s0),
  guards: Four<L.E<G, H>>, structures: Four<Structure(m, original, block)>,
  real: RootOfBlock(program(world), c, s0, block),
  refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
    E.observation_model(c, program(world), Some{s0}, original)) : Nat -> I.Fact -> Type},
  +u: Nat, f: I.Fact, observed: Q.observes(c, program(world), original, u, f)) -> Laws.Rule5(f, a, k, x, u):
  match block:
    case None{}:
      combined_four(Structure(m, original, None{}), Laws.Rule5(f, a, k, x, u), structures,
        e1 => e2 => e3 => e4 => fact_without_execution(a, k, x, c, program(world), original, u, f, e1, observed))
    case Some{+b}:
      rule5_of_block_concrete(program, c, world, G, H, a, k, x, m, s0, original, b,
        configuration, state, configuration_is_valid, state_valid, guards, structures, real, refinement, u, f, observed)

def rule5_of_route(~program: Nat -> S.Program, ~c: S.Configuration,
  +world: Nat, -G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  +m: R.Micro, +s0: D.State, +branch: R.Branch,
  configuration: {c == I.configuration(x) : S.Configuration}, state: {s0 == I.initial(x) : D.State},
  configuration_is_valid: I.ConfigurationValid(a, c), state_valid: Requirements.Valid(c, s0),
  guards: Four<L.E<G, H>>, real: RootOfBlock(program(world), c, s0, block_branch(m, s0, branch)),
  refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
    E.observation_model(c, program(world), Some{s0}, R.render(m, s0, branch))) : Nat -> I.Fact -> Type},
  +u: Nat, f: I.Fact, observed: Q.observes(c, program(world), R.render(m, s0, branch), u, f)) -> Laws.Rule5(f, a, k, x, u):
  rule5_of_block_optional(program, c, world, G, H, a, k, x, m, s0, R.render(m, s0, branch), block_branch(m, s0, branch),
    configuration, state, configuration_is_valid, state_valid, guards,
    Four{structure_of_route(m, s0, branch), structure_of_route(m, s0, branch), structure_of_route(m, s0, branch), structure_of_route(m, s0, branch)},
    real, refinement, u, f, observed)

# ConfigurationInUse/StateVisible are the only simultaneous facts synthesized
# by observes_service. Rule5 is Unit there; other cases use the query.
def raise_rule5_service(-a: I.Environment, -k: String, -x: I.Scenario,
  -c: S.Configuration, -p: S.Program, +initial: Maybe<&2, D.State>, +frames: List<&2, Q.Frame>, +t: Nat, f: I.Fact,
  resolve: @g: I.Fact -> Q.observes(c, p, frames, t, g) -> Laws.Rule5(g, a, k, x, t),
  observed: Q.observes_service(c, p, initial, frames, t, f)) -> Laws.Rule5(f, a, k, x, t):
  match f:
    case I.Evaluated{r, ctx, prog, execution_trace}: resolve(I.Evaluated{r, ctx, prog, execution_trace}, observed)
    case I.ProgramStarted{r, ctx, prog}: resolve(I.ProgramStarted{r, ctx, prog}, observed)
    case I.Operated{e, s, o, result}: resolve(I.Operated{e, s, o, result}, observed)
    case I.InspectionNotModeled{d}: resolve(I.InspectionNotModeled{d}, observed)
    case I.EffectNotModeled{d}: resolve(I.EffectNotModeled{d}, observed)
    case I.ConfigurationInUse{configuration}: Unit{}
    case I.InstanceStarted{s}: Unit{}
    case I.InitializationRefused{status}: Unit{}
    case I.ProofInitialAccepts{}: Unit{}
    case I.Encoded{v, result}: Unit{}
    case I.Decoded{bs, result}: Unit{}
    case I.Stored{s, bytes, abstraction}: Unit{}
    case I.CheckedLength{pos, n}: Unit{}
    case I.AllocatedField{pos, n}: Unit{}
    case I.ReadBody{before, n, declared}: Unit{}
    case I.ReceivedRequest{r}: Unit{}
    case I.Authenticated{r, ctx}: Unit{}
    case I.CertificateAccepted{r, ctx, program}: Unit{}
    case I.CertificateRejected{r, ctx}: Unit{}
    case I.Prepared{r, bs}: Unit{}
    case I.Published{s}: Unit{}
    case I.StateVisible{s}: Unit{}
    case I.FailedEnvironment{stage, id, fatal}: Unit{}
    case I.Concluded{r, s, closes}: Unit{}
    case I.DeliveredEverything{bs}: Unit{}
    case I.DeliveryInterrupted{prefix}: Unit{}
    case I.ClosedChannel{}: Unit{}
    case I.NextCall{previous, next}: Unit{}

def rule5_of_service(~program: Nat -> S.Program, ~c: S.Configuration,
  +world: Nat, -G: Type, -H: Type, -a: I.Environment, -k: String, -x: I.Scenario,
  +m: R.Micro, +s0: D.State, +branch: R.Branch,
  configuration: {c == I.configuration(x) : S.Configuration}, state: {s0 == I.initial(x) : D.State},
  configuration_is_valid: I.ConfigurationValid(a, c), state_valid: Requirements.Valid(c, s0),
  guards: Four<L.E<G, H>>, real: RootOfBlock(program(world), c, s0, block_branch(m, s0, branch)),
  refinement: {E.observation_real(a, k, x) == Ref.observation_stored(G, H,
    E.observation_model(c, program(world), Some{s0}, R.render(m, s0, branch))) : Nat -> I.Fact -> Type},
  +u: Nat, f: I.Fact, observed: Q.observes_service(c, program(world), Some{s0}, R.render(m, s0, branch), u, f)) -> Laws.Rule5(f, a, k, x, u):
  raise_rule5_service(a, k, x, c, program(world), Some{s0}, R.render(m, s0, branch), u, f,
    g => fact => rule5_of_route(program, c, world, G, H, a, k, x, m, s0, branch,
      configuration, state, configuration_is_valid, state_valid, guards, real, refinement, u, g, fact), observed)

def initial_accepts_without_execution(+m: R.Micro, +s: D.State, is_valid: Bool, result: R.ResultInitial) ->
  WithoutInterest(R.render(m, s, R.decide_accepted_initial(result, is_valid))):
  match is_valid result:
    case False{} R.InitializationFinished{}: structure_of_route(m, s, R.InitialRefusal{S.DataError{}})
    case True{} R.InitializationFinished{}: structure_of_route(m, s, R.InitialOk{})
    case +v R.FailedInitial{+accepts, +stage, +id, +fatal}:
      structure_of_route(m, s, R.InitialFailure{accepts && v, stage, id, fatal})
    case +v R.PendingInitial{+accepts}: structure_of_route(m, s, R.InitialPending{accepts && v})

def initial_cases_without_execution(+m: R.Micro, +s: D.State, +is_valid: Bool, judgment: R.Judgment, +result: R.ResultInitial) ->
  WithoutInterest(R.render(m, s, R.decide_judgment_initial(judgment, result, is_valid))):
  match judgment:
    case R.Accepted{}: initial_accepts_without_execution(m, s, is_valid, result)
    case R.Refused{}: structure_of_route(m, s, R.InitialRefusal{S.Certificate{}})
    case R.ErrorJudgment{+id, +fatal}: structure_of_route(m, s, R.InitialFailure{False{}, X.Verify{}, id, fatal})
    case R.PendingJudgment{}: structure_of_route(m, s, R.InitialPending{False{}})

def rule5_initial(~c: S.Configuration, -a: I.Environment, -k: String, -x: I.Scenario,
  -p: S.Program, +identity: String, +s: D.State, +m: R.Micro, +judgment: R.Judgment, +result: R.ResultInitial,
  +t: Nat, f: I.Fact,
  observed: Q.observes_service(c, p, None{}, R.generate_result_initial(c, identity, s, judgment, result, m), t, f)) ->
  Laws.Rule5(f, a, k, x, t):
  raise_rule5_service(a, k, x, c, p, None{}, R.generate_result_initial(c, identity, s, judgment, result, m), t, f,
    g => fact => fact_without_execution(a, k, x, c, p, R.generate_result_initial(c, identity, s, judgment, result, m), t, g,
      initial_cases_without_execution(m, s, Configuration.is_valid(c, identity), judgment, result), fact), observed)

def observation_of_call(~source: Source.Source, ~c: S.Configuration,
  +s: D.State, +reception: X.Reception, +data: Source.CallData) -> Nat -> I.Fact -> Type:
  t => f => Source.of_observation(source, c, Source.construct_call(c, s, reception, data), t, f)

def refinement_literal_of_call(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +s: D.State, +reception: X.Reception, +data: Source.CallData,
  canonical: {I.Serve{world, c, s, reception} == Source.scenario(source, world) : I.Scenario},
  same_call: {data == Source.call(source, world) : Source.CallData}) ->
  {E.observation_real(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}) ==
    Ref.observation_stored({Source.artifact(source) == Source.artifact(source) : String},
      {I.Serve{world, c, s, reception} == Source.scenario(source, world) : I.Scenario},
      observation_of_call(source, c, s, reception, data)) : Nat -> I.Fact -> Type}:
  Equal.trans((Nat -> I.Fact -> Type),
    E.observation_real(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}),
    Ref.observation_stored({Source.artifact(source) == Source.artifact(source) : String},
      {I.Serve{world, c, s, reception} == Source.scenario(source, world) : I.Scenario},
      t => f => Source.of_route(source, I.Serve{world, c, s, reception}, t, f)),
    Ref.observation_stored({Source.artifact(source) == Source.artifact(source) : String},
      {I.Serve{world, c, s, reception} == Source.scenario(source, world) : I.Scenario}, observation_of_call(source, c, s, reception, data)),
    Equal.cong(I.Scenario, (Nat -> I.Fact -> Type),
      x => t => f => L.E<{Source.artifact(source) == Source.artifact(source) : String},
        L.E<{I.Serve{world, c, s, reception} == Source.scenario(source, world) : I.Scenario}, Source.of_route(source, x, t, f)>>,
      Source.scenario(source, world), I.Serve{world, c, s, reception},
      Equal.sym(I.Scenario, I.Serve{world, c, s, reception}, Source.scenario(source, world), canonical)),
    Equal.cong(Source.CallData, (Nat -> I.Fact -> Type),
      d => Ref.observation_stored({Source.artifact(source) == Source.artifact(source) : String},
        {I.Serve{world, c, s, reception} == Source.scenario(source, world) : I.Scenario}, observation_of_call(source, c, s, reception, d)),
      Source.call(source, world), data,
      Equal.sym(Source.CallData, data, Source.call(source, world), same_call)))

def four_guards(-name: String, -x: I.Scenario, -canonical: I.Scenario,
  equal: {x == canonical : I.Scenario}) -> Four<L.E<{name == name : String}, {x == canonical : I.Scenario}>>:
  %equal : Four<L.E<{name == name : String}, {x == _ : I.Scenario}>>
  Four{L.Both{{==}, {==}}, L.Both{{==}, {==}}, L.Both{{==}, {==}}, L.Both{{==}, {==}}}

def NameCorrect(~source: Source.Source) -> Type:
  {Source.artifact(source) == Source.artifact(source) : String}

def CallCanonical(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +r: X.Reception) -> Type:
  {I.Serve{world, c, s, r} == Source.scenario(source, world) : I.Scenario}

def CallReal(~source: Source.Source, ~c: S.Configuration, +s: D.State, +reception: X.Reception,
  data: Source.CallData) -> Type:
  match data:
    case Source.CallData{cf, +origin, pf, tf, +state, +tools, micro}:
      FramingReal(source, c, s, origin, state, S.schema(c), S.limits(c), tools,
        X.decide_reception_in(S.limits(c), reception), R.preprocessing(tools))

def execution_of_decision(~source: Source.Source, ~c: S.Configuration, +s: D.State,
  +origin: Source.JudgmentSyntactic, +state: List<&2, U32>, +data: R.DataTools, +reception: X.Reception,
  real: FramingReal(source, c, s, origin, state, S.schema(c), S.limits(c), data,
    X.decide_reception_in(S.limits(c), reception), R.preprocessing(data))) ->
  BranchReal(source, c, s, origin, R.decide(c, reception, state, data)):
  L.and_left(BranchReal(source, c, s, origin, R.decide(c, reception, state, data)),
    L.E<AuthOfBranch(s, R.decide(c, reception, state, data)), GateOfBranch(R.judgment_of(data), R.decide(c, reception, state, data))>,
    route_real_decided(source, c, s, origin, state, data, reception, real))

def rule5_of_call(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +s: D.State, +reception: X.Reception, data: Source.CallData,
  configuration_is_valid: I.ConfigurationValid(Source.environment(source), c), state_valid: Requirements.Valid(c, s),
  canonical: CallCanonical(source, c, world, s, reception),
  same_call: {data == Source.call(source, world) : Source.CallData}, real: CallReal(source, c, s, reception, data),
  +t: Nat, f: I.Fact, observed: Source.of_route(source, I.Serve{world, c, s, reception}, t, f)) ->
  Laws.Rule5(f, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t):
  match data:
    case Source.CallData{+cf, +origin, +pf, +tf, +state, +tools, +micro}:
      combined_four({Source.CallData{cf, origin, pf, tf, state, tools, micro} == Source.call(source, world) : Source.CallData},
        Laws.Rule5(f, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t),
        four_equalities(Source.CallData, Source.CallData{cf, origin, pf, tf, state, tools, micro}, Source.call(source, world), same_call),
        d1 => d2 => d3 => d4 =>
          combined_four({Source.program(source, origin) == program_of_world(source, world) : S.Program},
            Laws.Rule5(f, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t),
            four_equalities(S.Program, Source.program(source, origin), program_of_world(source, world),
              same_root_of_call(source, world, Source.CallData{cf, origin, pf, tf, state, tools, micro}, d3)),
            p1 => p2 => p3 => p4 =>
              F.combined_pair(Laws.Rule5(f, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t),
                CallCanonical(source, c, world, s, reception), CallCanonical(source, c, world, s, reception),
                Call.duplicate_equality(I.Scenario, I.Serve{world, c, s, reception}, Source.scenario(source, world), canonical),
                h1 => h2 => rule5_of_service(program_of_world(source), c, world,
                  NameCorrect(source), CallCanonical(source, c, world, s, reception), Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception},
                  micro, s, R.decide(c, reception, state, tools), {==}, {==}, configuration_is_valid, state_valid,
                  four_guards(Source.artifact(source), I.Serve{world, c, s, reception}, Source.scenario(source, world), h2),
                  link_block_of_source(source, c, s, origin, program_of_world(source, world), block_branch(micro, s, R.decide(c, reception, state, tools)), p2,
                    block_real_of_route(source, c, s, origin, micro, R.decide(c, reception, state, tools),
                      execution_of_decision(source, c, s, origin, state, tools, reception, real))),
                  Equal.trans((Nat -> I.Fact -> Type),
                    E.observation_real(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}),
                    Ref.observation_stored(NameCorrect(source), CallCanonical(source, c, world, s, reception),
                      E.observation_model(c, Source.program(source, origin), Some{s}, R.render(micro, s, R.decide(c, reception, state, tools)))),
                    Ref.observation_stored(NameCorrect(source), CallCanonical(source, c, world, s, reception),
                      E.observation_model(c, program_of_world(source, world), Some{s}, R.render(micro, s, R.decide(c, reception, state, tools)))),
                    refinement_literal_of_call(source, c, world, s, reception, Source.CallData{cf, origin, pf, tf, state, tools, micro}, h1, d2),
                    Equal.cong(S.Program, (Nat -> I.Fact -> Type),
                      p => Ref.observation_stored(NameCorrect(source), CallCanonical(source, c, world, s, reception),
                        E.observation_model(c, p, Some{s}, R.render(micro, s, R.decide(c, reception, state, tools)))),
                      Source.program(source, origin), program_of_world(source, world), p1)), t, f,
                  (%p3 : Q.observes_service(c, _, Some{s}, R.render(micro, s, R.decide(c, reception, state, tools)), t, f)
                    %Equal.sym(Source.CallData, Source.CallData{cf, origin, pf, tf, state, tools, micro}, Source.call(source, world), d1) :
                      observation_of_call(source, c, s, reception, _)(t, f)
                    observed)))))

def observation_of_initial(~source: Source.Source, ~c: S.Configuration,
  +s: D.State, +data: Source.InitialData) -> Nat -> I.Fact -> Type:
  t => f => Source.of_observation(source, c, Source.construct_initial(Source.identity(source), c, s, data), t, f)

def rule5_of_initial(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +s: D.State, +pi: String, data: Source.InitialData,
  same: {data == Source.initial(source, world) : Source.InitialData}, +t: Nat, f: I.Fact,
  observed: Source.of_route(source, I.Initialize{world, c, s, pi}, t, f)) ->
  Laws.Rule5(f, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t):
  match data:
    case Source.InitialData{cf, sf, pf, +judgment, +result, +micro}:
      rule5_initial(c, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, Source.without_program(),
        Source.identity(source), s, micro, judgment, result, t, f,
        (%Equal.sym(Source.InitialData, Source.InitialData{cf, sf, pf, judgment, result, micro}, Source.initial(source, world), same) :
          observation_of_initial(source, c, s, _)(t, f) observed))

def OriginOfMoment(~source: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, +world: Nat, moment: Scenarios.Moment) -> Type:
  match moment:
    case Scenarios.Initialization{}: Unit
    case Scenarios.Service{r}:
      L.E<I.ConfigurationValid(Source.environment(source), c),
        L.E<Requirements.Valid(c, seed(Unit{})),
          L.E<History.Sources(c, history(world), seed(Unit{})),
            CallReal(source, c, History.state(history(world), seed(Unit{})), r, Source.call(source, world))>>>

def rule5_by_moment(~source: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~pi: String,
  +world: Nat, moment: Scenarios.Moment,
  canonical: {Scenarios.of_moment(c, seed, history, pi, moment, world) == Source.scenario(source, world) : I.Scenario},
  origin: OriginOfMoment(source, c, seed, history, world, moment), +t: Nat, f: I.Fact,
  observed: Source.of_route(source, Scenarios.of_moment(c, seed, history, pi, moment, world), t, f)) ->
  Laws.Rule5(f, Source.environment(source), Source.artifact(source), Scenarios.of_moment(c, seed, history, pi, moment, world), t):
  match moment:
    case Scenarios.Initialization{}:
      rule5_of_initial(source, c, world, seed(Unit{}), pi, Source.initial(source, world), {==}, t, f, observed)
    case Scenarios.Service{+r}:
      match origin:
        case L.Both{configuration_is_valid, L.Both{initial, L.Both{sources, real}}}:
          rule5_of_call(source, c, world, History.state(history(world), seed(Unit{})), r, Source.call(source, world),
            configuration_is_valid, History.history_preserves_validity(c, history(world), seed(Unit{}), initial, sources),
            canonical, {==}, real, t, f, observed)

def rule5_in_canonical(~source: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  +world: Nat,
  scenario: {Source.scenario(source, world) == Scenarios.canonical(c, seed, history, moment, pi, world) : I.Scenario},
  trace: OriginOfMoment(source, c, seed, history, world, moment(world)), +t: Nat, f: I.Fact,
  observed: Source.of_route(source, Source.scenario(source, world), t, f)) ->
  Laws.Rule5(f, Source.environment(source), Source.artifact(source), Source.scenario(source, world), t):
  F.combined_pair(Laws.Rule5(f, Source.environment(source), Source.artifact(source), Source.scenario(source, world), t),
    {Source.scenario(source, world) == Scenarios.canonical(c, seed, history, moment, pi, world) : I.Scenario},
    {Source.scenario(source, world) == Scenarios.canonical(c, seed, history, moment, pi, world) : I.Scenario},
    Call.duplicate_equality(I.Scenario, Source.scenario(source, world), Scenarios.canonical(c, seed, history, moment, pi, world), scenario),
    transport => origin => apply(Source.of_route(source, Source.scenario(source, world), t, f),
      Laws.Rule5(f, Source.environment(source), Source.artifact(source), Source.scenario(source, world), t),
      (%Equal.sym(I.Scenario, Source.scenario(source, world), Scenarios.canonical(c, seed, history, moment, pi, world), transport) :
        Source.of_route(source, _, t, f) -> Laws.Rule5(f, Source.environment(source), Source.artifact(source), _, t)
        raw => rule5_by_moment(source, c, seed, history, pi, world, moment(world),
          Equal.sym(I.Scenario, Source.scenario(source, world), Scenarios.canonical(c, seed, history, moment, pi, world), origin), trace, t, f, raw)), observed))

def rule5_of_origin_canonical(~source: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  -x: I.Scenario, +world: Nat,
  scenario: {Source.scenario(source, world) == Scenarios.canonical(c, seed, history, moment, pi, world) : I.Scenario},
  trace: OriginOfMoment(source, c, seed, history, world, moment(world)), +t: Nat, f: I.Fact,
  origin: L.E<NameCorrect(source), L.E<{x == Source.scenario(source, world) : I.Scenario},
    Source.of_route(source, Source.scenario(source, world), t, f)>>) ->
  Laws.Rule5(f, Source.environment(source), Source.artifact(source), x, t):
  match origin:
    case L.Both{name, L.Both{equal, raw}}:
      %Equal.sym(I.Scenario, x, Source.scenario(source, world), equal) : Laws.Rule5(f, Source.environment(source), Source.artifact(source), _, t)
      rule5_in_canonical(source, c, seed, history, moment, pi, world, scenario, trace, t, f, raw)

def law5_of_scenario(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  origins: @world: Nat -> OriginOfMoment(Model.source(base, c, seed, history, moment, pi), c, seed, history, world, moment(world)),
  x: I.Scenario, +t: Nat, f: I.Fact,
  observed: I.Happens(Source.environment(Model.source(base, c, seed, history, moment, pi)),
    Source.artifact(Model.source(base, c, seed, history, moment, pi)), x, t, f)) ->
  Laws.Rule5(f, Source.environment(Model.source(base, c, seed, history, moment, pi)),
    Source.artifact(Model.source(base, c, seed, history, moment, pi)), x, t):
  match x:
    case I.Initialize{+world, original, +s, +proof}:
      rule5_of_origin_canonical(Model.source(base, c, seed, history, moment, pi), c, seed, history, moment, pi,
        I.Initialize{world, original, s, proof}, world,
        Model.scenario_of_model(base, c, seed, history, moment, pi, world), origins(world), t, f,
        Source.eliminate_fact(Model.source(base, c, seed, history, moment, pi),
          Source.artifact(Model.source(base, c, seed, history, moment, pi)), I.Initialize{world, original, s, proof}, t, f, observed))
    case I.Serve{+world, original, +s, +reception}:
      rule5_of_origin_canonical(Model.source(base, c, seed, history, moment, pi), c, seed, history, moment, pi,
        I.Serve{world, original, s, reception}, world,
        Model.scenario_of_model(base, c, seed, history, moment, pi, world), origins(world), t, f,
        Source.eliminate_fact(Model.source(base, c, seed, history, moment, pi),
          Source.artifact(Model.source(base, c, seed, history, moment, pi)), I.Serve{world, original, s, reception}, t, f, observed))

# EXACT Law5 of the chosen environment; no final law is a premise.
def law5_of_model(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  origins: @world: Nat -> OriginOfMoment(Model.source(base, c, seed, history, moment, pi), c, seed, history, world, moment(world))) ->
  Laws.Law5(Source.environment(Model.source(base, c, seed, history, moment, pi)),
    Source.artifact(Model.source(base, c, seed, history, moment, pi))):
  x => +t => f => observed =>
    law5_of_scenario(base, c, seed, history, moment, pi, origins, x, t, f, observed)
