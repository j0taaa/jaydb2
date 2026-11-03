# Protocol of actual Core steps without copying continuations or programs.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Protocol.bend as P
import ../contract/Interface.bend as I
import ../contract/Links.bend as V
import ../contract/Logic.bend as L
import ../src/Core.bend as N
import ./Foundations.bend as F
import ./Machine.bend as M
import ./CodecSumsOrder.bend as Numbers
import ./CodecRelaxArithmeticNat.bend as Arithmetic
import ./ProtocolService.bend as Q
import ./Call.bend as Call

# The Data result determines the prefix, independently of the linear continuation.
def after(result: D.ResultOp, s: D.State, o: D.Operation,
  ts: List<&2, S.OperationEvent>) -> S.Trace:
  match result:
    case D.FailureData{}:
      S.Final{s, S.append(ts, S.OperationEvent{o, S.ErrorOfData{}}), S.response_error(S.DataError{})}
    case D.Observed{obs}:
      S.Prefix{s, S.append(ts, S.OperationEvent{o, S.Reading{obs}})}
    case D.Changed{w}:
      S.Prefix{w, S.append(ts, S.OperationEvent{o, S.Write{}})}

law after_satisfies_binding:
  for result: D.ResultOp
  for -s: D.State
  for -o: D.Operation
  for -ts: List<&2, S.OperationEvent>
  V.AfterOperation(result, s, o, ts, after(result, s, o, ts))
def after_satisfies_binding(result, s, o, ts):
  match result:
    case D.FailureData{}: {==}
    case D.Observed{obs}: L.Both{{==}, {==}}
    case D.Changed{w}: L.Both{{==}, {==}}

law after_and_o_step_real:
  for result: D.ResultOp
  for -s: D.State
  for -o: D.Operation
  for -ts: List<&2, S.OperationEvent>
  for -k: S.Return -> S.Action
  {after(result, s, o, ts) ==
    N.snapshot(N.step_machine(S.apply(result, s, o, k), ts)) : S.Trace}
def after_and_o_step_real(result, s, o, ts, k):
  match result:
    case D.FailureData{}: {==}
    case D.Observed{obs}: {==}
    case D.Changed{w}: {==}

law less_successor:
  for n: Nat
  {Nat.is_lt(n, Succ{n}) == True{} : Bool}
def less_successor(n):
  match n:
    case 0n: {==}
    case 1n+k: less_successor(k)

# A window between b and b+2 contains only position b+1.
law negative_less_zero:
  for n: Nat
  {Nat.is_lt(n, 0n) == False{} : Bool}
def negative_less_zero(n):
  match n:
    case 0n: {==}
    case 1n+k: {==}

law unique_between_two_successors:
  for b: Nat
  for u: Nat
  for left: {Nat.is_lt(b, u) == True{} : Bool}
  for right: {Nat.is_lt(u, Succ{Succ{b}}) == True{} : Bool}
  {u == Succ{b} : Nat}
def unique_between_two_successors(b, u, left, right):
  match b u:
    case 0n 0n:
      F.absurd_boolean({0n == 1n : Nat}, left)
    case 0n 1n+k:
      match k:
        case 0n: {==}
        case 1n+j:
          F.absurd_boolean({Succ{Succ{j}} == 1n : Nat},
            Equal.trans(Bool, False{}, Nat.is_lt(j, 0n), True{},
              Equal.sym(Bool, Nat.is_lt(j, 0n), False{}, negative_less_zero(j)), right))
    case 1n+b 0n:
      F.absurd_boolean({0n == Succ{Succ{b}} : Nat}, left)
    case 1n+b 1n+u:
      Equal.cong(Nat, Nat, x => Succ{x}, u, Succ{b},
        unique_between_two_successors(b, u, left, right))

def query(xs: List<&2, Q.FrameExec>, n: Nat) -> Maybe<&2, Q.FrameExec>:
  match xs n:
    case Nil{} _: None{}
    case Con{h, t} 0n: Some{h}
    case Con{h, t} 1n+k: query(t, k)

type Sequence is Data:
  Sequence{head: Q.FrameExec, tail: List<&2, Q.FrameExec>}

def head(s: Sequence) -> Q.FrameExec:
  Sequence{h, t} = s
  h

def tail(s: Sequence) -> List<&2, Q.FrameExec>:
  Sequence{h, t} = s
  t

def expand(+s: Sequence) -> List<&2, Q.FrameExec>:
  Con{head(s), tail(s)}

# n is only a mathematical witness; the sequence stops at the first Stopped state.
def generate_sequence(n: Nat, m: N.Machine, +e: D.Schema) -> Sequence:
  match n m:
    case _ N.Stopped{w, ts, r}:
      Sequence{Q.Evaluation{S.Final{w, ts, r}}, Nil{}}
    case 0n N.Running{w, a, ts}:
      Sequence{Q.Evaluation{S.Prefix{w, ts}}, Nil{}}
    case 1n+j N.Running{+w, a, +ts}:
      match a:
        case S.Finish{v}:
          Sequence{Q.Evaluation{S.Prefix{w, ts}}, [Q.Evaluation{S.Final{w, ts, S.Response{S.Success{}, v}}}]}
        case S.Refuse{v}:
          Sequence{Q.Evaluation{S.Prefix{w, ts}}, [Q.Evaluation{S.Final{w, ts, S.Response{S.Refusal{}, v}}}]}
        case S.Access{+o, k}:
          +res = D.operate(e, w, o)
          Sequence{Q.Evaluation{S.Prefix{w, ts}}, Q.Operation{e, w, o, res} <>
            expand(generate_sequence(j, N.step_machine(S.apply(res, w, o, k), ts), e))}

def generate(n: Nat, m: N.Machine, e: D.Schema) -> List<&2, Q.FrameExec>:
  expand(generate_sequence(n, m, e))

law generate_starts_in_state_real:
  for n: Nat
  for m: N.Machine
  for -e: D.Schema
  {query(generate(n, m, e), 0n) == Some{Q.Evaluation{N.snapshot(m)}} : Maybe<&2, Q.FrameExec>}
def generate_starts_in_state_real(n, m, e):
  match n m:
    case _ N.Stopped{w, ts, r}: {==}
    case 0n N.Running{w, a, ts}: {==}
    case 1n+j N.Running{w, a, ts}:
      match a:
        case S.Finish{v}: {==}
        case S.Refuse{v}: {==}
        case S.Access{o, k}: {==}

def OperationCorrect(-xs: List<&2, Q.FrameExec>, -t: Nat, q: Q.FrameExec, -e: D.Schema) -> Type:
  match q:
    case Q.Evaluation{execution_trace}: Unit
    case Q.Operation{e2, s, o, r}:
      L.E<{e2 == e : D.Schema}, L.E<{r == D.operate(e, s, o) : D.ResultOp},
        &b: Nat -> &ts: List<&2, S.OperationEvent> ->
          L.E<{t == Succ{b} : Nat},
            L.E<{query(xs, b) == Some{Q.Evaluation{S.Prefix{s, ts}}} : Maybe<&2, Q.FrameExec>},
              {query(xs, Succ{Succ{b}}) == Some{Q.Evaluation{after(r, s, o, ts)}} : Maybe<&2, Q.FrameExec>}>>>>

# No uniqueness premise: neighbors query the produced sequence.
def evaluation_correct(-xs: List<&2, Q.FrameExec>, -t: Nat, -e: D.Schema,
  +execution_trace: S.Trace, -q: Q.FrameExec,
  equality: {Some{Q.Evaluation{execution_trace}} == Some{q} : Maybe<&2, Q.FrameExec>}) ->
  OperationCorrect(xs, t, q, e):
  %F.some_injective(Q.FrameExec, Q.Evaluation{execution_trace}, q, equality) : OperationCorrect(xs, t, _, e)
  Unit{}

def shift_operation(-a: Q.FrameExec, -b: Q.FrameExec,
  -xs: List<&2, Q.FrameExec>, -t: Nat, q: Q.FrameExec, -e: D.Schema,
  correct: OperationCorrect(xs, t, q, e)) ->
  OperationCorrect(Con{a, Con{b, xs}}, Succ{Succ{t}}, q, e):
  match q:
    case Q.Evaluation{execution_trace}: Unit{}
    case Q.Operation{e2, s, o, r}:
      match correct:
        case L.Both{schema, L.Both{result, (start, ts, L.Both{position, L.Both{before, later}})}}:
          L.Both{schema, L.Both{result, (Succ{Succ{start}}, ts,
            L.Both{Equal.cong(Nat, Nat, n => Succ{Succ{n}}, t, Succ{start}, position), L.Both{before, later}})}}

law all_operations_generated_are_real:
  for n: Nat
  for m: N.Machine
  for +e: D.Schema
  for t: Nat
  for +q: Q.FrameExec
  for present: {query(generate(n, m, e), t) == Some{q} : Maybe<&2, Q.FrameExec>}
  OperationCorrect(generate(n, m, e), t, q, e)
def all_operations_generated_are_real(n, m, e, t, q, present):
  match n m:
    case _ N.Stopped{w, ts, r}:
      match t:
        case 0n: evaluation_correct(generate(n, N.Stopped{w, ts, r}, e), 0n, e, S.Final{w, ts, r}, q, present)
        case 1n+j:
          L.ex_false(OperationCorrect(generate(n, N.Stopped{w, ts, r}, e), 1n+j, q, e), F.none_negative_some(Q.FrameExec, q, present))
    case 0n N.Running{w, a, ts}:
      match t:
        case 0n: evaluation_correct(generate(0n, N.Running{w, a, ts}, e), 0n, e, S.Prefix{w, ts}, q, present)
        case 1n+j:
          L.ex_false(OperationCorrect(generate(0n, N.Running{w, a, ts}, e), 1n+j, q, e), F.none_negative_some(Q.FrameExec, q, present))
    case 1n+j N.Running{+w, a, +ts}:
      match a:
        case S.Finish{v}:
          match t:
            case 0n: evaluation_correct(generate(1n+j, N.Running{w, S.Finish{v}, ts}, e), 0n, e, S.Prefix{w, ts}, q, present)
            case 1n+k:
              match k:
                case 0n: evaluation_correct(generate(1n+j, N.Running{w, S.Finish{v}, ts}, e), 1n, e, S.Final{w, ts, S.Response{S.Success{}, v}}, q, present)
                case 1n+i:
                  L.ex_false(OperationCorrect(generate(1n+j, N.Running{w, S.Finish{v}, ts}, e), Succ{Succ{i}}, q, e), F.none_negative_some(Q.FrameExec, q, present))
        case S.Refuse{v}:
          match t:
            case 0n: evaluation_correct(generate(1n+j, N.Running{w, S.Refuse{v}, ts}, e), 0n, e, S.Prefix{w, ts}, q, present)
            case 1n+k:
              match k:
                case 0n: evaluation_correct(generate(1n+j, N.Running{w, S.Refuse{v}, ts}, e), 1n, e, S.Final{w, ts, S.Response{S.Refusal{}, v}}, q, present)
                case 1n+i:
                  L.ex_false(OperationCorrect(generate(1n+j, N.Running{w, S.Refuse{v}, ts}, e), Succ{Succ{i}}, q, e), F.none_negative_some(Q.FrameExec, q, present))
        case S.Access{+o, k}:
          match t:
            case 0n: evaluation_correct(generate(1n+j, N.Running{w, S.Access{o, k}, ts}, e), 0n, e, S.Prefix{w, ts}, q, present)
            case 1n+i:
              match i:
                case 0n:
                  %F.some_injective(Q.FrameExec, Q.Operation{e, w, o, D.operate(e, w, o)}, q, present) :
                    OperationCorrect(generate(1n+j, N.Running{w, S.Access{o, k}, ts}, e), 1n, _, e)
                  L.Both{{==}, L.Both{{==}, (0n, ts, L.Both{{==}, L.Both{{==},
                    (%Equal.sym(S.Trace, after(D.operate(e, w, o), w, o, ts),
                      N.snapshot(N.step_machine(S.apply(D.operate(e, w, o), w, o, k), ts)),
                      after_and_o_step_real(D.operate(e, w, o), w, o, ts, k)) :
                        {query(generate(j, N.step_machine(S.apply(D.operate(e, w, o), w, o, k), ts), e), 0n) == Some{Q.Evaluation{_}} : Maybe<&2, Q.FrameExec>}
                      generate_starts_in_state_real(j, N.step_machine(S.apply(D.operate(e, w, o), w, o, k), ts), e))}})}}
                case 1n+u:
                  shift_operation(Q.Evaluation{S.Prefix{w, ts}}, Q.Operation{e, w, o, D.operate(e, w, o)},
                    generate(j, N.step_machine(S.apply(D.operate(e, w, o), w, o, k), ts), e), u, q, e,
                    all_operations_generated_are_real(j, N.step_machine(S.apply(D.operate(e, w, o), w, o, k), ts), e, u, q, present))

# Number of real steps at an evaluation position (terminal may occupy an odd position).
def steps(t: Nat) -> Nat:
  match t:
    case 0n: 0n
    case 1n: 1n
    case 2n+j: 1n+steps(j)

def value_evaluation(q: Q.FrameExec) -> Maybe<&2, S.Trace>:
  match q:
    case Q.Evaluation{p}: Some{p}
    case Q.Operation{e, s, o, r}: None{}

def aval_injective(+a: S.Trace, -b: S.Trace,
  equal: {Some{Q.Evaluation{a}} == Some{Q.Evaluation{b}} : Maybe<&2, Q.FrameExec>}) -> {a == b : S.Trace}:
  F.some_injective(S.Trace, a, b,
    Equal.cong(Q.FrameExec, Maybe<&2, S.Trace>, value_evaluation,
      Q.Evaluation{a}, Q.Evaluation{b}, F.some_injective(Q.FrameExec, Q.Evaluation{a}, Q.Evaluation{b}, equal)))

def negative_and_evaluation(e: D.Schema, s: D.State, o: D.Operation, r: D.ResultOp, -p: S.Trace,
  equal: {Some{Q.Operation{e, s, o, r}} == Some{Q.Evaluation{p}} : Maybe<&2, Q.FrameExec>}) -> Empty:
  F.none_negative_some(S.Trace, p,
    Equal.cong(Q.FrameExec, Maybe<&2, S.Trace>, value_evaluation,
      Q.Operation{e, s, o, r}, Q.Evaluation{p}, F.some_injective(Q.FrameExec, Q.Operation{e, s, o, r}, Q.Evaluation{p}, equal)))

law evaluations_real:
  for n: Nat
  for m: N.Machine
  for +e: D.Schema
  for t: Nat
  for -p: S.Trace
  for present: {query(generate(n, m, e), t) == Some{Q.Evaluation{p}} : Maybe<&2, Q.FrameExec>}
  {N.traverse(steps(t), m, e) == p : S.Trace}
def evaluations_real(n, m, e, t, p, present):
  match n m:
    case _ N.Stopped{w, ts, r}:
      match t:
        case 0n: aval_injective(S.Final{w, ts, r}, p, present)
        case 1n+j:
          L.ex_false({N.traverse(steps(1n+j), N.Stopped{w, ts, r}, e) == p : S.Trace}, F.none_negative_some(Q.FrameExec, Q.Evaluation{p}, present))
    case 0n N.Running{w, a, ts}:
      match t:
        case 0n: aval_injective(S.Prefix{w, ts}, p, present)
        case 1n+j:
          L.ex_false({N.traverse(steps(1n+j), N.Running{w, a, ts}, e) == p : S.Trace}, F.none_negative_some(Q.FrameExec, Q.Evaluation{p}, present))
    case 1n+j N.Running{+w, a, +ts}:
      match a:
        case S.Finish{v}:
          match t:
            case 0n: aval_injective(S.Prefix{w, ts}, p, present)
            case 1n+k:
              match k:
                case 0n: aval_injective(S.Final{w, ts, S.Response{S.Success{}, v}}, p, present)
                case 1n+i:
                  L.ex_false({N.traverse(steps(Succ{Succ{i}}), N.Running{w, S.Finish{v}, ts}, e) == p : S.Trace}, F.none_negative_some(Q.FrameExec, Q.Evaluation{p}, present))
        case S.Refuse{v}:
          match t:
            case 0n: aval_injective(S.Prefix{w, ts}, p, present)
            case 1n+k:
              match k:
                case 0n: aval_injective(S.Final{w, ts, S.Response{S.Refusal{}, v}}, p, present)
                case 1n+i:
                  L.ex_false({N.traverse(steps(Succ{Succ{i}}), N.Running{w, S.Refuse{v}, ts}, e) == p : S.Trace}, F.none_negative_some(Q.FrameExec, Q.Evaluation{p}, present))
        case S.Access{+o, k}:
          match t:
            case 0n: aval_injective(S.Prefix{w, ts}, p, present)
            case 1n+i:
              match i:
                case 0n:
                  L.ex_false({N.traverse(1n, N.Running{w, S.Access{o, k}, ts}, e) == p : S.Trace}, negative_and_evaluation(e, w, o, D.operate(e, w, o), p, present))
                case 1n+u:
                  evaluations_real(j, N.step_machine(S.apply(D.operate(e, w, o), w, o, k), ts), e, u, p, present)

law steps_preserves_order:
  for u: Nat
  for v: Nat
  for order: {Nat.is_lt(u, v) == True{} : Bool}
  {Nat.is_le(steps(u), steps(v)) == True{} : Bool}
def steps_preserves_order(u, v, order):
  match u v:
    case 0n _: Arithmetic.zero_negative_greater(steps(v))
    case 1n 0n: F.absurd_boolean({Nat.is_le(1n, 0n) == True{} : Bool}, order)
    case 1n 1n: F.absurd_boolean({Nat.is_le(1n, 1n) == True{} : Bool}, order)
    case 1n 2n+j: Arithmetic.zero_negative_greater(steps(j))
    case 2n+i 0n: F.absurd_boolean({Nat.is_le(steps(2n+i), 0n) == True{} : Bool}, order)
    case 2n+i 1n: F.absurd_boolean({Nat.is_le(steps(2n+i), 1n) == True{} : Bool}, order)
    case 2n+i 2n+j: steps_preserves_order(i, j, order)

# The actual path uses the same indices; order does not depend on selecting different traces.
law prefixes_of_evaluations_in_order:
  for +u: Nat
  for +v: Nat
  for m: N.Machine
  for +e: D.Schema
  for -before: S.Trace
  for -later: S.Trace
  for order: {Nat.is_lt(u, v) == True{} : Bool}
  for first: {N.traverse(steps(u), m, e) == before : S.Trace}
  for second: {N.traverse(steps(v), m, e) == later : S.Trace}
  L.Prefix(S.OperationEvent, S.events_execution_trace(before), S.events_execution_trace(later))
def prefixes_of_evaluations_in_order(u, v, m, e, before, later, order, first, second):
  %second : L.Prefix(S.OperationEvent, S.events_execution_trace(before), S.events_execution_trace(_))
  %first : L.Prefix(S.OperationEvent, S.events_execution_trace(_), S.events_execution_trace(N.traverse(steps(v), m, e)))
  %Numbers.nat_decompose_limit(steps(u), steps(v), steps_preserves_order(u, v, order)) :
    L.Prefix(S.OperationEvent, S.events_execution_trace(N.traverse(steps(u), m, e)),
      S.events_execution_trace(N.traverse(_, m, e)))
  M.prefixes_of_machine_in_order(steps(u), Nat.sub(steps(v), steps(u)), m, e)

def TerminatesInFirst(xs: List<&2, Q.FrameExec>) -> Type:
  match xs:
    case Nil{}: Unit
    case Con{Q.Evaluation{S.Final{w, ts, r}}, t}: {t == Nil{} : List<&2, Q.FrameExec>}
    case Con{Q.Evaluation{S.Prefix{w, ts}}, t}: TerminatesInFirst(t)
    case Con{Q.Operation{e, s, o, r}, t}: TerminatesInFirst(t)

law generator_for_in_first_final:
  for n: Nat
  for m: N.Machine
  for +e: D.Schema
  TerminatesInFirst(generate(n, m, e))
def generator_for_in_first_final(n, m, e):
  match n m:
    case _ N.Stopped{w, ts, r}: {==}
    case 0n N.Running{w, a, ts}: Unit{}
    case 1n+j N.Running{+w, a, +ts}:
      match a:
        case S.Finish{v}: {==}
        case S.Refuse{v}: {==}
        case S.Access{+o, k}:
          generator_for_in_first_final(j, N.step_machine(S.apply(D.operate(e, w, o), w, o, k), ts), e)

def is_final(p: S.Trace) -> Bool:
  match p:
    case S.Prefix{w, ts}: False{}
    case S.Final{w, ts, r}: True{}

def prefix_negative_final(+w: D.State, +ts: List<&2, S.OperationEvent>, -fw: D.State,
  -fts: List<&2, S.OperationEvent>, -fr: S.Response,
  present: {Some{Q.Evaluation{S.Prefix{w, ts}}} == Some{Q.Evaluation{S.Final{fw, fts, fr}}} : Maybe<&2, Q.FrameExec>}) -> Empty:
  F.false_negative_true(Equal.cong(S.Trace, Bool,
    is_final,
    S.Prefix{w, ts}, S.Final{fw, fts, fr}, aval_injective(S.Prefix{w, ts}, S.Final{fw, fts, fr}, present)))

law final_prevents_query_subsequent:
  for xs: List<&2, Q.FrameExec>
  for u: Nat
  for v: Nat
  for -fw: D.State
  for -fts: List<&2, S.OperationEvent>
  for -fr: S.Response
  for -q: Q.FrameExec
  for order: {Nat.is_lt(u, v) == True{} : Bool}
  for final: {query(xs, u) == Some{Q.Evaluation{S.Final{fw, fts, fr}}} : Maybe<&2, Q.FrameExec>}
  for later: {query(xs, v) == Some{q} : Maybe<&2, Q.FrameExec>}
  for terminates: TerminatesInFirst(xs)
  Empty
def final_prevents_query_subsequent(xs, u, v, fw, fts, fr, q, order, final, later, terminates):
  match xs:
    case Nil{}: F.none_negative_some(Q.FrameExec, Q.Evaluation{S.Final{fw, fts, fr}}, final)
    case Con{Q.Evaluation{S.Final{w, ts, r}}, t}:
      match u:
        case 0n:
          match v:
            case 0n: F.false_negative_true(order)
            case 1n+j:
              F.none_negative_some(Q.FrameExec, q,
                (%terminates : {query(_, j) == Some{q} : Maybe<&2, Q.FrameExec>} later))
        case 1n+i:
          F.none_negative_some(Q.FrameExec, Q.Evaluation{S.Final{fw, fts, fr}},
            (%terminates : {query(_, i) == Some{Q.Evaluation{S.Final{fw, fts, fr}}} : Maybe<&2, Q.FrameExec>} final))
    case Con{Q.Evaluation{S.Prefix{+w, +ts}}, t}:
      match u:
        case 0n: prefix_negative_final(w, ts, fw, fts, fr, final)
        case 1n+i:
          match v:
            case 0n: F.false_negative_true(order)
            case 1n+j: final_prevents_query_subsequent(t, i, j, fw, fts, fr, q, order, final, later, terminates)
    case Con{Q.Operation{e, s, o, r}, t}:
      match u:
        case 0n: negative_and_evaluation(e, s, o, r, S.Final{fw, fts, fr}, final)
        case 1n+i:
          match v:
            case 0n: F.false_negative_true(order)
            case 1n+j: final_prevents_query_subsequent(t, i, j, fw, fts, fr, q, order, final, later, terminates)

def last(xs: List<&2, Q.FrameExec>) -> Maybe<&2, Q.FrameExec>:
  match xs:
    case Nil{}: None{}
    case Con{h, Nil{}}: Some{h}
    case Con{h, Con{j, t}}: last(Con{j, t})

law last_two_prefixes:
  for -a: Q.FrameExec
  for -b: Q.FrameExec
  for -seq: Sequence
  {last(Con{a, Con{b, expand(seq)}}) == last(expand(seq)) : Maybe<&2, Q.FrameExec>}
def last_two_prefixes(a, b, seq):
  {==}

law last_represents_all_execution_trace:
  for +n: Nat
  for m: N.Machine
  for +e: D.Schema
  {last(generate(n, m, e)) == Some{Q.Evaluation{N.traverse(n, m, e)}} : Maybe<&2, Q.FrameExec>}
def last_represents_all_execution_trace(n, m, e):
  match n m:
    case _ N.Stopped{+w, +ts, +r}:
      %Equal.sym(S.Trace, N.traverse(n, N.Stopped{w, ts, r}, e), S.Final{w, ts, r},
        N.stopped_absorbs(n, w, ts, r, e)) :
          {last(generate(n, N.Stopped{w, ts, r}, e)) == Some{Q.Evaluation{_}} : Maybe<&2, Q.FrameExec>}
      {==}
    case 0n N.Running{w, a, ts}: {==}
    case 1n+j N.Running{+w, a, +ts}:
      match a:
        case S.Finish{+v}:
          %Equal.sym(S.Trace, N.traverse(j, N.Stopped{w, ts, S.Response{S.Success{}, v}}, e), S.Final{w, ts, S.Response{S.Success{}, v}},
            N.stopped_absorbs(j, w, ts, S.Response{S.Success{}, v}, e)) :
              {last(generate(1n+j, N.Running{w, S.Finish{v}, ts}, e)) == Some{Q.Evaluation{_}} : Maybe<&2, Q.FrameExec>}
          {==}
        case S.Refuse{+v}:
          %Equal.sym(S.Trace, N.traverse(j, N.Stopped{w, ts, S.Response{S.Refusal{}, v}}, e), S.Final{w, ts, S.Response{S.Refusal{}, v}},
            N.stopped_absorbs(j, w, ts, S.Response{S.Refusal{}, v}, e)) :
              {last(generate(1n+j, N.Running{w, S.Refuse{v}, ts}, e)) == Some{Q.Evaluation{_}} : Maybe<&2, Q.FrameExec>}
          {==}
        case S.Access{+o, k}:
          Equal.trans(Maybe<&2, Q.FrameExec>,
            last(generate(1n+j, N.Running{w, S.Access{o, k}, ts}, e)),
            last(generate(j, N.step_machine(S.apply(D.operate(e, w, o), w, o, k), ts), e)),
            Some{Q.Evaluation{N.traverse(j, N.step_machine(S.apply(D.operate(e, w, o), w, o, k), ts), e)}},
            last_two_prefixes(Q.Evaluation{S.Prefix{w, ts}}, Q.Operation{e, w, o, D.operate(e, w, o)},
              generate_sequence(j, N.step_machine(S.apply(D.operate(e, w, o), w, o, k), ts), e)),
            last_represents_all_execution_trace(j, N.step_machine(S.apply(D.operate(e, w, o), w, o, k), ts), e))

def lift_index(-h: Q.FrameExec, -t: List<&2, Q.FrameExec>, -q: Q.FrameExec,
  result: &n: Nat -> {query(t, n) == Some{q} : Maybe<&2, Q.FrameExec>}) ->
  &n: Nat -> {query(Con{h, t}, n) == Some{q} : Maybe<&2, Q.FrameExec>}:
  match result:
    case (n, equal): (1n+n, equal)

law last_present_has_index:
  for xs: List<&2, Q.FrameExec>
  for -q: Q.FrameExec
  for present: {last(xs) == Some{q} : Maybe<&2, Q.FrameExec>}
  exs n: Nat
  {query(xs, n) == Some{q} : Maybe<&2, Q.FrameExec>}
def last_present_has_index(xs, q, present):
  match xs:
    case Nil{}:
      L.ex_false((&n: Nat -> {query(Nil{}, n) == Some{q} : Maybe<&2, Q.FrameExec>}), F.none_negative_some(Q.FrameExec, q, present))
    case Con{h, Nil{}}: (0n, present)
    case Con{h, Con{j, t}}:
      lift_index(h, Con{j, t}, q, last_present_has_index(Con{j, t}, q, present))

def expand_frame(r: P.Request, ctx: D.Context, q: Q.FrameExec) -> Q.Frame:
  match q:
    case Q.Evaluation{p}: Q.Evaluated{r, ctx, p}
    case Q.Operation{e, s, o, result}: Q.Operated{e, s, o, result}

def Reflection(-r: P.Request, -ctx: D.Context, -local: Maybe<&2, Q.FrameExec>, q: Q.Frame) -> Type:
  match q:
    case Q.Evaluated{r2, ctx2, p}:
      L.E<{r2 == r : P.Request}, L.E<{ctx2 == ctx : D.Context},
        {local == Some{Q.Evaluation{p}} : Maybe<&2, Q.FrameExec>}>>
    case Q.Operated{e, s, o, result}:
      {local == Some{Q.Operation{e, s, o, result}} : Maybe<&2, Q.FrameExec>}
    case _: Empty

law expand_reflects_query:
  for +r: P.Request
  for +ctx: D.Context
  for xs: List<&2, Q.FrameExec>
  for t: Nat
  for -q: Q.Frame
  for present: {Q.query(Q.expand_exec(r, ctx, xs), t) == Some{q} : Maybe<&2, Q.Frame>}
  Reflection(r, ctx, query(xs, t), q)
def expand_reflects_query(r, ctx, xs, t, q, present):
  match xs t:
    case Nil{} _:
      L.ex_false(Reflection(r, ctx, query(Nil{}, t), q), F.none_negative_some(Q.Frame, q, present))
    case Con{Q.Evaluation{+p}, rest} 0n:
      %F.some_injective(Q.Frame, Q.Evaluated{r, ctx, p}, q, present) :
        Reflection(r, ctx, query(Con{Q.Evaluation{p}, rest}, 0n), _)
      L.Both{{==}, L.Both{{==}, {==}}}
    case Con{Q.Operation{+e, +s, +o, +result}, rest} 0n:
      %F.some_injective(Q.Frame, Q.Operated{e, s, o, result}, q, present) :
        Reflection(r, ctx, query(Con{Q.Operation{e, s, o, result}, rest}, 0n), _)
      {==}
    case Con{Q.Evaluation{p}, rest} 1n+j:
      expand_reflects_query(r, ctx, rest, j, q, present)
    case Con{Q.Operation{e, s, o, result}, rest} 1n+j:
      expand_reflects_query(r, ctx, rest, j, q, present)

law expand_preserves_query:
  for +r: P.Request
  for +ctx: D.Context
  for xs: List<&2, Q.FrameExec>
  for t: Nat
  for -q: Q.FrameExec
  for present: {query(xs, t) == Some{q} : Maybe<&2, Q.FrameExec>}
  {Q.query(Q.expand_exec(r, ctx, xs), t) == Some{expand_frame(r, ctx, q)} : Maybe<&2, Q.Frame>}
def expand_preserves_query(r, ctx, xs, t, q, present):
  match xs t:
    case Nil{} _:
      L.ex_false({Q.query(Q.expand_exec(r, ctx, Nil{}), t) == Some{expand_frame(r, ctx, q)} : Maybe<&2, Q.Frame>},
        F.none_negative_some(Q.FrameExec, q, present))
    case Con{Q.Evaluation{+p}, rest} 0n:
      Equal.cong(Q.FrameExec, Maybe<&2, Q.Frame>, h => Some{expand_frame(r, ctx, h)},
        Q.Evaluation{p}, q, F.some_injective(Q.FrameExec, Q.Evaluation{p}, q, present))
    case Con{Q.Operation{+e, +s, +o, +result}, rest} 0n:
      Equal.cong(Q.FrameExec, Maybe<&2, Q.Frame>, h => Some{expand_frame(r, ctx, h)},
        Q.Operation{e, s, o, result}, q, F.some_injective(Q.FrameExec, Q.Operation{e, s, o, result}, q, present))
    case Con{Q.Evaluation{p}, rest} 1n+j:
      expand_preserves_query(r, ctx, rest, j, q, present)
    case Con{Q.Operation{e, s, o, result}, rest} 1n+j:
      expand_preserves_query(r, ctx, rest, j, q, present)

# The producer is static and closed: reconstructs the same root without copying a Type object.
law evaluation_exact_of_program:
  for ~program: Nat -> S.Program
  for +world: Nat
  for -c: S.Configuration
  for +e: D.Schema
  for +s: D.State
  for +r: P.Request
  for +ctx: D.Context
  for +n: Nat
  for +t: Nat
  for -execution_trace: S.Trace
  for schema: {e == S.schema(c) : D.Schema}
  for present: {query(generate(n, N.start(program(world), ctx, I.arguments(r), s), e), t) == Some{Q.Evaluation{execution_trace}} : Maybe<&2, Q.FrameExec>}
  I.ExecutionCorrect(c, s, r, ctx, program(world), execution_trace)
def evaluation_exact_of_program(program, world, c, e, s, r, ctx, n, t, execution_trace, schema, present):
  (steps(t),
    (%schema : {execution_trace == S.execute(steps(t), program(world), _, s, ctx, I.arguments(r)) : S.Trace}
      Equal.trans(S.Trace, execution_trace,
        N.traverse(steps(t), N.start(program(world), ctx, I.arguments(r), s), e),
        S.execute(steps(t), program(world), e, s, ctx, I.arguments(r)),
        Equal.sym(S.Trace,
          N.traverse(steps(t), N.start(program(world), ctx, I.arguments(r), s), e), execution_trace,
          evaluations_real(n, N.start(program(world), ctx, I.arguments(r), s), e, t, execution_trace, present)),
        N.fidelity_of_all_os_prefixes(steps(t), program(world), ctx, I.arguments(r), e, s))))

# Equality concerns the entire family: one refinement contract, not eight laws.
def observation_real(a: I.Environment, k: String, x: I.Scenario) -> Nat -> I.Fact -> Type:
  t => f => I.Happens(a, k, x, t, f)

def observation_model(-c: S.Configuration, -p: S.Program,
  +initial: Maybe<&2, D.State>, +xs: List<&2, Q.Frame>) -> Nat -> I.Fact -> Type:
  t => f => Q.observes_service(c, p, initial, xs, t, f)

# The same Links binding, parameterized by observation to permit J.
def Linkage(-ob: Nat -> I.Fact -> Type, -x: I.Scenario, -t: Nat,
  -e: D.Schema, -s: D.State, -o: D.Operation, -result: D.ResultOp) -> Type:
  &req: P.Request -> &ctx: D.Context -> &program: S.Program ->
    &ts: List<&2, S.OperationEvent> -> &before: Nat -> &later: Nat -> &after: S.Trace ->
      L.E<{e == S.schema(I.configuration(x)) : D.Schema},
        L.E<V.ObservationWindow(before, t, later),
          L.E<ob(before, I.Evaluated{req, ctx, program, S.Prefix{s, ts}}),
            L.E<ob(later, I.Evaluated{req, ctx, program, after}),
              L.E<V.AfterOperation(result, s, o, ts, after),
                @u: Nat -> @e2: D.Schema -> @s2: D.State -> @o2: D.Operation -> @r2: D.ResultOp ->
                  {Nat.is_lt(before, u) == True{} : Bool} -> {Nat.is_lt(u, later) == True{} : Bool} ->
                  ob(u, I.Operated{e2, s2, o2, r2}) ->
                    L.E<{u == t : Nat}, {I.Operated{e2, s2, o2, r2} == I.Operated{e, s, o, result} : I.Fact}>>>>>>

def unique_of_query(-c: S.Configuration, -p: S.Program,
  +xs: List<&2, Q.Frame>, +b: Nat, +e: D.Schema, +s: D.State, +o: D.Operation,
  known: {Q.query(xs, Succ{b}) == Some{Q.Operated{e, s, o, D.operate(e, s, o)}} : Maybe<&2, Q.Frame>},
  +u: Nat, -e2: D.Schema, -s2: D.State, -o2: D.Operation, -r2: D.ResultOp,
  left: {Nat.is_lt(b, u) == True{} : Bool}, right: {Nat.is_lt(u, Succ{Succ{b}}) == True{} : Bool},
  observed: Q.observes(c, p, xs, u, I.Operated{e2, s2, o2, r2})) ->
  L.E<{u == Succ{b} : Nat}, {I.Operated{e2, s2, o2, r2} == I.Operated{e, s, o, D.operate(e, s, o)} : I.Fact}>:
  F.combined_pair(
    L.E<{u == Succ{b} : Nat}, {I.Operated{e2, s2, o2, r2} == I.Operated{e, s, o, D.operate(e, s, o)} : I.Fact}>,
    {u == Succ{b} : Nat}, {u == Succ{b} : Nat},
    Call.duplicate_equality(Nat, u, Succ{b}, unique_between_two_successors(b, u, left, right)),
    stored => position => L.Both{stored,
      Q.observation_unique(c, p, xs, Succ{b}, I.Operated{e2, s2, o2, r2}, I.Operated{e, s, o, D.operate(e, s, o)},
        (%position : Q.observes(c, p, xs, _, I.Operated{e2, s2, o2, r2}) observed),
        Q.query_establishes_observation(c, p, xs, Succ{b}, Q.Operated{e, s, o, D.operate(e, s, o)},
          I.Operated{e, s, o, D.operate(e, s, o)}, known, {==}))})

def bind_queries(~program: Nat -> S.Program, +world: Nat, -x: I.Scenario, -c: S.Configuration,
  +initial: Maybe<&2, D.State>, +xs: List<&2, Q.Frame>, +r: P.Request, +ctx: D.Context,
  +e: D.Schema, +s: D.State, +o: D.Operation, +ts: List<&2, S.OperationEvent>, +b: Nat,
  schema: {e == S.schema(I.configuration(x)) : D.Schema},
  before: {Q.query(xs, b) == Some{Q.Evaluated{r, ctx, S.Prefix{s, ts}}} : Maybe<&2, Q.Frame>},
  operation: {Q.query(xs, Succ{b}) == Some{Q.Operated{e, s, o, D.operate(e, s, o)}} : Maybe<&2, Q.Frame>},
  later: {Q.query(xs, Succ{Succ{b}}) == Some{Q.Evaluated{r, ctx, after(D.operate(e, s, o), s, o, ts)}} : Maybe<&2, Q.Frame>}) ->
  Linkage(observation_model(c, program(world), initial, xs), x, Succ{b}, e, s, o, D.operate(e, s, o)):
  (r, ctx, program(world), ts, b, Succ{Succ{b}}, after(D.operate(e, s, o), s, o, ts),
    L.Both{schema, L.Both{L.Both{less_successor(b), less_successor(Succ{b})},
      L.Both{Q.query_establishes_observation(c, program(world), xs, b, Q.Evaluated{r, ctx, S.Prefix{s, ts}},
          I.Evaluated{r, ctx, program(world), S.Prefix{s, ts}}, before, {==}),
        L.Both{Q.query_establishes_observation(c, program(world), xs, Succ{Succ{b}},
            Q.Evaluated{r, ctx, after(D.operate(e, s, o), s, o, ts)}, I.Evaluated{r, ctx, program(world), after(D.operate(e, s, o), s, o, ts)}, later, {==}),
          L.Both{after_satisfies_binding(D.operate(e, s, o), s, o, ts),
            u => e2 => s2 => o2 => r2 => left => right => fact =>
              unique_of_query(c, program(world), xs, b, e, s, o, operation, u, e2, s2, o2, r2, left, right, fact)}}}}})

law operation_bound_in_observation_real:
  for ~program: Nat -> S.Program
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
  for schema: {e == S.schema(I.configuration(x)) : D.Schema}
  for before: {Q.query(xs, b) == Some{Q.Evaluated{r, ctx, S.Prefix{s, ts}}} : Maybe<&2, Q.Frame>}
  for operation: {Q.query(xs, Succ{b}) == Some{Q.Operated{e, s, o, D.operate(e, s, o)}} : Maybe<&2, Q.Frame>}
  for later: {Q.query(xs, Succ{Succ{b}}) == Some{Q.Evaluated{r, ctx, after(D.operate(e, s, o), s, o, ts)}} : Maybe<&2, Q.Frame>}
  for refinement: {observation_real(a, k, x) == observation_model(c, program(world), initial, xs) : Nat -> I.Fact -> Type}
  V.OperationBound(a, k, x, Succ{b}, e, s, o, D.operate(e, s, o))
def operation_bound_in_observation_real(program, world, a, k, x, c, initial, xs, r, ctx, e, s, o, ts, b,
  schema, before, operation, later, refinement):
  %Equal.sym((Nat -> I.Fact -> Type), observation_real(a, k, x),
    observation_model(c, program(world), initial, xs), refinement) : Linkage(_, x, Succ{b}, e, s, o, D.operate(e, s, o))
  bind_queries(program, world, x, c, initial, xs, r, ctx, e, s, o, ts, b, schema, before, operation, later)
