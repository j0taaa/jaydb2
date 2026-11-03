# First-child cut: segmentation follows from ACTUAL execution.
# The local machine preserves guards and is linked step by step to src/Codec.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecTrace.bend as R
import ./CodecAcceptanceStack.bend as J

def advance_local(q: R.Frame, outside: C.Stack, b: U32) -> R.Frame:
  R.Frame{body, ceiling, m} = q
  +rest = C.decrease64(body)
  +free = C.decrease64(ceiling)
  R.Frame{rest, free, J.step_local(m, outside, b, rest, free)}

def execute_local(bs: List<&2, U32>, +outside: C.Stack, q: R.Frame) -> R.Frame:
  match bs:
    case Nil{}:
      q
    case Con{b, t}:
      execute_local(t, outside, advance_local(q, outside, b))

def and_ready(m: C.Machine) -> Bool:
  match m:
    case C.DecodedReady{v}:
      True{}
    case _:
      False{}

def negative_emitted_negative_is_here_ready(+m: C.Machine, +outside: C.Stack, -v: D.Value,
  continues: J.Continue(m), equal: {J.link(m, outside) == C.DecodedReady{v} : C.Machine}) -> Empty:
  match m:
    case C.DecodedReady{w}:
      continues
    case C.Tag{p}:
      F.false_negative_true(Equal.cong(C.Machine, Bool, x => and_ready(x), J.link(m, outside), C.DecodedReady{v}, equal))
    case C.TagName{p}:
      F.false_negative_true(Equal.cong(C.Machine, Bool, x => and_ready(x), J.link(m, outside), C.DecodedReady{v}, equal))
    case C.WordInput{f, n, a, b, p}:
      F.false_negative_true(Equal.cong(C.Machine, Bool, x => and_ready(x), J.link(m, outside), C.DecodedReady{v}, equal))
    case C.Content{name, u, q, cp, s, p}:
      F.false_negative_true(Equal.cong(C.Machine, Bool, x => and_ready(x), J.link(m, outside), C.DecodedReady{v}, equal))
    case C.Invalid{}:
      F.false_negative_true(Equal.cong(C.Machine, Bool, x => and_ready(x), C.Invalid{}, C.DecodedReady{v}, equal))
    case C.Above{}:
      F.false_negative_true(Equal.cong(C.Machine, Bool, x => and_ready(x), C.Above{}, C.DecodedReady{v}, equal))

type Cut<-bs: List<&2, U32>, -body: B.Number64, -ceiling: B.Number64,
  -m: C.Machine, -outside: C.Stack, -v: D.Value> is Type:
  Cut{prefix: List<&2, U32>, suffix: List<&2, U32>, child: D.Value,
    body_final: B.Number64, ceiling_final: B.Number64,
    bytes: {bs == B.concatenate(prefix, suffix) : List<&2, U32>},
    local: {execute_local(prefix, outside, R.Frame{body, ceiling, m}) ==
      R.Frame{body_final, ceiling_final, C.DecodedReady{child}} : R.Frame},
    real: {R.execute(prefix, R.Frame{body, ceiling, J.link(m, outside)}) ==
      R.Frame{body_final, ceiling_final, C.emit(outside, child)} : R.Frame},
    remaining: {R.machine(R.execute(suffix, R.Frame{body_final, ceiling_final, C.emit(outside, child)})) == C.DecodedReady{v} : C.Machine}}

def advance_linked(+m: C.Machine, +outside: C.Stack, +b: U32, +body: B.Number64, +ceiling: B.Number64,
  internal: J.Internal(m), continues: J.Continue(m)) ->
  {R.advance(R.Frame{body, ceiling, J.link(m, outside)}, b) ==
    R.Frame{C.decrease64(body), C.decrease64(ceiling), J.link(J.step_local(m, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside)} : R.Frame}:
  Equal.cong(C.Machine, R.Frame, x => R.Frame{C.decrease64(body), C.decrease64(ceiling), x},
    C.step(J.link(m, outside), b, C.decrease64(body), C.decrease64(ceiling)),
    J.link(J.step_local(m, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside),
    Equal.sym(C.Machine,
      J.link(J.step_local(m, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside),
      C.step(J.link(m, outside), b, C.decrease64(body), C.decrease64(ceiling)),
      J.step_local_linked_and_o_step_real(m, outside, b, C.decrease64(body), C.decrease64(ceiling), internal, continues)))

def advance_acceptance(+b: U32, +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64,
  +m: C.Machine, +outside: C.Stack, -v: D.Value,
  advance: {R.advance(R.Frame{body, ceiling, J.link(m, outside)}, b) ==
    R.Frame{C.decrease64(body), C.decrease64(ceiling), J.link(J.step_local(m, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside)} : R.Frame},
  accepted: {R.machine(R.execute(Con{b, bs}, R.Frame{body, ceiling, J.link(m, outside)})) == C.DecodedReady{v} : C.Machine}) ->
  {R.machine(R.execute(bs, R.Frame{C.decrease64(body), C.decrease64(ceiling), J.link(J.step_local(m, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside)})) == C.DecodedReady{v} : C.Machine}:
  %advance : {R.machine(R.execute(bs, _)) == C.DecodedReady{v} : C.Machine}
  accepted

def raise_cut(+b: U32, +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64,
  +m: C.Machine, +outside: C.Stack, -v: D.Value,
  +advance: {R.advance(R.Frame{body, ceiling, J.link(m, outside)}, b) ==
    R.Frame{C.decrease64(body), C.decrease64(ceiling), J.link(J.step_local(m, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside)} : R.Frame},
  cut: Cut<bs, C.decrease64(body), C.decrease64(ceiling), J.step_local(m, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside, v>) ->
  Cut<Con{b, bs}, body, ceiling, m, outside, v>:
  match cut:
    case Cut{+pre, +suf, +child, +cf, +tf, bytes, local, real, remaining}:
      Cut{Con{b, pre}, suf, child, cf, tf,
        Equal.cong(List<&2, U32>, List<&2, U32>, t => Con{b, t}, bs, B.concatenate(pre, suf), bytes), local,
        (%Equal.sym(R.Frame, R.advance(R.Frame{body, ceiling, J.link(m, outside)}, b),
          R.Frame{C.decrease64(body), C.decrease64(ceiling), J.link(J.step_local(m, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside)}, advance) :
          {R.execute(pre, _) == R.Frame{cf, tf, C.emit(outside, child)} : R.Frame}
          real), remaining}

def cut_immediate(+bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64,
  +child: D.Value, +outside: C.Stack, -v: D.Value,
  accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling, C.emit(outside, child)})) == C.DecodedReady{v} : C.Machine}) ->
  Cut<bs, body, ceiling, C.DecodedReady{child}, outside, v>:
  Cut{Nil{}, bs, child, body, ceiling, {==}, {==}, {==}, accepted}

def cut_empty(+body: B.Number64, +ceiling: B.Number64, +m: C.Machine, +outside: C.Stack, -v: D.Value,
  continues: J.Continue(m), accepted: {J.link(m, outside) == C.DecodedReady{v} : C.Machine}) -> Cut<Nil{}, body, ceiling, m, outside, v>:
  L.ex_false(Cut<Nil{}, body, ceiling, m, outside, v>, negative_emitted_negative_is_here_ready(m, outside, v, continues, accepted))

def prove_advance(+m: C.Machine, +outside: C.Stack, +b: U32, +body: B.Number64, +ceiling: B.Number64,
  internal: J.Internal(m), continues: J.Continue(m)) ->
  L.E<J.Internal(J.step_local(m, outside, b, C.decrease64(body), C.decrease64(ceiling))),
    {R.advance(R.Frame{body, ceiling, J.link(m, outside)}, b) ==
      R.Frame{C.decrease64(body), C.decrease64(ceiling), J.link(J.step_local(m, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside)} : R.Frame}>:
  F.combined_pair(L.E<J.Internal(J.step_local(m, outside, b, C.decrease64(body), C.decrease64(ceiling))),
      {R.advance(R.Frame{body, ceiling, J.link(m, outside)}, b) ==
        R.Frame{C.decrease64(body), C.decrease64(ceiling), J.link(J.step_local(m, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside)} : R.Frame}>,
    J.Internal(m), J.Internal(m), J.duplicate_internal(m, internal),
    first => second => L.Both{
      J.step_local_preserves_interior(m, outside, b, C.decrease64(body), C.decrease64(ceiling), first),
      advance_linked(m, outside, b, body, ceiling, second, continues)})

law execution_real_accepts_extracts_to_first_emission:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +m: C.Machine
  for +outside: C.Stack
  for -v: D.Value
  for internal: J.Internal(m)
  for accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling, J.link(m, outside)})) == C.DecodedReady{v} : C.Machine}
  Cut<bs, body, ceiling, m, outside, v>
def execution_real_accepts_extracts_to_first_emission(bs, body, ceiling, m, outside, v, internal, accepted):
  match bs m:
    case _ C.DecodedReady{+child}:
      cut_immediate(bs, body, ceiling, child, outside, v, accepted)
    case Nil{} C.Tag{+p}:
      cut_empty(body, ceiling, C.Tag{p}, outside, v, Unit{}, accepted)
    case Nil{} C.TagName{+p}:
      cut_empty(body, ceiling, C.TagName{p}, outside, v, Unit{}, accepted)
    case Nil{} C.WordInput{+f, +n, +a, +b, +p}:
      cut_empty(body, ceiling, C.WordInput{f, n, a, b, p}, outside, v, Unit{}, accepted)
    case Nil{} C.Content{+name, +u, +q, +cp, +s, +p}:
      cut_empty(body, ceiling, C.Content{name, u, q, cp, s, p}, outside, v, Unit{}, accepted)
    case Nil{} C.Invalid{}:
      cut_empty(body, ceiling, C.Invalid{}, outside, v, Unit{}, accepted)
    case Nil{} C.Above{}:
      cut_empty(body, ceiling, C.Above{}, outside, v, Unit{}, accepted)
    case Con{+b, +t} C.Tag{+p}:
      +state = {C.Tag{p} : C.Machine}
      F.combined_pair(Cut<Con{b, t}, body, ceiling, state, outside, v>,
        J.Internal(J.step_local(state, outside, b, C.decrease64(body), C.decrease64(ceiling))),
        {R.advance(R.Frame{body, ceiling, J.link(state, outside)}, b) ==
          R.Frame{C.decrease64(body), C.decrease64(ceiling), J.link(J.step_local(state, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside)} : R.Frame},
        prove_advance(state, outside, b, body, ceiling, internal, Unit{}),
        next => fact =>
          (+advance = fact
           raise_cut(b, t, body, ceiling, state, outside, v, advance,
             execution_real_accepts_extracts_to_first_emission(t, C.decrease64(body), C.decrease64(ceiling),
               J.step_local(state, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside, v, next,
               advance_acceptance(b, t, body, ceiling, state, outside, v, advance, accepted)))))
    case Con{+b, +t} C.TagName{+p}:
      +state = {C.TagName{p} : C.Machine}
      F.combined_pair(Cut<Con{b, t}, body, ceiling, state, outside, v>,
        J.Internal(J.step_local(state, outside, b, C.decrease64(body), C.decrease64(ceiling))),
        {R.advance(R.Frame{body, ceiling, J.link(state, outside)}, b) ==
          R.Frame{C.decrease64(body), C.decrease64(ceiling), J.link(J.step_local(state, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside)} : R.Frame},
        prove_advance(state, outside, b, body, ceiling, internal, Unit{}),
        next => fact =>
          (+advance = fact
           raise_cut(b, t, body, ceiling, state, outside, v, advance,
             execution_real_accepts_extracts_to_first_emission(t, C.decrease64(body), C.decrease64(ceiling),
               J.step_local(state, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside, v, next,
               advance_acceptance(b, t, body, ceiling, state, outside, v, advance, accepted)))))
    case Con{+b, +t} C.WordInput{+f, +n, +a, +c, +p}:
      +state = {C.WordInput{f, n, a, c, p} : C.Machine}
      F.combined_pair(Cut<Con{b, t}, body, ceiling, state, outside, v>,
        J.Internal(J.step_local(state, outside, b, C.decrease64(body), C.decrease64(ceiling))),
        {R.advance(R.Frame{body, ceiling, J.link(state, outside)}, b) ==
          R.Frame{C.decrease64(body), C.decrease64(ceiling), J.link(J.step_local(state, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside)} : R.Frame},
        prove_advance(state, outside, b, body, ceiling, internal, Unit{}),
        next => fact =>
          (+advance = fact
           raise_cut(b, t, body, ceiling, state, outside, v, advance,
             execution_real_accepts_extracts_to_first_emission(t, C.decrease64(body), C.decrease64(ceiling),
               J.step_local(state, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside, v, next,
               advance_acceptance(b, t, body, ceiling, state, outside, v, advance, accepted)))))
    case Con{+b, +t} C.Content{+name, +u, +q, +cp, +s, +p}:
      +state = {C.Content{name, u, q, cp, s, p} : C.Machine}
      F.combined_pair(Cut<Con{b, t}, body, ceiling, state, outside, v>,
        J.Internal(J.step_local(state, outside, b, C.decrease64(body), C.decrease64(ceiling))),
        {R.advance(R.Frame{body, ceiling, J.link(state, outside)}, b) ==
          R.Frame{C.decrease64(body), C.decrease64(ceiling), J.link(J.step_local(state, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside)} : R.Frame},
        prove_advance(state, outside, b, body, ceiling, internal, Unit{}),
        next => fact =>
          (+advance = fact
           raise_cut(b, t, body, ceiling, state, outside, v, advance,
             execution_real_accepts_extracts_to_first_emission(t, C.decrease64(body), C.decrease64(ceiling),
               J.step_local(state, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside, v, next,
               advance_acceptance(b, t, body, ceiling, state, outside, v, advance, accepted)))))
    case Con{+b, +t} C.Invalid{}:
      +state = {C.Invalid{} : C.Machine}
      F.combined_pair(Cut<Con{b, t}, body, ceiling, state, outside, v>,
        J.Internal(J.step_local(state, outside, b, C.decrease64(body), C.decrease64(ceiling))),
        {R.advance(R.Frame{body, ceiling, J.link(state, outside)}, b) ==
          R.Frame{C.decrease64(body), C.decrease64(ceiling), J.link(J.step_local(state, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside)} : R.Frame},
        prove_advance(state, outside, b, body, ceiling, internal, Unit{}),
        next => fact =>
          (+advance = fact
           raise_cut(b, t, body, ceiling, state, outside, v, advance,
             execution_real_accepts_extracts_to_first_emission(t, C.decrease64(body), C.decrease64(ceiling),
               J.step_local(state, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside, v, next,
               advance_acceptance(b, t, body, ceiling, state, outside, v, advance, accepted)))))
    case Con{+b, +t} C.Above{}:
      +state = {C.Above{} : C.Machine}
      F.combined_pair(Cut<Con{b, t}, body, ceiling, state, outside, v>,
        J.Internal(J.step_local(state, outside, b, C.decrease64(body), C.decrease64(ceiling))),
        {R.advance(R.Frame{body, ceiling, J.link(state, outside)}, b) ==
          R.Frame{C.decrease64(body), C.decrease64(ceiling), J.link(J.step_local(state, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside)} : R.Frame},
        prove_advance(state, outside, b, body, ceiling, internal, Unit{}),
        next => fact =>
          (+advance = fact
           raise_cut(b, t, body, ceiling, state, outside, v, advance,
             execution_real_accepts_extracts_to_first_emission(t, C.decrease64(body), C.decrease64(ceiling),
               J.step_local(state, outside, b, C.decrease64(body), C.decrease64(ceiling)), outside, v, next,
               advance_acceptance(b, t, body, ceiling, state, outside, v, advance, accepted)))))
