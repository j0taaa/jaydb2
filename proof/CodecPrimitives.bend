# General public soundness of the three unit tags, without assuming size or
# return value. Rejection of every extra byte follows from execution.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecTrace.bend as R
import ./CodecMinimum.bend as M
import ./CodecContent.bend as G
import ./CodecSizes.bend as T
import ./CodecArities.bend as A

type AtomUnit is Data:
  Absence{}
  Boolean{value: Bool}

def octet(a: AtomUnit) -> U32:
  match a:
    case Absence{}:
      0
    case Boolean{False{}}:
      1
    case Boolean{True{}}:
      2

def value(a: AtomUnit) -> D.Value:
  match a:
    case Absence{}:
      D.VAbsent{}
    case Boolean{b}:
      D.VBool{b}

def value_result(r: C.Outcome) -> D.Value:
  match r:
    case C.Decoded{v}:
      v
    case _:
      D.VAbsent{}

law ready_accepted_requires_suffix_empty_and_value_exact:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +w: D.Value
  for -v: D.Value
  for accepted: {C.traverse(bs, body, ceiling, C.DecodedReady{w}) == C.Decoded{v} : C.Outcome}
  L.E<{bs == Nil{} : List<&2, U32>}, {v == w : D.Value}>
def ready_accepted_requires_suffix_empty_and_value_exact(bs, body, ceiling, w, v, accepted):
  match bs:
    case Nil{}:
      L.Both{{==}, Equal.sym(D.Value, w, v, Equal.cong(C.Outcome, D.Value, r => value_result(r), C.Decoded{w}, C.Decoded{v}, accepted))}
    case Con{+b, +t}:
      L.ex_false(L.E<{Con{b, t} == Nil{} : List<&2, U32>}, {v == w : D.Value}>,
        R.input_negative_decoded(v, Equal.trans(C.Outcome,
          C.Input{}, C.traverse(Con{b, t}, body, ceiling, C.DecodedReady{w}), C.Decoded{v},
          Equal.sym(C.Outcome, C.traverse(Con{b, t}, body, ceiling, C.DecodedReady{w}), C.Input{}, R.ready_refusal_any_octet_extra(b, t, body, ceiling, w)), accepted)))

law atom_unit_emits_exactly_o_value:
  for +a: AtomUnit
  for +stack: C.Stack
  for body: B.Number64
  for ceiling: B.Number64
  {C.step(C.Tag{stack}, octet(a), body, ceiling) == C.emit(stack, value(a)) : C.Machine}
def atom_unit_emits_exactly_o_value(a, stack, body, ceiling):
  match a:
    case Absence{}:
      {==}
    case Boolean{False{}}:
      {==}
    case Boolean{True{}}:
      {==}

law atom_unit_has_encoding_exact:
  for +a: AtomUnit
  P.Encoding(value(a), [octet(a)])
def atom_unit_has_encoding_exact(a):
  match a:
    case Absence{}:
      {==}
    case Boolean{False{}}:
      {==}
    case Boolean{True{}}:
      {==}

def atom_combined_execution_trace(+a: AtomUnit, +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  execution_trace: {C.traverse(Con{octet(a), bs}, body, ceiling, C.Tag{C.Root{}}) == C.Decoded{v} : C.Outcome}) -> P.Encoding(v, Con{octet(a), bs}):
  F.combined_pair(P.Encoding(v, Con{octet(a), bs}), {bs == Nil{} : List<&2, U32>}, {v == value(a) : D.Value},
    ready_accepted_requires_suffix_empty_and_value_exact(bs, C.decrease64(body), C.decrease64(ceiling), value(a), v,
      (%atom_unit_emits_exactly_o_value(a, C.Root{}, C.decrease64(body), C.decrease64(ceiling)) :
        {C.traverse(bs, C.decrease64(body), C.decrease64(ceiling), _) == C.Decoded{v} : C.Outcome}
        execution_trace)),
    end => equal =>
      (%Equal.sym(List<&2, U32>, bs, Nil{}, end) : P.Encoding(v, Con{octet(a), _})
        %Equal.sym(D.Value, v, value(a), equal) : P.Encoding(_, [octet(a)])
        atom_unit_has_encoding_exact(a)))

def atom_combined_input(+a: AtomUnit, +bs: List<&2, U32>, +ceiling: B.Number64, -v: D.Value,
  input: R.InputChecked<B.nat64(B.length(Con{octet(a), bs})), Con{octet(a), bs}, ceiling, v>) -> P.Encoding(v, Con{octet(a), bs}):
  match input:
    case R.Checked{body, measure, fits, octets, execution_trace}:
      atom_combined_execution_trace(a, bs, body, ceiling, v, execution_trace)

law all_acceptance_of_atom_unit_and_canonical:
  for +a: AtomUnit
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for -v: D.Value
  for accepted: {C.decode(Con{octet(a), bs}, ceiling) == C.Decoded{v} : C.Outcome}
  P.Encoding(v, Con{octet(a), bs})
def all_acceptance_of_atom_unit_and_canonical(a, bs, ceiling, v, accepted):
  atom_combined_input(a, bs, ceiling, v, R.acceptance_requires_body_representable_octets_and_limit(Con{octet(a), bs}, ceiling, v, accepted))

law input_empty_and_refused:
  for +ceiling: B.Number64
  {C.decode(Nil{}, ceiling) == C.Input{} : C.Outcome}
def input_empty_and_refused(ceiling):
  %Equal.sym(Bool, C.less_equal64(B.Number64{0, 0}, ceiling), True{}, M.zero64_negative_greater(ceiling)) :
    {C.decode_size(_, Nil{}, B.Number64{0, 0}, ceiling) == C.Input{} : C.Outcome}
  {==}

law any_acceptance_requires_to_minus_one_tag:
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for -v: D.Value
  for accepted: {C.decode(bs, ceiling) == C.Decoded{v} : C.Outcome}
  G.NotEmpty(bs)
def any_acceptance_requires_to_minus_one_tag(bs, ceiling, v, accepted):
  match bs:
    case Nil{}:
      R.input_negative_decoded(v,
        Equal.trans(C.Outcome, C.Input{}, C.decode(Nil{}, ceiling), C.Decoded{v},
          Equal.sym(C.Outcome, C.decode(Nil{}, ceiling), C.Input{}, input_empty_and_refused(ceiling)), accepted))
    case Con{b, t}:
      Unit{}

law any_acceptance_requires_one_octet:
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for -v: D.Value
  for accepted: {C.decode(bs, ceiling) == C.Decoded{v} : C.Outcome}
  {Nat.is_le(1n, B.length(bs)) == True{} : Bool}
def any_acceptance_requires_one_octet(bs, ceiling, v, accepted):
  T.bytes_negative_empty_has_by_minus_one_octet(bs, any_acceptance_requires_to_minus_one_tag(bs, ceiling, v, accepted))

# The same property holds at the start of a child with an arbitrary stack.
law tag_that_terminates_ready_consume_prefix_positive:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +stack: C.Stack
  for -v: D.Value
  for ready: {R.machine(R.execute(bs, R.Frame{body, ceiling, C.Tag{stack}})) == C.DecodedReady{v} : C.Machine}
  G.NotEmpty(bs)
def tag_that_terminates_ready_consume_prefix_positive(bs, body, ceiling, stack, v, ready):
  match bs:
    case Nil{}:
      A.tag_negative_and_ready(stack, v, ready)
    case Con{b, t}:
      Unit{}

law tags_naturals_above_of_six_are_refused:
  for n: Nat
  for bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for stack: C.Stack
  {C.traverse(bs, body, ceiling, C.read_tag(7n+n, stack)) == C.Input{} : C.Outcome}
def tags_naturals_above_of_six_are_refused(n, bs, body, ceiling, stack):
  R.invalid_absorbs_all_suffix(bs, body, ceiling)
