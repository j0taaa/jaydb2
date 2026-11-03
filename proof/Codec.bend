# General part of Law 2: validity of EVERY value actually accepted by Codec.
# Complete public equivalence is proved in CodecLaw2.bend.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecUnicode.bend as U
import ./CodecStructures.bend as E
import ./CodecTrace.bend as R
import ./CodecCanonical.bend as K
import ../contract/Protocol.bend as P
import ./CodecCounters.bend as Counters
import ./CodecUTF8.bend as UTF8
import ./CodecContent.bend as Content
import ./CodecUTF8Bits.bend as BitsUTF8
import ./CodecWordsInverse.bend as Words
import ./CodecIntegers.bend as Integers
import ./CodecArities.bend as Arities

law name_checked_preserves_validity:
  for +ok: Bool
  for u: Bool
  for q: B.Number64
  for +previous: String
  for +name: String
  for +xs: List<&2, D.Field>
  for +parent: C.Stack
  for fields: E.FieldsInverted(xs)
  for last: E.LastName(xs, previous)
  for above: E.StackValid(parent)
  for checks: {ok == True{} : Bool} -> {D.name_valid(name) && String.is_lt(previous, name) == True{} : Bool}
  E.MachineValid(C.name_checked(ok, u, q, name, xs, parent))
def name_checked_preserves_validity(ok, u, q, previous, name, xs, parent, fields, last, above, checks):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      +verified = checks({==})
      L.Both{F.and_boolean_left(D.name_valid(name), String.is_lt(previous, name), verified),
        L.Both{E.fields_previous_to_new_name(xs, previous, name, fields, last,
          F.and_boolean_right(D.name_valid(name), String.is_lt(previous, name), verified)), above}}

law emit_name_preserves_validity:
  for +stack: C.Stack
  for +name: String
  for structure: E.StackValid(stack)
  E.MachineValid(C.emit_name(stack, name))
def emit_name_preserves_validity(stack, name, structure):
  match stack:
    case C.Name{u, q, +previous, +xs, +parent}:
      match structure:
        case L.Both{fields, L.Both{last, above}}:
          name_checked_preserves_validity(D.name_valid(name) && String.is_lt(previous, name), u, q, previous, name, xs, parent, fields, last, above, e => e)
    case C.Root{}:
      Unit{}
    case C.ListFrame{u, q, xs, parent}:
      Unit{}
    case C.Field{u, q, n, xs, parent}:
      Unit{}

law emit_text_preserves_validity:
  for name: Bool
  for +text: String
  for +stack: C.Stack
  for structure: E.StackValid(stack)
  for valid: {D.unicode_valid(text) == True{} : Bool}
  E.MachineValid(C.emit_text(name, text, stack))
def emit_text_preserves_validity(name, text, stack, structure, valid):
  match name:
    case False{}:
      E.emit_preserves_validity(stack, D.VText{text}, structure, valid)
    case True{}:
      emit_name_preserves_validity(stack, text, structure)

law store_character_preserves_validity:
  for last: Bool
  for name: Bool
  for q: B.Number64
  for +text: String
  for +stack: C.Stack
  for structure: E.StackValid(stack)
  for valid: {D.unicode_valid(text) == True{} : Bool}
  E.MachineValid(C.store_character(last, name, q, text, stack))
def store_character_preserves_validity(last, name, q, text, stack, structure, valid):
  match last:
    case True{}:
      emit_text_preserves_validity(name, String.reverse(text), stack, structure, U.reverse_preserves_unicode(text, valid))
    case False{}:
      L.Both{valid, structure}

law store_partial_preserves_validity:
  for last: Bool
  for name: Bool
  for q: B.Number64
  for u: C.Unicode
  for +text: String
  for +stack: C.Stack
  for structure: E.StackValid(stack)
  for valid: {D.unicode_valid(text) == True{} : Bool}
  E.MachineValid(C.store_partial(last, name, q, u, text, stack))
def store_partial_preserves_validity(last, name, q, u, text, stack, structure, valid):
  match last:
    case True{}:
      Unit{}
    case False{}:
      L.Both{valid, structure}

law store_scalar_preserves_validity:
  for +scalar: C.Scalar
  for last: Bool
  for name: Bool
  for q: B.Number64
  for +text: String
  for +stack: C.Stack
  for structure: E.StackValid(stack)
  for valid: {D.unicode_valid(text) == True{} : Bool}
  for cp_valid: U.ScalarValid(scalar)
  E.MachineValid(C.store_scalar(scalar, last, name, q, text, stack))
def store_scalar_preserves_validity(scalar, last, name, q, text, stack, structure, valid, cp_valid):
  match scalar:
    case C.UTFInvalid{}:
      Unit{}
    case C.Character{+cp}:
      store_character_preserves_validity(last, name, q, SCon{Chr{cp}, text}, stack, structure,
        F.and_boolean_intro(D.scalar_valid(cp), D.unicode_valid(text), cp_valid, valid))
    case C.Partial{u}:
      store_partial_preserves_validity(last, name, q, u, text, stack, structure, valid)

law open_name_preserves_validity:
  for fits: Bool
  for n: B.Number64
  for +stack: C.Stack
  for structure: E.StackValid(stack)
  E.MachineValid(C.open_name(fits, n, stack))
def open_name_preserves_validity(fits, n, stack, structure):
  match fits:
    case False{}:
      Unit{}
    case True{}:
      L.Both{{==}, structure}

law open_variable_preserves_validity:
  for empty: Bool
  for f: C.Purpose
  for +n: B.Number64
  for +stack: C.Stack
  for structure: E.StackValid(stack)
  E.MachineValid(C.open_variable(empty, f, n, stack))
def open_variable_preserves_validity(empty, f, n, stack, structure):
  match empty f:
    case True{} C.TextValue{}:
      E.emit_preserves_validity(stack, D.VText{""}, structure, {==})
    case True{} C.CountsList{}:
      E.emit_preserves_validity(stack, D.VListEmpty{}, structure, {==})
    case True{} C.CountsRecord{}:
      E.emit_preserves_validity(stack, D.VRecordEmpty{}, structure, {==})
    case False{} C.TextValue{}:
      L.Both{{==}, structure}
    case False{} C.NameText{}:
      open_name_preserves_validity(C.less_equal64(n, B.Number64{0, 64}), n, stack, structure)
    case False{} C.CountsList{}:
      L.Both{Unit{}, structure}
    case False{} C.CountsRecord{}:
      L.Both{Unit{}, L.Both{Unit{}, structure}}
    case True{} C.Integer{}:
      Unit{}
    case True{} C.NameText{}:
      Unit{}
    case False{} C.Integer{}:
      Unit{}

law open_checked_preserves_validity:
  for check: C.Check
  for +f: C.Purpose
  for +n: B.Number64
  for +stack: C.Stack
  for structure: E.StackValid(stack)
  E.MachineValid(C.open_checked(check, f, n, stack))
def open_checked_preserves_validity(check, f, n, stack, structure):
  match check:
    case C.Large{}:
      Unit{}
    case C.Short{}:
      Unit{}
    case C.Fits{}:
      open_variable_preserves_validity(C.zero64(n), f, n, stack, structure)

law conclude_word_preserves_validity:
  for f: C.Purpose
  for +high: U32
  for +low: U32
  for +stack: C.Stack
  for body: B.Number64
  for ceiling: B.Number64
  for structure: E.StackValid(stack)
  E.MachineValid(C.conclude_word(f, high, low, stack, body, ceiling))
def conclude_word_preserves_validity(f, high, low, stack, body, ceiling, structure):
  match f:
    case C.Integer{}:
      E.emit_preserves_validity(stack, D.VInt{high, low}, structure, {==})
    case C.TextValue{}:
      +n = {B.Number64{high, low} : B.Number64}
      open_checked_preserves_validity(C.check(C.sum_optional(C.minimum_field(C.TextValue{}, n), C.minimum_stack(stack)), body, ceiling), C.TextValue{}, n, stack, structure)
    case C.NameText{}:
      +n = {B.Number64{high, low} : B.Number64}
      open_checked_preserves_validity(C.check(C.sum_optional(C.minimum_field(C.NameText{}, n), C.minimum_stack(stack)), body, ceiling), C.NameText{}, n, stack, structure)
    case C.CountsList{}:
      +n = {B.Number64{high, low} : B.Number64}
      open_checked_preserves_validity(C.check(C.sum_optional(C.minimum_field(C.CountsList{}, n), C.minimum_stack(stack)), body, ceiling), C.CountsList{}, n, stack, structure)
    case C.CountsRecord{}:
      +n = {B.Number64{high, low} : B.Number64}
      open_checked_preserves_validity(C.check(C.sum_optional(C.minimum_field(C.CountsRecord{}, n), C.minimum_stack(stack)), body, ceiling), C.CountsRecord{}, n, stack, structure)

law read_word_preserves_validity:
  for n: Nat
  for +f: C.Purpose
  for +high: U32
  for +low: U32
  for +b: U32
  for +stack: C.Stack
  for body: B.Number64
  for ceiling: B.Number64
  for structure: E.StackValid(stack)
  E.MachineValid(C.read_word(n, f, high, low, b, stack, body, ceiling))
def read_word_preserves_validity(n, f, high, low, b, stack, body, ceiling, structure):
  match n:
    case 0n:
      conclude_word_preserves_validity(f, (high * 256 + U32.shrn(low, 24n) : U32), (low * 256 + b : U32), stack, body, ceiling, structure)
    case 1n+p:
      structure

law read_tag_preserves_validity:
  for tag: Nat
  for +stack: C.Stack
  for structure: E.StackValid(stack)
  E.MachineValid(C.read_tag(tag, stack))
def read_tag_preserves_validity(tag, stack, structure):
  match tag:
    case 0n:
      E.emit_preserves_validity(stack, D.VAbsent{}, structure, {==})
    case 1n:
      E.emit_preserves_validity(stack, D.VBool{False{}}, structure, {==})
    case 2n:
      E.emit_preserves_validity(stack, D.VBool{True{}}, structure, {==})
    case 3n:
      structure
    case 4n:
      structure
    case 5n:
      structure
    case 6n:
      structure
    case 7n+p:
      Unit{}

law read_tag_name_preserves_validity:
  for correct: Bool
  for +stack: C.Stack
  for structure: E.StackValid(stack)
  E.MachineValid(C.read_tag_name(correct, stack))
def read_tag_name_preserves_validity(correct, stack, structure):
  match correct:
    case False{}:
      Unit{}
    case True{}:
      structure

law step_preserves_validity:
  for +m: C.Machine
  for +b: U32
  for body: B.Number64
  for ceiling: B.Number64
  for structure: E.MachineValid(m)
  E.MachineValid(C.step(m, b, body, ceiling))
def step_preserves_validity(m, b, body, ceiling, structure):
  match m:
    case C.Tag{+stack}:
      read_tag_preserves_validity(U32.to_nat(b), stack, structure)
    case C.TagName{+stack}:
      read_tag_name_preserves_validity(U32.is_eq(b, 4), stack, structure)
    case C.WordInput{f, n, high, low, +stack}:
      read_word_preserves_validity(n, f, high, low, b, stack, body, ceiling, structure)
    case C.Content{name, last, q, +u, +text, +stack}:
      match structure:
        case L.Both{valid, stack_is_valid}:
          store_scalar_preserves_validity(C.step_utf8(u, b), last, name, q, text, stack, stack_is_valid, valid, U.step_utf8_only_emits_scalars_all_valid(u, b))
    case C.DecodedReady{v}:
      Unit{}
    case C.Invalid{}:
      Unit{}
    case C.Above{}:
      Unit{}

def ResultValid(r: C.Outcome) -> Type:
  match r:
    case C.Decoded{v}:
      {D.value_valid(v) == True{} : Bool}
    case _:
      Unit

law finalize_preserves_validity:
  for +m: C.Machine
  for structure: E.MachineValid(m)
  ResultValid(C.finalize(m))
def finalize_preserves_validity(m, structure):
  match m:
    case C.Tag{stack}:
      Unit{}
    case C.TagName{stack}:
      Unit{}
    case C.WordInput{f, n, a, b, stack}:
      Unit{}
    case C.Content{name, last, q, u, text, stack}:
      Unit{}
    case C.DecodedReady{v}:
      structure
    case C.Invalid{}:
      Unit{}
    case C.Above{}:
      Unit{}

law traverse_preserves_validity:
  for bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +m: C.Machine
  for structure: E.MachineValid(m)
  ResultValid(C.traverse(bs, body, ceiling, m))
def traverse_preserves_validity(bs, body, ceiling, m, structure):
  match bs:
    case Nil{}:
      finalize_preserves_validity(m, structure)
    case Con{+b, t}:
      +rest = C.decrease64(body)
      +free = C.decrease64(ceiling)
      traverse_preserves_validity(t, rest, free, C.step(m, b, rest, free), step_preserves_validity(m, b, rest, free, structure))

law decode_octets_preserves_validity:
  for all_valid: Bool
  for bs: List<&2, U32>
  for body: B.Number64
  for ceiling: B.Number64
  ResultValid(C.decode_octets(all_valid, bs, body, ceiling))
def decode_octets_preserves_validity(all_valid, bs, body, ceiling):
  match all_valid:
    case False{}:
      Unit{}
    case True{}:
      traverse_preserves_validity(bs, body, ceiling, C.Tag{C.Root{}}, Unit{})

law decode_size_preserves_validity:
  for fits: Bool
  for +bs: List<&2, U32>
  for body: B.Number64
  for ceiling: B.Number64
  ResultValid(C.decode_size(fits, bs, body, ceiling))
def decode_size_preserves_validity(fits, bs, body, ceiling):
  match fits:
    case False{}:
      Unit{}
    case True{}:
      decode_octets_preserves_validity(B.octets_all_valid(bs), bs, body, ceiling)

law decode_measure_preserves_validity:
  for n: Maybe<&2, B.Number64>
  for bs: List<&2, U32>
  for +ceiling: B.Number64
  ResultValid(C.decode_measure(n, bs, ceiling))
def decode_measure_preserves_validity(n, bs, ceiling):
  match n:
    case None{}:
      Unit{}
    case Some{+body}:
      decode_size_preserves_validity(C.less_equal64(body, ceiling), bs, body, ceiling)

law decode_only_returns_value_valid:
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for -v: D.Value
  for accepted: {C.decode(bs, ceiling) == C.Decoded{v} : C.Outcome}
  {D.value_valid(v) == True{} : Bool}
def decode_only_returns_value_valid(bs, ceiling, v, accepted):
  %accepted : ResultValid(_)
  decode_measure_preserves_validity(B.nat64(B.length(bs)), bs, ceiling)

# Collects the guarantees actually proved; contains no Canonical premise.
type AcceptanceProven<-bs: List<&2, U32>, -ceiling: B.Number64, -v: D.Value> is Type:
  Acceptance{body: B.Number64,
    measure: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>},
    fits: {C.less_equal64(body, ceiling) == True{} : Bool},
    octets: {B.octets_all_valid(bs) == True{} : Bool},
    terminal: {R.machine(R.execute(bs, R.Frame{body, ceiling, C.Tag{C.Root{}}})) == C.DecodedReady{v} : C.Machine},
    valid: {D.value_valid(v) == True{} : Bool}}

def combine_acceptance(+bs: List<&2, U32>, +ceiling: B.Number64, -v: D.Value,
  checked: R.InputChecked<B.nat64(B.length(bs)), bs, ceiling, v>,
  valid: {D.value_valid(v) == True{} : Bool}) -> AcceptanceProven<bs, ceiling, v>:
  match checked:
    case R.Checked{+body, measure, fits, octets, execution_trace}:
      Acceptance{body, measure, fits, octets,
        R.execution_trace_accepted_terminates_ready(bs, R.Frame{body, ceiling, C.Tag{C.Root{}}}, v, execution_trace), valid}

law acceptance_guarantees_validity_limit_and_consumption_integral:
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for -v: D.Value
  for +accepted: {C.decode(bs, ceiling) == C.Decoded{v} : C.Outcome}
  AcceptanceProven<bs, ceiling, v>
def acceptance_guarantees_validity_limit_and_consumption_integral(bs, ceiling, v, accepted):
  combine_acceptance(bs, ceiling, v,
    R.acceptance_requires_body_representable_octets_and_limit(bs, ceiling, v, accepted),
    decode_only_returns_value_valid(bs, ceiling, v, accepted))

law value_accepted_releases_encoder_original:
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for +v: D.Value
  for accepted: {C.decode(bs, ceiling) == C.Decoded{v} : C.Outcome}
  {P.encode(v) == P.finalize(P.encode_partial(v)) : Maybe<&2, List<&2, U32>>}
def value_accepted_releases_encoder_original(bs, ceiling, v, accepted):
  K.value_valid_releases_encoding(v, decode_only_returns_value_valid(bs, ceiling, v, accepted))
