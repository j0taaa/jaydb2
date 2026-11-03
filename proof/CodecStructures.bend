# List, record and stack invariants of src/Codec, without structural ceilings.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F

# Every element already read is valid. No fixed Nat/u64 size is required.
def ValuesValid(xs: List<&2, D.Value>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{h, t}:
      L.E<{D.value_valid(h) == True{} : Bool}, ValuesValid(t)>

# The stack stores fields in reverse reading order. The boundary is strict.
def FieldsBefore(xs: List<&2, D.Field>, next: String) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{D.Field{n, v}, t}:
      L.E<{D.name_valid(n) == True{} : Bool},
        L.E<{D.value_valid(v) == True{} : Bool},
          L.E<{String.is_lt(n, next) == True{} : Bool}, FieldsBefore(t, n)>>>

def FieldsInverted(xs: List<&2, D.Field>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{D.Field{n, v}, t}:
      L.E<{D.name_valid(n) == True{} : Bool},
        L.E<{D.value_valid(v) == True{} : Bool}, FieldsBefore(t, n)>>

# Links previous to the accumulated field; an empty state invents no name.
def LastName(xs: List<&2, D.Field>, previous: String) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{D.Field{n, v}, t}:
      {n == previous : String}

law assemble_list_preserves_form:
  for xs: List<&2, D.Value>
  for +acc: D.Value
  for form: {D.is_list(acc) == True{} : Bool}
  {D.is_list(C.assemble_list(xs, acc)) == True{} : Bool}
def assemble_list_preserves_form(xs, acc, form):
  match xs:
    case Nil{}:
      form
    case Con{h, t}:
      assemble_list_preserves_form(t, D.VList{h, acc}, {==})

law assemble_list_preserves_validity:
  for +xs: List<&2, D.Value>
  for +acc: D.Value
  for elements: ValuesValid(xs)
  for form: {D.is_list(acc) == True{} : Bool}
  for is_valid: {D.value_valid(acc) == True{} : Bool}
  {D.value_valid(C.assemble_list(xs, acc)) == True{} : Bool}
def assemble_list_preserves_validity(xs, acc, elements, form, is_valid):
  match xs:
    case Nil{}:
      is_valid
    case Con{+h, t}:
      match elements:
        case L.Both{head, tail}:
          assemble_list_preserves_validity(t, D.VList{h, acc}, tail, {==},
            F.and_boolean_intro(D.value_valid(h) && D.is_list(acc), D.value_valid(acc),
              F.and_boolean_intro(D.value_valid(h), D.is_list(acc), head, form), is_valid))

law assemble_record_preserves_form:
  for xs: List<&2, D.Field>
  for +acc: D.Value
  for form: {D.is_record(acc) == True{} : Bool}
  {D.is_record(C.assemble_record(xs, acc)) == True{} : Bool}
def assemble_record_preserves_form(xs, acc, form):
  match xs:
    case Nil{}:
      form
    case Con{D.Field{n, v}, t}:
      assemble_record_preserves_form(t, D.VRecord{n, v, acc}, {==})

law assemble_record_after_head:
  for +xs: List<&2, D.Field>
  for +n: String
  for +v: D.Value
  for +r: D.Value
  for fields: FieldsBefore(xs, n)
  for is_valid: {D.value_valid(D.VRecord{n, v, r}) == True{} : Bool}
  {D.value_valid(C.assemble_record(xs, D.VRecord{n, v, r})) == True{} : Bool}
def assemble_record_after_head(xs, n, v, r, fields, is_valid):
  match xs:
    case Nil{}:
      is_valid
    case Con{D.Field{+previous, +value}, t}:
      match fields:
        case L.Both{name, L.Both{datum, L.Both{order, tail}}}:
          assemble_record_after_head(t, previous, value, D.VRecord{n, v, r}, tail,
            F.and_boolean_intro(D.name_valid(previous) && D.value_valid(value) && String.is_lt(previous, n), D.value_valid(D.VRecord{n, v, r}),
              F.and_boolean_intro(D.name_valid(previous) && D.value_valid(value), String.is_lt(previous, n),
                F.and_boolean_intro(D.name_valid(previous), D.value_valid(value), name, datum), order), is_valid))

law assemble_record_preserves_validity:
  for +xs: List<&2, D.Field>
  for fields: FieldsInverted(xs)
  {D.value_valid(C.assemble_record(xs, D.VRecordEmpty{})) == True{} : Bool}
def assemble_record_preserves_validity(xs, fields):
  match xs:
    case Nil{}:
      {==}
    case Con{D.Field{+n, +v}, t}:
      match fields:
        case L.Both{name, L.Both{value, tail}}:
          assemble_record_after_head(t, n, v, D.VRecordEmpty{}, tail,
            F.and_boolean_intro(D.name_valid(n) && D.value_valid(v) && True{}, True{},
              F.and_boolean_intro(D.name_valid(n) && D.value_valid(v), True{},
                F.and_boolean_intro(D.name_valid(n), D.value_valid(v), name, value), {==}), {==}))

law fields_previous_to_new_name:
  for +xs: List<&2, D.Field>
  for +previous: String
  for +name: String
  for fields: FieldsInverted(xs)
  for last: LastName(xs, previous)
  for order: {String.is_lt(previous, name) == True{} : Bool}
  FieldsBefore(xs, name)
def fields_previous_to_new_name(xs, previous, name, fields, last, order):
  match xs:
    case Nil{}:
      Unit{}
    case Con{D.Field{+n, +v}, t}:
      match fields:
        case L.Both{valid, L.Both{value, tail}}:
          L.Both{valid, L.Both{value, L.Both{
            (%Equal.sym(String, n, previous, last) : {String.is_lt(_, name) == True{} : Bool}
              order), tail}}}

def StackValid(stack: C.Stack) -> Type:
  match stack:
    case C.Root{}:
      Unit
    case C.ListFrame{u, q, xs, parent}:
      L.E<ValuesValid(xs), StackValid(parent)>
    case C.Name{u, q, previous, xs, parent}:
      L.E<FieldsInverted(xs), L.E<LastName(xs, previous), StackValid(parent)>>
    case C.Field{u, q, name, xs, parent}:
      L.E<{D.name_valid(name) == True{} : Bool}, L.E<FieldsBefore(xs, name), StackValid(parent)>>

def MachineValid(m: C.Machine) -> Type:
  match m:
    case C.Tag{stack}:
      StackValid(stack)
    case C.TagName{stack}:
      StackValid(stack)
    case C.WordInput{f, n, a, b, stack}:
      StackValid(stack)
    case C.Content{name, last, q, u, text, stack}:
      L.E<{D.unicode_valid(text) == True{} : Bool}, StackValid(stack)>
    case C.DecodedReady{v}:
      {D.value_valid(v) == True{} : Bool}
    case C.Invalid{}:
      Unit
    case C.Above{}:
      Unit

law emit_preserves_validity:
  for +stack: C.Stack
  for +value: D.Value
  for structure: StackValid(stack)
  for valid: {D.value_valid(value) == True{} : Bool}
  MachineValid(C.emit(stack, value))
def emit_preserves_validity(stack, value, structure, valid):
  match stack:
    case C.Root{}:
      valid
    case C.ListFrame{True{}, q, +xs, +parent}:
      match structure:
        case L.Both{elements, above}:
          emit_preserves_validity(parent, C.assemble_list(Con{value, xs}, D.VListEmpty{}), above,
            assemble_list_preserves_validity(Con{value, xs}, D.VListEmpty{}, L.Both{valid, elements}, {==}, {==}))
    case C.ListFrame{False{}, q, xs, parent}:
      match structure:
        case L.Both{elements, above}:
          L.Both{L.Both{valid, elements}, above}
    case C.Field{True{}, q, +name, +xs, +parent}:
      match structure:
        case L.Both{name_valid, L.Both{fields, above}}:
          emit_preserves_validity(parent, C.assemble_record(Con{D.Field{name, value}, xs}, D.VRecordEmpty{}), above,
            assemble_record_preserves_validity(Con{D.Field{name, value}, xs}, L.Both{name_valid, L.Both{valid, fields}}))
    case C.Field{False{}, q, name, xs, parent}:
      match structure:
        case L.Both{name_valid, L.Both{fields, above}}:
          L.Both{L.Both{name_valid, L.Both{valid, fields}}, L.Both{{==}, above}}
    case C.Name{u, q, name, xs, parent}:
      Unit{}
