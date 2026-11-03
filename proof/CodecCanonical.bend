# General link between reversed parser accumulators and the original encoder:
# exact byte order, cardinality and None propagation.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecStructures.bend as E

law concatenation_associative:
  for xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +zs: List<&2, U32>
  {B.concatenate(B.concatenate(xs, ys), zs) == B.concatenate(xs, B.concatenate(ys, zs)) : List<&2, U32>}
def concatenation_associative(xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, rest => Con{h, rest},
        B.concatenate(B.concatenate(t, ys), zs), B.concatenate(t, B.concatenate(ys, zs)), concatenation_associative(t, ys, zs))

law concatenation_optional_associative:
  for a: Maybe<&2, List<&2, U32>>
  for b: Maybe<&2, List<&2, U32>>
  for c: Maybe<&2, List<&2, U32>>
  {P.concatenate_optional(P.concatenate_optional(a, b), c) ==
    P.concatenate_optional(a, P.concatenate_optional(b, c)) : Maybe<&2, List<&2, U32>>}
def concatenation_optional_associative(a, b, c):
  match a b c:
    case Some{xs} Some{ys} Some{zs}:
      Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, rest => Some{rest},
        B.concatenate(B.concatenate(xs, ys), zs), B.concatenate(xs, B.concatenate(ys, zs)), concatenation_associative(xs, ys, zs))
    case None{} _ _:
      {==}
    case Some{xs} None{} _:
      {==}
    case Some{xs} Some{ys} None{}:
      {==}

law sum_successor_right:
  for a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}
def sum_successor_right(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 1n+b), 1n+Nat.add(p, b), sum_successor_right(p, b))

def count_values(xs: List<&2, D.Value>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+count_values(t)

def count_fields(xs: List<&2, D.Field>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+count_fields(t)

# Content in reading order, even when the buffer is reversed.
def content_values(xs: List<&2, D.Value>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case Con{h, t}:
      P.concatenate_optional(content_values(t), P.finalize(P.encode_partial(h)))

def content_field(field: D.Field) -> Maybe<&2, List<&2, U32>>:
  D.Field{n, v} = field
  P.concatenate_optional(P.text(n), P.finalize(P.encode_partial(v)))

def content_fields(xs: List<&2, D.Field>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case Con{h, t}:
      P.concatenate_optional(content_fields(t), content_field(h))

def list_bytes(n: Nat, bs: Maybe<&2, List<&2, U32>>) -> P.Partial:
  match bs:
    case None{}:
      P.Impossible{}
    case Some{xs}:
      P.ListFrame{n, xs}

def record_bytes(n: Nat, bs: Maybe<&2, List<&2, U32>>) -> P.Partial:
  match bs:
    case None{}:
      P.Impossible{}
    case Some{xs}:
      P.Record{n, xs}

law list_cases_concatenates_bytes:
  for h: Maybe<&2, List<&2, U32>>
  for n: Nat
  for bs: Maybe<&2, List<&2, U32>>
  {P.list_cases(h, list_bytes(n, bs)) == list_bytes(1n+n, P.concatenate_optional(h, bs)) : P.Partial}
def list_cases_concatenates_bytes(h, n, bs):
  match h bs:
    case None{} None{}:
      {==}
    case None{} Some{xs}:
      {==}
    case Some{xs} None{}:
      {==}
    case Some{xs} Some{ys}:
      {==}

law record_cases_concatenates_bytes:
  for name: Maybe<&2, List<&2, U32>>
  for value: Maybe<&2, List<&2, U32>>
  for n: Nat
  for bs: Maybe<&2, List<&2, U32>>
  {P.record_cases(name, value, record_bytes(n, bs)) ==
    record_bytes(1n+n, P.concatenate_optional(P.concatenate_optional(name, value), bs)) : P.Partial}
def record_cases_concatenates_bytes(name, value, n, bs):
  match name value bs:
    case Some{xs} Some{ys} Some{zs}:
      Equal.cong(List<&2, U32>, P.Partial, rest => P.Record{1n+n, rest},
        B.concatenate(xs, B.concatenate(ys, zs)), B.concatenate(B.concatenate(xs, ys), zs),
        Equal.sym(List<&2, U32>, B.concatenate(B.concatenate(xs, ys), zs), B.concatenate(xs, B.concatenate(ys, zs)), concatenation_associative(xs, ys, zs)))
    case None{} None{} _:
      {==}
    case None{} Some{ys} _:
      {==}
    case Some{xs} None{} _:
      {==}
    case Some{xs} Some{ys} None{}:
      {==}

law assembly_list_preserves_bytes_and_count:
  for +xs: List<&2, D.Value>
  for +acc: D.Value
  for +n: Nat
  for +bs: Maybe<&2, List<&2, U32>>
  for partial: {P.encode_partial(acc) == list_bytes(n, bs) : P.Partial}
  {P.encode_partial(C.assemble_list(xs, acc)) ==
    list_bytes(Nat.add(count_values(xs), n), P.concatenate_optional(content_values(xs), bs)) : P.Partial}
def assembly_list_preserves_bytes_and_count(xs, acc, n, bs, partial):
  match xs:
    case Nil{}:
      match bs:
        case None{}:
          partial
        case Some{bytes}:
          partial
    case Con{+h, +t}:
      step = Equal.trans(P.Partial, P.encode_partial(D.VList{h, acc}),
        P.list_cases(P.finalize(P.encode_partial(h)), list_bytes(n, bs)),
        list_bytes(1n+n, P.concatenate_optional(P.finalize(P.encode_partial(h)), bs)),
        Equal.cong(P.Partial, P.Partial, p => P.list_cases(P.finalize(P.encode_partial(h)), p),
          P.encode_partial(acc), list_bytes(n, bs), partial),
        list_cases_concatenates_bytes(P.finalize(P.encode_partial(h)), n, bs))
      %sum_successor_right(count_values(t), n) :
        {P.encode_partial(C.assemble_list(t, D.VList{h, acc})) == list_bytes(_, P.concatenate_optional(P.concatenate_optional(content_values(t), P.finalize(P.encode_partial(h))), bs)) : P.Partial}
      %Equal.sym(Maybe<&2, List<&2, U32>>,
        P.concatenate_optional(P.concatenate_optional(content_values(t), P.finalize(P.encode_partial(h))), bs),
        P.concatenate_optional(content_values(t), P.concatenate_optional(P.finalize(P.encode_partial(h)), bs)),
        concatenation_optional_associative(content_values(t), P.finalize(P.encode_partial(h)), bs)) :
        {P.encode_partial(C.assemble_list(t, D.VList{h, acc})) == list_bytes(Nat.add(count_values(t), 1n+n), _) : P.Partial}
      assembly_list_preserves_bytes_and_count(t, D.VList{h, acc}, 1n+n, P.concatenate_optional(P.finalize(P.encode_partial(h)), bs), step)

law assembly_record_preserves_bytes_and_count:
  for +xs: List<&2, D.Field>
  for +acc: D.Value
  for +n: Nat
  for +bs: Maybe<&2, List<&2, U32>>
  for partial: {P.encode_partial(acc) == record_bytes(n, bs) : P.Partial}
  {P.encode_partial(C.assemble_record(xs, acc)) ==
    record_bytes(Nat.add(count_fields(xs), n), P.concatenate_optional(content_fields(xs), bs)) : P.Partial}
def assembly_record_preserves_bytes_and_count(xs, acc, n, bs, partial):
  match xs:
    case Nil{}:
      match bs:
        case None{}:
          partial
        case Some{bytes}:
          partial
    case Con{D.Field{+name, +v}, +t}:
      step = Equal.trans(P.Partial, P.encode_partial(D.VRecord{name, v, acc}),
        P.record_cases(P.text(name), P.finalize(P.encode_partial(v)), record_bytes(n, bs)),
        record_bytes(1n+n, P.concatenate_optional(content_field(D.Field{name, v}), bs)),
        Equal.cong(P.Partial, P.Partial, p => P.record_cases(P.text(name), P.finalize(P.encode_partial(v)), p),
          P.encode_partial(acc), record_bytes(n, bs), partial),
        record_cases_concatenates_bytes(P.text(name), P.finalize(P.encode_partial(v)), n, bs))
      %sum_successor_right(count_fields(t), n) :
        {P.encode_partial(C.assemble_record(t, D.VRecord{name, v, acc})) == record_bytes(_, P.concatenate_optional(P.concatenate_optional(content_fields(t), content_field(D.Field{name, v})), bs)) : P.Partial}
      %Equal.sym(Maybe<&2, List<&2, U32>>,
        P.concatenate_optional(P.concatenate_optional(content_fields(t), content_field(D.Field{name, v})), bs),
        P.concatenate_optional(content_fields(t), P.concatenate_optional(content_field(D.Field{name, v}), bs)),
        concatenation_optional_associative(content_fields(t), content_field(D.Field{name, v}), bs)) :
        {P.encode_partial(C.assemble_record(t, D.VRecord{name, v, acc})) == record_bytes(Nat.add(count_fields(t), 1n+n), _) : P.Partial}
      assembly_record_preserves_bytes_and_count(t, D.VRecord{name, v, acc}, 1n+n, P.concatenate_optional(content_field(D.Field{name, v}), bs), step)

law value_valid_releases_encoding:
  for +v: D.Value
  for valid: {D.value_valid(v) == True{} : Bool}
  {P.encode(v) == P.finalize(P.encode_partial(v)) : Maybe<&2, List<&2, U32>>}
def value_valid_releases_encoding(v, valid):
  %Equal.sym(Bool, D.value_valid(v), True{}, valid) :
    {P.encode_cases(_, P.finalize(P.encode_partial(v))) == P.finalize(P.encode_partial(v)) : Maybe<&2, List<&2, U32>>}
  {==}

law list_assembled_has_encoding_exact:
  for +xs: List<&2, D.Value>
  for elements: E.ValuesValid(xs)
  {P.encode(C.assemble_list(xs, D.VListEmpty{})) ==
    P.finalize(list_bytes(Nat.add(count_values(xs), 0n), P.concatenate_optional(content_values(xs), Some{Nil{}}))) : Maybe<&2, List<&2, U32>>}
def list_assembled_has_encoding_exact(xs, elements):
  Equal.trans(Maybe<&2, List<&2, U32>>, P.encode(C.assemble_list(xs, D.VListEmpty{})),
    P.finalize(P.encode_partial(C.assemble_list(xs, D.VListEmpty{}))),
    P.finalize(list_bytes(Nat.add(count_values(xs), 0n), P.concatenate_optional(content_values(xs), Some{Nil{}}))),
    value_valid_releases_encoding(C.assemble_list(xs, D.VListEmpty{}), E.assemble_list_preserves_validity(xs, D.VListEmpty{}, elements, {==}, {==})),
    Equal.cong(P.Partial, Maybe<&2, List<&2, U32>>, p => P.finalize(p),
      P.encode_partial(C.assemble_list(xs, D.VListEmpty{})),
      list_bytes(Nat.add(count_values(xs), 0n), P.concatenate_optional(content_values(xs), Some{Nil{}})),
      assembly_list_preserves_bytes_and_count(xs, D.VListEmpty{}, 0n, Some{Nil{}}, {==})))

law record_assembled_has_encoding_exact:
  for +xs: List<&2, D.Field>
  for fields: E.FieldsInverted(xs)
  {P.encode(C.assemble_record(xs, D.VRecordEmpty{})) ==
    P.finalize(record_bytes(Nat.add(count_fields(xs), 0n), P.concatenate_optional(content_fields(xs), Some{Nil{}}))) : Maybe<&2, List<&2, U32>>}
def record_assembled_has_encoding_exact(xs, fields):
  Equal.trans(Maybe<&2, List<&2, U32>>, P.encode(C.assemble_record(xs, D.VRecordEmpty{})),
    P.finalize(P.encode_partial(C.assemble_record(xs, D.VRecordEmpty{}))),
    P.finalize(record_bytes(Nat.add(count_fields(xs), 0n), P.concatenate_optional(content_fields(xs), Some{Nil{}}))),
    value_valid_releases_encoding(C.assemble_record(xs, D.VRecordEmpty{}), E.assemble_record_preserves_validity(xs, fields)),
    Equal.cong(P.Partial, Maybe<&2, List<&2, U32>>, p => P.finalize(p),
      P.encode_partial(C.assemble_record(xs, D.VRecordEmpty{})),
      record_bytes(Nat.add(count_fields(xs), 0n), P.concatenate_optional(content_fields(xs), Some{Nil{}})),
      assembly_record_preserves_bytes_and_count(xs, D.VRecordEmpty{}, 0n, Some{Nil{}}, {==})))
