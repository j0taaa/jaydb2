# Complete segmentation of RAW fields in an actually accepted record.
# Names are extracted canonically; values retain only the local trace.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecTrace.bend as R
import ./CodecArities.bend as A
import ./CodecCanonical.bend as K
import ./CodecLimitsSequences.bend as S
import ./CodecAcceptanceWord.bend as W
import ./CodecAcceptancePrefix.bend as X
import ./CodecAcceptanceChildren.bend as H
import ./CodecAcceptanceList.bend as I
import ./CodecAcceptanceName.bend as N

# No canonical value encoding is a premise of this witness.
def FieldsRead(xs: List<&2, S.FieldSegmented>, +max: Nat) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{S.FieldSegmented{name, value, nb, vb}, t}:
      L.E<{D.name_valid(name) == True{} : Bool},
        L.E<{P.text(name) == Some{nb} : Maybe<&2, List<&2, U32>>},
          L.E<H.ChildRead<value, vb, max>, FieldsRead(t, max)>>>

type Segmentation<-bs: List<&2, U32>, -start: C.Machine, -v: D.Value, -max: Nat> is Type:
  Segmentation{xs: List<&2, S.FieldSegmented>,
    bytes: {bs == S.bytes_fields(xs) : List<&2, U32>},
    delivery: {A.deliver_fields(S.fields(xs), start) == C.DecodedReady{v} : C.Machine},
    fields: FieldsRead(xs, max)}

type StateRecord is Data:
  Reading{last: Bool, remaining: B.Number64, previous: String, inverted: List<&2, D.Field>}
  Terminated{value: D.Value}

def machine_record(e: StateRecord) -> C.Machine:
  match e:
    case Reading{u, q, previous, xs}:
      C.TagName{C.Name{u, q, previous, xs, C.Root{}}}
    case Terminated{v}:
      C.DecodedReady{v}

# Value positivity already makes the name+value prefix positive.
def prefix_field_positive(nb: List<&2, U32>, +vb: List<&2, U32>,
  positive: H.BytesPositive(vb)) -> H.BytesPositive(B.concatenate(nb, vb)):
  match nb:
    case Nil{}:
      positive
    case Con{b, t}:
      Unit{}

def suffix_valid(+bs: List<&2, U32>, +pre: List<&2, U32>, +suf: List<&2, U32>,
  bytes: {bs == B.concatenate(pre, suf) : List<&2, U32>},
  all_valid: {B.octets_all_valid(bs) == True{} : Bool}) ->
  {B.octets_all_valid(suf) == True{} : Bool}:
  F.combined_pair({B.octets_all_valid(suf) == True{} : Bool},
    {B.octets_all_valid(pre) == True{} : Bool}, {B.octets_all_valid(suf) == True{} : Bool},
    W.separate_octets_all_valid(pre, suf,
      (%bytes : {B.octets_all_valid(_) == True{} : Bool}
        all_valid)), prefix_valid => rest_valid => rest_valid)

def name_extracted_emits_field(+u: Bool, +q: B.Number64,
  +previous: String, +name: String, +inverted: List<&2, D.Field>,
  valid: {D.name_valid(name) == True{} : Bool},
  order: {String.is_lt(previous, name) == True{} : Bool}) ->
  {C.emit_name(C.Name{u, q, previous, inverted, C.Root{}}, name) ==
    C.Tag{C.Field{u, q, name, inverted, C.Root{}}} : C.Machine}:
  %Equal.sym(Bool, D.name_valid(name) && String.is_lt(previous, name), True{},
    F.and_boolean_intro(D.name_valid(name), String.is_lt(previous, name), valid, order)) :
    {C.name_checked(_, u, q, name, inverted, C.Root{}) ==
      C.Tag{C.Field{u, q, name, inverted, C.Root{}}} : C.Machine}
  {==}

def attach_field_read(+bs: List<&2, U32>, +nb: List<&2, U32>, +vb: List<&2, U32>,
  +suf: List<&2, U32>, +u: Bool, +q: B.Number64, +previous: String,
  +inverted: List<&2, D.Field>, +name: String, +h: D.Value, -v: D.Value, +max: Nat,
  bytes: {bs == B.concatenate(B.concatenate(nb, vb), suf) : List<&2, U32>},
  +valid: {D.name_valid(name) == True{} : Bool},
  order: {String.is_lt(previous, name) == True{} : Bool},
  canonical: {P.text(name) == Some{nb} : Maybe<&2, List<&2, U32>>},
  child: H.ChildRead<h, vb, max>,
  tail: Segmentation<suf, C.emit(C.Field{u, q, name, inverted, C.Root{}}, h), v, max>) ->
  Segmentation<bs, C.TagName{C.Name{u, q, previous, inverted, C.Root{}}}, v, max>:
  match tail:
    case Segmentation{+xs, rest_bytes, delivery, fields}:
      Segmentation{Con{S.FieldSegmented{name, h, nb, vb}, xs},
        Equal.trans(List<&2, U32>, bs, B.concatenate(B.concatenate(nb, vb), suf),
          B.concatenate(B.concatenate(nb, vb), S.bytes_fields(xs)), bytes,
          Equal.cong(List<&2, U32>, List<&2, U32>, t => B.concatenate(B.concatenate(nb, vb), t),
            suf, S.bytes_fields(xs), rest_bytes)),
        Equal.trans(C.Machine,
          A.deliver_fields(S.fields(xs), A.deliver_field(
            C.TagName{C.Name{u, q, previous, inverted, C.Root{}}}, D.Field{name, h})),
          A.deliver_fields(S.fields(xs), C.emit(C.Field{u, q, name, inverted, C.Root{}}, h)),
          C.DecodedReady{v}, A.resume_fields(S.fields(xs), q, previous, name, h, inverted,
            C.Root{}, valid, order, u), delivery),
        L.Both{valid, L.Both{canonical, L.Both{child, fields}}}}

# Only the actual last Boolean selects the next Name or DecodedReady.
def resume_after_field(last: Bool, +q: B.Number64, +name: String, +h: D.Value,
  +inverted: List<&2, D.Field>, +suf: List<&2, U32>, +cf: B.Number64, +tf: B.Number64,
  +n: Nat, -v: D.Value, +max: Nat,
  limit_n: {Nat.is_le(B.length(suf), n) == True{} : Bool},
  limit_max: {Nat.is_le(B.length(suf), max) == True{} : Bool},
  all_valid: {B.octets_all_valid(suf) == True{} : Bool},
  remaining: {R.machine(R.execute(suf,
    R.Frame{cf, tf, C.emit(C.Field{last, q, name, inverted, C.Root{}}, h)})) == C.DecodedReady{v} : C.Machine},
  resume: @suf: List<&2, U32> -> @cf: B.Number64 -> @tf: B.Number64 -> @state: StateRecord ->
    {Nat.is_le(B.length(suf), n) == True{} : Bool} ->
    {Nat.is_le(B.length(suf), max) == True{} : Bool} ->
    {B.octets_all_valid(suf) == True{} : Bool} ->
    {R.machine(R.execute(suf, R.Frame{cf, tf, machine_record(state)})) == C.DecodedReady{v} : C.Machine} ->
    Segmentation<suf, machine_record(state), v, max>) ->
  Segmentation<suf, C.emit(C.Field{last, q, name, inverted, C.Root{}}, h), v, max>:
  match last:
    case True{}:
      resume(suf, cf, tf, Terminated{C.assemble_record(Con{D.Field{name, h}, inverted}, D.VRecordEmpty{})},
        limit_n, limit_max, all_valid, remaining)
    case False{}:
      resume(suf, cf, tf, Reading{C.one64(q), C.decrease64(q), name, Con{D.Field{name, h}, inverted}},
        limit_n, limit_max, all_valid, remaining)

def resume_cut_record(+n: Nat, +bs: List<&2, U32>, +cn: B.Number64, +tn: B.Number64,
  +u: Bool, +q: B.Number64, +previous: String, +inverted: List<&2, D.Field>,
  +nb: List<&2, U32>, +name: String, +name_suffix: List<&2, U32>, -v: D.Value, +max: Nat,
  limit_n: {Nat.is_le(B.length(bs), 1n+n) == True{} : Bool},
  limit_max: {Nat.is_le(B.length(bs), max) == True{} : Bool},
  +bytes_name: {bs == B.concatenate(nb, name_suffix) : List<&2, U32>},
  valid: {D.name_valid(name) == True{} : Bool},
  order: {String.is_lt(previous, name) == True{} : Bool},
  canonical: {P.text(name) == Some{nb} : Maybe<&2, List<&2, U32>>},
  all_valid: {B.octets_all_valid(name_suffix) == True{} : Bool},
  cut: X.Cut<name_suffix, cn, tn, C.Tag{C.Root{}}, C.Field{u, q, name, inverted, C.Root{}}, v>,
  resume: @suf: List<&2, U32> -> @cf: B.Number64 -> @tf: B.Number64 -> @state: StateRecord ->
    {Nat.is_le(B.length(suf), n) == True{} : Bool} ->
    {Nat.is_le(B.length(suf), max) == True{} : Bool} ->
    {B.octets_all_valid(suf) == True{} : Bool} ->
    {R.machine(R.execute(suf, R.Frame{cf, tf, machine_record(state)})) == C.DecodedReady{v} : C.Machine} ->
    Segmentation<suf, machine_record(state), v, max>) ->
  Segmentation<bs, C.TagName{C.Name{u, q, previous, inverted, C.Root{}}}, v, max>:
  match cut:
    case X.Cut{+vb, +suf, +h, +cf, +tf, +bytes_value, local, real, remaining}:
      +outside = {C.Field{u, q, name, inverted, C.Root{}} : C.Stack}
      +pre = B.concatenate(nb, vb)
      +bytes = Equal.trans(List<&2, U32>, bs, B.concatenate(nb, name_suffix), B.concatenate(pre, suf), bytes_name,
        Equal.trans(List<&2, U32>, B.concatenate(nb, name_suffix), B.concatenate(nb, B.concatenate(vb, suf)),
          B.concatenate(pre, suf),
          Equal.cong(List<&2, U32>, List<&2, U32>, t => B.concatenate(nb, t),
            name_suffix, B.concatenate(vb, suf), bytes_value),
          Equal.sym(List<&2, U32>, B.concatenate(pre, suf), B.concatenate(nb, B.concatenate(vb, suf)),
            K.concatenation_associative(nb, vb, suf))))
      +local_accepted = Equal.cong(R.Frame, C.Machine, frame => R.machine(frame),
        X.execute_local(vb, outside, R.Frame{cn, tn, C.Tag{C.Root{}}}), R.Frame{cf, tf, C.DecodedReady{h}}, local)
      +cut_max = H.limit_of_bytes_equal(bs, B.concatenate(pre, suf), max, bytes, limit_max)
      attach_field_read(bs, nb, vb, suf, u, q, previous, inverted, name, h, v, max,
        bytes, valid, order, canonical,
        H.ChildRead{cn, tn, outside, local_accepted,
          H.limit_suffix(nb, vb, max, H.limit_prefix(pre, suf, max, cut_max))},
        resume_after_field(u, q, name, h, inverted, suf, cf, tf, n, v, max,
          H.suffix_after_prefix_positive(pre, suf, n,
            prefix_field_positive(nb, vb, H.tag_root_local_accepted_has_bytes(vb, outside, cn, tn, h, local_accepted)),
            H.limit_of_bytes_equal(bs, B.concatenate(pre, suf), 1n+n, bytes, limit_n)),
          H.limit_suffix(pre, suf, max, cut_max),
          suffix_valid(name_suffix, vb, suf, bytes_value, all_valid), remaining, resume))

def resume_name_record(+n: Nat, +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64,
  +u: Bool, +q: B.Number64, +previous: String, +inverted: List<&2, D.Field>, -v: D.Value, +max: Nat,
  limit_n: {Nat.is_le(B.length(bs), 1n+n) == True{} : Bool},
  limit_max: {Nat.is_le(B.length(bs), max) == True{} : Bool},
  extracted: N.NameExtracted<bs, body, ceiling, C.Name{u, q, previous, inverted, C.Root{}}, v>,
  resume: @suf: List<&2, U32> -> @cf: B.Number64 -> @tf: B.Number64 -> @state: StateRecord ->
    {Nat.is_le(B.length(suf), n) == True{} : Bool} ->
    {Nat.is_le(B.length(suf), max) == True{} : Bool} ->
    {B.octets_all_valid(suf) == True{} : Bool} ->
    {R.machine(R.execute(suf, R.Frame{cf, tf, machine_record(state)})) == C.DecodedReady{v} : C.Machine} ->
    Segmentation<suf, machine_record(state), v, max>) ->
  Segmentation<bs, C.TagName{C.Name{u, q, previous, inverted, C.Root{}}}, v, max>:
  match extracted:
    case N.NameExtracted{+nb, +name, +name_suffix, high, low, utf8, +cn, +tn,
      header, factoring, octets_name, rest_valid, positive, bytes, measure,
      +valid, order_name, canonical, body_exact, ceiling_exact, emission, execution, continuation}:
      +order = {order_name : {String.is_lt(previous, name) == True{} : Bool}}
      resume_cut_record(n, bs, cn, tn, u, q, previous, inverted, nb, name, name_suffix, v, max,
        limit_n, limit_max, factoring, valid, order, canonical, rest_valid,
        X.execution_real_accepts_extracts_to_first_emission(name_suffix, cn, tn, C.Tag{C.Root{}},
          C.Field{u, q, name, inverted, C.Root{}}, v, Unit{},
          (%name_extracted_emits_field(u, q, previous, name, inverted, valid, order) :
            {R.machine(R.execute(name_suffix, R.Frame{cn, tn, _})) == C.DecodedReady{v} : C.Machine}
            continuation)), resume)

# n bounds only remaining bytes; max never changes during recursion.
law extract_record_by_fuel:
  for n: Nat
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +state: StateRecord
  for -v: D.Value
  for +max: Nat
  for limit_n: {Nat.is_le(B.length(bs), n) == True{} : Bool}
  for limit_max: {Nat.is_le(B.length(bs), max) == True{} : Bool}
  for all_valid: {B.octets_all_valid(bs) == True{} : Bool}
  for accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling, machine_record(state)})) == C.DecodedReady{v} : C.Machine}
  Segmentation<bs, machine_record(state), v, max>
def extract_record_by_fuel(n, bs, body, ceiling, state, v, max, limit_n, limit_max, all_valid, accepted):
  match n bs state:
    case _ Nil{} Reading{u, q, previous, xs}:
      L.ex_false(Segmentation<Nil{}, machine_record(state), v, max>,
        F.false_negative_true(Equal.cong(C.Machine, Bool, m => X.and_ready(m), machine_record(state), C.DecodedReady{v}, accepted)))
    case _ Nil{} Terminated{w}:
      Segmentation{Nil{}, {==}, accepted, Unit{}}
    case 0n Con{b, t} _:
      F.absurd_boolean(Segmentation<bs, machine_record(state), v, max>, limit_n)
    case 1n+ +less Con{b, t} Terminated{+w}:
      L.ex_false(Segmentation<bs, C.DecodedReady{w}, v, max>, I.ready_combined_suffix_impossible(b, t, body, ceiling, w, v, accepted))
    case 1n+ +less Con{b, t} Reading{+u, +q, +previous, +inverted}:
      resume_name_record(less, bs, body, ceiling, u, q, previous, inverted, v, max, limit_n, limit_max,
        N.name_accepted_extracts_prefix_canonical(bs, body, ceiling, u, q, previous, inverted, C.Root{}, v, all_valid, accepted),
        suf => cf => tf => next => ln => lm => vs => accepted_rest =>
          extract_record_by_fuel(less, suf, cf, tf, next, v, max, ln, lm, vs, accepted_rest))

def extract_opening_record(empty: Bool, +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64,
  +q: B.Number64, -v: D.Value,
  all_valid: {B.octets_all_valid(bs) == True{} : Bool},
  accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling, C.open_variable(empty, C.CountsRecord{}, q, C.Root{})})) == C.DecodedReady{v} : C.Machine}) ->
  Segmentation<bs, C.open_variable(empty, C.CountsRecord{}, q, C.Root{}), v, B.length(bs)>:
  match empty:
    case True{}:
      extract_record_by_fuel(B.length(bs), bs, body, ceiling, Terminated{D.VRecordEmpty{}}, v, B.length(bs),
        S.limit_reflexive(B.length(bs)), S.limit_reflexive(B.length(bs)), all_valid, accepted)
    case False{}:
      extract_record_by_fuel(B.length(bs), bs, body, ceiling, Reading{C.one64(q), C.decrease64(q), "", Nil{}}, v, B.length(bs),
        S.limit_reflexive(B.length(bs)), S.limit_reflexive(B.length(bs)), all_valid, accepted)

law record_accepted_extracts_all_os_fields:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +q: B.Number64
  for -v: D.Value
  for all_valid: {B.octets_all_valid(bs) == True{} : Bool}
  for accepted: {R.machine(R.execute(bs, R.Frame{body, ceiling, C.open_variable(C.zero64(q), C.CountsRecord{}, q, C.Root{})})) == C.DecodedReady{v} : C.Machine}
  Segmentation<bs, C.open_variable(C.zero64(q), C.CountsRecord{}, q, C.Root{}), v, B.length(bs)>
def record_accepted_extracts_all_os_fields(bs, body, ceiling, q, v, all_valid, accepted):
  extract_opening_record(C.zero64(q), bs, body, ceiling, q, v, all_valid, accepted)
