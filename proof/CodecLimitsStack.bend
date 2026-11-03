# Bridge between real C.Stack counters and pending canonical bytes.
# The plan describes unread siblings in reading order. In the Name frame
# it also includes the current field value; the name may still be in progress.
# No premise states that the minimum fits: that is a conclusion.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecSizes.bend as T
import ./CodecLimitsNames.bend as N
import ./CodecLimitsSequences.bend as S
import ./CodecMinimumStack.bend as M
import ./CodecSums.bend as A
import ./CodecSumsMinimum.bend as G
import ./CodecReservations.bend as R

type Plan is Data:
  End{}
  SiblingsValues{values: List<&2, S.ValueSegmented>, parent: Plan}
  SiblingsFields{fields: List<&2, S.FieldSegmented>, parent: Plan}
  ValueAfterName{value: D.Value, bytes: List<&2, U32>, fields: List<&2, S.FieldSegmented>, parent: Plan}

# The only numeric premises are COUNT measures of actual segments.
# Accumulators and the last bit do not affect the lower bound.
def PlanCanonical(stack: C.Stack, plan: Plan) -> Type:
  match stack plan:
    case C.Root{} End{}:
      Unit
    case C.ListFrame{u, q, xs, parent} SiblingsValues{values, above}:
      L.E<{B.nat64(S.count_values(values)) == Some{q} : Maybe<&2, B.Number64>},
        L.E<S.ValuesCanonical(values), PlanCanonical(parent, above)>>
    case C.Field{u, q, n, xs, parent} SiblingsFields{fields, above}:
      L.E<{B.nat64(S.count_fields(fields)) == Some{q} : Maybe<&2, B.Number64>},
        L.E<S.FieldsCanonical(fields), PlanCanonical(parent, above)>>
    case C.Name{u, q, n, xs, parent} ValueAfterName{v, bs, fields, above}:
      L.E<{B.nat64(S.count_fields(fields)) == Some{q} : Maybe<&2, B.Number64>},
        L.E<P.Encoding(v, bs), L.E<S.FieldsCanonical(fields), PlanCanonical(parent, above)>>>
    case _ _:
      Empty

def bytes_pending(plan: Plan) -> List<&2, U32>:
  match plan:
    case End{}:
      Nil{}
    case SiblingsValues{xs, parent}:
      B.concatenate(S.bytes_values(xs), bytes_pending(parent))
    case SiblingsFields{xs, parent}:
      B.concatenate(S.bytes_fields(xs), bytes_pending(parent))
    case ValueAfterName{v, bs, xs, parent}:
      B.concatenate(bs, B.concatenate(S.bytes_fields(xs), bytes_pending(parent)))

def minimum_natural(plan: Plan) -> Nat:
  match plan:
    case End{}:
      0n
    case SiblingsValues{xs, parent}:
      Nat.add(S.count_values(xs), minimum_natural(parent))
    case SiblingsFields{xs, parent}:
      Nat.add(Nat.mul(11n, S.count_fields(xs)), minimum_natural(parent))
    case ValueAfterName{v, bs, xs, parent}:
      1n+Nat.add(Nat.mul(11n, S.count_fields(xs)), minimum_natural(parent))

def Certificate(stack: C.Stack, +plan: Plan) -> Type:
  L.E<{C.minimum_stack(stack) == B.nat64(minimum_natural(plan)) : Maybe<&2, B.Number64>},
    {Nat.is_le(minimum_natural(plan), B.length(bytes_pending(plan))) == True{} : Bool}>

# Recursion consumes only the parent stack and parent plan. Sequence
# bounds are proved on the tails of the corresponding segments.
law minimum_stack_canonical_and_exact_and_bounded_by_bytes_pending:
  for +stack: C.Stack
  for +plan: Plan
  for canonical: PlanCanonical(stack, plan)
  Certificate(stack, plan)
def minimum_stack_canonical_and_exact_and_bounded_by_bytes_pending(stack, plan, canonical):
  match stack plan:
    case C.Root{} End{}:
      L.Both{{==}, {==}}
    case C.ListFrame{u, +q, xs, +parent} SiblingsValues{+values, +above}:
      match canonical:
        case L.Both{measured, L.Both{segments, previous}}:
          F.combined_pair(Certificate(stack, plan),
            {C.minimum_stack(parent) == B.nat64(minimum_natural(above)) : Maybe<&2, B.Number64>},
            {Nat.is_le(minimum_natural(above), B.length(bytes_pending(above))) == True{} : Bool},
            minimum_stack_canonical_and_exact_and_bounded_by_bytes_pending(parent, above, previous),
            exact => limit => L.Both{
                (%Equal.sym(Maybe<&2, B.Number64>, C.minimum_stack(parent), B.nat64(minimum_natural(above)), exact) :
                  {C.sum_pending(q, 1n, _) == B.nat64(minimum_natural(plan)) : Maybe<&2, B.Number64>}
                  %A.nat_sum_zero_right(S.count_values(values)) :
                    {C.sum_pending(q, 1n, B.nat64(minimum_natural(above))) == B.nat64(Nat.add(_, minimum_natural(above))) : Maybe<&2, B.Number64>}
                  M.sum_pending_nat64_exact(S.count_values(values), q, 1n, minimum_natural(above), measured)),
                S.concatenate_segments_preserves_sum_of_limits(S.bytes_values(values), bytes_pending(above), S.count_values(values), minimum_natural(above),
                  S.sequence_of_values_canonical_requires_one_octet_by_value(values, segments), limit)})
    case C.Field{u, +q, n, xs, +parent} SiblingsFields{+fields, +above}:
      match canonical:
        case L.Both{measured, L.Both{segments, previous}}:
          F.combined_pair(Certificate(stack, plan),
            {C.minimum_stack(parent) == B.nat64(minimum_natural(above)) : Maybe<&2, B.Number64>},
            {Nat.is_le(minimum_natural(above), B.length(bytes_pending(above))) == True{} : Bool},
            minimum_stack_canonical_and_exact_and_bounded_by_bytes_pending(parent, above, previous),
            exact => limit => L.Both{
                (%Equal.sym(Maybe<&2, B.Number64>, C.minimum_stack(parent), B.nat64(minimum_natural(above)), exact) :
                  {C.sum_pending(q, 11n, _) == B.nat64(minimum_natural(plan)) : Maybe<&2, B.Number64>}
                  M.sum_pending_nat64_exact(S.count_fields(fields), q, 11n, minimum_natural(above), measured)),
                S.concatenate_segments_preserves_sum_of_limits(S.bytes_fields(fields), bytes_pending(above), Nat.mul(11n, S.count_fields(fields)), minimum_natural(above),
                  S.sequence_of_fields_canonical_requires_eleven_octets_by_field(fields, segments), limit)})
    case C.Name{u, +q, n, xs, +parent} ValueAfterName{+v, +bs, +fields, +above}:
      match canonical:
        case L.Both{measured, L.Both{value, L.Both{segments, previous}}}:
          F.combined_pair(Certificate(stack, plan),
            {C.minimum_stack(parent) == B.nat64(minimum_natural(above)) : Maybe<&2, B.Number64>},
            {Nat.is_le(minimum_natural(above), B.length(bytes_pending(above))) == True{} : Bool},
            minimum_stack_canonical_and_exact_and_bounded_by_bytes_pending(parent, above, previous),
            exact => limit => L.Both{
                (%Equal.sym(Maybe<&2, B.Number64>, C.minimum_stack(parent), B.nat64(minimum_natural(above)), exact) :
                  {C.sum_optional(Some{B.Number64{0, 1}}, C.sum_pending(q, 11n, _)) == B.nat64(minimum_natural(plan)) : Maybe<&2, B.Number64>}
                  %Equal.sym(Maybe<&2, B.Number64>, C.sum_pending(q, 11n, B.nat64(minimum_natural(above))), B.nat64(Nat.add(Nat.mul(11n, S.count_fields(fields)), minimum_natural(above))),
                    M.sum_pending_nat64_exact(S.count_fields(fields), q, 11n, minimum_natural(above), measured)) :
                    {C.sum_optional(B.nat64(1n), _) == B.nat64(minimum_natural(plan)) : Maybe<&2, B.Number64>}
                  A.sum_optional_nat64_exact(1n, Nat.add(Nat.mul(11n, S.count_fields(fields)), minimum_natural(above)))),
                S.concatenate_segments_preserves_sum_of_limits(bs, B.concatenate(S.bytes_fields(fields), bytes_pending(above)), 1n, Nat.add(Nat.mul(11n, S.count_fields(fields)), minimum_natural(above)),
                  T.all_value_canonical_requires_by_minus_one_octet(v, bs, value),
                  S.concatenate_segments_preserves_sum_of_limits(S.bytes_fields(fields), bytes_pending(above), Nat.mul(11n, S.count_fields(fields)), minimum_natural(above),
                    S.sequence_of_fields_canonical_requires_eleven_octets_by_field(fields, segments), limit))})
    case C.Root{} SiblingsValues{values, above}:
      L.ex_false(Certificate(stack, plan), canonical)
    case C.Root{} SiblingsFields{fields, above}:
      L.ex_false(Certificate(stack, plan), canonical)
    case C.Root{} ValueAfterName{v, bs, fields, above}:
      L.ex_false(Certificate(stack, plan), canonical)
    case C.ListFrame{u, q, xs, parent} End{}:
      L.ex_false(Certificate(stack, plan), canonical)
    case C.ListFrame{u, q, xs, parent} SiblingsFields{fields, above}:
      L.ex_false(Certificate(stack, plan), canonical)
    case C.ListFrame{u, q, xs, parent} ValueAfterName{v, bs, fields, above}:
      L.ex_false(Certificate(stack, plan), canonical)
    case C.Field{u, q, n, xs, parent} End{}:
      L.ex_false(Certificate(stack, plan), canonical)
    case C.Field{u, q, n, xs, parent} SiblingsValues{values, above}:
      L.ex_false(Certificate(stack, plan), canonical)
    case C.Field{u, q, n, xs, parent} ValueAfterName{v, bs, fields, above}:
      L.ex_false(Certificate(stack, plan), canonical)
    case C.Name{u, q, n, xs, parent} End{}:
      L.ex_false(Certificate(stack, plan), canonical)
    case C.Name{u, q, n, xs, parent} SiblingsValues{values, above}:
      L.ex_false(Certificate(stack, plan), canonical)
    case C.Name{u, q, n, xs, parent} SiblingsFields{fields, above}:
      L.ex_false(Certificate(stack, plan), canonical)

# In-progress bytes may precedes all pending stack entries.
# This law permits the same plan during headers and contents.
law prefix_current_preserves_limit_of_stack:
  for +stack: C.Stack
  for +plan: Plan
  for +current: List<&2, U32>
  for canonical: PlanCanonical(stack, plan)
  L.E<{C.minimum_stack(stack) == B.nat64(minimum_natural(plan)) : Maybe<&2, B.Number64>},
    {Nat.is_le(minimum_natural(plan), B.length(B.concatenate(current, bytes_pending(plan)))) == True{} : Bool}>
def prefix_current_preserves_limit_of_stack(stack, plan, current, canonical):
  F.combined_pair(
    L.E<{C.minimum_stack(stack) == B.nat64(minimum_natural(plan)) : Maybe<&2, B.Number64>},
      {Nat.is_le(minimum_natural(plan), B.length(B.concatenate(current, bytes_pending(plan)))) == True{} : Bool}>,
    {C.minimum_stack(stack) == B.nat64(minimum_natural(plan)) : Maybe<&2, B.Number64>},
    {Nat.is_le(minimum_natural(plan), B.length(bytes_pending(plan))) == True{} : Bool},
    minimum_stack_canonical_and_exact_and_bounded_by_bytes_pending(stack, plan, canonical),
    exact => limit => L.Both{exact,
        S.concatenate_segments_preserves_sum_of_limits(current, bytes_pending(plan), 0n, minimum_natural(plan),
          T.zero_natural_negative_greater(B.length(current)), limit)})

law minimum_stack_canonical_fits_in_suffix_real:
  for +stack: C.Stack
  for +plan: Plan
  for +current: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for canonical: PlanCanonical(stack, plan)
  for measured: {B.nat64(B.length(B.concatenate(current, bytes_pending(plan)))) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {C.check(C.minimum_stack(stack), body, ceiling) == C.Fits{} : C.Check}
def minimum_stack_canonical_fits_in_suffix_real(stack, plan, current, body, ceiling, canonical, measured, fits):
  F.combined_pair({C.check(C.minimum_stack(stack), body, ceiling) == C.Fits{} : C.Check},
    {C.minimum_stack(stack) == B.nat64(minimum_natural(plan)) : Maybe<&2, B.Number64>},
    {Nat.is_le(minimum_natural(plan), B.length(B.concatenate(current, bytes_pending(plan)))) == True{} : Bool},
    prefix_current_preserves_limit_of_stack(stack, plan, current, canonical),
    exact => limit =>
      %Equal.sym(Maybe<&2, B.Number64>, C.minimum_stack(stack), B.nat64(minimum_natural(plan)), exact) :
        {C.check(_, body, ceiling) == C.Fits{} : C.Check}
      R.minimum_natural_inside_of_body_and_ceiling_u64_fits(minimum_natural(plan), B.length(B.concatenate(current, bytes_pending(plan))), body, ceiling, measured, limit, fits))

# Content of the field whose header was just read. For text the count
# is literally the byte count; for containers it counts segments.
type SegmentCurrent is Data:
  Octets{bytes: List<&2, U32>}
  Values{values: List<&2, S.ValueSegmented>}
  Fields{fields: List<&2, S.FieldSegmented>}

def count_current(s: SegmentCurrent) -> Nat:
  match s:
    case Octets{bs}:
      B.length(bs)
    case Values{xs}:
      S.count_values(xs)
    case Fields{xs}:
      S.count_fields(xs)

def bytes_current(s: SegmentCurrent) -> List<&2, U32>:
  match s:
    case Octets{bs}:
      bs
    case Values{xs}:
      S.bytes_values(xs)
    case Fields{xs}:
      S.bytes_fields(xs)

def SegmentCompatible(f: C.Purpose, s: SegmentCurrent) -> Type:
  match f s:
    case C.Integer{} Octets{bs}:
      Unit
    case C.TextValue{} Octets{bs}:
      Unit
    case C.NameText{} Octets{bs}:
      Unit
    case C.CountsList{} Values{xs}:
      S.ValuesCanonical(xs)
    case C.CountsRecord{} Fields{xs}:
      S.FieldsCanonical(xs)
    case _ _:
      Empty

law segment_compatible_requires_minimum_field_natural:
  for +f: C.Purpose
  for +s: SegmentCurrent
  for compatible: SegmentCompatible(f, s)
  {Nat.is_le(G.minimum_field_natural(f, count_current(s)), B.length(bytes_current(s))) == True{} : Bool}
def segment_compatible_requires_minimum_field_natural(f, s, compatible):
  match f s:
    case C.Integer{} Octets{+bs}:
      S.limit_reflexive(B.length(bs))
    case C.TextValue{} Octets{+bs}:
      S.limit_reflexive(B.length(bs))
    case C.NameText{} Octets{+bs}:
      S.limit_reflexive(B.length(bs))
    case C.CountsList{} Values{+xs}:
      S.sequence_of_values_canonical_requires_one_octet_by_value(xs, compatible)
    case C.CountsRecord{} Fields{+xs}:
      S.sequence_of_fields_canonical_requires_eleven_octets_by_field(xs, compatible)
    case C.Integer{} Values{xs}:
      L.ex_false({Nat.is_le(G.minimum_field_natural(f, count_current(s)), B.length(bytes_current(s))) == True{} : Bool}, compatible)
    case C.Integer{} Fields{xs}:
      L.ex_false({Nat.is_le(G.minimum_field_natural(f, count_current(s)), B.length(bytes_current(s))) == True{} : Bool}, compatible)
    case C.TextValue{} Values{xs}:
      L.ex_false({Nat.is_le(G.minimum_field_natural(f, count_current(s)), B.length(bytes_current(s))) == True{} : Bool}, compatible)
    case C.TextValue{} Fields{xs}:
      L.ex_false({Nat.is_le(G.minimum_field_natural(f, count_current(s)), B.length(bytes_current(s))) == True{} : Bool}, compatible)
    case C.NameText{} Values{xs}:
      L.ex_false({Nat.is_le(G.minimum_field_natural(f, count_current(s)), B.length(bytes_current(s))) == True{} : Bool}, compatible)
    case C.NameText{} Fields{xs}:
      L.ex_false({Nat.is_le(G.minimum_field_natural(f, count_current(s)), B.length(bytes_current(s))) == True{} : Bool}, compatible)
    case C.CountsList{} Octets{bs}:
      L.ex_false({Nat.is_le(G.minimum_field_natural(f, count_current(s)), B.length(bytes_current(s))) == True{} : Bool}, compatible)
    case C.CountsList{} Fields{xs}:
      L.ex_false({Nat.is_le(G.minimum_field_natural(f, count_current(s)), B.length(bytes_current(s))) == True{} : Bool}, compatible)
    case C.CountsRecord{} Octets{bs}:
      L.ex_false({Nat.is_le(G.minimum_field_natural(f, count_current(s)), B.length(bytes_current(s))) == True{} : Bool}, compatible)
    case C.CountsRecord{} Values{xs}:
      L.ex_false({Nat.is_le(G.minimum_field_natural(f, count_current(s)), B.length(bytes_current(s))) == True{} : Bool}, compatible)

# Corollary for the REAL check called by conclude_word. The only
# assumed reserve is the measured body containing these canonical segments.
law field_and_stack_canonical_fit_in_suffix_real:
  for +f: C.Purpose
  for +q: B.Number64
  for +stack: C.Stack
  for +s: SegmentCurrent
  for +plan: Plan
  for +body: B.Number64
  for +ceiling: B.Number64
  for measured: {B.nat64(count_current(s)) == Some{q} : Maybe<&2, B.Number64>}
  for compatible: SegmentCompatible(f, s)
  for canonical: PlanCanonical(stack, plan)
  for body_measured: {B.nat64(B.length(B.concatenate(bytes_current(s), bytes_pending(plan)))) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {C.check(C.sum_optional(C.minimum_field(f, q), C.minimum_stack(stack)), body, ceiling) == C.Fits{} : C.Check}
def field_and_stack_canonical_fit_in_suffix_real(f, q, stack, s, plan, body, ceiling, measured, compatible, canonical, body_measured, fits):
  F.combined_pair({C.check(C.sum_optional(C.minimum_field(f, q), C.minimum_stack(stack)), body, ceiling) == C.Fits{} : C.Check},
    {C.minimum_stack(stack) == B.nat64(minimum_natural(plan)) : Maybe<&2, B.Number64>},
    {Nat.is_le(minimum_natural(plan), B.length(bytes_pending(plan))) == True{} : Bool},
    minimum_stack_canonical_and_exact_and_bounded_by_bytes_pending(stack, plan, canonical),
    exact => limit => R.check_minimum_composed_by_body_real(f, count_current(s), minimum_natural(plan), B.length(B.concatenate(bytes_current(s), bytes_pending(plan))), q, stack, body, ceiling,
        measured, exact, body_measured,
        S.concatenate_segments_preserves_sum_of_limits(bytes_current(s), bytes_pending(plan), G.minimum_field_natural(f, count_current(s)), minimum_natural(plan),
          segment_compatible_requires_minimum_field_natural(f, s, compatible), limit), fits))
