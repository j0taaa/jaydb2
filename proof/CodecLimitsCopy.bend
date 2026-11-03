# Constructive duplication of structural proofs used by completeness.
# Only equalities are copied directly; conjunctions are reconstructed.
import Base
import ../contract/Bytes.bend as B
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ./Foundations.bend as F
import ./CodecLimitsSequences.bend as S
import ./CodecLimitsStack.bend as Q
import ../src/Codec.bend as C

law duplicate_values_canonical:
  for +xs: List<&2, S.ValueSegmented>
  for canonical: S.ValuesCanonical(xs)
  L.E<S.ValuesCanonical(xs), S.ValuesCanonical(xs)>
def duplicate_values_canonical(xs, canonical):
  match xs:
    case Nil{}:
      L.Both{Unit{}, Unit{}}
    case Con{S.ValueSegmented{+v, +bs}, +t}:
      match canonical:
        case L.Both{head, tail}:
          +encoded = {head : {P.encode(v) == Some{bs} : Maybe<&2, List<&2, U32>>}}
          F.combined_pair(L.E<S.ValuesCanonical(xs), S.ValuesCanonical(xs)>, S.ValuesCanonical(t), S.ValuesCanonical(t),
            duplicate_values_canonical(t, tail),
            left => right => L.Both{L.Both{encoded, left}, L.Both{encoded, right}})

law duplicate_fields_canonical:
  for +xs: List<&2, S.FieldSegmented>
  for canonical: S.FieldsCanonical(xs)
  L.E<S.FieldsCanonical(xs), S.FieldsCanonical(xs)>
def duplicate_fields_canonical(xs, canonical):
  match xs:
    case Nil{}:
      L.Both{Unit{}, Unit{}}
    case Con{S.FieldSegmented{+n, +v, +nb, +vb}, +t}:
      match canonical:
        case L.Both{+name, L.Both{+text, L.Both{value, tail}}}:
          +encoded = {value : {P.encode(v) == Some{vb} : Maybe<&2, List<&2, U32>>}}
          F.combined_pair(L.E<S.FieldsCanonical(xs), S.FieldsCanonical(xs)>, S.FieldsCanonical(t), S.FieldsCanonical(t),
            duplicate_fields_canonical(t, tail),
            left => right => L.Both{
              L.Both{name, L.Both{text, L.Both{encoded, left}}},
              L.Both{name, L.Both{text, L.Both{encoded, right}}}})

law duplicate_plan_canonical:
  for +stack: C.Stack
  for +plan: Q.Plan
  for canonical: Q.PlanCanonical(stack, plan)
  L.E<Q.PlanCanonical(stack, plan), Q.PlanCanonical(stack, plan)>
def duplicate_plan_canonical(stack, plan, canonical):
  match stack plan:
    case C.Root{} Q.End{}:
      L.Both{Unit{}, Unit{}}
    case C.ListFrame{u, +q, xs, +parent} Q.SiblingsValues{+values, +above}:
      match canonical:
        case L.Both{+measured, L.Both{segments, ancestors}}:
          F.combined_pair(L.E<Q.PlanCanonical(stack, plan), Q.PlanCanonical(stack, plan)>,
            S.ValuesCanonical(values), S.ValuesCanonical(values), duplicate_values_canonical(values, segments),
            v1 => v2 => F.combined_pair(L.E<Q.PlanCanonical(stack, plan), Q.PlanCanonical(stack, plan)>,
              Q.PlanCanonical(parent, above), Q.PlanCanonical(parent, above), duplicate_plan_canonical(parent, above, ancestors),
              p1 => p2 => L.Both{L.Both{measured, L.Both{v1, p1}}, L.Both{measured, L.Both{v2, p2}}}))
    case C.Field{u, +q, n, xs, +parent} Q.SiblingsFields{+fields, +above}:
      match canonical:
        case L.Both{+measured, L.Both{segments, ancestors}}:
          F.combined_pair(L.E<Q.PlanCanonical(stack, plan), Q.PlanCanonical(stack, plan)>,
            S.FieldsCanonical(fields), S.FieldsCanonical(fields), duplicate_fields_canonical(fields, segments),
            c1 => c2 => F.combined_pair(L.E<Q.PlanCanonical(stack, plan), Q.PlanCanonical(stack, plan)>,
              Q.PlanCanonical(parent, above), Q.PlanCanonical(parent, above), duplicate_plan_canonical(parent, above, ancestors),
              p1 => p2 => L.Both{L.Both{measured, L.Both{c1, p1}}, L.Both{measured, L.Both{c2, p2}}}))
    case C.Name{u, +q, n, xs, +parent} Q.ValueAfterName{+v, +bs, +fields, +above}:
      match canonical:
        case L.Both{+measured, L.Both{value, L.Both{segments, ancestors}}}:
          +encoded = {value : {P.encode(v) == Some{bs} : Maybe<&2, List<&2, U32>>}}
          F.combined_pair(L.E<Q.PlanCanonical(stack, plan), Q.PlanCanonical(stack, plan)>,
            S.FieldsCanonical(fields), S.FieldsCanonical(fields), duplicate_fields_canonical(fields, segments),
            c1 => c2 => F.combined_pair(L.E<Q.PlanCanonical(stack, plan), Q.PlanCanonical(stack, plan)>,
              Q.PlanCanonical(parent, above), Q.PlanCanonical(parent, above), duplicate_plan_canonical(parent, above, ancestors),
              p1 => p2 => L.Both{
                L.Both{measured, L.Both{encoded, L.Both{c1, p1}}},
                L.Both{measured, L.Both{encoded, L.Both{c2, p2}}}}))
    case C.Root{} Q.SiblingsValues{values, above}:
      L.ex_false(L.E<Q.PlanCanonical(stack, plan), Q.PlanCanonical(stack, plan)>, canonical)
    case C.Root{} Q.SiblingsFields{fields, above}:
      L.ex_false(L.E<Q.PlanCanonical(stack, plan), Q.PlanCanonical(stack, plan)>, canonical)
    case C.Root{} Q.ValueAfterName{v, bs, fields, above}:
      L.ex_false(L.E<Q.PlanCanonical(stack, plan), Q.PlanCanonical(stack, plan)>, canonical)
    case C.ListFrame{u, q, xs, parent} Q.End{}:
      L.ex_false(L.E<Q.PlanCanonical(stack, plan), Q.PlanCanonical(stack, plan)>, canonical)
    case C.ListFrame{u, q, xs, parent} Q.SiblingsFields{fields, above}:
      L.ex_false(L.E<Q.PlanCanonical(stack, plan), Q.PlanCanonical(stack, plan)>, canonical)
    case C.ListFrame{u, q, xs, parent} Q.ValueAfterName{v, bs, fields, above}:
      L.ex_false(L.E<Q.PlanCanonical(stack, plan), Q.PlanCanonical(stack, plan)>, canonical)
    case C.Field{u, q, n, xs, parent} Q.End{}:
      L.ex_false(L.E<Q.PlanCanonical(stack, plan), Q.PlanCanonical(stack, plan)>, canonical)
    case C.Field{u, q, n, xs, parent} Q.SiblingsValues{values, above}:
      L.ex_false(L.E<Q.PlanCanonical(stack, plan), Q.PlanCanonical(stack, plan)>, canonical)
    case C.Field{u, q, n, xs, parent} Q.ValueAfterName{v, bs, fields, above}:
      L.ex_false(L.E<Q.PlanCanonical(stack, plan), Q.PlanCanonical(stack, plan)>, canonical)
    case C.Name{u, q, n, xs, parent} Q.End{}:
      L.ex_false(L.E<Q.PlanCanonical(stack, plan), Q.PlanCanonical(stack, plan)>, canonical)
    case C.Name{u, q, n, xs, parent} Q.SiblingsValues{values, above}:
      L.ex_false(L.E<Q.PlanCanonical(stack, plan), Q.PlanCanonical(stack, plan)>, canonical)
    case C.Name{u, q, n, xs, parent} Q.SiblingsFields{fields, above}:
      L.ex_false(L.E<Q.PlanCanonical(stack, plan), Q.PlanCanonical(stack, plan)>, canonical)
