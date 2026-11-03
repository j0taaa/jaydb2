# Relaxation of exact natural bounds; None still means overflow.
import Base
import ../contract/Bytes.bend as B
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecSums.bend as S
import ./CodecSumsOrder.bend as O
import ./CodecMinimumStack.bend as M
import ./CodecAcceptanceStack.bend as J

law zero_negative_greater:
  for n: Nat
  {Nat.is_le(0n, n) == True{} : Bool}
def zero_negative_greater(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

law sum_prefix_preserves_order:
  for +k: Nat
  for +n: Nat
  for +m: Nat
  for reads: {Nat.is_le(n, m) == True{} : Bool}
  {Nat.is_le(Nat.add(k, n), Nat.add(k, m)) == True{} : Bool}
def sum_prefix_preserves_order(k, n, m, reads):
  match k:
    case 0n:
      reads
    case 1n+p:
      sum_prefix_preserves_order(p, n, m, reads)

law order_transitive:
  for +n: Nat
  for +m: Nat
  for +t: Nat
  for nm: {Nat.is_le(n, m) == True{} : Bool}
  for mt: {Nat.is_le(m, t) == True{} : Bool}
  {Nat.is_le(n, t) == True{} : Bool}
def order_transitive(n, m, t, nm, mt):
  match n m t:
    case 0n _ _:
      zero_negative_greater(t)
    case 1n+p 0n _:
      F.absurd_boolean({Nat.is_le(1n+p, t) == True{} : Bool}, nm)
    case 1n+p 1n+q 0n:
      F.absurd_boolean({False{} == True{} : Bool}, mt)
    case 1n+p 1n+q 1n+r:
      order_transitive(p, q, r, nm, mt)

# Both conversions are exact, but may return None. No minimum
# representability is required to construct this relation.
type OrderNatural<-a: Maybe<&2, B.Number64>, -b: Maybe<&2, B.Number64>> is Type:
  OrderNatural{less: Nat, greater: Nat,
    exact_less: {a == B.nat64(less) : Maybe<&2, B.Number64>},
    exact_greater: {b == B.nat64(greater) : Maybe<&2, B.Number64>},
    order: {Nat.is_le(less, greater) == True{} : Bool}}

def sum_exact(+a: Maybe<&2, B.Number64>, +b: Maybe<&2, B.Number64>, +n: Nat, +m: Nat,
  ea: {a == B.nat64(n) : Maybe<&2, B.Number64>},
  eb: {b == B.nat64(m) : Maybe<&2, B.Number64>}) ->
  {C.sum_optional(a, b) == B.nat64(Nat.add(n, m)) : Maybe<&2, B.Number64>}:
  %Equal.sym(Maybe<&2, B.Number64>, a, B.nat64(n), ea) :
    {C.sum_optional(_, b) == B.nat64(Nat.add(n, m)) : Maybe<&2, B.Number64>}
  %Equal.sym(Maybe<&2, B.Number64>, b, B.nat64(m), eb) :
    {C.sum_optional(B.nat64(n), _) == B.nat64(Nat.add(n, m)) : Maybe<&2, B.Number64>}
  S.sum_optional_nat64_exact(n, m)

def sum_to_order(+prefix: Maybe<&2, B.Number64>, +k: Nat,
  +a: Maybe<&2, B.Number64>, +b: Maybe<&2, B.Number64>,
  +exact: {prefix == B.nat64(k) : Maybe<&2, B.Number64>},
  h: OrderNatural<a, b>) -> OrderNatural<C.sum_optional(prefix, a), C.sum_optional(prefix, b)>:
  match h:
    case OrderNatural{+n, +m, ea, eb, reads}:
      OrderNatural{Nat.add(k, n), Nat.add(k, m),
        sum_exact(prefix, a, k, n, exact, ea),
        sum_exact(prefix, b, k, m, exact, eb),
        sum_prefix_preserves_order(k, n, m, reads)}

def pending_exact(+q: B.Number64, +k: Nat, +a: Maybe<&2, B.Number64>, +n: Nat, +r: Nat,
  measured: {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>},
  exact: {a == B.nat64(r) : Maybe<&2, B.Number64>}) ->
  {C.sum_pending(q, k, a) == B.nat64(Nat.add(Nat.mul(k, n), r)) : Maybe<&2, B.Number64>}:
  %Equal.sym(Maybe<&2, B.Number64>, a, B.nat64(r), exact) :
    {C.sum_pending(q, k, _) == B.nat64(Nat.add(Nat.mul(k, n), r)) : Maybe<&2, B.Number64>}
  M.sum_pending_nat64_exact(n, q, k, r, measured)

def pending_to_order(+q: B.Number64, +k: Nat,
  +a: Maybe<&2, B.Number64>, +b: Maybe<&2, B.Number64>, +n: Nat,
  +measured: {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>},
  h: OrderNatural<a, b>) -> OrderNatural<C.sum_pending(q, k, a), C.sum_pending(q, k, b)>:
  match h:
    case OrderNatural{+r, +s, ea, eb, reads}:
      OrderNatural{Nat.add(Nat.mul(k, n), r), Nat.add(Nat.mul(k, n), s),
        pending_exact(q, k, a, n, r, measured, ea),
        pending_exact(q, k, b, n, s, measured, eb),
        sum_prefix_preserves_order(Nat.mul(k, n), r, s, reads)}

def order_in_root(-outside: C.Stack, minimum: M.MinimumExact<outside>) ->
  OrderNatural<C.minimum_stack(C.Root{}), C.minimum_stack(outside)>:
  match minimum:
    case M.MinimumExact{+n, exact}:
      OrderNatural{0n, n, {==}, exact, zero_negative_greater(n)}

# The structural proof uses only counter measures, without requiring
# any compound minimum to be representable.
law minimum_linked_naturals:
  for +p: C.Stack
  for +outside: C.Stack
  for measures_p: M.MeasuresStack(p)
  for measures_outside: M.MeasuresStack(outside)
  OrderNatural<C.minimum_stack(p), C.minimum_stack(J.link_stack(p, outside))>
def minimum_linked_naturals(p, outside, measures_p, measures_outside):
  match p:
    case C.Root{}:
      order_in_root(outside, M.all_os_minimum_of_stack_measure_are_exact(outside, measures_outside))
    case C.ListFrame{u, +q, xs, +parent}:
      match measures_p:
        case L.Both{M.CounterMeasured{+n, measured}, above}:
          pending_to_order(q, 1n, C.minimum_stack(parent), C.minimum_stack(J.link_stack(parent, outside)), n, measured,
            minimum_linked_naturals(parent, outside, above, measures_outside))
    case C.Field{u, +q, name, xs, +parent}:
      match measures_p:
        case L.Both{M.CounterMeasured{+n, measured}, above}:
          pending_to_order(q, 11n, C.minimum_stack(parent), C.minimum_stack(J.link_stack(parent, outside)), n, measured,
            minimum_linked_naturals(parent, outside, above, measures_outside))
    case C.Name{u, +q, previous, xs, +parent}:
      match measures_p:
        case L.Both{M.CounterMeasured{+n, measured}, above}:
          sum_to_order(Some{B.Number64{0, 1}}, 1n,
            C.sum_pending(q, 11n, C.minimum_stack(parent)),
            C.sum_pending(q, 11n, C.minimum_stack(J.link_stack(parent, outside))), {==},
            pending_to_order(q, 11n, C.minimum_stack(parent), C.minimum_stack(J.link_stack(parent, outside)), n, measured,
              minimum_linked_naturals(parent, outside, above, measures_outside)))

def and_fits(c: C.Check) -> Bool:
  match c:
    case C.Fits{}:
      True{}
    case C.Short{}:
      False{}
    case C.Large{}:
      False{}

def check_requires_representation(+a: Maybe<&2, B.Number64>, +body: B.Number64, +ceiling: B.Number64,
  fits: {C.check(a, body, ceiling) == C.Fits{} : C.Check}) -> O.NumberRepresented<a>:
  match a:
    case None{}:
      F.absurd_boolean(O.NumberRepresented<None{}>,
        Equal.cong(C.Check, Bool, c => and_fits(c), C.Large{}, C.Fits{}, fits))
    case Some{q}:
      O.Represented{q, {==}}

def check_cases_requires_limits(+t: Bool, +c: Bool,
  fits: {C.check_cases(t, c) == C.Fits{} : C.Check}) ->
  L.E<{t == True{} : Bool}, {c == True{} : Bool}>:
  match t c:
    case True{} True{}:
      L.Both{{==}, {==}}
    case True{} False{}:
      F.absurd_boolean(L.E<{True{} == True{} : Bool}, {False{} == True{} : Bool}>,
        Equal.cong(C.Check, Bool, x => and_fits(x), C.Short{}, C.Fits{}, fits))
    case False{} _:
      F.absurd_boolean(L.E<{False{} == True{} : Bool}, {c == True{} : Bool}>,
        Equal.cong(C.Check, Bool, x => and_fits(x), C.Large{}, C.Fits{}, fits))

def limit_natural_of_guard(+m: Nat, +c: Nat, +total: B.Number64, +body: B.Number64,
  measured: {B.nat64(m) == Some{total} : Maybe<&2, B.Number64>},
  mc: {B.nat64(c) == Some{body} : Maybe<&2, B.Number64>},
  limit: {C.less_equal64(total, body) == True{} : Bool}) -> {Nat.is_le(m, c) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(m, c), C.less_equal64(total, body), True{},
    Equal.sym(Bool, C.less_equal64(total, body), Nat.is_le(m, c),
      O.less_equal64_reflects_order_nat(m, c, total, body, measured, mc)), limit)

def check_natural_less_represented(+n: Nat, +m: Nat, +c: Nat, +t: Nat,
  +body: B.Number64, +ceiling: B.Number64,
  +mc: {B.nat64(c) == Some{body} : Maybe<&2, B.Number64>},
  +mt: {B.nat64(t) == Some{ceiling} : Maybe<&2, B.Number64>},
  +reads: {Nat.is_le(n, m) == True{} : Bool},
  represented: O.NumberRepresented<B.nat64(m)>,
  fits: {C.check(B.nat64(m), body, ceiling) == C.Fits{} : C.Check}) ->
  {C.check(B.nat64(n), body, ceiling) == C.Fits{} : C.Check}:
  match represented:
    case O.Represented{+total, +measured}:
      limits = check_cases_requires_limits(C.less_equal64(total, ceiling), C.less_equal64(total, body),
        (%measured : {C.check(_, body, ceiling) == C.Fits{} : C.Check}
          fits))
      F.combined_pair({C.check(B.nat64(n), body, ceiling) == C.Fits{} : C.Check},
        {C.less_equal64(total, ceiling) == True{} : Bool}, {C.less_equal64(total, body) == True{} : Bool},
        limits, lt => lc =>
          O.check_natural_bounded(n, c, t, body, ceiling, mc, mt,
            order_transitive(n, m, c, reads, limit_natural_of_guard(m, c, total, body, measured, mc, lc)),
            order_transitive(n, m, t, reads, limit_natural_of_guard(m, t, total, ceiling, measured, mt, lt))))

law check_natural_less:
  for +n: Nat
  for +m: Nat
  for +c: Nat
  for +t: Nat
  for +body: B.Number64
  for +ceiling: B.Number64
  for +mc: {B.nat64(c) == Some{body} : Maybe<&2, B.Number64>}
  for +mt: {B.nat64(t) == Some{ceiling} : Maybe<&2, B.Number64>}
  for +reads: {Nat.is_le(n, m) == True{} : Bool}
  for +fits: {C.check(B.nat64(m), body, ceiling) == C.Fits{} : C.Check}
  {C.check(B.nat64(n), body, ceiling) == C.Fits{} : C.Check}
def check_natural_less(n, m, c, t, body, ceiling, mc, mt, reads, fits):
  check_natural_less_represented(n, m, c, t, body, ceiling, mc, mt, reads,
    check_requires_representation(B.nat64(m), body, ceiling, fits), fits)
