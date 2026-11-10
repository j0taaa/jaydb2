# Variable-length global semantic event time. Each block length is the length
# of a finite actual phase rendering, not a constant stride or physical budget.
# Bounded local events from different blocks have disjoint ordered times.
import Base
import ../../../contract/Logic.bend as L
import ../../Foundations.bend as F

def prefix(lengths: List<&2, Nat>, index: Nat) -> Nat:
  match lengths index:
    case Nil{} _: 0n
    case Con{length, rest} 0n: 0n
    case Con{length, rest} 1n+k: Nat.add(length, prefix(rest, k))

def clock(lengths: List<&2, Nat>, index: Nat, base: Nat, local: Nat) -> Nat:
  Nat.add(base, Nat.add(prefix(lengths, index), local))

def Local(lengths: List<&2, Nat>, index: Nat, -local: Nat) -> Type:
  match lengths index:
    case Nil{} _: Empty
    case Con{length, rest} 0n: {Nat.is_lt(local, length) == True{} : Bool}
    case Con{length, rest} 1n+k: Local(rest, k, local)

law addition_associative:
  for a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}
def addition_associative(a, b, c):
  match a:
    case 0n: {==}
    case 1n+k: Equal.cong(Nat, Nat, q => Succ{q}, Nat.add(Nat.add(k, b), c), Nat.add(k, Nat.add(b, c)), addition_associative(k, b, c))

law adding_prefix_preserves_strict_order:
  for base: Nat
  for +a: Nat
  for +b: Nat
  for strict: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(Nat.add(base, a), Nat.add(base, b)) == True{} : Bool}
def adding_prefix_preserves_strict_order(base, a, b, strict):
  match base:
    case 0n: strict
    case 1n+k: adding_prefix_preserves_strict_order(k, a, b, strict)

def strict_right_extension(a: Nat, b: Nat, +extra: Nat,
  strict: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(a, Nat.add(b, extra)) == True{} : Bool}:
  match a b:
    case 0n 0n: F.absurd_boolean({Nat.is_lt(0n, extra) == True{} : Bool}, strict)
    case 0n 1n+k: {==}
    case 1n+k 0n: F.absurd_boolean({Nat.is_lt(1n+k, extra) == True{} : Bool}, strict)
    case 1n+k 1n+j: strict_right_extension(k, j, extra, strict)

law next_block_adds_exact_previous_block_length:
  for +length: Nat
  for +rest: List<&2, Nat>
  for +index: Nat
  for +base: Nat
  for +local: Nat
  {clock(Con{length, rest}, 1n+index, base, local) == clock(rest, index, Nat.add(base, length), local) : Nat}
def next_block_adds_exact_previous_block_length(length, rest, index, base, local):
  Equal.trans(Nat,
    Nat.add(base, Nat.add(Nat.add(length, prefix(rest, index)), local)),
    Nat.add(base, Nat.add(length, Nat.add(prefix(rest, index), local))),
    Nat.add(Nat.add(base, length), Nat.add(prefix(rest, index), local)),
    Equal.cong(Nat, Nat, q => Nat.add(base, q), Nat.add(Nat.add(length, prefix(rest, index)), local),
      Nat.add(length, Nat.add(prefix(rest, index), local)), addition_associative(length, prefix(rest, index), local)),
    Equal.sym(Nat, Nat.add(Nat.add(base, length), Nat.add(prefix(rest, index), local)),
      Nat.add(base, Nat.add(length, Nat.add(prefix(rest, index), local))), addition_associative(base, length, Nat.add(prefix(rest, index), local))))

def first_precedes_later(+length: Nat, +rest: List<&2, Nat>, +later: Nat,
  +base: Nat, +first_local: Nat, +later_local: Nat,
  inside: {Nat.is_lt(first_local, length) == True{} : Bool}) ->
  {Nat.is_lt(clock(Con{length, rest}, 0n, base, first_local), clock(Con{length, rest}, 1n+later, base, later_local)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.add(length, prefix(rest, later)), later_local), Nat.add(length, Nat.add(prefix(rest, later), later_local)),
    addition_associative(length, prefix(rest, later), later_local)) :
      {Nat.is_lt(Nat.add(base, first_local), Nat.add(base, _)) == True{} : Bool}
  adding_prefix_preserves_strict_order(base, first_local, Nat.add(length, Nat.add(prefix(rest, later), later_local)),
    strict_right_extension(first_local, length, Nat.add(prefix(rest, later), later_local), inside))

def transport_strict(-a: Nat, -b: Nat, -c: Nat, -d: Nat,
  left: {a == c : Nat}, right: {b == d : Nat}, strict: {Nat.is_lt(c, d) == True{} : Bool}) ->
  {Nat.is_lt(a, b) == True{} : Bool}:
  %Equal.sym(Nat, a, c, left) : {Nat.is_lt(_, b) == True{} : Bool}
  %Equal.sym(Nat, b, d, right) : {Nat.is_lt(c, _) == True{} : Bool}
  strict

law every_local_event_precedes_all_later_blocks:
  for +lengths: List<&2, Nat>
  for first: Nat
  for later: Nat
  for +base: Nat
  for +first_local: Nat
  for +later_local: Nat
  for valid: Local(lengths, first, first_local)
  for ordered: {Nat.is_lt(first, later) == True{} : Bool}
  {Nat.is_lt(clock(lengths, first, base, first_local), clock(lengths, later, base, later_local)) == True{} : Bool}
def every_local_event_precedes_all_later_blocks(lengths, first, later, base, first_local, later_local, valid, ordered):
  match lengths first later:
    case Nil{} _ _: L.ex_false({Nat.is_lt(Nat.add(base, first_local), Nat.add(base, later_local)) == True{} : Bool}, valid)
    case Con{length, rest} 0n 0n:
      F.absurd_boolean({Nat.is_lt(clock(Con{length, rest}, 0n, base, first_local), clock(Con{length, rest}, 0n, base, later_local)) == True{} : Bool}, ordered)
    case Con{length, rest} 0n 1n+k: first_precedes_later(length, rest, k, base, first_local, later_local, valid)
    case Con{length, rest} 1n+k 0n:
      F.absurd_boolean({Nat.is_lt(clock(Con{length, rest}, 1n+k, base, first_local), clock(Con{length, rest}, 0n, base, later_local)) == True{} : Bool}, ordered)
    case Con{+length, +rest} Succ{+k} Succ{+j}:
      transport_strict(clock(Con{length, rest}, 1n+k, base, first_local), clock(Con{length, rest}, 1n+j, base, later_local),
        clock(rest, k, Nat.add(base, length), first_local), clock(rest, j, Nat.add(base, length), later_local),
        next_block_adds_exact_previous_block_length(length, rest, k, base, first_local),
        next_block_adds_exact_previous_block_length(length, rest, j, base, later_local),
        every_local_event_precedes_all_later_blocks(rest, k, j, Nat.add(base, length), first_local, later_local, valid, ordered))

law within_block_order_is_preserved:
  for +lengths: List<&2, Nat>
  for +index: Nat
  for +base: Nat
  for +a: Nat
  for +b: Nat
  for ordered: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(clock(lengths, index, base, a), clock(lengths, index, base, b)) == True{} : Bool}
def within_block_order_is_preserved(lengths, index, base, a, b, ordered):
  adding_prefix_preserves_strict_order(base, Nat.add(prefix(lengths, index), a), Nat.add(prefix(lengths, index), b),
    adding_prefix_preserves_strict_order(prefix(lengths, index), a, b, ordered))

def previous(n: Nat) -> Nat:
  match n:
    case 0n: 0n
    case 1n+k: k

def cancel_prefix(base: Nat, +a: Nat, +b: Nat,
  same: {Nat.add(base, a) == Nat.add(base, b) : Nat}) -> {a == b : Nat}:
  match base:
    case 0n: same
    case 1n+k:
      cancel_prefix(k, a, b, Equal.cong(Nat, Nat, q => previous(q), Succ{Nat.add(k, a)}, Succ{Nat.add(k, b)}, same))

law strict_order_is_irreflexive:
  for n: Nat
  {Nat.is_lt(n, n) == False{} : Bool}
def strict_order_is_irreflexive(n):
  match n:
    case 0n: {==}
    case 1n+k: strict_order_is_irreflexive(k)

def strict_not_equal(+a: Nat, -b: Nat, strict: {Nat.is_lt(a, b) == True{} : Bool}, same: {a == b : Nat}) -> Empty:
  F.false_negative_true(Equal.trans(Bool, False{}, Nat.is_lt(a, a), True{},
    Equal.sym(Bool, Nat.is_lt(a, a), False{}, strict_order_is_irreflexive(a)),
    (%Equal.sym(Nat, a, b, same) : {Nat.is_lt(a, _) == True{} : Bool} strict)))

def transport_equal(-a: Nat, -b: Nat, -c: Nat, -d: Nat,
  left: {a == c : Nat}, right: {b == d : Nat}, same: {a == b : Nat}) -> {c == d : Nat}:
  Equal.trans(Nat, c, a, d, Equal.sym(Nat, a, c, left), Equal.trans(Nat, a, b, d, same, right))

def lift_injective(-a: Nat, -b: Nat, -x: Nat, -y: Nat,
  equal: L.E<{a == b : Nat}, {x == y : Nat}>) -> L.E<{1n+a == 1n+b : Nat}, {x == y : Nat}>:
  match equal:
    case L.Both{indices, locals}: L.Both{Equal.cong(Nat, Nat, q => Succ{q}, a, b, indices), locals}

law bounded_phase_events_have_injective_global_times:
  for +lengths: List<&2, Nat>
  for first: Nat
  for later: Nat
  for +base: Nat
  for +first_local: Nat
  for +later_local: Nat
  for first_valid: Local(lengths, first, first_local)
  for later_valid: Local(lengths, later, later_local)
  for same: {clock(lengths, first, base, first_local) == clock(lengths, later, base, later_local) : Nat}
  L.E<{first == later : Nat}, {first_local == later_local : Nat}>
def bounded_phase_events_have_injective_global_times(lengths, first, later, base, first_local, later_local, first_valid, later_valid, same):
  match lengths first later:
    case Nil{} _ _: L.ex_false(L.E<{first == later : Nat}, {first_local == later_local : Nat}>, first_valid)
    case Con{length, rest} 0n 0n: L.Both{{==}, cancel_prefix(base, first_local, later_local, same)}
    case Con{+length, +rest} 0n Succ{+k}:
      L.ex_false(L.E<{0n == 1n+k : Nat}, {first_local == later_local : Nat}>,
        strict_not_equal(clock(Con{length, rest}, 0n, base, first_local), clock(Con{length, rest}, 1n+k, base, later_local),
          first_precedes_later(length, rest, k, base, first_local, later_local, first_valid), same))
    case Con{+length, +rest} Succ{+k} 0n:
      L.ex_false(L.E<{1n+k == 0n : Nat}, {first_local == later_local : Nat}>,
        strict_not_equal(clock(Con{length, rest}, 0n, base, later_local), clock(Con{length, rest}, 1n+k, base, first_local),
          first_precedes_later(length, rest, k, base, later_local, first_local, later_valid),
          Equal.sym(Nat, clock(Con{length, rest}, 1n+k, base, first_local), clock(Con{length, rest}, 0n, base, later_local), same)))
    case Con{+length, +rest} Succ{+k} Succ{+j}:
      lift_injective(k, j, first_local, later_local,
        bounded_phase_events_have_injective_global_times(rest, k, j, Nat.add(base, length), first_local, later_local, first_valid, later_valid,
          transport_equal(clock(Con{length, rest}, 1n+k, base, first_local), clock(Con{length, rest}, 1n+j, base, later_local),
            clock(rest, k, Nat.add(base, length), first_local), clock(rest, j, Nat.add(base, length), later_local),
            next_block_adds_exact_previous_block_length(length, rest, k, base, first_local),
            next_block_adds_exact_previous_block_length(length, rest, j, base, later_local), same)))
