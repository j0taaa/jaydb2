# Pure finite-list algorithms over obtained values. No database access.
import Base
import ../contract/Data.bend as D

def include(b: Bool, x: D.Value, tail: List<&2, D.Value>) -> List<&2, D.Value>:
  match b:
    case True{}: Con{x, tail}
    case False{}: tail

def filter(~keep: D.Value -> Bool, xs: List<&2, D.Value>) -> List<&2, D.Value>:
  match xs:
    case Nil{}: Nil{}
    case Con{+x, rest}: include(keep(x), x, filter(~keep, rest))

def take(n: Nat, xs: List<&2, D.Value>) -> List<&2, D.Value>:
  match n xs:
    case Succ{m} Con{x, rest}: Con{x, take(m, rest)}
    case _ _: Nil{}

def drop(n: Nat, xs: List<&2, D.Value>) -> List<&2, D.Value>:
  match n xs:
    case Succ{m} Con{x, rest}: drop(m, rest)
    case _ xs: xs

def page(offset: Nat, size: Nat, xs: List<&2, D.Value>) -> List<&2, D.Value>:
  take(size, drop(offset, xs))

# Stable insertion sort. less must be a strict order for sortedness.
def insert(~less: D.Value -> D.Value -> Bool, +x: D.Value, xs: List<&2, D.Value>) -> List<&2, D.Value>:
  match xs:
    case Nil{}: [x]
    case Con{+h, +rest}:
      Bool.pick(List<&2, D.Value>, Bool.not(less(h, x)), Con{x, Con{h, rest}}, Con{h, insert(~less, x, rest)})

def sort(~less: D.Value -> D.Value -> Bool, xs: List<&2, D.Value>) -> List<&2, D.Value>:
  match xs:
    case Nil{}: Nil{}
    case Con{x, rest}: insert(~less, x, sort(~less, rest))

type Group is Data:
  Group{key: String, items: List<&2, D.Value>}

# Insert into existing matching group or append a new group.
def group_insert(+key: String, +x: D.Value, gs: List<&2, Group>) -> List<&2, Group>:
  match gs:
    case Nil{}: [Group{key, [x]}]
    case Con{Group{+k, +items}, +rest}:
      Bool.pick(List<&2, Group>, String.eq(key, k),
        Con{Group{k, Con{x, items}}, rest}, Con{Group{k, items}, group_insert(key, x, rest)})

# Right fold gives group order by last occurrence, items in input order.
# Use sort first if a particular group ordering is desired.
def group(~key: D.Value -> String, xs: List<&2, D.Value>) -> List<&2, Group>:
  match xs:
    case Nil{}: Nil{}
    case Con{+x, rest}: group_insert(key(x), x, group(~key, rest))

def values(xs: List<&2, D.Value>) -> D.Value:
  match xs:
    case Nil{}: D.VListEmpty{}
    case Con{x, rest}: D.VList{x, values(rest)}

def length(xs: List<&2, D.Value>) -> Nat:
  match xs:
    case Nil{}: 0n
    case Con{x, rest}: Succ{length(rest)}

def insert_length_choice(~less: D.Value -> D.Value -> Bool, b: Bool, +x: D.Value, +h: D.Value,
  +rest: List<&2, D.Value>, rec: {length(insert(~less, x, rest)) == Succ{length(rest)} : Nat}) ->
  {length(Bool.pick(List<&2, D.Value>, b, Con{x, Con{h, rest}}, Con{h, insert(~less, x, rest)})) == Succ{Succ{length(rest)}} : Nat}:
  match b:
    case True{}: {==}
    case False{}: Equal.cong(Nat, Nat, n => Succ{n}, length(insert(~less, x, rest)), Succ{length(rest)}, rec)


law insert_length:
  for ~less: D.Value -> D.Value -> Bool
  for +x: D.Value
  for xs: List<&2, D.Value>
  {length(insert(~less, x, xs)) == Succ{length(xs)} : Nat}
def insert_length(less, x, xs):
  match xs:
    case Nil{}: {==}
    case Con{+h, +rest}:
      insert_length_choice(~less, Bool.not(less(h, x)), x, h, rest, insert_length(~less, x, rest))

law sort_length:
  for ~less: D.Value -> D.Value -> Bool
  for +xs: List<&2, D.Value>
  {length(sort(~less, xs)) == length(xs) : Nat}
def sort_length(less, xs):
  match xs:
    case Nil{}: {==}
    case Con{+x, +rest}:
      Equal.trans(Nat, length(insert(~less, x, sort(~less, rest))), Succ{length(sort(~less, rest))}, Succ{length(rest)},
        insert_length(~less, x, sort(~less, rest)), Equal.cong(Nat, Nat, n => Succ{n}, length(sort(~less, rest)), length(rest), sort_length(~less, rest)))

law take_all:
  for +xs: List<&2, D.Value>
  {take(length(xs), xs) == xs : List<&2, D.Value>}
def take_all(xs):
  match xs:
    case Nil{}: {==}
    case Con{+x, +rest}:
      Equal.cong(List<&2, D.Value>, List<&2, D.Value>, t => Con{x, t}, take(length(rest), rest), rest, take_all(rest))

law drop_all:
  for +xs: List<&2, D.Value>
  {drop(length(xs), xs) == Nil{} : List<&2, D.Value>}
def drop_all(xs):
  match xs:
    case Nil{}: {==}
    case Con{x, rest}: drop_all(rest)

law first_page:
  for n: Nat
  for xs: List<&2, D.Value>
  {page(0n, n, xs) == take(n, xs) : List<&2, D.Value>}
def first_page(n, xs): {==}
