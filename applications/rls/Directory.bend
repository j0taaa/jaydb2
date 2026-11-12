# Exact directory algebra over the ACTUAL row upserts, removals and table swaps.
import Base
import ./Data.bend as D
import ./Logic.bend as L
import ./Policy.bend as P
import ./Ownership.bend as O
import ./Orders.bend as Ord
import ./RowLookupProofs.bend as RL
import ./RowRemovalLookupProofs.bend as RR
import ./CollectionFrameProofs.bend as Frame
import ./MutationStateShapeProofs.bend as Shape

def cast(+p: String, -ds: List<&2, D.Row>, -ds2: List<&2, D.Row>, -ns: List<&2, D.Row>, -ns2: List<&2, D.Row>,
  ed: {ds == ds2 : List<&2, D.Row>}, en: {ns == ns2 : List<&2, D.Row>}, h: P.Agree(p, ds, ns)) -> P.Agree(p, ds2, ns2):
  %ed : P.Agree(p, _, ns2)
  %en : P.Agree(p, ds, _)
  h

# Under the every-prefix ownership law, a note at k belongs to key_owner(k).
def not_owned_row(b: Bool, +us: List<&2, D.Row>, +name: String, +rk: String, +rfs: List<&2, D.Field>,
  +t: List<&2, D.Row>, +k: String, +q: String, e: {String.eq(rk, k) == b : Bool},
  hr: P.Owner(us, name, D.Row{rk, rfs}), foreign: {String.eq(P.key_owner(k), q) == False{} : Bool},
  rest: {P.owned(q, t, k) == False{} : Bool}) ->
  {P.row_owner(Bool.pick(Maybe<&2, D.Row>, b, Some{D.Row{rk, rfs}}, D.find_row(t, k)), q) == False{} : Bool}:
  match b:
    case True{}:
      P.Both{valid, P.Both{field, registered}} = hr
      %Equal.sym(Maybe<&2, D.Value>, D.find_field(rfs, "owner"), Some{D.VText{P.key_owner(rk)}}, field) : {P.owner_is(_, q) == False{} : Bool}
      %Equal.sym(String, rk, k, Ord.string_equal(rk, k, e)) : {String.eq(P.key_owner(_), q) == False{} : Bool}
      foreign
    case False{}: rest

def not_owned(ns: List<&2, D.Row>, +us: List<&2, D.Row>, +name: String, +k: String, +q: String,
  h: P.Rows(us, name, ns), +foreign: {String.eq(P.key_owner(k), q) == False{} : Bool}) ->
  {P.owned(q, ns, k) == False{} : Bool}:
  match ns:
    case Nil{}: {==}
    case Con{D.Row{+rk, +rfs}, +t}:
      P.Both{hr, ht} = h
      not_owned_row(String.eq(rk, k), us, name, rk, rfs, t, k, q, {==}, hr, foreign, not_owned(t, us, name, k, q, ht, foreign))

def save_key(b: Bool, +p: String, +ds: List<&2, D.Row>, +ns: List<&2, D.Row>, +id: String,
  +nfs: List<&2, D.Field>, +dfs: List<&2, D.Field>, +k: String, +e: {String.eq(id, k) == b : Bool},
  own: {P.owner_is(D.find_field(nfs, "owner"), p) == True{} : Bool}, h: P.Agree(p, ds, ns)) ->
  {P.listed(D.insert_row(ds, D.Row{id, dfs}), k) == P.owned(p, D.insert_row(ns, D.Row{id, nfs}), k) : Bool}:
  match b:
    case True{}:
      %Ord.string_equal(id, k, e) : {P.listed(D.insert_row(ds, D.Row{id, dfs}), _) == P.owned(p, D.insert_row(ns, D.Row{id, nfs}), _) : Bool}
      Equal.trans(Bool, P.listed(D.insert_row(ds, D.Row{id, dfs}), id), True{}, P.owned(p, D.insert_row(ns, D.Row{id, nfs}), id),
        Equal.cong(Maybe<&2, D.Row>, Bool, m => D.exists_row(m), D.find_row(D.insert_row(ds, D.Row{id, dfs}), id), Some{D.Row{id, dfs}},
          RL.an_actual_upsert_exposes_exactly_the_new_row_at_its_own_key(ds, D.Row{id, dfs})),
        Equal.sym(Bool, P.owned(p, D.insert_row(ns, D.Row{id, nfs}), id), True{},
          Equal.trans(Bool, P.owned(p, D.insert_row(ns, D.Row{id, nfs}), id), P.row_owner(Some{D.Row{id, nfs}}, p), True{},
            Equal.cong(Maybe<&2, D.Row>, Bool, m => P.row_owner(m, p), D.find_row(D.insert_row(ns, D.Row{id, nfs}), id), Some{D.Row{id, nfs}},
              RL.an_actual_upsert_exposes_exactly_the_new_row_at_its_own_key(ns, D.Row{id, nfs})), own)))
    case False{}:
      Equal.trans(Bool, P.listed(D.insert_row(ds, D.Row{id, dfs}), k), P.listed(ds, k), P.owned(p, D.insert_row(ns, D.Row{id, nfs}), k),
        Equal.cong(Maybe<&2, D.Row>, Bool, m => D.exists_row(m), D.find_row(D.insert_row(ds, D.Row{id, dfs}), k), D.find_row(ds, k),
          RL.an_actual_upsert_preserves_every_other_exact_key_lookup(ds, D.Row{id, dfs}, k, e)),
        Equal.trans(Bool, P.listed(ds, k), P.owned(p, ns, k), P.owned(p, D.insert_row(ns, D.Row{id, nfs}), k), h(k),
          Equal.sym(Bool, P.owned(p, D.insert_row(ns, D.Row{id, nfs}), k), P.owned(p, ns, k),
            Equal.cong(Maybe<&2, D.Row>, Bool, m => P.row_owner(m, p), D.find_row(D.insert_row(ns, D.Row{id, nfs}), k), D.find_row(ns, k),
              RL.an_actual_upsert_preserves_every_other_exact_key_lookup(ns, D.Row{id, nfs}, k, e)))))

def remove_key(b: Bool, +p: String, +ds: List<&2, D.Row>, +ns: List<&2, D.Row>, +id: String, +k: String,
  +e: {String.eq(id, k) == b : Bool}, h: P.Agree(p, ds, ns)) ->
  {P.listed(D.remove_row(ds, id), k) == P.owned(p, D.remove_row(ns, id), k) : Bool}:
  match b:
    case True{}:
      %Ord.string_equal(id, k, e) : {P.listed(D.remove_row(ds, id), _) == P.owned(p, D.remove_row(ns, id), _) : Bool}
      Equal.trans(Bool, P.listed(D.remove_row(ds, id), id), False{}, P.owned(p, D.remove_row(ns, id), id),
        Equal.cong(Maybe<&2, D.Row>, Bool, m => D.exists_row(m), D.find_row(D.remove_row(ds, id), id), None{},
          RR.actual_row_removal_excludes_every_occurrence_of_its_own_key(ds, id)),
        Equal.sym(Bool, P.owned(p, D.remove_row(ns, id), id), False{},
          Equal.cong(Maybe<&2, D.Row>, Bool, m => P.row_owner(m, p), D.find_row(D.remove_row(ns, id), id), None{},
            RR.actual_row_removal_excludes_every_occurrence_of_its_own_key(ns, id))))
    case False{}:
      Equal.trans(Bool, P.listed(D.remove_row(ds, id), k), P.listed(ds, k), P.owned(p, D.remove_row(ns, id), k),
        Equal.cong(Maybe<&2, D.Row>, Bool, m => D.exists_row(m), D.find_row(D.remove_row(ds, id), k), D.find_row(ds, k),
          RR.actual_row_removal_preserves_every_other_exact_key_lookup(ds, id, k, e)),
        Equal.trans(Bool, P.listed(ds, k), P.owned(p, ns, k), P.owned(p, D.remove_row(ns, id), k), h(k),
          Equal.sym(Bool, P.owned(p, D.remove_row(ns, id), k), P.owned(p, ns, k),
            Equal.cong(Maybe<&2, D.Row>, Bool, m => P.row_owner(m, p), D.find_row(D.remove_row(ns, id), k), D.find_row(ns, k),
              RR.actual_row_removal_preserves_every_other_exact_key_lookup(ns, id, k, e)))))

# The other principal's directory is untouched; the changed id was never theirs.
def other_key(b: Bool, +q: String, +ds: List<&2, D.Row>, +ns: List<&2, D.Row>, -ns2: List<&2, D.Row>,
  +id: String, +k: String, +e: {String.eq(id, k) == b : Bool}, at: {P.owned(q, ns2, id) == False{} : Bool},
  away: {String.eq(id, k) == False{} : Bool} -> {P.owned(q, ns2, k) == P.owned(q, ns, k) : Bool},
  before: {P.owned(q, ns, id) == False{} : Bool}, h: P.Agree(q, ds, ns)) ->
  {P.listed(ds, k) == P.owned(q, ns2, k) : Bool}:
  match b:
    case True{}:
      %Ord.string_equal(id, k, e) : {P.listed(ds, _) == P.owned(q, ns2, _) : Bool}
      Equal.trans(Bool, P.listed(ds, id), False{}, P.owned(q, ns2, id),
        Equal.trans(Bool, P.listed(ds, id), P.owned(q, ns, id), False{}, h(id), before),
        Equal.sym(Bool, P.owned(q, ns2, id), False{}, at))
    case False{}:
      Equal.trans(Bool, P.listed(ds, k), P.owned(q, ns, k), P.owned(q, ns2, k), h(k),
        Equal.sym(Bool, P.owned(q, ns2, k), P.owned(q, ns, k), away(e)))

def save_same(+p: String, +ds: List<&2, D.Row>, +ns: List<&2, D.Row>, +id: String,
  +nfs: List<&2, D.Field>, +dfs: List<&2, D.Field>,
  +own: {P.owner_is(D.find_field(nfs, "owner"), p) == True{} : Bool}, h: P.Agree(p, ds, ns)) ->
  P.Agree(p, D.insert_row(ds, D.Row{id, dfs}), D.insert_row(ns, D.Row{id, nfs})):
  +k => save_key(String.eq(id, k), p, ds, ns, id, nfs, dfs, k, {==}, own, h)

def remove_same(+p: String, +ds: List<&2, D.Row>, +ns: List<&2, D.Row>, +id: String, h: P.Agree(p, ds, ns)) ->
  P.Agree(p, D.remove_row(ds, id), D.remove_row(ns, id)):
  +k => remove_key(String.eq(id, k), p, ds, ns, id, k, {==}, h)

def save_other(+q: String, +ds: List<&2, D.Row>, +ns: List<&2, D.Row>, +id: String, +nfs: List<&2, D.Field>,
  +us: List<&2, D.Row>, +name: String, +rows: P.Rows(us, name, ns),
  +own: {P.owner_is(D.find_field(nfs, "owner"), q) == False{} : Bool},
  +foreign: {String.eq(P.key_owner(id), q) == False{} : Bool}, h: P.Agree(q, ds, ns)) ->
  P.Agree(q, ds, D.insert_row(ns, D.Row{id, nfs})):
  +k => other_key(String.eq(id, k), q, ds, ns, D.insert_row(ns, D.Row{id, nfs}), id, k, {==},
    Equal.trans(Bool, P.owned(q, D.insert_row(ns, D.Row{id, nfs}), id), P.row_owner(Some{D.Row{id, nfs}}, q), False{},
      Equal.cong(Maybe<&2, D.Row>, Bool, m => P.row_owner(m, q), D.find_row(D.insert_row(ns, D.Row{id, nfs}), id), Some{D.Row{id, nfs}},
        RL.an_actual_upsert_exposes_exactly_the_new_row_at_its_own_key(ns, D.Row{id, nfs})), own),
    d => Equal.cong(Maybe<&2, D.Row>, Bool, m => P.row_owner(m, q), D.find_row(D.insert_row(ns, D.Row{id, nfs}), k), D.find_row(ns, k),
      RL.an_actual_upsert_preserves_every_other_exact_key_lookup(ns, D.Row{id, nfs}, k, d)),
    not_owned(ns, us, name, id, q, rows, foreign), h)

def remove_other(+q: String, +ds: List<&2, D.Row>, +ns: List<&2, D.Row>, +id: String,
  +us: List<&2, D.Row>, +name: String, +rows: P.Rows(us, name, ns),
  +foreign: {String.eq(P.key_owner(id), q) == False{} : Bool}, h: P.Agree(q, ds, ns)) ->
  P.Agree(q, ds, D.remove_row(ns, id)):
  +k => other_key(String.eq(id, k), q, ds, ns, D.remove_row(ns, id), id, k, {==},
    Equal.cong(Maybe<&2, D.Row>, Bool, m => P.row_owner(m, q), D.find_row(D.remove_row(ns, id), id), None{},
      RR.actual_row_removal_excludes_every_occurrence_of_its_own_key(ns, id)),
    d => Equal.cong(Maybe<&2, D.Row>, Bool, m => P.row_owner(m, q), D.find_row(D.remove_row(ns, id), k), D.find_row(ns, k),
      RR.actual_row_removal_preserves_every_other_exact_key_lookup(ns, id, k, d)),
    not_owned(ns, us, name, id, q, rows, foreign), h)

# State-level frame: which table views a swap changes, and which it keeps.
def notes_rows(+s: D.State, +ns: List<&2, D.Row>,
  found: {D.rows_collection(D.Application{"notes"}, s) == Some{ns} : Maybe<&2, List<&2, D.Row>>},
  owners: P.Owners(s)) -> P.Rows(O.users(s), "notes", ns):
  match s:
    case D.State{+ts, +us}:
      %found : O.Found(us, "notes", _)
      O.find_preserves(us, ts, "notes", owners)

def found_rows(+name: String, +s: D.State, +prev: List<&2, D.Row>,
  found: {D.rows_collection(D.Application{name}, s) == Some{prev} : Maybe<&2, List<&2, D.Row>>}) ->
  {P.rows(name, s) == prev : List<&2, D.Row>}:
  Equal.cong(Maybe<&2, List<&2, D.Row>>, List<&2, D.Row>, m => P.view(m), D.rows_collection(D.Application{name}, s), Some{prev}, found)

def swapped(+name: String, +s: D.State, +prev: List<&2, D.Row>, +repl: List<&2, D.Row>,
  found: {D.rows_collection(D.Application{name}, s) == Some{prev} : Maybe<&2, List<&2, D.Row>>}) ->
  {P.rows(name, D.swap_collection(D.Application{name}, s, repl)) == repl : List<&2, D.Row>}:
  Equal.cong(Maybe<&2, List<&2, D.Row>>, List<&2, D.Row>, m => P.view(m),
    D.rows_collection(D.Application{name}, D.swap_collection(D.Application{name}, s, repl)), Some{repl},
    Frame.replacing_an_existing_collection_has_the_exact_new_row_view(D.Application{name}, s, prev, repl, found))

def framed(+target: String, +watched: String, +s: D.State, +repl: List<&2, D.Row>,
  sep: {String.eq(target, watched) == False{} : Bool}) ->
  {P.rows(watched, D.swap_collection(D.Application{target}, s, repl)) == P.rows(watched, s) : List<&2, D.Row>}:
  Equal.cong(Maybe<&2, List<&2, D.Row>>, List<&2, D.Row>, m => P.view(m),
    D.rows_collection(D.Application{watched}, D.swap_collection(D.Application{target}, s, repl)),
    D.rows_collection(D.Application{watched}, s),
    Frame.replacing_a_collection_preserves_every_separate_collection_view(D.Application{target}, D.Application{watched}, s, repl, sep))

def first(s: D.State, tn: Shape.Transform, ns: List<&2, D.Row>) -> D.State:
  D.swap_collection(D.Application{"notes"}, s, Shape.apply(tn, ns))

def second(p: String, s: D.State, tn: Shape.Transform, ns: List<&2, D.Row>, td: Shape.Transform, ds: List<&2, D.Row>) -> D.State:
  D.swap_collection(D.Application{P.dir_name(p)}, first(s, tn, ns), Shape.apply(td, ds))

# A note change followed by the matching change of p's own directory.
def pair(+p: String, +q: String, +s: D.State, +tn: Shape.Transform, +td: Shape.Transform,
  +ns: List<&2, D.Row>, +ds: List<&2, D.Row>,
  +found1: {D.rows_collection(D.Application{"notes"}, s) == Some{ns} : Maybe<&2, List<&2, D.Row>>},
  +found2: {D.rows_collection(D.Application{P.dir_name(p)}, first(s, tn, ns)) == Some{ds} : Maybe<&2, List<&2, D.Row>>},
  pn: {String.eq(P.dir_name(p), "notes") == False{} : Bool}, np: {String.eq("notes", P.dir_name(p)) == False{} : Bool},
  nq: {String.eq("notes", P.dir_name(q)) == False{} : Bool}, pq: {String.eq(P.dir_name(p), P.dir_name(q)) == False{} : Bool},
  same: P.Agree(p, ds, ns) -> P.Agree(p, Shape.apply(td, ds), Shape.apply(tn, ns)),
  other: P.Agree(q, P.rows(P.dir_name(q), s), ns) -> P.Agree(q, P.rows(P.dir_name(q), s), Shape.apply(tn, ns)),
  hp: P.Agree(p, P.rows(P.dir_name(p), s), P.rows("notes", s)),
  hq: P.Agree(q, P.rows(P.dir_name(q), s), P.rows("notes", s))) ->
  L.E<P.Agree(p, P.rows(P.dir_name(p), second(p, s, tn, ns, td, ds)), P.rows("notes", second(p, s, tn, ns, td, ds))),
    P.Agree(q, P.rows(P.dir_name(q), second(p, s, tn, ns, td, ds)), P.rows("notes", second(p, s, tn, ns, td, ds)))>:
  +en = found_rows("notes", s, ns, found1)
  +ed = found_rows(P.dir_name(p), s, ds,
    Equal.trans(Maybe<&2, List<&2, D.Row>>, D.rows_collection(D.Application{P.dir_name(p)}, s),
      D.rows_collection(D.Application{P.dir_name(p)}, first(s, tn, ns)), Some{ds},
      Equal.sym(Maybe<&2, List<&2, D.Row>>, D.rows_collection(D.Application{P.dir_name(p)}, first(s, tn, ns)),
        D.rows_collection(D.Application{P.dir_name(p)}, s),
        Frame.replacing_a_collection_preserves_every_separate_collection_view(D.Application{"notes"}, D.Application{P.dir_name(p)}, s, Shape.apply(tn, ns), np)),
      found2))
  +n2 = Equal.trans(List<&2, D.Row>, P.rows("notes", second(p, s, tn, ns, td, ds)), P.rows("notes", first(s, tn, ns)), Shape.apply(tn, ns),
    framed(P.dir_name(p), "notes", first(s, tn, ns), Shape.apply(td, ds), pn),
    swapped("notes", s, ns, Shape.apply(tn, ns), found1))
  +d2 = swapped(P.dir_name(p), first(s, tn, ns), ds, Shape.apply(td, ds), found2)
  +q2 = Equal.trans(List<&2, D.Row>, P.rows(P.dir_name(q), second(p, s, tn, ns, td, ds)), P.rows(P.dir_name(q), first(s, tn, ns)), P.rows(P.dir_name(q), s),
    framed(P.dir_name(p), P.dir_name(q), first(s, tn, ns), Shape.apply(td, ds), pq),
    framed("notes", P.dir_name(q), s, Shape.apply(tn, ns), nq))
  L.Both{
    cast(p, Shape.apply(td, ds), P.rows(P.dir_name(p), second(p, s, tn, ns, td, ds)), Shape.apply(tn, ns), P.rows("notes", second(p, s, tn, ns, td, ds)),
      Equal.sym(List<&2, D.Row>, P.rows(P.dir_name(p), second(p, s, tn, ns, td, ds)), Shape.apply(td, ds), d2),
      Equal.sym(List<&2, D.Row>, P.rows("notes", second(p, s, tn, ns, td, ds)), Shape.apply(tn, ns), n2),
      same(cast(p, P.rows(P.dir_name(p), s), ds, P.rows("notes", s), ns, ed, en, hp))),
    cast(q, P.rows(P.dir_name(q), s), P.rows(P.dir_name(q), second(p, s, tn, ns, td, ds)), Shape.apply(tn, ns), P.rows("notes", second(p, s, tn, ns, td, ds)),
      Equal.sym(List<&2, D.Row>, P.rows(P.dir_name(q), second(p, s, tn, ns, td, ds)), P.rows(P.dir_name(q), s), q2),
      Equal.sym(List<&2, D.Row>, P.rows("notes", second(p, s, tn, ns, td, ds)), Shape.apply(tn, ns), n2),
      other(cast(q, P.rows(P.dir_name(q), s), P.rows(P.dir_name(q), s), P.rows("notes", s), ns, {==}, en, hq)))}
