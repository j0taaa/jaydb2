# Instance-local prepared metadata. These functions describe registry changes;
# their Boolean inputs do not prove authentication, checking, or file integrity.
# The extended laws separately bind those inputs to their actual meanings.
import Base
import ./Logic.bend as L

type Entry is Data:
  Entry{instance: String, handle: String, code: String, proof: String,
    read_only: Bool, seal: String}

def instance(e: Entry) -> String:
  Entry{i, h, c, p, r, s} = e
  i

def handle(e: Entry) -> String:
  Entry{i, h, c, p, r, s} = e
  h

def code(e: Entry) -> String:
  Entry{i, h, c, p, r, s} = e
  c

def proof(e: Entry) -> String:
  Entry{i, h, c, p, r, s} = e
  p

def read_only(e: Entry) -> Bool:
  Entry{i, h, c, p, r, s} = e
  r

def seal(e: Entry) -> String:
  Entry{i, h, c, p, r, s} = e
  s

def matches(i: String, h: String, e: Entry) -> Bool:
  Entry{ei, eh, c, p, r, s} = e
  String.eq(i, ei) && String.eq(h, eh)

def lookup(+i: String, +h: String, entries: List<&2, Entry>) -> Maybe<&2, Entry>:
  match entries:
    case Nil{}: None{}
    case Con{+entry, rest}:
      Bool.pick(Maybe<&2, Entry>, matches(i, h, entry), Some{entry}, lookup(i, h, rest))

type Resolution is Data:
  Unauthorized{}
  Missing{}
  Resolved{entry: Entry}

def resolve_result(found: Maybe<&2, Entry>) -> Resolution:
  match found:
    case None{}: Missing{}
    case Some{entry}: Resolved{entry}

def resolve(authenticated: Bool, i: String, h: String, entries: List<&2, Entry>) -> Resolution:
  match authenticated:
    case False{}: Unauthorized{}
    case True{}: resolve_result(lookup(i, h, entries))

# Removal filters every matching entry, including a malformed duplicate.
def remove(+i: String, +h: String, entries: List<&2, Entry>) -> List<&2, Entry>:
  match entries:
    case Nil{}: Nil{}
    case Con{+entry, +rest}:
      Bool.pick(List<&2, Entry>, matches(i, h, entry), remove(i, h, rest), Con{entry, remove(i, h, rest)})

def invalidate(authenticated: Bool, i: String, h: String, entries: List<&2, Entry>) -> List<&2, Entry>:
  match authenticated:
    case False{}: entries
    case True{}: remove(i, h, entries)

# Scope includes the complete instance/handle match. Nothing overwrites an
# existing entry, and successful insertion retains every original field.
def insert_fresh(found: Maybe<&2, Entry>, entry: Entry, +entries: List<&2, Entry>) -> List<&2, Entry>:
  match found:
    case None{}: Con{entry, entries}
    case Some{previous}: entries

def insert(authenticated: Bool, +i: String, +entry: Entry, +entries: List<&2, Entry>) -> List<&2, Entry>:
  Bool.pick(List<&2, Entry>, authenticated && matches(i, handle(entry), entry),
    insert_fresh(lookup(i, handle(entry), entries), entry, entries), entries)

def false_negative_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : Bool.pick(Type, _, Empty, Unit)
  Unit{}

def found(result: Maybe<&2, Entry>) -> Bool:
  match result:
    case None{}: False{}
    case Some{entry}: True{}

def none_negative_some(-entry: Entry,
  e: {None{} == Some{entry} : Maybe<&2, Entry>}) -> Empty:
  false_negative_true(Equal.cong(Maybe<&2, Entry>, Bool, found, None{}, Some{entry}, e))

def choose(result: Maybe<&2, Entry>, fallback: Entry) -> Entry:
  match result:
    case None{}: fallback
    case Some{entry}: entry

def some_injective(+left: Entry, -right: Entry,
  e: {Some{left} == Some{right} : Maybe<&2, Entry>}) -> {left == right : Entry}:
  Equal.cong(Maybe<&2, Entry>, Entry, result => choose(result, left), Some{left}, Some{right}, e)

def resolved(result: Resolution) -> Bool:
  match result:
    case Resolved{entry}: True{}
    case _: False{}

def resolution_entry(result: Resolution, fallback: Entry) -> Entry:
  match result:
    case Resolved{entry}: entry
    case _: fallback

def resolve_result_origin(result: Maybe<&2, Entry>, +entry: Entry,
  same: {resolve_result(result) == Resolved{entry} : Resolution}) ->
  {result == Some{entry} : Maybe<&2, Entry>}:
  match result:
    case None{}:
      L.ex_false({None{} == Some{entry} : Maybe<&2, Entry>},
        false_negative_true(Equal.cong(Resolution, Bool, resolved, Missing{}, Resolved{entry}, same)))
    case Some{+original}:
      Equal.cong(Entry, Maybe<&2, Entry>, e => Some{e}, original, entry,
        Equal.cong(Resolution, Entry, result => resolution_entry(result, entry), Resolved{original}, Resolved{entry}, same))

law resolved_entry_requires_authentication_and_exact_lookup:
  for authenticated: Bool
  for i: String
  for h: String
  for entries: List<&2, Entry>
  for +entry: Entry
  for same: {resolve(authenticated, i, h, entries) == Resolved{entry} : Resolution}
  L.E<{authenticated == True{} : Bool}, {lookup(i, h, entries) == Some{entry} : Maybe<&2, Entry>}>
def resolved_entry_requires_authentication_and_exact_lookup(authenticated, i, h, entries, entry, same):
  match authenticated:
    case False{}:
      L.ex_false(L.E<{False{} == True{} : Bool}, {lookup(i, h, entries) == Some{entry} : Maybe<&2, Entry>}>,
        false_negative_true(Equal.cong(Resolution, Bool, resolved, Unauthorized{}, Resolved{entry}, same)))
    case True{}:
      L.Both{{==}, resolve_result_origin(lookup(i, h, entries), entry, same)}

law unauthenticated_resolution_has_no_lookup:
  for -i: String
  for -h: String
  for -entries: List<&2, Entry>
  {resolve(False{}, i, h, entries) == Unauthorized{} : Resolution}
def unauthenticated_resolution_has_no_lookup(i, h, entries):
  {==}

law unknown_resolution_is_missing:
  for -i: String
  for -h: String
  for -entries: List<&2, Entry>
  for absent: {lookup(i, h, entries) == None{} : Maybe<&2, Entry>}
  {resolve(True{}, i, h, entries) == Missing{} : Resolution}
def unknown_resolution_is_missing(i, h, entries, absent):
  Equal.cong(Maybe<&2, Entry>, Resolution, resolve_result, lookup(i, h, entries), None{}, absent)

def lookup_binds_head(+i: String, +h: String, +head: Entry, -rest: List<&2, Entry>, -entry: Entry,
  test: Bool, same: {matches(i, h, head) == test : Bool},
  present: {Bool.pick(Maybe<&2, Entry>, test, Some{head}, lookup(i, h, rest)) == Some{entry} : Maybe<&2, Entry>},
  tail: {lookup(i, h, rest) == Some{entry} : Maybe<&2, Entry>} -> {matches(i, h, entry) == True{} : Bool}) ->
  {matches(i, h, entry) == True{} : Bool}:
  match test:
    case False{}: tail(present)
    case True{}:
      %some_injective(head, entry, present) : {matches(i, h, _) == True{} : Bool}
      same

law lookup_binds_instance_and_handle:
  for +i: String
  for +h: String
  for entries: List<&2, Entry>
  for -entry: Entry
  for present: {lookup(i, h, entries) == Some{entry} : Maybe<&2, Entry>}
  {matches(i, h, entry) == True{} : Bool}
def lookup_binds_instance_and_handle(i, h, entries, entry, present):
  match entries:
    case Nil{}:
      L.ex_false({matches(i, h, entry) == True{} : Bool}, none_negative_some(entry, present))
    case Con{+head, rest}:
      lookup_binds_head(i, h, head, rest, entry, matches(i, h, head), {==}, present,
        in_tail => lookup_binds_instance_and_handle(i, h, rest, entry, in_tail))

def removed_head(+i: String, +h: String, +entry: Entry, +rest: List<&2, Entry>, test: Bool,
  same: {matches(i, h, entry) == test : Bool},
  absent: {lookup(i, h, rest) == None{} : Maybe<&2, Entry>}) ->
  {lookup(i, h, Bool.pick(List<&2, Entry>, test, rest, Con{entry, rest})) == None{} : Maybe<&2, Entry>}:
  match test:
    case True{}: absent
    case False{}:
      %Equal.sym(Bool, matches(i, h, entry), False{}, same) :
        {Bool.pick(Maybe<&2, Entry>, _, Some{entry}, lookup(i, h, rest)) == None{} : Maybe<&2, Entry>}
      absent

law removed_handle_cannot_resolve:
  for +i: String
  for +h: String
  for entries: List<&2, Entry>
  {lookup(i, h, remove(i, h, entries)) == None{} : Maybe<&2, Entry>}
def removed_handle_cannot_resolve(i, h, entries):
  match entries:
    case Nil{}: {==}
    case Con{+entry, +rest}:
      removed_head(i, h, entry, remove(i, h, rest), matches(i, h, entry), {==},
        removed_handle_cannot_resolve(i, h, rest))

law unauthenticated_invalidation_preserves_registry:
  for -i: String
  for -h: String
  for -entries: List<&2, Entry>
  {invalidate(False{}, i, h, entries) == entries : List<&2, Entry>}
def unauthenticated_invalidation_preserves_registry(i, h, entries):
  {==}

law unauthenticated_insert_preserves_registry:
  for -i: String
  for -entry: Entry
  for -entries: List<&2, Entry>
  {insert(False{}, i, entry, entries) == entries : List<&2, Entry>}
def unauthenticated_insert_preserves_registry(i, entry, entries):
  {==}

law fresh_scoped_insert_retains_original_entry:
  for -i: String
  for -entry: Entry
  for -entries: List<&2, Entry>
  for scoped: {matches(i, handle(entry), entry) == True{} : Bool}
  for fresh: {lookup(i, handle(entry), entries) == None{} : Maybe<&2, Entry>}
  {insert(True{}, i, entry, entries) == Con{entry, entries} : List<&2, Entry>}
def fresh_scoped_insert_retains_original_entry(i, entry, entries, scoped, fresh):
  %Equal.sym(Bool, matches(i, handle(entry), entry), True{}, scoped) :
    {Bool.pick(List<&2, Entry>, _,
      insert_fresh(lookup(i, handle(entry), entries), entry, entries), entries) == Con{entry, entries} : List<&2, Entry>}
  %Equal.sym(Maybe<&2, Entry>, lookup(i, handle(entry), entries), None{}, fresh) :
    {insert_fresh(_, entry, entries) == Con{entry, entries} : List<&2, Entry>}
  {==}

law foreign_entry_cannot_be_inserted:
  for -i: String
  for -entry: Entry
  for -entries: List<&2, Entry>
  for foreign: {matches(i, handle(entry), entry) == False{} : Bool}
  {insert(True{}, i, entry, entries) == entries : List<&2, Entry>}
def foreign_entry_cannot_be_inserted(i, entry, entries, foreign):
  %Equal.sym(Bool, matches(i, handle(entry), entry), False{}, foreign) :
    {Bool.pick(List<&2, Entry>, _, insert_fresh(lookup(i, handle(entry), entries), entry, entries), entries) == entries : List<&2, Entry>}
  {==}

def duplicate_insert(scoped: Bool, -i: String, -entry: Entry, -entries: List<&2, Entry>, -previous: Entry,
  present: {lookup(i, handle(entry), entries) == Some{previous} : Maybe<&2, Entry>}) ->
  {Bool.pick(List<&2, Entry>, scoped, insert_fresh(lookup(i, handle(entry), entries), entry, entries), entries) == entries : List<&2, Entry>}:
  match scoped:
    case False{}: {==}
    case True{}:
      %Equal.sym(Maybe<&2, Entry>, lookup(i, handle(entry), entries), Some{previous}, present) :
        {insert_fresh(_, entry, entries) == entries : List<&2, Entry>}
      {==}

law existing_handle_cannot_be_overwritten:
  for i: String
  for +entry: Entry
  for -entries: List<&2, Entry>
  for -previous: Entry
  for present: {lookup(i, handle(entry), entries) == Some{previous} : Maybe<&2, Entry>}
  {insert(True{}, i, entry, entries) == entries : List<&2, Entry>}
def existing_handle_cannot_be_overwritten(i, entry, entries, previous, present):
  duplicate_insert(matches(i, handle(entry), entry), i, entry, entries, previous, present)

# An arbitrary entry invariant can express actual source binding, universal
# derivation, or a registered artifact's identity. No Boolean checker result
# is substituted for that invariant. Filtering retains its original proof.
def AllEntries(~Property: Entry -> Type, entries: List<&2, Entry>) -> Type:
  match entries:
    case Nil{}: Unit
    case Con{entry, rest}: L.E<Property(entry), AllEntries(Property, rest)>

def lookup_property_head(~Property: Entry -> Type, +head: Entry, -entry: Entry,
  -tail_result: Maybe<&2, Entry>, test: Bool,
  present: {Bool.pick(Maybe<&2, Entry>, test, Some{head}, tail_result) == Some{entry} : Maybe<&2, Entry>},
  head_property: Property(head),
  tail_property: {tail_result == Some{entry} : Maybe<&2, Entry>} -> Property(entry)) -> Property(entry):
  match test:
    case False{}: tail_property(present)
    case True{}:
      %some_injective(head, entry, present) : Property(_)
      head_property

law lookup_recovers_registered_entry_property:
  for ~Property: Entry -> Type
  for +i: String
  for +h: String
  for entries: List<&2, Entry>
  for -entry: Entry
  for properties: AllEntries(Property, entries)
  for present: {lookup(i, h, entries) == Some{entry} : Maybe<&2, Entry>}
  Property(entry)
def lookup_recovers_registered_entry_property(Property, i, h, entries, entry, properties, present):
  match entries:
    case Nil{}:
      L.ex_false(Property(entry), none_negative_some(entry, present))
    case Con{+head, rest}:
      match properties:
        case L.Both{first, later}:
          lookup_property_head(Property, head, entry, lookup(i, h, rest), matches(i, h, head), present, first,
            in_tail => lookup_recovers_registered_entry_property(Property, i, h, rest, entry, later, in_tail))

def remove_property_case(~Property: Entry -> Type, -entry: Entry, -rest: List<&2, Entry>, test: Bool,
  first: Property(entry), later: AllEntries(Property, rest)) ->
  AllEntries(Property, Bool.pick(List<&2, Entry>, test, rest, Con{entry, rest})):
  match test:
    case True{}: later
    case False{}: L.Both{first, later}

law removal_preserves_registered_entry_properties:
  for ~Property: Entry -> Type
  for +i: String
  for +h: String
  for +entries: List<&2, Entry>
  for properties: AllEntries(Property, entries)
  AllEntries(Property, remove(i, h, entries))
def removal_preserves_registered_entry_properties(Property, i, h, entries, properties):
  match entries:
    case Nil{}: Unit{}
    case Con{+entry, +rest}:
      match properties:
        case L.Both{first, later}:
          remove_property_case(Property, entry, remove(i, h, rest), matches(i, h, entry), first,
            removal_preserves_registered_entry_properties(Property, i, h, rest, later))

law invalidation_preserves_registered_entry_properties:
  for ~Property: Entry -> Type
  for authenticated: Bool
  for +i: String
  for +h: String
  for +entries: List<&2, Entry>
  for properties: AllEntries(Property, entries)
  AllEntries(Property, invalidate(authenticated, i, h, entries))
def invalidation_preserves_registered_entry_properties(Property, authenticated, i, h, entries, properties):
  match authenticated:
    case False{}: properties
    case True{}: removal_preserves_registered_entry_properties(Property, i, h, entries, properties)

def fresh_property_case(~Property: Entry -> Type, found: Maybe<&2, Entry>, -entry: Entry,
  -entries: List<&2, Entry>, first: Property(entry), later: AllEntries(Property, entries)) ->
  AllEntries(Property, insert_fresh(found, entry, entries)):
  match found:
    case None{}: L.Both{first, later}
    case Some{previous}: later

def insert_property_case(~Property: Entry -> Type, -entry: Entry, -entries: List<&2, Entry>,
  test: Bool, +found: Maybe<&2, Entry>, first: Property(entry), later: AllEntries(Property, entries)) ->
  AllEntries(Property, Bool.pick(List<&2, Entry>, test, insert_fresh(found, entry, entries), entries)):
  match test:
    case False{}: later
    case True{}: fresh_property_case(Property, found, entry, entries, first, later)

law insertion_preserves_registered_entry_properties:
  for ~Property: Entry -> Type
  for authenticated: Bool
  for +i: String
  for +entry: Entry
  for +entries: List<&2, Entry>
  for first: Property(entry)
  for later: AllEntries(Property, entries)
  AllEntries(Property, insert(authenticated, i, entry, entries))
def insertion_preserves_registered_entry_properties(Property, authenticated, i, entry, entries, first, later):
  insert_property_case(Property, entry, entries, authenticated && matches(i, handle(entry), entry),
    lookup(i, handle(entry), entries), first, later)
