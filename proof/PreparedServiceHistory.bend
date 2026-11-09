# One interleaved database/registry invariant, starting from the proved seed
# and an empty registry. This is a transition-history theorem, not a claim
# that the host supplied a complete physical history or authorized each event.
import Base
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/Logic.bend as L
import ../contract/PreparedLaws.bend as H
import ../contract/PreparedRegistry.bend as G
import ../contract/PreparedProtocol.bend as W
import ../contract/Requirements.bend as R
import ../contract/Semantics.bend as S
import ./HistoryService.bend as Database
import ./PreparedRegistryHistory.bend as Registry

# The response fields are not discarded by the implementation. They do not
# affect this state invariant; separate control proofs cover their exact bytes.
type Published is Data:
  Published{database: D.State, entries: List<&2, G.Entry>}

type Record is Data:
  Transaction{record: Database.Record}
  Register{entry: G.Entry}
  Invalidate{handle: String, cleanup_failed: Bool}
  Unchanged{}

def database(pair: Published) -> D.State:
  Published{state, entries} = pair
  state

def entries(pair: Published) -> List<&2, G.Entry>:
  Published{state, entries} = pair
  entries

def result_pair(result: H.ControlResult) -> Published:
  H.ControlResult{state, entries, response} = result
  Published{state, entries}

def next(~c: S.Configuration, instance: String, pair: Published, record: Record) -> Published:
  Published{state, before} = pair
  match record:
    case Transaction{r}: Published{Database.next(state, r), before}
    case Register{entry}: result_pair(H.register(c, state, instance, entry, before))
    case Invalidate{handle, failed}:
      result_pair(H.cleanup_invalidation(failed, H.invalidate(c, state, instance, handle, before)))
    case Unchanged{}: Published{state, before}

def run(~c: S.Configuration, +instance: String, history: List<&2, Record>, pair: Published) -> Published:
  match history:
    case Nil{}: pair
    case Con{record, rest}: run(c, instance, rest, next(c, instance, pair, record))

def Valid(~a: I.Environment, ~c: S.Configuration, pair: Published) -> Type:
  Published{state, before} = pair
  L.E<R.Valid(c, state), G.AllEntries(Registry.EntryProperty(a, c), before)>

# No desired final-state or registry invariant is an origin premise.
def Origin(~a: I.Environment, ~c: S.Configuration, +pair: Published, record: Record) -> Type:
  match record:
    case Transaction{r}: Database.Origin(c, database(pair), r)
    case Register{entry}: Registry.EntryAdmission(a, c, entry)
    case Invalidate{handle, failed}: Unit
    case Unchanged{}: Unit

def Sources(~a: I.Environment, ~c: S.Configuration, +instance: String,
  history: List<&2, Record>, +pair: Published) -> Type:
  match history:
    case Nil{}: Unit
    case Con{+record, rest}:
      L.E<Origin(a, c, pair, record), Sources(a, c, instance, rest, next(c, instance, pair, record))>

def register_fits_valid(~a: I.Environment, ~c: S.Configuration, fits: Bool,
  -state: D.State, -entry: G.Entry, -before: List<&2, G.Entry>,
  state_valid: R.Valid(c, state), admitted: Registry.EntryAdmission(a, c, entry),
  registered: G.AllEntries(Registry.EntryProperty(a, c), before)) ->
  Valid(a, c, result_pair(H.register_fits(fits, state, entry, before))):
  match fits:
    case False{}: L.Both{state_valid, registered}
    case True{}: L.Both{state_valid, L.Both{admitted, registered}}

def register_found_valid(~a: I.Environment, ~c: S.Configuration, found: Maybe<&2, G.Entry>,
  -state: D.State, +entry: G.Entry, -before: List<&2, G.Entry>,
  state_valid: R.Valid(c, state), admitted: Registry.EntryAdmission(a, c, entry),
  registered: G.AllEntries(Registry.EntryProperty(a, c), before)) ->
  Valid(a, c, result_pair(H.register_found(found, c, state, entry, before))):
  match found:
    case Some{previous}: L.Both{state_valid, registered}
    case None{}:
      register_fits_valid(a, c,
        R.fits(R.limit_response(S.limits(c)), H.response_value(H.Metadata{W.PreparedReceipt{G.handle(entry)}})),
        state, entry, before, state_valid, admitted, registered)

def invalidate_fits_valid(~a: I.Environment, ~c: S.Configuration, fits: Bool,
  -state: D.State, +instance: String, +handle: String, +before: List<&2, G.Entry>,
  state_valid: R.Valid(c, state), registered: G.AllEntries(Registry.EntryProperty(a, c), before)) ->
  Valid(a, c, result_pair(H.invalidate_fits(fits, state, instance, handle, before))):
  match fits:
    case False{}: L.Both{state_valid, registered}
    case True{}:
      L.Both{state_valid, G.removal_preserves_registered_entry_properties(
        Registry.EntryProperty(a, c), instance, handle, before, registered)}

def invalidate_found_valid(~a: I.Environment, ~c: S.Configuration, found: Maybe<&2, G.Entry>,
  -state: D.State, +instance: String, +handle: String, +before: List<&2, G.Entry>,
  state_valid: R.Valid(c, state), registered: G.AllEntries(Registry.EntryProperty(a, c), before)) ->
  Valid(a, c, result_pair(H.invalidate_found(found, c, state, instance, handle, before))):
  match found:
    case None{}: L.Both{state_valid, registered}
    case Some{entry}:
      invalidate_fits_valid(a, c, R.fits(R.limit_response(S.limits(c)), H.response_value(H.Metadata{W.InvalidatedReceipt{}})),
        state, instance, handle, before, state_valid, registered)

law cleanup_preserves_published_pair:
  for failed: Bool
  for result: H.ControlResult
  {result_pair(H.cleanup_invalidation(failed, result)) == result_pair(result) : Published}
def cleanup_preserves_published_pair(failed, result):
  match failed result:
    case False{} _: {==}
    case True{} H.ControlResult{s, es, H.Metadata{receipt}}:
      match receipt:
        case W.PreparedReceipt{handle}: {==}
        case W.InvalidatedReceipt{}: {==}
    case True{} H.ControlResult{s, es, H.Error{status}}: {==}

law step_preserves_database_and_registered_certificates:
  for ~a: I.Environment
  for ~c: S.Configuration
  for +instance: String
  for +pair: Published
  for +record: Record
  for valid: Valid(a, c, pair)
  for origin: Origin(a, c, pair, record)
  Valid(a, c, next(c, instance, pair, record))
def step_preserves_database_and_registered_certificates(a, c, instance, pair, record, valid, origin):
  match pair:
    case Published{+state, +before}:
      match record valid:
        case Transaction{+r} L.Both{state_valid, registered}:
          L.Both{Database.step_preserves_validity(c, state, r, state_valid, origin), registered}
        case Register{+entry} L.Both{state_valid, registered}:
          register_found_valid(a, c, G.lookup(instance, G.handle(entry), before), state, entry, before,
            state_valid, origin, registered)
        case Invalidate{+handle, +failed} L.Both{state_valid, registered}:
          %Equal.sym(Published,
            result_pair(H.cleanup_invalidation(failed, H.invalidate(c, state, instance, handle, before))),
            result_pair(H.invalidate(c, state, instance, handle, before)),
            cleanup_preserves_published_pair(failed, H.invalidate(c, state, instance, handle, before))) : Valid(a, c, _)
          invalidate_found_valid(a, c, G.lookup(instance, handle, before), state, instance, handle, before,
            state_valid, registered)
        case Unchanged{} L.Both{state_valid, registered}: L.Both{state_valid, registered}

law interleaved_history_preserves_database_and_registered_certificates:
  for ~a: I.Environment
  for ~c: S.Configuration
  for +instance: String
  for history: List<&2, Record>
  for +pair: Published
  for initial: Valid(a, c, pair)
  for sources: Sources(a, c, instance, history, pair)
  Valid(a, c, run(c, instance, history, pair))
def interleaved_history_preserves_database_and_registered_certificates(a, c, instance, history, pair, initial, sources):
  match history sources:
    case Nil{} _: initial
    case Con{+record, rest} L.Both{origin, later}:
      interleaved_history_preserves_database_and_registered_certificates(a, c, instance, rest,
        next(c, instance, pair, record), step_preserves_database_and_registered_certificates(
          a, c, instance, pair, record, initial, origin), later)

law valid_seed_and_empty_registry_suffice_for_whole_history:
  for ~a: I.Environment
  for ~c: S.Configuration
  for +instance: String
  for history: List<&2, Record>
  for +seed: D.State
  for seed_valid: R.Valid(c, seed)
  for sources: Sources(a, c, instance, history, Published{seed, Nil{}})
  Valid(a, c, run(c, instance, history, Published{seed, Nil{}}))
def valid_seed_and_empty_registry_suffice_for_whole_history(a, c, instance, history, seed, seed_valid, sources):
  interleaved_history_preserves_database_and_registered_certificates(a, c, instance, history,
    Published{seed, Nil{}}, L.Both{seed_valid, Unit{}}, sources)

# Current-state validity and the exact stored universal/read certificate come
# from the same history; neither is an arbitrary per-call host assertion.
def lookup_in_valid_pair(~a: I.Environment, ~c: S.Configuration,
  +instance: String, +handle: String, pair: Published, +entry: G.Entry,
  valid: Valid(a, c, pair),
  present: {G.lookup(instance, handle, entries(pair)) == Some{entry} : Maybe<&2, G.Entry>}) ->
  L.E<R.Valid(c, database(pair)), Registry.EntryAdmission(a, c, entry)>:
  match pair valid:
    case Published{state, +before} L.Both{state_valid, registered}:
      L.Both{state_valid, G.lookup_recovers_registered_entry_property(Registry.EntryProperty(a, c),
        instance, handle, before, entry, registered, present)}

law current_database_and_exact_certificate_follow_from_seed_history:
  for ~a: I.Environment
  for ~c: S.Configuration
  for +instance: String
  for +history: List<&2, Record>
  for +seed: D.State
  for +handle: String
  for +entry: G.Entry
  for seed_valid: R.Valid(c, seed)
  for sources: Sources(a, c, instance, history, Published{seed, Nil{}})
  for present: {G.lookup(instance, handle, entries(run(c, instance, history, Published{seed, Nil{}}))) == Some{entry} : Maybe<&2, G.Entry>}
  L.E<R.Valid(c, database(run(c, instance, history, Published{seed, Nil{}}))),
    Registry.EntryAdmission(a, c, entry)>
def current_database_and_exact_certificate_follow_from_seed_history(a, c, instance, history, seed, handle, entry, seed_valid, sources, present):
  lookup_in_valid_pair(a, c, instance, handle, run(c, instance, history, Published{seed, Nil{}}), entry,
    valid_seed_and_empty_registry_suffice_for_whole_history(a, c, instance, history, seed, seed_valid, sources), present)
