# Complete finite histories OF THE OPERATIONAL RELATION in Host.bend.
# No external observation is defined equal to these histories. Establishing
# that the actual host follows this relation remains a separate simulation.
import Base
import ../../SourceService.bend as Source
import ../../../contract/Data.bend as D
import ../../../contract/Logic.bend as L
import ../../../contract/Requirements.bend as R
import ../../../contract/Semantics.bend as S
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/PreparedLaws.bend as Prepared
import ../../../contract/Interface.bend as I
import ./Host.bend as H

type Edge is Data:
  Edge{position: Nat, invocation: Nat, before: H.Published, after: H.Published}

def run(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: H.InputBook, +instance: String,
  ids: List<&2, Nat>, state: H.Published) -> H.Published:
  match ids:
    case Nil{}: state
    case Con{index, rest}: run(c, binding, public, book, instance, rest, H.next(c, instance, state, H.call(c, binding, public, book, index)))

def Steps(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: H.InputBook, +instance: String,
  ids: List<&2, Nat>, +state: H.Published) -> Type:
  match ids:
    case Nil{}: Unit
    case Con{+index, rest}:
      L.E<H.Step(c, instance, state, H.call(c, binding, public, book, index)),
        Steps(c, binding, public, book, instance, rest, H.next(c, instance, state, H.call(c, binding, public, book, index)))>

def count(ids: List<&2, Nat>) -> Nat:
  match ids:
    case Nil{}: 0n
    case Con{index, rest}: 1n+count(rest)

def Primitive(~c: S.Configuration, ~binding: Source.Source,
  ~public: List<&2, Source.FileSource>, ~book: H.InputBook) -> Type:
  L.E<H.Checks(c, binding, public, book), H.Executions(c, binding, public, book)>

def Copies(-P: Type, n: Nat) -> Type:
  match n:
    case 0n: Unit
    case 1n+k: L.E<P, Copies(P, k)>

# Every call opens the ORIGINAL closed primitive declaration anew. No
# captured affine proof, arbitrary certificate or Type program is duplicated.
def reopen_copies(~P: Type, ~reopen: Unit -> P, n: Nat) -> Copies(P, n):
  match n:
    case 0n: Unit{}
    case 1n+k: L.Both{reopen(Unit{}), reopen_copies(P, reopen, k)}

def reopen_primitives(~P: Type, ~reopen: Unit -> P, -Q: Type,
  same: {P == Q : Type}, n: Nat) -> Copies(Q, n):
  %same : Copies(_, n)
  reopen_copies(P, reopen, n)

law arbitrary_ordinary_prepared_interleaving_preserves_current_state_and_original_checks:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~book: H.InputBook
  for +instance: String
  for ids: List<&2, Nat>
  for +state: H.Published
  for initial: H.Valid(c, binding, public, book, instance, state)
  for inputs: Copies(Primitive(c, binding, public, book), count(ids))
  for steps: Steps(c, binding, public, book, instance, ids, state)
  H.Valid(c, binding, public, book, instance, run(c, binding, public, book, instance, ids, state))
def arbitrary_ordinary_prepared_interleaving_preserves_current_state_and_original_checks(c, binding, public, book, instance, ids, state, initial, inputs, steps):
  match ids inputs steps:
    case Nil{} _ _: initial
    case Con{+index, rest} L.Both{L.Both{checks, executions}, later_inputs} L.Both{step, later}:
      arbitrary_ordinary_prepared_interleaving_preserves_current_state_and_original_checks(c, binding, public, book, instance,
        rest, H.next(c, instance, state, H.call(c, binding, public, book, index)),
        H.operational_transition_preserves_shared_database_and_registry(c, binding, public, book, checks, executions, instance, state, index, initial, step), later_inputs, later)

# Each operational edge records both endpoints of exactly one actual pure
# transition, including control errors and delivery-independent state changes.
def history(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: H.InputBook, +instance: String,
  ids: List<&2, Nat>, +position: Nat, +state: H.Published) -> List<&2, Edge>:
  match ids:
    case Nil{}: Nil{}
    case Con{+index, rest}:
      +after = H.next(c, instance, state, H.call(c, binding, public, book, index))
      Con{Edge{position, index, state, after}, history(c, binding, public, book, instance, rest, 1n+position, after)}

def Linked(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: H.InputBook, +instance: String,
  edges: List<&2, Edge>, -state: H.Published) -> Type:
  match edges:
    case Nil{}: Unit
    case Con{Edge{position, +index, +before, +after}, rest}:
      L.E<{before == state : H.Published},
        L.E<{after == H.next(c, instance, before, H.call(c, binding, public, book, index)) : H.Published},
          Linked(c, binding, public, book, instance, rest, after)>>

law every_history_edge_is_the_actual_transition_and_links_to_its_predecessor:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~book: H.InputBook
  for +instance: String
  for ids: List<&2, Nat>
  for +position: Nat
  for +state: H.Published
  Linked(c, binding, public, book, instance, history(c, binding, public, book, instance, ids, position, state), state)
def every_history_edge_is_the_actual_transition_and_links_to_its_predecessor(c, binding, public, book, instance, ids, position, state):
  match ids:
    case Nil{}: Unit{}
    case Con{+index, rest}:
      L.Both{{==}, L.Both{{==}, every_history_edge_is_the_actual_transition_and_links_to_its_predecessor(
        c, binding, public, book, instance, rest, 1n+position, H.next(c, instance, state, H.call(c, binding, public, book, index)))}}

def replay(edges: List<&2, Edge>, state: H.Published) -> H.Published:
  match edges:
    case Nil{}: state
    case Con{Edge{position, index, before, after}, rest}: replay(rest, after)

law history_replay_is_exact_current_complete_published_pair_and_registry:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~book: H.InputBook
  for +instance: String
  for ids: List<&2, Nat>
  for +position: Nat
  for +state: H.Published
  {replay(history(c, binding, public, book, instance, ids, position, state), state) == run(c, binding, public, book, instance, ids, state) : H.Published}
def history_replay_is_exact_current_complete_published_pair_and_registry(c, binding, public, book, instance, ids, position, state):
  match ids:
    case Nil{}: {==}
    case Con{index, rest}:
      history_replay_is_exact_current_complete_published_pair_and_registry(c, binding, public, book, instance,
        rest, 1n+position, H.next(c, instance, state, H.call(c, binding, public, book, index)))

def Occurs(-edge: Edge, edges: List<&2, Edge>) -> Type:
  match edges:
    case Nil{}: Empty
    case Con{head, rest}: L.Disjunction<{head == edge : Edge}, Occurs(edge, rest)>

# At is the position-indexed transition relation. Its successor follows the
# actual next state, so a skipped mutation changes the later transition domain.
def At(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: H.InputBook, +instance: String,
  ids: List<&2, Nat>, +position: Nat, +state: H.Published, offset: Nat, -edge: Edge) -> Type:
  match ids offset:
    case Nil{} _: Empty
    case Con{+index, rest} 0n:
      {Edge{position, index, state, H.next(c, instance, state, H.call(c, binding, public, book, index))} == edge : Edge}
    case Con{index, rest} 1n+k:
      At(c, binding, public, book, instance, rest, 1n+position, H.next(c, instance, state, H.call(c, binding, public, book, index)), k, edge)

law no_operational_transition_is_omitted_from_history:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~book: H.InputBook
  for +instance: String
  for +ids: List<&2, Nat>
  for +position: Nat
  for +state: H.Published
  for offset: Nat
  for -edge: Edge
  for at: At(c, binding, public, book, instance, ids, position, state, offset, edge)
  Occurs(edge, history(c, binding, public, book, instance, ids, position, state))
def no_operational_transition_is_omitted_from_history(c, binding, public, book, instance, ids, position, state, offset, edge, at):
  match ids offset:
    case Nil{} _: L.ex_false(Occurs(edge, Nil{}), at)
    case Con{index, rest} 0n: L.Left{at}
    case Con{+index, rest} 1n+k:
      L.Right{no_operational_transition_is_omitted_from_history(c, binding, public, book, instance, rest, 1n+position,
        H.next(c, instance, state, H.call(c, binding, public, book, index)), k, edge, at)}

def Complete(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: H.InputBook, +instance: String,
  +ids: List<&2, Nat>, +position: Nat, +state: H.Published) -> Type:
  @offset: Nat -> @edge: Edge -> At(c, binding, public, book, instance, ids, position, state, offset, edge) ->
    Occurs(edge, history(c, binding, public, book, instance, ids, position, state))

law proved_seed_empty_registry_and_original_closed_primitives_give_invariant_and_complete_history:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~book: H.InputBook
  for ~P: Type
  for ~reopen: Unit -> P
  for +instance: String
  for +ids: List<&2, Nat>
  for +seed: D.State
  for seed_valid: R.Valid(c, seed)
  for same: {P == Primitive(c, binding, public, book) : Type}
  for steps: Steps(c, binding, public, book, instance, ids, H.Published{seed, Nil{}, Nil{}})
  L.E<H.Valid(c, binding, public, book, instance, run(c, binding, public, book, instance, ids, H.Published{seed, Nil{}, Nil{}})),
    L.E<Linked(c, binding, public, book, instance, history(c, binding, public, book, instance, ids, 0n, H.Published{seed, Nil{}, Nil{}}), H.Published{seed, Nil{}, Nil{}}),
      L.E<{replay(history(c, binding, public, book, instance, ids, 0n, H.Published{seed, Nil{}, Nil{}}), H.Published{seed, Nil{}, Nil{}}) ==
        run(c, binding, public, book, instance, ids, H.Published{seed, Nil{}, Nil{}}) : H.Published},
        Complete(c, binding, public, book, instance, ids, 0n, H.Published{seed, Nil{}, Nil{}})>>>
def proved_seed_empty_registry_and_original_closed_primitives_give_invariant_and_complete_history(c, binding, public, book, P, reopen, instance, ids, seed, seed_valid, same, steps):
  L.Both{arbitrary_ordinary_prepared_interleaving_preserves_current_state_and_original_checks(c, binding, public, book, instance,
    ids, H.Published{seed, Nil{}, Nil{}}, L.Both{seed_valid, Unit{}},
    reopen_primitives(P, reopen, Primitive(c, binding, public, book), same, count(ids)), steps),
    L.Both{every_history_edge_is_the_actual_transition_and_links_to_its_predecessor(c, binding, public, book, instance, ids, 0n, H.Published{seed, Nil{}, Nil{}}),
      L.Both{history_replay_is_exact_current_complete_published_pair_and_registry(c, binding, public, book, instance, ids, 0n, H.Published{seed, Nil{}, Nil{}}),
        offset => edge => at => no_operational_transition_is_omitted_from_history(c, binding, public, book, instance, ids, 0n, H.Published{seed, Nil{}, Nil{}}, offset, edge, at)}}}

def current_mode(~c: S.Configuration, ~binding: Source.Source,
  ~public: List<&2, Source.FileSource>, ~book: H.InputBook,
  checks: H.Checks(c, binding, public, book), +instance: String,
  state: H.Published, +handle: String, +entry: G.Entry,
  valid: H.Valid(c, binding, public, book, instance, state),
  present: {G.lookup(instance, handle, H.entries(state)) == Some{entry} : Maybe<&2, G.Entry>}) ->
  L.E<R.Valid(c, H.database(state)),
    Prepared.ModeCertificateValid(Source.environment(binding), c, entry,
      Source.program(binding, H.origin(public, G.code(entry))))>:
  match state valid:
    case H.Published{database, response, +es} L.Both{state_valid, origins}:
      L.Both{state_valid, H.current_origin_reopens_original_universal_certificate(c, binding, public, book, checks,
        instance, entry, G.lookup_recovers_registered_entry_property(H.EntryProperty(c, binding, public, book),
          instance, handle, es, entry, origins, present))}

law current_database_and_exact_original_mode_certificate_follow_from_operational_history:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~book: H.InputBook
  for checks: H.Checks(c, binding, public, book)
  for +instance: String
  for +ids: List<&2, Nat>
  for +seed: D.State
  for +handle: String
  for +entry: G.Entry
  for seed_valid: R.Valid(c, seed)
  for inputs: Copies(Primitive(c, binding, public, book), count(ids))
  for steps: Steps(c, binding, public, book, instance, ids, H.Published{seed, Nil{}, Nil{}})
  for present: {G.lookup(instance, handle, H.entries(run(c, binding, public, book, instance, ids, H.Published{seed, Nil{}, Nil{}}))) == Some{entry} : Maybe<&2, G.Entry>}
  L.E<R.Valid(c, H.database(run(c, binding, public, book, instance, ids, H.Published{seed, Nil{}, Nil{}}))),
    Prepared.ModeCertificateValid(Source.environment(binding), c, entry,
      Source.program(binding, H.origin(public, G.code(entry))))>
def current_database_and_exact_original_mode_certificate_follow_from_operational_history(c, binding, public, book, checks,
  instance, ids, seed, handle, entry, seed_valid, inputs, steps, present):
  current_mode(c, binding, public, book, checks, instance,
    run(c, binding, public, book, instance, ids, H.Published{seed, Nil{}, Nil{}}), handle, entry,
    arbitrary_ordinary_prepared_interleaving_preserves_current_state_and_original_checks(c, binding, public, book,
      instance, ids, H.Published{seed, Nil{}, Nil{}}, L.Both{seed_valid, Unit{}}, inputs, steps), present)
