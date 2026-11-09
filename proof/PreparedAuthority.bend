# The registry/certificate authority needed by the full service contract comes
# from ONE operational history. Current validity, stored certification and a
# concrete specialization are conclusions, not arbitrary runtime premises.
import Base
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/Logic.bend as L
import ../contract/PreparedLaws.bend as H
import ../contract/PreparedRegistry.bend as G
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as R
import ../contract/Resources.bend as X
import ../contract/Semantics.bend as S
import ./SourceService.bend as Source
import ./HostTransitions.bend as Host
import ./HostHistory.bend as History
import ./PreparedDispatch.bend as Execute

def Authority(~c: S.Configuration, ~binding: Source.Source,
  ~public: List<&2, Source.FileSource>, -artifacts: H.Artifacts, -native: String,
  -world: Nat, -time: Nat, +instance: String, +current: Host.Published,
  +input: X.Reception, +raw: P.Request, -context: D.Context, +entry: G.Entry) -> Type:
  L.E<R.Valid(c, Host.database(current)),
    L.E<H.Ready(Source.environment(binding), artifacts, native, world, time, c,
      Host.database(current), input, instance, Host.entries(current), raw, entry, context,
      Source.program(binding, Host.origin(public, G.code(entry)))),
      R.Certifies(c, I.code(H.resolved(raw, entry)), Source.program(binding, Host.origin(public, G.code(entry))),
        context, I.arguments(H.resolved(raw, entry)))>>

def authority_with_data_provenance(~c: S.Configuration, ~binding: Source.Source,
  ~public: List<&2, Source.FileSource>, ~book: Host.InputBook,
  -artifacts: H.Artifacts, -native: String, -world: Nat, -time: Nat,
  +instance: String, +state: D.State, +previous: List<&2, U32>, +es: List<&2, G.Entry>,
  -input: X.Reception, +raw: P.Request, +context: D.Context, +entry: G.Entry,
  state_valid: R.Valid(c, state),
  checks: L.E<Host.Checks(c, binding, public, book), Host.Checks(c, binding, public, book)>,
  origins: L.E<G.AllEntries(Host.EntryProperty(c, binding, public, book), es), G.AllEntries(Host.EntryProperty(c, binding, public, book), es)>,
  selected: Execute.SelectedData(c, instance, Host.Published{state, previous, es}, input, raw, context, entry),
  intact: H.Intact(artifacts, native, instance, c, entry, Source.program(binding, Host.origin(public, G.code(entry))),
    I.Serve{world, c, state, input}, time)) ->
  Authority(c, binding, public, artifacts, native, world, time, instance, Host.Published{state, previous, es}, input, raw, context, entry):
  match raw checks origins selected:
    case P.Request{+credential, +handle, +arguments, +proof}
      L.Both{first_check, second_check} L.Both{first_origin, second_origin}
      L.Both{received, L.Both{authenticated, L.Both{fields, +present}}}:
        L.Both{state_valid, L.Both{
          L.Both{received, L.Both{authenticated, L.Both{fields, L.Both{present, L.Both{
            Host.current_origin_reopens_original_universal_certificate(c, binding, public, book, first_check, instance, entry,
              G.lookup_recovers_registered_entry_property(Host.EntryProperty(c, binding, public, book), instance, handle, es, entry, first_origin, present)), intact}}}}},
          Host.universal_from_mode(Source.environment(binding), c, entry, Source.program(binding, Host.origin(public, G.code(entry))),
            Host.current_origin_reopens_original_universal_certificate(c, binding, public, book, second_check, instance, entry,
              G.lookup_recovers_registered_entry_property(Host.EntryProperty(c, binding, public, book), instance, handle, es, entry, second_origin, present)))(context, arguments)}}

def authority_from_current(~c: S.Configuration, ~binding: Source.Source,
  ~public: List<&2, Source.FileSource>, ~book: Host.InputBook,
  -artifacts: H.Artifacts, -native: String, -world: Nat, -time: Nat,
  +instance: String, current: Host.Published, -input: X.Reception,
  +raw: P.Request, +context: D.Context, +entry: G.Entry,
  checks: L.E<Host.Checks(c, binding, public, book), Host.Checks(c, binding, public, book)>,
  valid: Host.Valid(c, binding, public, book, instance, current),
  selected: Execute.SelectedData(c, instance, current, input, raw, context, entry),
  intact: H.Intact(artifacts, native, instance, c, entry, Source.program(binding, Host.origin(public, G.code(entry))),
    I.Serve{world, c, Host.database(current), input}, time)) ->
  Authority(c, binding, public, artifacts, native, world, time, instance, current, input, raw, context, entry):
  match current valid:
    case Host.Published{state, previous, +es} L.Both{state_valid, origins}:
      authority_with_data_provenance(c, binding, public, book, artifacts, native, world, time, instance,
        state, previous, es, input, raw, context, entry, state_valid, checks,
        Host.registry_copy(c, binding, public, book, instance, es, origins), selected, intact)

def authority_after_reopening(~c: S.Configuration, ~binding: Source.Source,
  ~public: List<&2, Source.FileSource>, ~book: Host.InputBook,
  -artifacts: H.Artifacts, -native: String, -world: Nat, -time: Nat,
  +instance: String, +ids: List<&2, Nat>, +seed: D.State,
  -input: X.Reception, +raw: P.Request, +context: D.Context, +entry: G.Entry,
  seed_valid: R.Valid(c, seed),
  inputs: History.Copies(History.Primitive(c, binding, public, book), 2n+History.count(ids)),
  steps: History.Steps(c, binding, public, book, instance, ids, Host.Published{seed, Nil{}, Nil{}}),
  selected: Execute.SelectedData(c, instance, History.run(c, binding, public, book, instance, ids, Host.Published{seed, Nil{}, Nil{}}), input, raw, context, entry),
  intact: H.Intact(artifacts, native, instance, c, entry, Source.program(binding, Host.origin(public, G.code(entry))),
    I.Serve{world, c, Host.database(History.run(c, binding, public, book, instance, ids, Host.Published{seed, Nil{}, Nil{}})), input}, time)) ->
  Authority(c, binding, public, artifacts, native, world, time, instance,
    History.run(c, binding, public, book, instance, ids, Host.Published{seed, Nil{}, Nil{}}), input, raw, context, entry):
  match inputs:
    case L.Both{L.Both{first_check, first_execution}, L.Both{L.Both{second_check, second_execution}, rest}}:
      authority_from_current(c, binding, public, book, artifacts, native, world, time, instance,
        History.run(c, binding, public, book, instance, ids, Host.Published{seed, Nil{}, Nil{}}), input, raw, context, entry,
        L.Both{first_check, second_check},
        History.arbitrary_ordinary_prepared_interleaving_preserves_current_state_and_original_checks(c, binding, public, book, instance,
          ids, Host.Published{seed, Nil{}, Nil{}}, L.Both{seed_valid, Unit{}}, rest, steps), selected, intact)

law current_selection_after_interleaving_has_original_ready_and_actual_argument_certificate:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~book: Host.InputBook
  for ~P: Type
  for ~reopen: Unit -> P
  for -artifacts: H.Artifacts
  for -native: String
  for -world: Nat
  for -time: Nat
  for +instance: String
  for +ids: List<&2, Nat>
  for +seed: D.State
  for -input: X.Reception
  for +raw: P.Request
  for +context: D.Context
  for +entry: G.Entry
  for seed_valid: R.Valid(c, seed)
  for same: {P == History.Primitive(c, binding, public, book) : Type}
  for steps: History.Steps(c, binding, public, book, instance, ids, Host.Published{seed, Nil{}, Nil{}})
  for selected: Execute.SelectedData(c, instance, History.run(c, binding, public, book, instance, ids, Host.Published{seed, Nil{}, Nil{}}), input, raw, context, entry)
  for intact: H.Intact(artifacts, native, instance, c, entry, Source.program(binding, Host.origin(public, G.code(entry))),
    I.Serve{world, c, Host.database(History.run(c, binding, public, book, instance, ids, Host.Published{seed, Nil{}, Nil{}})), input}, time)
  Authority(c, binding, public, artifacts, native, world, time, instance,
    History.run(c, binding, public, book, instance, ids, Host.Published{seed, Nil{}, Nil{}}), input, raw, context, entry)
def current_selection_after_interleaving_has_original_ready_and_actual_argument_certificate(c, binding, public, book, P, reopen,
  artifacts, native, world, time, instance, ids, seed, input, raw, context, entry, seed_valid, same, steps, selected, intact):
  authority_after_reopening(c, binding, public, book, artifacts, native, world, time, instance, ids, seed, input, raw, context, entry,
    seed_valid, History.reopen_primitives(P, reopen, History.Primitive(c, binding, public, book), same, 2n+History.count(ids)), steps, selected, intact)
