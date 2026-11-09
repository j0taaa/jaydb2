# Total cached-execution selection: fresh authentication, proof-field check,
# then current scoped lookup. Selected pure programs complete by their ORIGINAL
# checked declarations. Native/artifact/IO simulation is not asserted here.
import Base
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/Logic.bend as L
import ../contract/PreparedLaws.bend as H
import ../contract/PreparedProtocol.bend as W
import ../contract/PreparedRegistry.bend as G
import ../contract/Protocol.bend as P
import ../contract/Resources.bend as X
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ./Orders.bend as O
import ./PreparedInvalidationDispatch.bend as Invalidation
import ./SourceService.bend as Source
import ./HostTransitions.bend as Host
import ./PreparedProgress.bend as Progress

type Choice is Data:
  Unauthenticated{}
  BadProof{context: D.Context}
  Missing{context: D.Context}
  Selected{context: D.Context, entry: G.Entry}

def choose_lookup(context: D.Context, found: Maybe<&2, G.Entry>) -> Choice:
  match found:
    case None{}: Missing{context}
    case Some{entry}: Selected{context, entry}

def choose_proof(empty: Bool, instance: String, before: List<&2, G.Entry>, raw: P.Request, context: D.Context) -> Choice:
  match empty:
    case False{}: BadProof{context}
    case True{}: choose_lookup(context, G.lookup(instance, I.code(raw), before))

def choose_auth(authentication: Maybe<&2, D.Context>, instance: String,
  before: List<&2, G.Entry>, +raw: P.Request) -> Choice:
  match authentication:
    case None{}: Unauthenticated{}
    case Some{context}: choose_proof(String.eq(I.proof(raw), ""), instance, before, raw, context)

def choose(instance: String, +before: Host.Published, +raw: P.Request) -> Choice:
  choose_auth(D.authenticate(Host.database(before), I.credential(raw)), instance, Host.entries(before), raw)

def SelectedData(~c: S.Configuration, +instance: String, +before: Host.Published,
  +input: X.Reception, +raw: P.Request, -context: D.Context, -entry: G.Entry) -> Type:
  L.E<W.Received(c, input, W.Extension{W.Execute{}, raw}),
    L.E<{D.authenticate(Host.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
      L.E<H.HandleFields(raw, entry), {G.lookup(instance, I.code(raw), Host.entries(before)) == Some{entry} : Maybe<&2, G.Entry>}>>>

def Correct(~c: S.Configuration, +instance: String, +before: Host.Published,
  +input: X.Reception, +raw: P.Request, choice: Choice) -> Type:
  match choice:
    case Unauthenticated{}:
      {D.authenticate(Host.database(before), I.credential(raw)) == None{} : Maybe<&2, D.Context>}
    case BadProof{context}:
      L.E<{D.authenticate(Host.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
        {String.eq(I.proof(raw), "") == False{} : Bool}>
    case Missing{context}:
      L.E<{D.authenticate(Host.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
        L.E<{I.proof(raw) == "" : String}, {G.lookup(instance, I.code(raw), Host.entries(before)) == None{} : Maybe<&2, G.Entry>}>>
    case Selected{context, entry}: SelectedData(c, instance, before, input, raw, context, entry)

def selected_data(~c: S.Configuration, +instance: String, +before: Host.Published,
  -input: X.Reception, +raw: P.Request, +context: D.Context, +entry: G.Entry,
  received: W.Received(c, input, W.Extension{W.Execute{}, raw}),
  authenticated: {D.authenticate(Host.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  empty: {I.proof(raw) == "" : String},
  +present: {G.lookup(instance, I.code(raw), Host.entries(before)) == Some{entry} : Maybe<&2, G.Entry>}) ->
  SelectedData(c, instance, before, input, raw, context, entry):
  L.Both{received, L.Both{authenticated, L.Both{
    L.Both{Invalidation.handle_from_match(instance, I.code(raw), entry,
      G.lookup_binds_instance_and_handle(instance, I.code(raw), Host.entries(before), entry, present)), empty}, present}}}

def correct_lookup(~c: S.Configuration, +instance: String, +before: Host.Published,
  +input: X.Reception, +raw: P.Request, +context: D.Context, found: Maybe<&2, G.Entry>,
  received: W.Received(c, input, W.Extension{W.Execute{}, raw}),
  authenticated: {D.authenticate(Host.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  empty: {I.proof(raw) == "" : String},
  looked_up: {G.lookup(instance, I.code(raw), Host.entries(before)) == found : Maybe<&2, G.Entry>}) ->
  Correct(c, instance, before, input, raw, choose_lookup(context, found)):
  match found:
    case None{}: L.Both{authenticated, L.Both{empty, looked_up}}
    case Some{entry}: selected_data(c, instance, before, input, raw, context, entry, received, authenticated, empty, looked_up)

def correct_proof(~c: S.Configuration, +instance: String, +before: Host.Published,
  +input: X.Reception, +raw: P.Request, +context: D.Context, empty: Bool,
  received: W.Received(c, input, W.Extension{W.Execute{}, raw}),
  authenticated: {D.authenticate(Host.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  checked: {String.eq(I.proof(raw), "") == empty : Bool}) ->
  Correct(c, instance, before, input, raw, choose_proof(empty, instance, Host.entries(before), raw, context)):
  match empty:
    case False{}: L.Both{authenticated, checked}
    case True{}:
      correct_lookup(c, instance, before, input, raw, context, G.lookup(instance, I.code(raw), Host.entries(before)),
        received, authenticated, O.string_equal(I.proof(raw), "", checked), {==})

def correct_auth(~c: S.Configuration, +instance: String, +before: Host.Published,
  +input: X.Reception, +raw: P.Request, authentication: Maybe<&2, D.Context>,
  received: W.Received(c, input, W.Extension{W.Execute{}, raw}),
  checked: {D.authenticate(Host.database(before), I.credential(raw)) == authentication : Maybe<&2, D.Context>}) ->
  Correct(c, instance, before, input, raw, choose_auth(authentication, instance, Host.entries(before), raw)):
  match authentication:
    case None{}: checked
    case Some{context}:
      correct_proof(c, instance, before, input, raw, context, String.eq(I.proof(raw), ""), received, checked, {==})

law deterministic_cached_selection_has_only_exact_error_causes_or_current_authenticated_entry:
  for ~c: S.Configuration
  for +instance: String
  for +before: Host.Published
  for +input: X.Reception
  for +raw: P.Request
  for received: W.Received(c, input, W.Extension{W.Execute{}, raw})
  Correct(c, instance, before, input, raw, choose(instance, before, raw))
def deterministic_cached_selection_has_only_exact_error_causes_or_current_authenticated_entry(c, instance, before, input, raw, received):
  correct_auth(c, instance, before, input, raw, D.authenticate(Host.database(before), I.credential(raw)), received, {==})

law selected_current_cached_entry_has_termination_derived_complete_adapter_output:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~book: Host.InputBook
  for +instance: String
  for +before: Host.Published
  for +input: X.Reception
  for +raw: P.Request
  for +context: D.Context
  for +entry: G.Entry
  for checks: Host.Checks(c, binding, public, book)
  for valid: Host.Valid(c, binding, public, book, instance, before)
  for selected: Correct(c, instance, before, input, raw, Selected{context, entry})
  for configured: {R.configuration_is_valid(c) == True{} : Bool}
  exs n: Nat
  exs w: D.State
  exs events: List<&2, S.OperationEvent>
  exs response: S.Response
  Progress.Productive(c, binding, public, G.code(entry), context, I.arguments(raw), Host.database(before), n, w, events, response)
def selected_current_cached_entry_has_termination_derived_complete_adapter_output(c, binding, public, book,
  instance, before, input, raw, context, entry, checks, valid, selected, configured):
  match selected:
    case L.Both{received, L.Both{authenticated, L.Both{fields, present}}}:
      Progress.current_registered_original_declarations_force_cached_adapter_completion(c, binding, public, book, checks,
        instance, before, raw, entry, context, valid, present, authenticated, configured)
