# Registry provenance follows the actual controller deltas; transactions keep
# the same registry. Removing an entry also removes its provenance witness.
import Base
import ../contract/Theorems.bend as T
import ../contract/Logic.bend as L
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/PreparedRegistry.bend as G
import ../contract/PreparedProtocol.bend as W
import ../contract/Requirements.bend as R
import ../contract/Semantics.bend as S
import ../src/Control.bend as C
import ../src/Dispatch.bend as Dispatch
import ../src/Input.bend as Input
import ../src/Gate.bend as Gate
import ../src/Resolve.bend as Resolve
import ./ControlClauses.bend as Clauses
import ./Foundations.bend as F
import ./Iteration.bend as Iteration
import ./Orders.bend as Orders

# The exact source/proof/instance tuple has a sound universal admission.
def EntryAdmitted(-c: S.Configuration, e: G.Entry) -> Type:
  match e:
    case G.Entry{i, h, code, proof, ro, seal}:
      &a: C.Admission -> L.E<T.ControlAdmissionSound(c, a),
        {C.admission_matches(a, i, P.Request{"", code, D.VAbsent{}, proof}) == True{} : Bool}>

def Tracked(-c: S.Configuration, es: List<&2, G.Entry>) -> Type:
  match es:
    case Nil{}: Unit
    case Con{e, rest}: L.E<EntryAdmitted(c, e), Tracked(c, rest)>

def lookup_case(same: Bool, -c: S.Configuration, +i: String, +h: String,
  +entry: G.Entry, +rest: List<&2, G.Entry>, -e: G.Entry,
  head: EntryAdmitted(c, entry), later: {G.lookup(i, h, rest) == Some{e} : Maybe<&2, G.Entry>} -> EntryAdmitted(c, e),
  found: {Bool.pick(Maybe<&2, G.Entry>, same, Some{entry}, G.lookup(i, h, rest)) == Some{e} : Maybe<&2, G.Entry>}) ->
  EntryAdmitted(c, e):
  match same:
    case True{}:
      %F.some_injective(G.Entry, entry, e, found) : EntryAdmitted(c, _)
      head
    case False{}: later(found)

def lookup_admitted(-c: S.Configuration, +i: String, +h: String, es: List<&2, G.Entry>,
  -e: G.Entry, tracked: Tracked(c, es),
  found: {G.lookup(i, h, es) == Some{e} : Maybe<&2, G.Entry>}) -> EntryAdmitted(c, e):
  match es tracked:
    case Nil{} _:
      L.ex_false(EntryAdmitted(c, e), F.none_negative_some(G.Entry, e, found))
    case Con{+entry, +rest} L.Both{head, tail}:
      lookup_case(G.matches(i, h, entry), c, i, h, entry, rest, e, head, later => lookup_admitted(c, i, h, rest, e, tail, later), found)

def remove_case(same: Bool, -c: S.Configuration, -entry: G.Entry, -rest: List<&2, G.Entry>,
  head: EntryAdmitted(c, entry), tail: Tracked(c, rest)) ->
  Tracked(c, C.remove_if(same, entry, rest)):
  match same:
    case True{}: tail
    case False{}: L.Both{head, tail}

def removed(-c: S.Configuration, +i: String, +h: String, es: List<&2, G.Entry>, tracked: Tracked(c, es)) ->
  Tracked(c, C.remove(i, h, es)):
  match es tracked:
    case Nil{} _: Unit{}
    case Con{+entry, rest} L.Both{head, tail}:
      remove_case(G.matches(i, h, entry), c, entry, C.remove(i, h, rest),
        head, removed(c, i, h, rest, tail))

def admitted_request(-c: S.Configuration, +i: String, +h: String, r: P.Request,
  +a: C.Admission, sound: T.ControlAdmissionSound(c, a),
  matched: {C.admission_matches(a, i, r) == True{} : Bool}) ->
  EntryAdmitted(c, G.Entry{i, h, Gate.code(r), Resolve.proof(r), False{}, ""}):
  match r:
    case P.Request{credential, code, args, proof}: (a, L.Both{sound, matched})

def added(-c: S.Configuration, reg: C.Registry, e: G.Entry, admitted: EntryAdmitted(c, e),
  tracked: Tracked(c, C.entries(reg))) -> Tracked(c, C.entries(C.apply(C.ControlAdd{e}, reg))):
  match reg e:
    case C.ControlRegistry{es, history} G.Entry{i, h, code, proof, ro, seal}: L.Both{admitted, tracked}

def removed_registry(-c: S.Configuration, +i: String, +h: String, reg: C.Registry,
  tracked: Tracked(c, C.entries(reg))) -> Tracked(c, C.entries(C.apply(C.ControlRemove{i, h}, reg))):
  match reg:
    case C.ControlRegistry{es, history}: removed(c, i, h, es, tracked)

def changed(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, prepare: Bool, invalidate: Bool, +reg: C.Registry,
  +r: P.Request, +a: C.Admission, +h: String, +change: C.Change, -receipt: W.Receipt,
  tracked: Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(reg)), sound: T.ControlAdmissionSound(S.Configuration{schema, laws, limits, instance}, a),
  checked: T.ControlChangeAt(prepare, invalidate, S.Configuration{schema, laws, limits, instance}, reg, r, a, h, change, receipt)) ->
  Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(C.apply(change, reg))):
  match prepare invalidate:
    case True{} _:
      L.Both{matched, L.Both{shape, L.Both{fresh, L.Both{exact, received}}}} = checked
      %Equal.sym(C.Change, change, C.ControlAdd{G.Entry{instance, h, Gate.code(r), Resolve.proof(r), False{}, ""}}, exact) :
        Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(C.apply(_, reg)))
      added(S.Configuration{schema, laws, limits, instance}, reg, G.Entry{instance, h, Gate.code(r), Resolve.proof(r), False{}, ""},
        admitted_request(S.Configuration{schema, laws, limits, instance}, instance, h, r, a, sound, matched), tracked)
    case False{} True{}:
      L.Both{empty, L.Both{found, L.Both{exact, received}}} = checked
      %Equal.sym(C.Change, change, C.ControlRemove{instance, Gate.code(r)}, exact) :
        Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(C.apply(_, reg)))
      removed_registry(S.Configuration{schema, laws, limits, instance}, instance, Gate.code(r), reg, tracked)
    case False{} False{}: match checked:

def next_registry(result: C.Transition) -> C.Registry:
  C.ControlResult{root, last, registry, outcome} = result
  registry


def error_plan(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, +plan: C.Plan, +s: D.State, +reg: C.Registry,
  tracked: Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(reg)), checked: T.ControlErrors(plan)) ->
  Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(next_registry(C.finish(plan, s, Nil{}, reg)))):
  match plan:
    case C.ControlDenied{status}: tracked
    case C.ControlReady{ctx, change, receipt, bytes}: match checked:

def projected(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, +plan: C.Plan, +s: D.State, +r: P.Request,
  +prepare: Bool, +invalidate: Bool, +root: D.State, +reg: C.Registry, +a: C.Admission, +h: String,
  tracked: Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(reg)), sound: T.ControlAdmissionSound(S.Configuration{schema, laws, limits, instance}, a),
  checked: T.ControlPlanAt(plan, S.Configuration{schema, laws, limits, instance}, s, r, prepare, invalidate, reg, a, h)) ->
  Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(next_registry(C.finish(plan, root, Nil{}, reg)))):
  match plan:
    case C.ControlDenied{status}: tracked
    case C.ControlReady{ctx, +change, receipt, bytes}:
      L.Both{auth, L.Both{change_ok, receipt_ok}} = checked
      changed(schema, laws, limits, instance, prepare, invalidate, reg, r, a, h, change, receipt, tracked, sound, change_ok)

def rooted_plan(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, +input: Dispatch.Routed, +plan: C.Plan, +root: D.State,
  +reg: C.Registry, +a: C.Admission, +h: String,
  tracked: Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(reg)), sound: T.ControlAdmissionSound(S.Configuration{schema, laws, limits, instance}, a),
  checked: T.ControlPlan(plan, input, S.Configuration{schema, laws, limits, instance}, reg, a, h)) ->
  Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(next_registry(C.finish(plan, root, Nil{}, reg)))):
  match input:
    case Dispatch.Routed{+tag, Input.InputReady{+s, +r}}:
      # Registry projection is independent of root and last-response bytes.
      projected(schema, laws, limits, instance, plan, s, r, U32.is_eq(tag, 3), U32.is_eq(tag, 5), root, reg, a, h, tracked, sound, checked)
    case Dispatch.Routed{tag, Input.ErrorMessage{status}}: error_plan(schema, laws, limits, instance, plan, root, reg, tracked, checked)
    case Dispatch.Routed{tag, Input.ErrorTransport{}}: error_plan(schema, laws, limits, instance, plan, root, reg, tracked, checked)

def control_tracked(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, +root: D.State, +reg: C.Registry,
  +body: List<&2, U32>, +a: C.Admission, +h: String,
  tracked: Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(reg)), sound: T.ControlAdmissionSound(S.Configuration{schema, laws, limits, instance}, a)) ->
  Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(next_registry(C.control(S.Configuration{schema, S.NoneLaw{}, limits, instance}, root, Nil{}, reg, body, a, h)))):
  rooted_plan(schema, laws, limits, instance, Dispatch.received(limits, body, root), C.plan(S.Configuration{schema, S.NoneLaw{}, limits, instance}, root, reg, body, a, h),
    root, reg, a, h, tracked, sound, Clauses.routed(schema, laws, limits, instance, Dispatch.received(limits, body, root), reg, a, h))

type ServiceRun<-c: S.Configuration, -root: D.State, -registry: C.Registry> is Type:
  ServiceEnd{}
  ServiceTransaction{request: P.Request, admit: Gate.Oracle(), next: D.State,
    sound: T.OracleSoundness(c, request, admit), step: T.Step<c, root, request, admit, next>,
    rest: ServiceRun<c, next, registry>}
  ServiceControl{body: List<&2, U32>, admission: C.Admission, candidate: String,
    sound: T.ControlAdmissionSound(c, admission),
    rest: ServiceRun<c, root, next_registry(C.control(c, root, Nil{}, registry, body, admission, candidate))>}

# Reached roots are valid; every live lookup has a sound universal source
# admission. Rest indices use the actual checked delta, never a host event.
def ServiceAt(j: Nat, -c: S.Configuration, -root: D.State, -reg: C.Registry,
  run: ServiceRun<c, root, reg>) -> Type:
  match j run:
    case _ ServiceEnd{}: L.E<R.Valid(c, root), Tracked(c, C.entries(reg))>
    case 0n ServiceTransaction{request, admit, next, sound, step, rest}:
      L.E<R.Valid(c, root), Tracked(c, C.entries(reg))>
    case 0n ServiceControl{body, a, h, sound, rest}:
      L.E<R.Valid(c, root), Tracked(c, C.entries(reg))>
    case 1n+i ServiceTransaction{request, admit, next, sound, step, rest}: ServiceAt(i, c, next, reg, rest)
    case 1n+i ServiceControl{body, a, h, sound, rest}:
      ServiceAt(i, c, root, next_registry(C.control(c, root, Nil{}, reg, body, a, h)), rest)

def transaction_valid(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String,
  +s: D.State, +r: P.Request, -admit: Gate.Oracle(), -next: D.State,
  step: T.Step<S.Configuration{schema, laws, limits, instance}, s, r, admit, next>,
  sound: T.OracleSoundness(S.Configuration{schema, laws, limits, instance}, r, admit),
  valid: R.Valid(S.Configuration{schema, laws, limits, instance}, s),
  configured: {R.configuration_is_valid(S.Configuration{schema, laws, limits, instance}) == True{} : Bool}) ->
  R.Valid(S.Configuration{schema, laws, limits, instance}, next):
  Iteration.advanced(schema, laws, limits, instance, s, r, admit, next, step, sound, valid, configured)

def service_fold(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, j: Nat, +root: D.State, +reg: C.Registry,
  run: ServiceRun<S.Configuration{schema, laws, limits, instance}, root, reg>, +configured: {R.configuration_is_valid(S.Configuration{schema, laws, limits, instance}) == True{} : Bool},
  valid: R.Valid(S.Configuration{schema, laws, limits, instance}, root), tracked: Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(reg))) -> ServiceAt(j, S.Configuration{schema, laws, limits, instance}, root, reg, run):
  match j run:
    case _ ServiceEnd{}: L.Both{valid, tracked}
    case 0n ServiceTransaction{request, admit, next, sound, step, rest}: L.Both{valid, tracked}
    case 0n ServiceControl{body, a, h, sound, rest}: L.Both{valid, tracked}
    case 1n+i ServiceTransaction{+request, admit, +next, sound, step, rest}:
      service_fold(schema, laws, limits, instance, i, next, reg, rest, configured,
        transaction_valid(schema, laws, limits, instance, root, request, admit, next, step, sound, valid, configured), tracked)
    case 1n+i ServiceControl{+body, +a, +h, sound, rest}:
      service_fold(schema, laws, limits, instance, i, root, next_registry(C.control(S.Configuration{schema, S.NoneLaw{}, limits, instance}, root, Nil{}, reg, body, a, h)), rest,
        configured, valid, control_tracked(schema, laws, limits, instance, root, reg, body, a, h, tracked, sound))

def ServiceFoldTheorem() -> Type:
  @c: S.Configuration -> @root: D.State -> @run: ServiceRun<c, root, C.ControlRegistry{Nil{}, Nil{}}> ->
    {R.configuration_is_valid(c) == True{} : Bool} -> R.Valid(c, root) ->
      @j: Nat -> ServiceAt(j, c, root, C.ControlRegistry{Nil{}, Nil{}}, run)

def service_config(c: S.Configuration, +root: D.State, run: ServiceRun<c, root, C.ControlRegistry{Nil{}, Nil{}}>,
  configured: {R.configuration_is_valid(c) == True{} : Bool}, valid: R.Valid(c, root), j: Nat) ->
  ServiceAt(j, c, root, C.ControlRegistry{Nil{}, Nil{}}, run):
  match c:
    case S.Configuration{+schema, laws, +limits, +instance}:
      service_fold(schema, laws, limits, instance, j, root, C.ControlRegistry{Nil{}, Nil{}}, run, configured, valid, Unit{})

def service_fold_theorem() -> ServiceFoldTheorem():
  c => root => run => configured => valid => j => service_config(c, root, run, configured, valid, j)

def lookup_removed_case(same: Bool, +i: String, +h: String, +entry: G.Entry, +rest: List<&2, G.Entry>,
  exact: {G.matches(i, h, entry) == same : Bool},
  tail: {G.lookup(i, h, rest) == None{} : Maybe<&2, G.Entry>}) ->
  {G.lookup(i, h, C.remove_if(same, entry, rest)) == None{} : Maybe<&2, G.Entry>}:
  match same:
    case True{}: tail
    case False{}:
      %Equal.sym(Bool, G.matches(i, h, entry), False{}, exact) :
        {Bool.pick(Maybe<&2, G.Entry>, _, Some{entry}, G.lookup(i, h, rest)) == None{} : Maybe<&2, G.Entry>}
      tail

law invalidation_removes_every_named_scoped_lookup:
  for +i: String
  for +h: String
  for es: List<&2, G.Entry>
  {G.lookup(i, h, C.remove(i, h, es)) == None{} : Maybe<&2, G.Entry>}
def invalidation_removes_every_named_scoped_lookup(i, h, es):
  match es:
    case Nil{}: {==}
    case Con{+entry, +rest}:
      lookup_removed_case(G.matches(i, h, entry), i, h, entry, C.remove(i, h, rest), {==},
        invalidation_removes_every_named_scoped_lookup(i, h, rest))

law invalidation_keeps_all_allocated_history:
  for +i: String
  for +h: String
  for reg: C.Registry
  {C.used(C.apply(C.ControlRemove{i, h}, reg)) == C.used(reg) : List<&2, String>}
def invalidation_keeps_all_allocated_history(i, h, reg):
  match reg:
    case C.ControlRegistry{es, history}: {==}

def history_or(head: Bool, -tail: Bool, known: {tail == True{} : Bool}) -> {head || tail == True{} : Bool}:
  match head:
    case True{}: {==}
    case False{}: known

law history_is_in_allocation_domain:
  for +h: String
  for es: List<&2, G.Entry>
  for +history: List<&2, String>
  for present: {C.member(h, history) == True{} : Bool}
  {C.member(h, C.keys(es, history)) == True{} : Bool}
def history_is_in_allocation_domain(h, es, history, present):
  match es:
    case Nil{}: present
    case Con{G.Entry{i, +key, code, proof, ro, seal}, rest}:
      history_or(String.eq(h, key), C.member(h, C.keys(rest, history)),
        history_is_in_allocation_domain(h, rest, history, present))

law fresh_entry_records_irrevocable_history:
  for +i: String
  for +h: String
  for +code: String
  for +proof: String
  for reg: C.Registry
  {C.member(h, C.used(C.apply(C.ControlAdd{G.Entry{i, h, code, proof, False{}, ""}}, reg))) == True{} : Bool}
def fresh_entry_records_irrevocable_history(i, h, code, proof, reg):
  match reg:
    case C.ControlRegistry{es, history}:
      %Equal.sym(Bool, String.eq(h, h), True{}, Orders.string_eq_refl(h)) :
        {_ || C.member(h, history) == True{} : Bool}
      {==}

def membership_from_head(+head: Bool, -tail: Bool, same: {head == True{} : Bool}) -> {head || tail == True{} : Bool}:
  %Equal.sym(Bool, head, True{}, same) : {_ || tail == True{} : Bool}
  {==}

def lookup_member_case(same: Bool, +i: String, +h: String, +entry: G.Entry, +rest: List<&2, G.Entry>,
  +history: List<&2, String>, -e: G.Entry,
  exact: {G.matches(i, h, entry) == same : Bool},
  later: {G.lookup(i, h, rest) == Some{e} : Maybe<&2, G.Entry>} -> {C.member(h, C.keys(rest, history)) == True{} : Bool},
  found: {Bool.pick(Maybe<&2, G.Entry>, same, Some{entry}, G.lookup(i, h, rest)) == Some{e} : Maybe<&2, G.Entry>}) ->
  {C.member(h, C.keys(Con{entry, rest}, history)) == True{} : Bool}:
  match same entry:
    case True{} G.Entry{ei, +eh, code, proof, ro, seal}:
      membership_from_head(String.eq(h, eh), C.member(h, C.keys(rest, history)),
        F.and_boolean_right(String.eq(i, ei), String.eq(h, eh), exact))
    case False{} G.Entry{ei, +eh, code, proof, ro, seal}:
      history_or(String.eq(h, eh), C.member(h, C.keys(rest, history)), later(found))

def lookup_is_in_allocation_domain(+i: String, +h: String, es: List<&2, G.Entry>, +history: List<&2, String>,
  -e: G.Entry, found: {G.lookup(i, h, es) == Some{e} : Maybe<&2, G.Entry>}) ->
  {C.member(h, C.keys(es, history)) == True{} : Bool}:
  match es:
    case Nil{}:
      L.ex_false({C.member(h, history) == True{} : Bool}, F.none_negative_some(G.Entry, e, found))
    case Con{+entry, +rest}:
      lookup_member_case(G.matches(i, h, entry), i, h, entry, rest, history, e, {==},
        found => lookup_is_in_allocation_domain(i, h, rest, history, e, found), found)

def fresh_lookup(result: Maybe<&2, G.Entry>, +i: String, +h: String, +es: List<&2, G.Entry>, +history: List<&2, String>,
  fresh: {C.member(h, C.keys(es, history)) == False{} : Bool},
  exact: {G.lookup(i, h, es) == result : Maybe<&2, G.Entry>}) -> {result == None{} : Maybe<&2, G.Entry>}:
  match result:
    case None{}: {==}
    case Some{e}:
      L.ex_false({Some{e} == None{} : Maybe<&2, G.Entry>},
        F.false_negative_true(Equal.trans(Bool, False{}, C.member(h, C.keys(es, history)), True{},
          Equal.sym(Bool, C.member(h, C.keys(es, history)), False{}, fresh),
          lookup_is_in_allocation_domain(i, h, es, history, e, exact))))

law freshness_excludes_every_existing_scoped_lookup:
  for +i: String
  for +h: String
  for reg: C.Registry
  for fresh: {C.member(h, C.allocated(reg)) == False{} : Bool}
  {G.lookup(i, h, C.entries(reg)) == None{} : Maybe<&2, G.Entry>}
def freshness_excludes_every_existing_scoped_lookup(i, h, reg, fresh):
  match reg:
    case C.ControlRegistry{+es, +history}:
      fresh_lookup(G.lookup(i, h, es), i, h, es, history, fresh, {==})

def UniversalSource(-c: S.Configuration, -code: String) -> Type:
  &program: S.Program ->
    L.E<(@ctx: D.Context -> @args: D.Value -> R.Certifies(c, code, program, ctx, args)),
      (@state: D.State -> @ctx: D.Context -> @args: D.Value -> T.Terminates(program, c, state, ctx, args))>

def accepted_source(a: C.Admission, -c: S.Configuration, +i: String, +code: String, +proof: String,
  sound: T.ControlAdmissionSound(c, a),
  +matched: {C.admission_matches(a, i, P.Request{"", code, D.VAbsent{}, proof}) == True{} : Bool}) ->
  UniversalSource(c, code):
  match a:
    case C.ControlUnaccepted{}: L.ex_false(UniversalSource(c, code), F.false_negative_true(matched))
    case C.ControlUniversal{+ai, +ac, +ap}:
      %Orders.string_equal(ac, code,
        F.and_boolean_right(String.eq(ai, i), String.eq(ac, code),
          F.and_boolean_left(String.eq(ai, i) && String.eq(ac, code), String.eq(ap, proof), matched))) :
        UniversalSource(c, _)
      sound

def entry_has_universal_source(-c: S.Configuration, +e: G.Entry, admitted: EntryAdmitted(c, e)) ->
  UniversalSource(c, G.code(e)):
  match e:
    case G.Entry{+i, h, +code, +proof, ro, seal}:
      (a, L.Both{sound, matched}) = admitted
      accepted_source(a, c, i, code, proof, sound, matched)

law every_live_lookup_has_the_exact_universal_source:
  for -c: S.Configuration
  for +i: String
  for +h: String
  for +es: List<&2, G.Entry>
  for +e: G.Entry
  for tracked: Tracked(c, es)
  for found: {G.lookup(i, h, es) == Some{e} : Maybe<&2, G.Entry>}
  UniversalSource(c, G.code(e))
def every_live_lookup_has_the_exact_universal_source(c, i, h, es, e, tracked, found):
  entry_has_universal_source(c, e, lookup_admitted(c, i, h, es, e, tracked, found))
