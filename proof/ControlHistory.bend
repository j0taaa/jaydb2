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

def lookup_case(same: Bool, -c: S.Configuration, +i: String, +h: String,
  +entry: G.Entry, +rest: List<&2, G.Entry>, -e: G.Entry,
  head: T.EntryAdmitted(c, entry), later: {G.lookup(i, h, rest) == Some{e} : Maybe<&2, G.Entry>} -> T.EntryAdmitted(c, e),
  found: {Bool.pick(Maybe<&2, G.Entry>, same, Some{entry}, G.lookup(i, h, rest)) == Some{e} : Maybe<&2, G.Entry>}) ->
  T.EntryAdmitted(c, e):
  match same:
    case True{}:
      %F.some_injective(G.Entry, entry, e, found) : T.EntryAdmitted(c, _)
      head
    case False{}: later(found)

def lookup_admitted(-c: S.Configuration, +i: String, +h: String, es: List<&2, G.Entry>,
  -e: G.Entry, tracked: T.Tracked(c, es),
  found: {G.lookup(i, h, es) == Some{e} : Maybe<&2, G.Entry>}) -> T.EntryAdmitted(c, e):
  match es tracked:
    case Nil{} _:
      L.ex_false(T.EntryAdmitted(c, e), F.none_negative_some(G.Entry, e, found))
    case Con{+entry, +rest} L.Both{head, tail}:
      lookup_case(G.matches(i, h, entry), c, i, h, entry, rest, e, head, later => lookup_admitted(c, i, h, rest, e, tail, later), found)

def remove_case(same: Bool, -c: S.Configuration, -entry: G.Entry, -rest: List<&2, G.Entry>,
  head: T.EntryAdmitted(c, entry), tail: T.Tracked(c, rest)) ->
  T.Tracked(c, C.remove_if(same, entry, rest)):
  match same:
    case True{}: tail
    case False{}: L.Both{head, tail}

def removed(-c: S.Configuration, +i: String, +h: String, es: List<&2, G.Entry>, tracked: T.Tracked(c, es)) ->
  T.Tracked(c, C.remove(i, h, es)):
  match es tracked:
    case Nil{} _: Unit{}
    case Con{+entry, rest} L.Both{head, tail}:
      remove_case(G.matches(i, h, entry), c, entry, C.remove(i, h, rest),
        head, removed(c, i, h, rest, tail))

def admitted_request(-c: S.Configuration, +i: String, +h: String, r: P.Request,
  +a: C.Admission, sound: T.ControlAdmissionSound(c, a),
  matched: {C.admission_matches(a, i, r) == True{} : Bool}) ->
  T.EntryAdmitted(c, G.Entry{i, h, Gate.code(r), Resolve.proof(r), False{}, ""}):
  match r:
    case P.Request{credential, code, args, proof}: (a, L.Both{sound, matched})

def added(-c: S.Configuration, reg: C.Registry, e: G.Entry, admitted: T.EntryAdmitted(c, e),
  tracked: T.Tracked(c, C.entries(reg))) -> T.Tracked(c, C.entries(C.apply(C.ControlAdd{e}, reg))):
  match reg e:
    case C.ControlRegistry{es, history} G.Entry{i, h, code, proof, ro, seal}: L.Both{admitted, tracked}

def removed_registry(-c: S.Configuration, +i: String, +h: String, reg: C.Registry,
  tracked: T.Tracked(c, C.entries(reg))) -> T.Tracked(c, C.entries(C.apply(C.ControlRemove{i, h}, reg))):
  match reg:
    case C.ControlRegistry{es, history}: removed(c, i, h, es, tracked)

def changed(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, prepare: Bool, invalidate: Bool, +reg: C.Registry,
  +r: P.Request, +a: C.Admission, +h: String, +change: C.Change, -receipt: W.Receipt,
  tracked: T.Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(reg)), sound: T.ControlAdmissionSound(S.Configuration{schema, laws, limits, instance}, a),
  checked: T.ControlChangeAt(prepare, invalidate, S.Configuration{schema, laws, limits, instance}, reg, r, a, h, change, receipt)) ->
  T.Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(C.apply(change, reg))):
  match prepare invalidate:
    case True{} _:
      L.Both{matched, L.Both{shape, L.Both{fresh, L.Both{exact, received}}}} = checked
      %Equal.sym(C.Change, change, C.ControlAdd{G.Entry{instance, h, Gate.code(r), Resolve.proof(r), False{}, ""}}, exact) :
        T.Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(C.apply(_, reg)))
      added(S.Configuration{schema, laws, limits, instance}, reg, G.Entry{instance, h, Gate.code(r), Resolve.proof(r), False{}, ""},
        admitted_request(S.Configuration{schema, laws, limits, instance}, instance, h, r, a, sound, matched), tracked)
    case False{} True{}:
      L.Both{empty, L.Both{found, L.Both{exact, received}}} = checked
      %Equal.sym(C.Change, change, C.ControlRemove{instance, Gate.code(r)}, exact) :
        T.Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(C.apply(_, reg)))
      removed_registry(S.Configuration{schema, laws, limits, instance}, instance, Gate.code(r), reg, tracked)
    case False{} False{}: match checked:

def error_plan(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, +plan: C.Plan, +s: D.State, +reg: C.Registry,
  tracked: T.Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(reg)), checked: T.ControlErrors(plan)) ->
  T.Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(T.next_registry(C.finish(plan, s, Nil{}, reg)))):
  match plan:
    case C.ControlDenied{status}: tracked
    case C.ControlReady{ctx, change, receipt, bytes}: match checked:

def projected(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, +plan: C.Plan, +s: D.State, +r: P.Request,
  +prepare: Bool, +invalidate: Bool, +root: D.State, +reg: C.Registry, +a: C.Admission, +h: String,
  tracked: T.Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(reg)), sound: T.ControlAdmissionSound(S.Configuration{schema, laws, limits, instance}, a),
  checked: T.ControlPlanAt(plan, S.Configuration{schema, laws, limits, instance}, s, r, prepare, invalidate, reg, a, h)) ->
  T.Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(T.next_registry(C.finish(plan, root, Nil{}, reg)))):
  match plan:
    case C.ControlDenied{status}: tracked
    case C.ControlReady{ctx, +change, receipt, bytes}:
      L.Both{auth, L.Both{change_ok, receipt_ok}} = checked
      changed(schema, laws, limits, instance, prepare, invalidate, reg, r, a, h, change, receipt, tracked, sound, change_ok)

def rooted_plan(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, +input: Dispatch.Routed, +plan: C.Plan, +root: D.State,
  +reg: C.Registry, +a: C.Admission, +h: String,
  tracked: T.Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(reg)), sound: T.ControlAdmissionSound(S.Configuration{schema, laws, limits, instance}, a),
  checked: T.ControlPlan(plan, input, S.Configuration{schema, laws, limits, instance}, reg, a, h)) ->
  T.Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(T.next_registry(C.finish(plan, root, Nil{}, reg)))):
  match input:
    case Dispatch.Routed{+tag, Input.InputReady{+s, +r}}:
      # Registry projection is independent of root and last-response bytes.
      projected(schema, laws, limits, instance, plan, s, r, U32.is_eq(tag, 3), U32.is_eq(tag, 5), root, reg, a, h, tracked, sound, checked)
    case Dispatch.Routed{tag, Input.ErrorMessage{status}}: error_plan(schema, laws, limits, instance, plan, root, reg, tracked, checked)
    case Dispatch.Routed{tag, Input.ErrorTransport{}}: error_plan(schema, laws, limits, instance, plan, root, reg, tracked, checked)

def control_tracked(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, +root: D.State, +reg: C.Registry,
  +body: List<&2, U32>, +a: C.Admission, +h: String,
  tracked: T.Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(reg)), sound: T.ControlAdmissionSound(S.Configuration{schema, laws, limits, instance}, a)) ->
  T.Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(T.next_registry(C.control(S.Configuration{schema, S.NoneLaw{}, limits, instance}, root, Nil{}, reg, body, a, h)))):
  rooted_plan(schema, laws, limits, instance, Dispatch.received(limits, body, root), C.plan(S.Configuration{schema, S.NoneLaw{}, limits, instance}, root, reg, body, a, h),
    root, reg, a, h, tracked, sound, Clauses.routed(schema, laws, limits, instance, Dispatch.received(limits, body, root), reg, a, h))

def transaction_valid(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String,
  +s: D.State, +r: P.Request, -admit: Gate.Oracle(), -next: D.State,
  step: T.Step<S.Configuration{schema, laws, limits, instance}, s, r, admit, next>,
  sound: T.OracleSoundness(S.Configuration{schema, laws, limits, instance}, r, admit),
  valid: R.Valid(S.Configuration{schema, laws, limits, instance}, s),
  configured: {R.configuration_is_valid(S.Configuration{schema, laws, limits, instance}) == True{} : Bool}) ->
  R.Valid(S.Configuration{schema, laws, limits, instance}, next):
  Iteration.advanced(schema, laws, limits, instance, s, r, admit, next, step, sound, valid, configured)

def service_fold(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, j: Nat, +root: D.State, +reg: C.Registry,
  run: T.ServiceRun<S.Configuration{schema, laws, limits, instance}, root, reg>, +configured: {R.configuration_is_valid(S.Configuration{schema, laws, limits, instance}) == True{} : Bool},
  valid: R.Valid(S.Configuration{schema, laws, limits, instance}, root), tracked: T.Tracked(S.Configuration{schema, laws, limits, instance}, C.entries(reg)),
  history: T.RegistryHistory<S.Configuration{schema, laws, limits, instance}, reg>) -> T.ServiceAt(j, S.Configuration{schema, laws, limits, instance}, root, reg, run):
  match j run:
    case _ T.ServiceEnd{}: L.Both{valid, L.Both{tracked, history}}
    case 0n T.ServiceTransaction{request, admit, next, sound, step, rest}: L.Both{valid, L.Both{tracked, history}}
    case 0n T.ServiceControl{body, a, h, sound, rest}: L.Both{valid, L.Both{tracked, history}}
    case 1n+i T.ServiceTransaction{+request, admit, +next, sound, step, rest}:
      service_fold(schema, laws, limits, instance, i, next, reg, rest, configured,
        transaction_valid(schema, laws, limits, instance, root, request, admit, next, step, sound, valid, configured), tracked, history)
    case 1n+i T.ServiceControl{+body, +a, +h, sound, rest}:
      service_fold(schema, laws, limits, instance, i, root, T.next_registry(C.control(S.Configuration{schema, S.NoneLaw{}, limits, instance}, root, Nil{}, reg, body, a, h)), rest,
        configured, valid, control_tracked(schema, laws, limits, instance, root, reg, body, a, h, tracked, sound),
        T.RegistryControl{reg, root, body, a, h, history, {==}})

def service_config(c: S.Configuration, +root: D.State, run: T.ServiceRun<c, root, C.ControlRegistry{Nil{}, Nil{}}>,
  configured: {R.configuration_is_valid(c) == True{} : Bool}, valid: R.Valid(c, root), j: Nat) ->
  T.ServiceAt(j, c, root, C.ControlRegistry{Nil{}, Nil{}}, run):
  match c:
    case S.Configuration{+schema, laws, +limits, +instance}:
      service_fold(schema, laws, limits, instance, j, root, C.ControlRegistry{Nil{}, Nil{}}, run, configured, valid, Unit{}, T.RegistryEmpty{{==}})

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

def accepted_source(a: C.Admission, -c: S.Configuration, +i: String, +code: String, +proof: String,
  sound: T.ControlAdmissionSound(c, a),
  +matched: {C.admission_matches(a, i, P.Request{"", code, D.VAbsent{}, proof}) == True{} : Bool}) ->
  T.UniversalSource(c, code):
  match a:
    case C.ControlUnaccepted{}: L.ex_false(T.UniversalSource(c, code), F.false_negative_true(matched))
    case C.ControlUniversal{+ai, +ac, +ap}:
      %Orders.string_equal(ac, code,
        F.and_boolean_right(String.eq(ai, i), String.eq(ac, code),
          F.and_boolean_left(String.eq(ai, i) && String.eq(ac, code), String.eq(ap, proof), matched))) :
        T.UniversalSource(c, _)
      sound

def entry_has_universal_source(-c: S.Configuration, +e: G.Entry, admitted: T.EntryAdmitted(c, e)) ->
  T.UniversalSource(c, G.code(e)):
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
  for tracked: T.Tracked(c, es)
  for found: {G.lookup(i, h, es) == Some{e} : Maybe<&2, G.Entry>}
  T.UniversalSource(c, G.code(e))
def every_live_lookup_has_the_exact_universal_source(c, i, h, es, e, tracked, found):
  entry_has_universal_source(c, e, lookup_admitted(c, i, h, es, e, tracked, found))

# Full finite-run preservation of allocation history, not only one removal.
def used_after_change(change: C.Change, reg: C.Registry, +h: String,
  present: {C.member(h, C.used(reg)) == True{} : Bool}) ->
  {C.member(h, C.used(C.apply(change, reg))) == True{} : Bool}:
  match change reg:
    case C.ControlAdd{G.Entry{i, k, code, proof, ro, seal}} C.ControlRegistry{es, history}:
      history_or(String.eq(h, k), C.member(h, history), present)
    case C.ControlRemove{i, k} C.ControlRegistry{es, history}: present

def used_after_plan(plan: C.Plan, +root: D.State, +reg: C.Registry, +h: String,
  present: {C.member(h, C.used(reg)) == True{} : Bool}) ->
  {C.member(h, C.used(T.next_registry(C.finish(plan, root, Nil{}, reg)))) == True{} : Bool}:
  match plan:
    case C.ControlDenied{status}: present
    case C.ControlReady{ctx, change, receipt, bytes}: used_after_change(change, reg, h, present)

def used_allocated(+h: String, reg: C.Registry, present: {C.member(h, C.used(reg)) == True{} : Bool}) ->
  {C.member(h, C.allocated(reg)) == True{} : Bool}:
  match reg:
    case C.ControlRegistry{es, +history}: history_is_in_allocation_domain(h, es, history, present)

def cannot_reuse_case(valid: Bool, +limits: S.Limits, +instance: String, +ctx: D.Context, +i: String,
  +h: String, +reg: C.Registry, +r: P.Request,
  allocated: {C.member(h, C.allocated(reg)) == True{} : Bool}) ->
  {C.fresh(limits, instance, valid && Bool.not(C.member(h, C.allocated(reg))), ctx, i, h, r) == C.ControlDenied{S.Failure{}} : C.Plan}:
  match valid:
    case False{}: {==}
    case True{}:
      %Equal.sym(Bool, C.member(h, C.allocated(reg)), True{}, allocated) :
        {C.fresh(limits, instance, Bool.not(_), ctx, i, h, r) == C.ControlDenied{S.Failure{}} : C.Plan}
      {==}

def handle_retired(+h: String, +reg: C.Registry, +present: {C.member(h, C.used(reg)) == True{} : Bool}) ->
  T.HandleRetired(h, reg):
  L.Both{present, limits => instance => ctx => i => r =>
    cannot_reuse_case(C.candidate_valid(h), limits, instance, ctx, i, h, reg, r, used_allocated(h, reg, present))}

def lifetime_fold(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, j: Nat,
  +root: D.State, +reg: C.Registry, +h: String,
  run: T.ServiceRun<S.Configuration{schema, laws, limits, instance}, root, reg>,
  +present: {C.member(h, C.used(reg)) == True{} : Bool}) ->
  T.HandleRetiredAt(j, h, S.Configuration{schema, laws, limits, instance}, root, reg, run):
  match j run:
    case _ T.ServiceEnd{}: handle_retired(h, reg, present)
    case 0n T.ServiceTransaction{request, admit, next, sound, step, rest}: handle_retired(h, reg, present)
    case 0n T.ServiceControl{body, a, candidate, sound, rest}: handle_retired(h, reg, present)
    case 1n+n T.ServiceTransaction{request, admit, +next, sound, step, rest}:
      lifetime_fold(schema, laws, limits, instance, n, next, reg, h, rest, present)
    case 1n+n T.ServiceControl{+body, +a, +candidate, sound, rest}:
      lifetime_fold(schema, laws, limits, instance, n, root,
        T.next_registry(C.control(S.Configuration{schema, S.NoneLaw{}, limits, instance}, root, Nil{}, reg, body, a, candidate)), h, rest,
        used_after_plan(C.plan(S.Configuration{schema, S.NoneLaw{}, limits, instance}, root, reg, body, a, candidate), root, reg, h, present))

def lifetime_configuration(c: S.Configuration, root: D.State, reg: C.Registry, h: String,
  run: T.ServiceRun<c, root, reg>, known: {C.member(h, C.used(reg)) == True{} : Bool}, j: Nat) ->
  T.HandleRetiredAt(j, h, c, root, reg, run):
  match c:
    case S.Configuration{schema, laws, limits, instance}:
      lifetime_fold(schema, laws, limits, instance, j, root, reg, h, run, known)

def service_lifetime_theorem() -> T.ServiceLifetimeTheorem():
  c => root => reg => h => run => present => j => lifetime_configuration(c, root, reg, h, run, present, j)

def registry_invalidation(+i: String, +h: String, reg: C.Registry) ->
  L.E<{G.lookup(i, h, C.entries(C.apply(C.ControlRemove{i, h}, reg))) == None{} : Maybe<&2, G.Entry>},
    {C.used(C.apply(C.ControlRemove{i, h}, reg)) == C.used(reg) : List<&2, String>}>:
  match reg:
    case C.ControlRegistry{es, history}:
      L.Both{invalidation_removes_every_named_scoped_lookup(i, h, es), {==}}

def registry_invalidation_theorem() -> T.RegistryInvalidationTheorem():
  i => h => reg => registry_invalidation(i, h, reg)

def registry_lookup_theorem() -> T.RegistryLookupTheorem():
  c => i => h => es => e => tracked => found => every_live_lookup_has_the_exact_universal_source(c, i, h, es, e, tracked, found)

# Removing any subset of entries cannot create a lookup that was absent.
def absent_head(same: Bool, -entry: G.Entry, -tail: Maybe<&2, G.Entry>,
  absent: {Bool.pick(Maybe<&2, G.Entry>, same, Some{entry}, tail) == None{} : Maybe<&2, G.Entry>}) ->
  L.E<{same == False{} : Bool}, {tail == None{} : Maybe<&2, G.Entry>}>:
  match same:
    case False{}: L.Both{{==}, absent}
    case True{}:
      L.ex_false(L.E<{True{} == False{} : Bool}, {tail == None{} : Maybe<&2, G.Entry>}>,
        F.none_negative_some(G.Entry, entry, Equal.sym(Maybe<&2, G.Entry>, Some{entry}, None{}, absent)))

def absent_remove_case(remove: Bool, +i: String, +h: String, +entry: G.Entry, +es: List<&2, G.Entry>,
  no_head: {G.matches(i, h, entry) == False{} : Bool},
  no_tail: {G.lookup(i, h, es) == None{} : Maybe<&2, G.Entry>}) ->
  {G.lookup(i, h, C.remove_if(remove, entry, es)) == None{} : Maybe<&2, G.Entry>}:
  match remove:
    case True{}: no_tail
    case False{}:
      %Equal.sym(Bool, G.matches(i, h, entry), False{}, no_head) :
        {Bool.pick(Maybe<&2, G.Entry>, _, Some{entry}, G.lookup(i, h, es)) == None{} : Maybe<&2, G.Entry>}
      no_tail

def absent_remove(+i: String, +h: String, +ri: String, +rh: String, es: List<&2, G.Entry>,
  absent: {G.lookup(i, h, es) == None{} : Maybe<&2, G.Entry>}) ->
  {G.lookup(i, h, C.remove(ri, rh, es)) == None{} : Maybe<&2, G.Entry>}:
  match es:
    case Nil{}: {==}
    case Con{+entry, +rest}:
      F.combined_pair({G.lookup(i, h, C.remove(ri, rh, Con{entry, rest})) == None{} : Maybe<&2, G.Entry>},
        {G.matches(i, h, entry) == False{} : Bool}, {G.lookup(i, h, rest) == None{} : Maybe<&2, G.Entry>},
        absent_head(G.matches(i, h, entry), entry, G.lookup(i, h, rest), absent),
        no_head => no_tail => absent_remove_case(G.matches(ri, rh, entry), i, h, entry, C.remove(ri, rh, rest), no_head,
          absent_remove(i, h, ri, rh, rest, no_tail)))

def absent_remove_registry(+i: String, +h: String, +ri: String, +rh: String, reg: C.Registry,
  absent: {G.lookup(i, h, C.entries(reg)) == None{} : Maybe<&2, G.Entry>}) ->
  {G.lookup(i, h, C.entries(C.apply(C.ControlRemove{ri, rh}, reg))) == None{} : Maybe<&2, G.Entry>}:
  match reg:
    case C.ControlRegistry{es, history}: absent_remove(i, h, ri, rh, es, absent)

def distinct_fresh_case(same: Bool, +h: String, +candidate: String, +reg: C.Registry,
  known: {C.member(h, C.used(reg)) == True{} : Bool},
  fresh: {C.member(candidate, C.allocated(reg)) == False{} : Bool},
  exact: {String.eq(h, candidate) == same : Bool}) -> {String.eq(h, candidate) == False{} : Bool}:
  match same:
    case False{}: exact
    case True{}:
      L.ex_false({String.eq(h, candidate) == False{} : Bool},
        F.false_negative_true(Equal.trans(Bool, False{}, C.member(candidate, C.allocated(reg)), True{},
          Equal.sym(Bool, C.member(candidate, C.allocated(reg)), False{}, fresh),
          (%Orders.string_equal(h, candidate, exact) : {C.member(_, C.allocated(reg)) == True{} : Bool}
            used_allocated(h, reg, known)))))

def and_false(a: Bool, -b: Bool, no: {b == False{} : Bool}) -> {a && b == False{} : Bool}:
  match a:
    case False{}: {==}
    case True{}: no

def absent_add(+i: String, +h: String, +instance: String, +candidate: String,
  code: String, proof: String, reg: C.Registry,
  no_head: {String.eq(h, candidate) == False{} : Bool},
  absent: {G.lookup(i, h, C.entries(reg)) == None{} : Maybe<&2, G.Entry>}) ->
  {G.lookup(i, h, C.entries(C.apply(C.ControlAdd{G.Entry{instance, candidate, code, proof, False{}, ""}}, reg))) == None{} : Maybe<&2, G.Entry>}:
  match reg:
    case C.ControlRegistry{es, history}:
      %Equal.sym(Bool, String.eq(i, instance) && String.eq(h, candidate), False{},
        and_false(String.eq(i, instance), String.eq(h, candidate), no_head)) :
        {Bool.pick(Maybe<&2, G.Entry>, _, Some{G.Entry{instance, candidate, code, proof, False{}, ""}}, G.lookup(i, h, es)) == None{} : Maybe<&2, G.Entry>}
      absent

def absent_change(+i: String, +h: String, prepare: Bool, invalidate: Bool, +limits: S.Limits, +instance: String,
  +reg: C.Registry, +r: P.Request, +a: C.Admission, +candidate: String, +change: C.Change, -receipt: W.Receipt,
  known: {C.member(h, C.used(reg)) == True{} : Bool},
  absent: {G.lookup(i, h, C.entries(reg)) == None{} : Maybe<&2, G.Entry>},
  checked: T.ControlChangeAt(prepare, invalidate, S.Configuration{D.Schema{Nil{}}, S.NoneLaw{}, limits, instance}, reg, r, a, candidate, change, receipt)) ->
  {G.lookup(i, h, C.entries(C.apply(change, reg))) == None{} : Maybe<&2, G.Entry>}:
  match prepare invalidate:
    case True{} _:
      L.Both{matched, L.Both{shape, L.Both{fresh, L.Both{exact, received}}}} = checked
      %Equal.sym(C.Change, change, C.ControlAdd{G.Entry{instance, candidate, Gate.code(r), Resolve.proof(r), False{}, ""}}, exact) :
        {G.lookup(i, h, C.entries(C.apply(_, reg))) == None{} : Maybe<&2, G.Entry>}
      absent_add(i, h, instance, candidate, Gate.code(r), Resolve.proof(r), reg,
        distinct_fresh_case(String.eq(h, candidate), h, candidate, reg, known, fresh, {==}), absent)
    case False{} True{}:
      L.Both{empty, L.Both{found, L.Both{exact, received}}} = checked
      %Equal.sym(C.Change, change, C.ControlRemove{instance, Gate.code(r)}, exact) :
        {G.lookup(i, h, C.entries(C.apply(_, reg))) == None{} : Maybe<&2, G.Entry>}
      absent_remove_registry(i, h, instance, Gate.code(r), reg, absent)
    case False{} False{}: match checked:

def absent_projected(+i: String, +h: String, +limits: S.Limits, +instance: String, +plan: C.Plan,
  -s: D.State, +r: P.Request, prepare: Bool, invalidate: Bool, +root: D.State, +reg: C.Registry, +a: C.Admission, +candidate: String,
  known: {C.member(h, C.used(reg)) == True{} : Bool},
  absent: {G.lookup(i, h, C.entries(reg)) == None{} : Maybe<&2, G.Entry>},
  checked: T.ControlPlanAt(plan, S.Configuration{D.Schema{Nil{}}, S.NoneLaw{}, limits, instance}, s, r, prepare, invalidate, reg, a, candidate)) ->
  {G.lookup(i, h, C.entries(T.next_registry(C.finish(plan, root, Nil{}, reg)))) == None{} : Maybe<&2, G.Entry>}:
  match plan:
    case C.ControlDenied{status}: absent
    case C.ControlReady{ctx, +change, receipt, bytes}:
      L.Both{auth, L.Both{change_ok, receipt_ok}} = checked
      absent_change(i, h, prepare, invalidate, limits, instance, reg, r, a, candidate, change, receipt, known, absent, change_ok)

def absent_errors(+i: String, +h: String, +plan: C.Plan, +root: D.State, +reg: C.Registry,
  absent: {G.lookup(i, h, C.entries(reg)) == None{} : Maybe<&2, G.Entry>}, checked: T.ControlErrors(plan)) ->
  {G.lookup(i, h, C.entries(T.next_registry(C.finish(plan, root, Nil{}, reg)))) == None{} : Maybe<&2, G.Entry>}:
  match plan:
    case C.ControlDenied{status}: absent
    case C.ControlReady{ctx, change, receipt, bytes}: match checked:

def absent_routed(+i: String, +h: String, +limits: S.Limits, +instance: String, +input: Dispatch.Routed, +plan: C.Plan,
  +root: D.State, +reg: C.Registry, +a: C.Admission, +candidate: String,
  known: {C.member(h, C.used(reg)) == True{} : Bool},
  absent: {G.lookup(i, h, C.entries(reg)) == None{} : Maybe<&2, G.Entry>},
  checked: T.ControlPlan(plan, input, S.Configuration{D.Schema{Nil{}}, S.NoneLaw{}, limits, instance}, reg, a, candidate)) ->
  {G.lookup(i, h, C.entries(T.next_registry(C.finish(plan, root, Nil{}, reg)))) == None{} : Maybe<&2, G.Entry>}:
  match input:
    case Dispatch.Routed{+tag, Input.InputReady{+s, +r}}:
      absent_projected(i, h, limits, instance, plan, s, r, U32.is_eq(tag, 3), U32.is_eq(tag, 5), root, reg, a, candidate, known, absent, checked)
    case Dispatch.Routed{tag, Input.ErrorMessage{status}}: absent_errors(i, h, plan, root, reg, absent, checked)
    case Dispatch.Routed{tag, Input.ErrorTransport{}}: absent_errors(i, h, plan, root, reg, absent, checked)

def no_revival_fold(+schema: D.Schema, -laws: S.Laws, +limits: S.Limits, +instance: String, j: Nat,
  +root: D.State, +reg: C.Registry, +i: String, +h: String,
  run: T.ServiceRun<S.Configuration{schema, laws, limits, instance}, root, reg>,
  +known: {C.member(h, C.used(reg)) == True{} : Bool},
  absent: {G.lookup(i, h, C.entries(reg)) == None{} : Maybe<&2, G.Entry>}) ->
  T.RevokedAt(j, i, h, S.Configuration{schema, laws, limits, instance}, root, reg, run):
  match j run:
    case _ T.ServiceEnd{}: L.Both{handle_retired(h, reg, known), absent}
    case 0n T.ServiceTransaction{request, admit, next, sound, step, rest}: L.Both{handle_retired(h, reg, known), absent}
    case 0n T.ServiceControl{body, a, candidate, sound, rest}: L.Both{handle_retired(h, reg, known), absent}
    case 1n+n T.ServiceTransaction{request, admit, +next, sound, step, rest}:
      no_revival_fold(schema, laws, limits, instance, n, next, reg, i, h, rest, known, absent)
    case 1n+n T.ServiceControl{+body, +a, +candidate, sound, rest}:
      no_revival_fold(schema, laws, limits, instance, n, root,
        T.next_registry(C.control(S.Configuration{schema, S.NoneLaw{}, limits, instance}, root, Nil{}, reg, body, a, candidate)), i, h, rest,
        used_after_plan(C.plan(S.Configuration{schema, S.NoneLaw{}, limits, instance}, root, reg, body, a, candidate), root, reg, h, known),
        absent_routed(i, h, limits, instance, Dispatch.received(limits, body, root),
          C.plan(S.Configuration{schema, S.NoneLaw{}, limits, instance}, root, reg, body, a, candidate), root, reg, a, candidate, known, absent,
          Clauses.routed(schema, laws, limits, instance, Dispatch.received(limits, body, root), reg, a, candidate)))

def no_revival_configuration(c: S.Configuration, root: D.State, reg: C.Registry, i: String, h: String,
  run: T.ServiceRun<c, root, reg>, known: {C.member(h, C.used(reg)) == True{} : Bool},
  absent: {G.lookup(i, h, C.entries(reg)) == None{} : Maybe<&2, G.Entry>}, j: Nat) ->
  T.RevokedAt(j, i, h, c, root, reg, run):
  match c:
    case S.Configuration{schema, laws, limits, instance}:
      no_revival_fold(schema, laws, limits, instance, j, root, reg, i, h, run, known, absent)

def service_no_revival_theorem() -> T.ServiceNoRevivalTheorem():
  c => root => reg => i => h => run => known => absent => j => no_revival_configuration(c, root, reg, i, h, run, known, absent, j)

def service_fold_theorem() -> T.ServiceFoldTheorem():
  c => root => run => configured => valid => j =>
    L.Both{service_config(c, root, run, configured, valid, j),
      L.Both{registry_lookup_theorem(), L.Both{registry_invalidation_theorem(),
        L.Both{service_lifetime_theorem(), service_no_revival_theorem()}}}}
