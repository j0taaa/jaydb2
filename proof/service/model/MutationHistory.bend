# Mutation-only history in the FULL service specification's physical vocabulary.
# A missing mutation is not justified by unchanged DB alone: successful reads
# update the published response pair, and failed invalidation cleanup still
# leaves a real registry removal. No actual observer/trace equality is assumed.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/Logic.bend as L
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/Protocol.bend as P
import ../../../contract/Requirements.bend as R
import ../../../contract/Semantics.bend as S
import ../../../src/Core.bend as N
import ../../SourceService.bend as Source
import ../../Foundations.bend as F
import ../specification/ServiceLaws.bend as E
import ./Host.bend as Host
import ./History.bend as History

type Effect is Data:
  Effect{prepared: Bool, mutation: E.Mutation}

def snapshot(instance: String, +state: Host.Published) -> E.Snapshot:
  E.Snapshot{instance, Host.database(state), Host.response(state), Host.entries(state)}

def transaction_effect(prepared: Bool, result: N.Prepared) -> Maybe<&2, Effect>:
  match result:
    case N.Prepared{state, events, S.Response{S.Success{}, value}, bytes}:
      Some{Effect{prepared, E.Publish{S.Response{S.Success{}, value}, bytes}}}
    case _: None{}

def control_effect(mutation: E.Mutation, result: H.ControlResult) -> Maybe<&2, Effect>:
  match result:
    case H.ControlResult{state, es, H.Metadata{receipt}}: Some{Effect{True{}, mutation}}
    case H.ControlResult{state, es, H.Error{status}}: None{}

def effect(~c: S.Configuration, +instance: String, +before: Host.Published, invocation: Host.Invocation) -> Maybe<&2, Effect>:
  match invocation:
    case Host.Invocation{world, selected, input, Host.Ordinary{request, execution}}:
      transaction_effect(False{}, Host.execution_prepared(execution))
    case Host.Invocation{world, selected, input, Host.Execute{raw, entry, execution}}:
      transaction_effect(True{}, Host.execution_prepared(execution))
    case Host.Invocation{world, selected, input, Host.Prepare{+raw, context, +read_only, +handle, +seal}}:
      +entry = {G.Entry{instance, handle, I.code(raw), I.proof(raw), read_only, seal} : G.Entry}
      control_effect(E.Register{entry}, H.register(c, Host.database(before), instance, entry, Host.entries(before)))
    case Host.Invocation{world, selected, input, Host.Invalidate{raw, context, failed}}:
      +handle = I.code(raw)
      control_effect(E.Invalidate{handle}, H.invalidate(c, Host.database(before), instance, handle, Host.entries(before)))
    case Host.Invocation{world, selected, input, Host.Unchanged{}}: None{}

def Silent(option: Maybe<&2, Effect>, -before: Host.Published, -after: Host.Published) -> Type:
  match option:
    case None{}: {after == before : Host.Published}
    case Some{effect}: Unit

def transaction_silent(prepared: Bool, result: N.Prepared, -state: D.State,
  -previous: List<&2, U32>, -es: List<&2, G.Entry>) ->
  Silent(transaction_effect(prepared, result), Host.Published{state, previous, es},
    Host.transaction(N.conclude(result, state), previous, es)):
  match result:
    case N.Prepared{w, ts, S.Response{S.Success{}, value}, bytes}: Unit{}
    case N.Prepared{w, ts, S.Response{S.Refusal{}, value}, bytes}: {==}
    case N.Prepared{w, ts, S.Response{S.Input{}, value}, bytes}: {==}
    case N.Prepared{w, ts, S.Response{S.Authentication{}, value}, bytes}: {==}
    case N.Prepared{w, ts, S.Response{S.Certificate{}, value}, bytes}: {==}
    case N.Prepared{w, ts, S.Response{S.DataError{}, value}, bytes}: {==}
    case N.Prepared{w, ts, S.Response{S.Limit{}, value}, bytes}: {==}
    case N.Prepared{w, ts, S.Response{S.Failure{}, value}, bytes}: {==}

def register_fits_silent(fits: Bool, -state: D.State, -previous: List<&2, U32>, -es: List<&2, G.Entry>, +entry: G.Entry) ->
  Silent(control_effect(E.Register{entry}, H.register_fits(fits, state, entry, es)), Host.Published{state, previous, es},
    Host.control(H.register_fits(fits, state, entry, es), previous)):
  match fits:
    case False{}: {==}
    case True{}: Unit{}

def register_found_silent(~c: S.Configuration, found: Maybe<&2, G.Entry>,
  -state: D.State, -previous: List<&2, U32>, -es: List<&2, G.Entry>, +entry: G.Entry) ->
  Silent(control_effect(E.Register{entry}, H.register_found(found, c, state, entry, es)), Host.Published{state, previous, es},
    Host.control(H.register_found(found, c, state, entry, es), previous)):
  match found:
    case Some{old}: {==}
    case None{}:
      register_fits_silent(R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{G.handle(entry)})), state, previous, es, entry)

def invalidate_fits_silent(fits: Bool, -state: D.State, -previous: List<&2, U32>, +es: List<&2, G.Entry>, +instance: String, +handle: String) ->
  Silent(control_effect(E.Invalidate{handle}, H.invalidate_fits(fits, state, instance, handle, es)), Host.Published{state, previous, es},
    Host.control(H.invalidate_fits(fits, state, instance, handle, es), previous)):
  match fits:
    case False{}: {==}
    case True{}: Unit{}

def invalidate_found_silent(~c: S.Configuration, found: Maybe<&2, G.Entry>,
  -state: D.State, -previous: List<&2, U32>, +es: List<&2, G.Entry>, +instance: String, +handle: String) ->
  Silent(control_effect(E.Invalidate{handle}, H.invalidate_found(found, c, state, instance, handle, es)), Host.Published{state, previous, es},
    Host.control(H.invalidate_found(found, c, state, instance, handle, es), previous)):
  match found:
    case None{}: {==}
    case Some{entry}:
      invalidate_fits_silent(R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})), state, previous, es, instance, handle)

law every_unrecorded_transition_preserves_entire_published_pair_and_registry:
  for ~c: S.Configuration
  for +instance: String
  for before: Host.Published
  for invocation: Host.Invocation
  Silent(effect(c, instance, before, invocation), before, Host.next(c, instance, before, invocation))
def every_unrecorded_transition_preserves_entire_published_pair_and_registry(c, instance, before, invocation):
  match before invocation:
    case Host.Published{state, previous, es} Host.Invocation{world, selected, input, Host.Ordinary{request, execution}}:
      transaction_silent(False{}, Host.execution_prepared(execution), state, previous, es)
    case Host.Published{state, previous, es} Host.Invocation{world, selected, input, Host.Execute{raw, entry, execution}}:
      transaction_silent(True{}, Host.execution_prepared(execution), state, previous, es)
    case Host.Published{+state, previous, +es} Host.Invocation{world, selected, input, Host.Prepare{+raw, context, +read_only, +handle, +seal}}:
      register_found_silent(c, G.lookup(instance, handle, es), state, previous, es,
        G.Entry{instance, handle, I.code(raw), I.proof(raw), read_only, seal})
    case Host.Published{+state, +previous, +es} Host.Invocation{world, selected, input, Host.Invalidate{raw, context, +failed}}:
      +handle = I.code(raw)
      %Equal.sym(Host.Published,
        Host.control(H.cleanup_invalidation(failed, H.invalidate(c, state, instance, handle, es)), previous),
        Host.control(H.invalidate(c, state, instance, handle, es), previous),
        Host.cleanup_keeps_complete_published_pair(failed, H.invalidate(c, state, instance, handle, es), previous)) :
        Silent(control_effect(E.Invalidate{handle}, H.invalidate(c, state, instance, handle, es)), Host.Published{state, previous, es}, _)
      invalidate_found_silent(c, G.lookup(instance, handle, es), state, previous, es, instance, handle)
    case Host.Published{state, previous, es} Host.Invocation{world, selected, input, Host.Unchanged{}}: {==}

def record(effect: Effect, +instance: String, invocation: Host.Invocation,
  time: Nat, before: Host.Published, after: Host.Published) -> E.Past:
  Effect{mode, mutation} = effect
  Host.Invocation{world, selected, input, command} = invocation
  E.Past{world, input, time, mode, mutation, snapshot(instance, before), snapshot(instance, after)}

def record_if(option: Maybe<&2, Effect>, +instance: String, invocation: Host.Invocation,
  time: Nat, before: Host.Published, after: Host.Published, rest: List<&2, E.Past>) -> List<&2, E.Past>:
  match option:
    case None{}: rest
    case Some{effect}: Con{record(effect, instance, invocation, time, before, after), rest}

def extract(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: Host.InputBook,
  +instance: String, ids: List<&2, Nat>, +position: Nat, +before: Host.Published) -> List<&2, E.Past>:
  match ids:
    case Nil{}: Nil{}
    case Con{index, rest}:
      +invocation = Host.call(c, binding, public, book, index)
      +after = Host.next(c, instance, before, invocation)
      record_if(effect(c, instance, before, invocation), instance, invocation, 1n+position, before, after,
        extract(c, binding, public, book, instance, rest, 1n+position, after))

def replay_step(option: Maybe<&2, Effect>, +instance: String, +invocation: Host.Invocation,
  +time: Nat, +before: Host.Published, +after: Host.Published, +rest: List<&2, E.Past>, -final: Host.Published,
  silent: Silent(option, before, after),
  replay: {E.replay(rest, snapshot(instance, after)) == snapshot(instance, final) : E.Snapshot}) ->
  {E.replay(record_if(option, instance, invocation, time, before, after, rest), snapshot(instance, before)) == snapshot(instance, final) : E.Snapshot}:
  match option:
    case None{}:
      %silent : {E.replay(rest, snapshot(instance, _)) == snapshot(instance, final) : E.Snapshot}
      replay
    case Some{Effect{mode, mutation}}:
      match invocation:
        case Host.Invocation{world, selected, input, command}: replay

law mutation_only_replay_is_exact_full_operational_current_state:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~book: Host.InputBook
  for +instance: String
  for +ids: List<&2, Nat>
  for +position: Nat
  for +before: Host.Published
  {E.replay(extract(c, binding, public, book, instance, ids, position, before), snapshot(instance, before)) ==
    snapshot(instance, History.run(c, binding, public, book, instance, ids, before)) : E.Snapshot}
def mutation_only_replay_is_exact_full_operational_current_state(c, binding, public, book, instance, ids, position, before):
  match ids:
    case Nil{}: {==}
    case Con{index, +rest}:
      +invocation = Host.call(c, binding, public, book, index)
      +after = Host.next(c, instance, before, invocation)
      replay_step(effect(c, instance, before, invocation), instance, invocation, 1n+position, before, after,
        extract(c, binding, public, book, instance, rest, 1n+position, after), History.run(c, binding, public, book, instance, rest, after),
        every_unrecorded_transition_preserves_entire_published_pair_and_registry(c, instance, before, invocation),
        mutation_only_replay_is_exact_full_operational_current_state(c, binding, public, book, instance, rest, 1n+position, after))

def RecordAt(option: Maybe<&2, Effect>, +instance: String, invocation: Host.Invocation,
  time: Nat, before: Host.Published, after: Host.Published, -past: E.Past) -> Type:
  match option:
    case None{}: Empty
    case Some{effect}: {record(effect, instance, invocation, time, before, after) == past : E.Past}

def MutationAt(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~book: Host.InputBook,
  +instance: String, ids: List<&2, Nat>, +position: Nat, +before: Host.Published, offset: Nat, -past: E.Past) -> Type:
  match ids offset:
    case Nil{} _: Empty
    case Con{index, rest} 0n:
      +invocation = Host.call(c, binding, public, book, index)
      RecordAt(effect(c, instance, before, invocation), instance, invocation, 1n+position, before, Host.next(c, instance, before, invocation), past)
    case Con{index, rest} 1n+k:
      MutationAt(c, binding, public, book, instance, rest, 1n+position, Host.next(c, instance, before, Host.call(c, binding, public, book, index)), k, past)

def first_record_occurs(option: Maybe<&2, Effect>, +instance: String, +invocation: Host.Invocation,
  +time: Nat, +before: Host.Published, +after: Host.Published, +rest: List<&2, E.Past>, -past: E.Past,
  at: RecordAt(option, instance, invocation, time, before, after, past)) ->
  E.Occurs(past, record_if(option, instance, invocation, time, before, after, rest)):
  match option:
    case None{}: L.ex_false(E.Occurs(past, rest), at)
    case Some{effect}: L.Left{at}

def later_record_occurs(option: Maybe<&2, Effect>, +instance: String, +invocation: Host.Invocation,
  +time: Nat, +before: Host.Published, +after: Host.Published, +rest: List<&2, E.Past>, -past: E.Past,
  later: E.Occurs(past, rest)) -> E.Occurs(past, record_if(option, instance, invocation, time, before, after, rest)):
  match option:
    case None{}: later
    case Some{effect}: L.Right{later}

law every_operational_mutation_is_in_the_physical_service_history:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~book: Host.InputBook
  for +instance: String
  for +ids: List<&2, Nat>
  for +position: Nat
  for +before: Host.Published
  for offset: Nat
  for -past: E.Past
  for at: MutationAt(c, binding, public, book, instance, ids, position, before, offset, past)
  E.Occurs(past, extract(c, binding, public, book, instance, ids, position, before))
def every_operational_mutation_is_in_the_physical_service_history(c, binding, public, book, instance, ids, position, before, offset, past, at):
  match ids offset:
    case Nil{} _: L.ex_false(E.Occurs(past, Nil{}), at)
    case Con{index, +rest} 0n:
      +invocation = Host.call(c, binding, public, book, index)
      +after = Host.next(c, instance, before, invocation)
      first_record_occurs(effect(c, instance, before, invocation), instance, invocation, 1n+position, before, after,
        extract(c, binding, public, book, instance, rest, 1n+position, after), past, at)
    case Con{index, +rest} 1n+k:
      +invocation = Host.call(c, binding, public, book, index)
      +after = Host.next(c, instance, before, invocation)
      later_record_occurs(effect(c, instance, before, invocation), instance, invocation, 1n+position, before, after,
        extract(c, binding, public, book, instance, rest, 1n+position, after), past,
        every_operational_mutation_is_in_the_physical_service_history(c, binding, public, book, instance, rest, 1n+position, after, k, past, at))

law successor_is_strictly_after:
  for n: Nat
  {Nat.is_lt(n, 1n+n) == True{} : Bool}
def successor_is_strictly_after(n):
  match n:
    case 0n: {==}
    case 1n+k: successor_is_strictly_after(k)

def lower_strict_bound(n: Nat, time: Nat, proof: {Nat.is_lt(1n+n, time) == True{} : Bool}) ->
  {Nat.is_lt(n, time) == True{} : Bool}:
  match n time:
    case 0n 0n: F.absurd_boolean({False{} == True{} : Bool}, proof)
    case 0n 1n+t: {==}
    case 1n+k 0n: F.absurd_boolean({False{} == True{} : Bool}, proof)
    case 1n+k 1n+t: lower_strict_bound(k, t, proof)

def OrderedFrom(-lower: Nat, records: List<&2, E.Past>) -> Type:
  match records:
    case Nil{}: Unit
    case Con{E.Past{world, input, +time, mode, mutation, before, after}, rest}:
      L.E<{Nat.is_lt(lower, time) == True{} : Bool}, OrderedFrom(time, rest)>

def weaken_start(+position: Nat, records: List<&2, E.Past>, ordered: OrderedFrom(1n+position, records)) -> OrderedFrom(position, records):
  match records ordered:
    case Nil{} _: Unit{}
    case Con{E.Past{world, input, +time, mode, mutation, before, after}, rest} L.Both{first, later}:
      L.Both{lower_strict_bound(position, time, first), later}

def ordered_if(option: Maybe<&2, Effect>, +instance: String, invocation: Host.Invocation,
  +position: Nat, before: Host.Published, after: Host.Published, +rest: List<&2, E.Past>,
  ordered: OrderedFrom(1n+position, rest)) ->
  OrderedFrom(position, record_if(option, instance, invocation, 1n+position, before, after, rest)):
  match option:
    case None{}: weaken_start(position, rest, ordered)
    case Some{Effect{mode, mutation}}:
      match invocation:
        case Host.Invocation{world, selected, input, command}: L.Both{successor_is_strictly_after(position), ordered}

law mutation_records_are_in_strict_chronological_order:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~book: Host.InputBook
  for +instance: String
  for +ids: List<&2, Nat>
  for +position: Nat
  for +before: Host.Published
  OrderedFrom(position, extract(c, binding, public, book, instance, ids, position, before))
def mutation_records_are_in_strict_chronological_order(c, binding, public, book, instance, ids, position, before):
  match ids:
    case Nil{}: Unit{}
    case Con{index, +rest}:
      +invocation = Host.call(c, binding, public, book, index)
      +after = Host.next(c, instance, before, invocation)
      ordered_if(effect(c, instance, before, invocation), instance, invocation, position, before, after,
        extract(c, binding, public, book, instance, rest, 1n+position, after),
        mutation_records_are_in_strict_chronological_order(c, binding, public, book, instance, rest, 1n+position, after))

def end_position(ids: List<&2, Nat>, position: Nat) -> Nat:
  match ids:
    case Nil{}: position
    case Con{index, rest}: end_position(rest, 1n+position)

law final_selection_is_after_every_start_position:
  for ids: List<&2, Nat>
  for +position: Nat
  {Nat.is_lt(position, 1n+end_position(ids, position)) == True{} : Bool}
def final_selection_is_after_every_start_position(ids, position):
  match ids:
    case Nil{}: successor_is_strictly_after(position)
    case Con{index, +rest}:
      lower_strict_bound(position, 1n+end_position(rest, 1n+position), final_selection_is_after_every_start_position(rest, 1n+position))

def Before(-upper: Nat, records: List<&2, E.Past>) -> Type:
  match records:
    case Nil{}: Unit
    case Con{E.Past{world, input, time, mode, mutation, before, after}, rest}:
      L.E<{Nat.is_lt(time, upper) == True{} : Bool}, Before(upper, rest)>

def bounded_if(option: Maybe<&2, Effect>, +instance: String, invocation: Host.Invocation,
  +position: Nat, before: Host.Published, after: Host.Published, rest: List<&2, E.Past>, -upper: Nat,
  first: {Nat.is_lt(1n+position, upper) == True{} : Bool}, bounded: Before(upper, rest)) ->
  Before(upper, record_if(option, instance, invocation, 1n+position, before, after, rest)):
  match option:
    case None{}: bounded
    case Some{Effect{mode, mutation}}:
      match invocation:
        case Host.Invocation{world, selected, input, command}: L.Both{first, bounded}

law every_record_precedes_selection_of_the_current_call:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~book: Host.InputBook
  for +instance: String
  for +ids: List<&2, Nat>
  for +position: Nat
  for +before: Host.Published
  Before(1n+end_position(ids, position), extract(c, binding, public, book, instance, ids, position, before))
def every_record_precedes_selection_of_the_current_call(c, binding, public, book, instance, ids, position, before):
  match ids:
    case Nil{}: Unit{}
    case Con{index, +rest}:
      +invocation = Host.call(c, binding, public, book, index)
      +after = Host.next(c, instance, before, invocation)
      bounded_if(effect(c, instance, before, invocation), instance, invocation, position, before, after,
        extract(c, binding, public, book, instance, rest, 1n+position, after), 1n+end_position(rest, 1n+position),
        final_selection_is_after_every_start_position(rest, 1n+position),
        every_record_precedes_selection_of_the_current_call(c, binding, public, book, instance, rest, 1n+position, after))

def Linked(-initial: E.Snapshot, records: List<&2, E.Past>) -> Type:
  match records:
    case Nil{}: Unit
    case Con{E.Past{world, input, time, mode, mutation, +before, +after}, rest}:
      L.E<{before == initial : E.Snapshot},
        L.E<{E.instance(before) == E.instance(after) : String}, Linked(after, rest)>>

def linked_if(option: Maybe<&2, Effect>, +instance: String, invocation: Host.Invocation,
  +time: Nat, +before: Host.Published, +after: Host.Published, +rest: List<&2, E.Past>,
  silent: Silent(option, before, after), linked: Linked(snapshot(instance, after), rest)) ->
  Linked(snapshot(instance, before), record_if(option, instance, invocation, time, before, after, rest)):
  match option:
    case None{}:
      %silent : Linked(snapshot(instance, _), rest)
      linked
    case Some{Effect{mode, mutation}}:
      match invocation:
        case Host.Invocation{world, selected, input, command}: L.Both{{==}, L.Both{{==}, linked}}

law mutation_history_links_exact_complete_snapshots_from_the_seed:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~book: Host.InputBook
  for +instance: String
  for +ids: List<&2, Nat>
  for +position: Nat
  for +before: Host.Published
  Linked(snapshot(instance, before), extract(c, binding, public, book, instance, ids, position, before))
def mutation_history_links_exact_complete_snapshots_from_the_seed(c, binding, public, book, instance, ids, position, before):
  match ids:
    case Nil{}: Unit{}
    case Con{index, +rest}:
      +invocation = Host.call(c, binding, public, book, index)
      +after = Host.next(c, instance, before, invocation)
      linked_if(effect(c, instance, before, invocation), instance, invocation, 1n+position, before, after,
        extract(c, binding, public, book, instance, rest, 1n+position, after),
        every_unrecorded_transition_preserves_entire_published_pair_and_registry(c, instance, before, invocation),
        mutation_history_links_exact_complete_snapshots_from_the_seed(c, binding, public, book, instance, rest, 1n+position, after))
