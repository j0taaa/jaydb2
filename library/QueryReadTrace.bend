# Exact REAL execution through a successfully observed owned read prefix.
# The domain certificate identifies each actual D.operate result separately;
# it never assumes the final trace, selection, continuation, or completion.
# Actual data failure is handled separately by Operate's stopping theorem.
import Base
import ./QuerySelectionModel.bend as Model
import ./ValueScalarProofs.bend as Scalar
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ./Query.bend as Query
import ./ReadProgram.bend as Program
import ./Laws.bend as Depth
import ./Proofs.bend as Event
import ../src/Termination.bend as T


def returned(~Env: Data,~observation: Env -> Nat -> D.Observation,env: Env,index: Nat) -> S.Return:
  S.Datum{observation(env,index)}

def ObservedReads(~Env: Data,~observation: Env -> Nat -> D.Observation,+env: Env,names: List<&2,String>,+index: Nat,+schema: D.Schema,+state: D.State,+collection: D.Collection,+key: String) -> Data:
  match names:
    case Nil{}: Unit
    case Con{name,tail}: Scalar.Both<{D.operate(schema,state,D.ReadCell{collection,key,name}) == D.Observed{observation(env,index)} : D.ResultOp},ObservedReads(~Env,~observation,env,tail,1n+index,schema,state,collection,key)>


def events(~Env: Data,~observation: Env -> Nat -> D.Observation,+env: Env,names: List<&2,String>,+index: Nat,+collection: D.Collection,+key: String) -> List<&2,S.OperationEvent>:
  match names:
    case Nil{}: Nil{}
    case Con{name,tail}: Con{S.OperationEvent{D.ReadCell{collection,key,name},S.Reading{observation(env,index)}},events(~Env,~observation,env,tail,1n+index,collection,key)}

def append_events(later: List<&2,S.OperationEvent>,history: List<&2,S.OperationEvent>) -> List<&2,S.OperationEvent>:
  match later:
    case Nil{}: history
    case Con{event,tail}: append_events(tail,S.append(history,event))

law actual_observed_read_prefix_retains_exact_events_then_hands_off_exact_selection:
  for ~Env: Data
  for ~observation: Env -> Nat -> D.Observation
  for +env: Env
  for +names: List<&2,String>
  for +index: Nat
  for +remaining: Nat
  for +schema: D.Schema
  for +state: D.State
  for +collection: D.Collection
  for +key: String
  for -done: Query.Selection -> S.Action
  for +history: List<&2,S.OperationEvent>
  for observed: ObservedReads(~Env,~observation,env,names,index,schema,state,collection,key)
  {T.observe(Depth.depth(names,remaining),Query.read_fields(collection,key,names,done),schema,state,history) == T.observe(remaining,done(Model.expected(~Env,~returned(~Env,~observation),env,index,names)),schema,state,append_events(events(~Env,~observation,env,names,index,collection,key),history)) : S.Trace}
def actual_observed_read_prefix_retains_exact_events_then_hands_off_exact_selection(Env,observation,env,names,index,remaining,schema,state,collection,key,done,history,observed):
  match names observed:
    case Nil{} Unit{}: {==}
    case Con{+name,+tail} Scalar.Both{head,rest}:
      Equal.trans(S.Trace,
        T.observe(Depth.depth(Con{name,tail},remaining),Query.read_fields(collection,key,Con{name,tail},done),schema,state,history),
        T.observe(Depth.depth(tail,remaining),Query.read_fields(collection,key,tail,result => done(Query.combine(name,returned(~Env,~observation,env,index),result))),schema,state,S.append(history,S.OperationEvent{D.ReadCell{collection,key,name},S.Reading{observation(env,index)}})),
        T.observe(remaining,done(Model.expected(~Env,~returned(~Env,~observation),env,index,Con{name,tail})),schema,state,append_events(events(~Env,~observation,env,Con{name,tail},index,collection,key),history)),
        Event.read_continuation(Depth.depth(tail,remaining),schema,state,D.ReadCell{collection,key,name},observation(env,index),Query.received(name,done,next => Query.read_fields(collection,key,tail,next)),history,head),
        Equal.trans(S.Trace,
          T.observe(Depth.depth(tail,remaining),Query.read_fields(collection,key,tail,result => done(Query.combine(name,returned(~Env,~observation,env,index),result))),schema,state,S.append(history,S.OperationEvent{D.ReadCell{collection,key,name},S.Reading{observation(env,index)}})),
          T.observe(remaining,done(Query.combine(name,returned(~Env,~observation,env,index),Model.expected(~Env,~returned(~Env,~observation),env,1n+index,tail))),schema,state,append_events(events(~Env,~observation,env,tail,1n+index,collection,key),S.append(history,S.OperationEvent{D.ReadCell{collection,key,name},S.Reading{observation(env,index)}}))),
          T.observe(remaining,done(Model.expected(~Env,~returned(~Env,~observation),env,index,Con{name,tail})),schema,state,append_events(events(~Env,~observation,env,Con{name,tail},index,collection,key),history)),
          actual_observed_read_prefix_retains_exact_events_then_hands_off_exact_selection(~Env,~observation,env,tail,1n+index,remaining,schema,state,collection,key,result => done(Query.combine(name,returned(~Env,~observation,env,index),result)),S.append(history,S.OperationEvent{D.ReadCell{collection,key,name},S.Reading{observation(env,index)}}),rest),
          Equal.cong(Query.Selection,S.Trace,result => T.observe(remaining,done(result),schema,state,append_events(events(~Env,~observation,env,Con{name,tail},index,collection,key),history)),
            Query.combine(name,returned(~Env,~observation,env,index),Model.expected(~Env,~returned(~Env,~observation),env,1n+index,tail)),Model.expected(~Env,~returned(~Env,~observation),env,index,Con{name,tail}),
            Equal.sym(Query.Selection,Model.expected(~Env,~returned(~Env,~observation),env,index,Con{name,tail}),Query.combine(name,returned(~Env,~observation,env,index),Model.expected(~Env,~returned(~Env,~observation),env,1n+index,tail)),Model.independent_selection_meaning_has_exact_head_and_tail_composition(~Env,~returned(~Env,~observation),env,index,name,tail)))))
