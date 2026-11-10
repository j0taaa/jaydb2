import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Logic.bend as L
import ./Requirements.bend as R
import ./Termination.bend as T
import ./RequestFacts.bend as F
import ./Model.bend as M
import ./Policy.bend as P
import ./CheckedActions.bend as H
import ./Completion.bend as End
import ./Configuration.bend as C
import ./Client.bend as Client
import ./Action.bend as A
import ./Index.bend as X
import ./Instance.bend as I
import ./Bindings.bend as B
import ./Environment.bend as E
import ./Orders.bend as O

def set_alice(+a:Bool,+b:Bool,+kind:String,new:Bool) ->
  H.Safe(6n,C.schema(),D.Context{"alice",kind},M.state(a,b),Client.command("alice",Client.Set{new})):
  match new:
    case False{}: L.Both{{==},L.Both{M.Laid{a,b,Nil{},[M.entry(b)],{==}},L.Both{{==},L.Both{M.Laid{a,b,[M.entry(False{})],[M.entry(b)],{==}},L.Both{{==},L.Both{M.Laid{False{},b,[M.entry(False{})],[M.entry(b)],{==}},L.Both{{==},{==}}}}}}}}
    case True{}: L.Both{{==},L.Both{M.Laid{a,b,Nil{},[M.entry(b)],{==}},L.Both{{==},L.Both{M.Laid{a,b,[M.entry(True{})],[M.entry(b)],{==}},L.Both{{==},L.Both{M.Laid{True{},b,[M.entry(True{})],[M.entry(b)],{==}},L.Both{{==},{==}}}}}}}}

def query_alice(+a:Bool,+b:Bool,+kind:String,wanted:Bool) ->
  H.Safe(6n,C.schema(),D.Context{"alice",kind},M.state(a,b),Client.command("alice",Client.Query{wanted})):
  L.Both{{==},L.Both{{==},L.Both{{==},L.Both{{==},{==}}}}}

def rebuild_alice(+a:Bool,+b:Bool,+kind:String) ->
  H.Safe(6n,C.schema(),D.Context{"alice",kind},M.state(a,b),Client.command("alice",Client.Rebuild{})):
  match a:
    case False{}: L.Both{{==},L.Both{{==},L.Both{{==},L.Both{M.Laid{False{},b,Nil{},[M.entry(b)],{==}},L.Both{{==},L.Both{M.Laid{False{},b,[M.entry(False{})],[M.entry(b)],{==}},L.Both{{==},{==}}}}}}}}
    case True{}: L.Both{{==},L.Both{{==},L.Both{{==},L.Both{M.Laid{True{},b,Nil{},[M.entry(b)],{==}},L.Both{{==},L.Both{M.Laid{True{},b,[M.entry(True{})],[M.entry(b)],{==}},L.Both{{==},{==}}}}}}}}

def set_bob(+a:Bool,+b:Bool,+kind:String,new:Bool) ->
  H.Safe(6n,C.schema(),D.Context{"bob",kind},M.state(a,b),Client.command("bob",Client.Set{new})):
  match new:
    case False{}: L.Both{{==},L.Both{M.Laid{a,b,[M.entry(a)],Nil{},{==}},L.Both{{==},L.Both{M.Laid{a,b,[M.entry(a)],[M.entry(False{})],{==}},L.Both{{==},L.Both{M.Laid{a,False{},[M.entry(a)],[M.entry(False{})],{==}},L.Both{{==},{==}}}}}}}}
    case True{}: L.Both{{==},L.Both{M.Laid{a,b,[M.entry(a)],Nil{},{==}},L.Both{{==},L.Both{M.Laid{a,b,[M.entry(a)],[M.entry(True{})],{==}},L.Both{{==},L.Both{M.Laid{a,True{},[M.entry(a)],[M.entry(True{})],{==}},L.Both{{==},{==}}}}}}}}

def query_bob(+a:Bool,+b:Bool,+kind:String,wanted:Bool) ->
  H.Safe(6n,C.schema(),D.Context{"bob",kind},M.state(a,b),Client.command("bob",Client.Query{wanted})):
  L.Both{{==},L.Both{{==},L.Both{{==},L.Both{{==},{==}}}}}

def rebuild_bob(+a:Bool,+b:Bool,+kind:String) ->
  H.Safe(6n,C.schema(),D.Context{"bob",kind},M.state(a,b),Client.command("bob",Client.Rebuild{})):
  match b:
    case False{}: L.Both{{==},L.Both{{==},L.Both{{==},L.Both{M.Laid{a,False{},[M.entry(a)],Nil{},{==}},L.Both{{==},L.Both{M.Laid{a,False{},[M.entry(a)],[M.entry(False{})],{==}},L.Both{{==},{==}}}}}}}}
    case True{}: L.Both{{==},L.Both{{==},L.Both{{==},L.Both{M.Laid{a,True{},[M.entry(a)],Nil{},{==}},L.Both{{==},L.Both{M.Laid{a,True{},[M.entry(a)],[M.entry(True{})],{==}},L.Both{{==},{==}}}}}}}}


def alice_command_safe(+a:Bool,+b:Bool,+kind:String,p:Client.Command) ->
  H.Safe(6n,C.schema(),D.Context{"alice",kind},M.state(a,b),Client.command("alice",p)):
  match p:
    case Client.Set{n}: set_alice(a,b,kind,n)
    case Client.Query{n}: query_alice(a,b,kind,n)
    case Client.Rebuild{}: rebuild_alice(a,b,kind)
    case Client.Invalid{}: L.Both{{==},{==}}

def bob_command_safe(+a:Bool,+b:Bool,+kind:String,p:Client.Command) ->
  H.Safe(6n,C.schema(),D.Context{"bob",kind},M.state(a,b),Client.command("bob",p)):
  match p:
    case Client.Set{n}: set_bob(a,b,kind,n)
    case Client.Query{n}: query_bob(a,b,kind,n)
    case Client.Rebuild{}: rebuild_bob(a,b,kind)
    case Client.Invalid{}: L.Both{{==},{==}}

def flags_safe(alice:Bool,bob:Bool,+a:Bool,+b:Bool,+id:String,+kind:String,+args:D.Value,
  ha:{String.eq(id,"alice") == alice : Bool},hb:{String.eq(id,"bob") == bob : Bool}) ->
  H.Safe(6n,C.schema(),D.Context{id,kind},M.state(a,b),Client.flags(alice,bob,args)):
  match alice bob:
    case True{} bob:
      %Equal.sym(String,id,"alice",O.string_equal(id,"alice",ha)) : H.Safe(6n,C.schema(),D.Context{_,kind},M.state(a,b),Client.command("alice",Client.analyze(args)))
      alice_command_safe(a,b,kind,Client.analyze(args))
    case False{} True{}:
      %Equal.sym(String,id,"bob",O.string_equal(id,"bob",hb)) : H.Safe(6n,C.schema(),D.Context{_,kind},M.state(a,b),Client.command("bob",Client.analyze(args)))
      bob_command_safe(a,b,kind,Client.analyze(args))
    case False{} False{}: L.Both{{==},{==}}

def start_safe(+a:Bool,+b:Bool,ctx:D.Context,args:D.Value) -> H.Safe(6n,C.schema(),ctx,M.state(a,b),S.start(Client.program(),ctx,args)):
  D.Context{+id,kind}=ctx
  flags_safe(String.eq(id,"alice"),String.eq(id,"bob"),a,b,id,kind,args,{==},{==})

def Target(+ctx:D.Context,+args:D.Value,code:String,+n:Nat,+s:D.State) -> Type:
  R.SafetyTrace(S.execute(n,Client.program(),C.schema(),s,ctx,args),C.config(),s,ctx,code,args)

def certify_canonical(+ctx:D.Context,+args:D.Value,-code:String,+a:Bool,+b:Bool,+n:Nat) -> Target(ctx,args,code,n,M.state(a,b)):
  H.execution_trace(S.execute(n,Client.program(),C.schema(),M.state(a,b),ctx,args),C.schema(),C.limits(),E.identity(),M.state(a,b),ctx,code,args,
    H.rewind(ctx,S.execute(n,Client.program(),C.schema(),M.state(a,b),ctx,args),T.observe(n,S.start(Client.program(),ctx,args),C.schema(),M.state(a,b),Nil{}),
      Equal.sym(S.Trace,T.observe(n,S.start(Client.program(),ctx,args),C.schema(),M.state(a,b),Nil{}),S.execute(n,Client.program(),C.schema(),M.state(a,b),ctx,args),T.reference(n,S.start(Client.program(),ctx,args),C.schema(),M.state(a,b))),
      H.safe(6n,n,S.start(Client.program(),ctx,args),ctx,C.schema(),M.state(a,b),Nil{},start_safe(a,b,ctx,args),P.Both{M.Laid{a,b,[M.entry(a)],[M.entry(b)],{==}},Unit{}})))

def initial(+s:D.State,valid:R.Valid(C.config(),s)) -> M.Coherent(s):
  match valid:
    case L.Both{structure,L.Both{layout,L.Both{indexes,Unit{}}}}: M.canonical(s,layout,indexes)

def certify(+ctx:D.Context,+args:D.Value,-code:String,+n:Nat,+s:D.State,exact:M.Coherent(s)) -> Target(ctx,args,code,n,s):
  match exact:
    case M.Exact{+a,+b,eq}:
      %Equal.sym(D.State,s,M.state(a,b),eq) : Target(ctx,args,code,n,_)
      certify_canonical(ctx,args,code,a,b,n)

# Actual termination on arbitrary states, including invalid/malformed tables.
# Enumeration determines a finite list-dependent bound; it is not assumed to
# return the valid-state singleton, and it does not use a host resource limit.
def rebuild_complete(+owner:String,info:Client.Availability,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>) ->
  End.Complete(Client.rebuild_known(owner,info),e,s,ts):
  match info:
    case Client.Known{b}: End.rebuild(D.Application{owner ++ "_index"},M.entry(b),e,s,ts)
    case Client.InvalidAvailability{}: End.finite(1n,S.Refuse{D.VText{"invalid availability"}},e,s,ts,Unit{})

def command_complete(+owner:String,p:Client.Command,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>) -> End.Complete(Client.command(owner,p),e,s,ts):
  match p:
    case Client.Set{+b}:
      End.finite(4n,Client.command(owner,Client.Set{b}),e,s,ts,
        End.removes(["item"],3n,D.Application{owner ++ "_index"},A.define_rows(D.Application{owner ++ "_index"},[M.entry(b)],A.define_rows(D.Application{owner},[M.business(b)],S.Finish{D.VBool{b}})),
          End.writes([M.entry(b)],2n,D.Application{owner ++ "_index"},A.define_rows(D.Application{owner},[M.business(b)],S.Finish{D.VBool{b}}),End.writes([M.business(b)],1n,D.Application{owner},S.Finish{D.VBool{b}},Unit{}))))
    case Client.Query{b}: End.lookup(D.Application{owner ++ "_index"},[M.tag(b)],e,s,ts)
    case Client.Rebuild{}:
      End.access(D.ReadCell{D.Application{owner},"item","available"},r => Client.rebuild_known(owner,Client.availability(r)),e,s,ts,
        r => w => events => rebuild_complete(owner,Client.availability(r),e,w,events))
    case Client.Invalid{}: End.finite(1n,S.Refuse{D.VText{"invalid request"}},e,s,ts,Unit{})

def flags_complete(alice:Bool,bob:Bool,+args:D.Value,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>) -> End.Complete(Client.flags(alice,bob,args),e,s,ts):
  match alice bob:
    case True{} bob: command_complete("alice",Client.analyze(args),e,s,ts)
    case False{} True{}: command_complete("bob",Client.analyze(args),e,s,ts)
    case False{} False{}: End.finite(1n,S.Refuse{D.VText{"unknown principal"}},e,s,ts,Unit{})

def start_complete(ctx:D.Context,+args:D.Value,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>) -> End.Complete(S.start(Client.program(),ctx,args),e,s,ts):
  D.Context{+id,kind}=ctx
  flags_complete(String.eq(id,"alice"),String.eq(id,"bob"),args,e,s,ts)

def terminates_complete(+s:D.State,+ctx:D.Context,+args:D.Value,h:End.Complete(S.start(Client.program(),ctx,args),C.schema(),s,Nil{})) -> F.Terminates(Client.program(),C.schema(),s,ctx,args):
  match h:
    case (+n,w,events,r,eq): T.witness_program(n,Client.program(),C.schema(),s,ctx,args,(w,events,r,eq))

def B.certificate(s,valid,identity,n):
  +s=s
  certify(I.context(),I.arguments(),B.code(),n,s,initial(s,valid))

def B.terminates(s,ctx,args):
  +s=s
  +ctx=ctx
  +args=args
  terminates_complete(s,ctx,args,start_complete(ctx,args,C.schema(),s,Nil{}))
