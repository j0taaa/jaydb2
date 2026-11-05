# Executed serial protocol. Only Effects.drive interprets HostWait/HostExit.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../src/Transport.bend as T
import ./Policy.bend as P
import ./Effects.bend as E

type Handle is Data:
  Handle{key: P.Bytes, artifact: P.Bytes, code: P.Bytes, proof: P.Bytes}

type Database is Data:
  Database{limits: P.Limits, state: P.Bytes, handles: List<&2, Handle>}

type State is Type:
  Boot{}
  HostWait{bytes: P.Bytes, next: P.Bytes -> State}
  ReadHeader{database: Database}
  SendResponse{database: Database, response: P.Bytes}
  RandomHandle{database: Database, artifact: P.Bytes, code: P.Bytes, proof: P.Bytes}
  HostExit{code: U32}

type Reply is Data:
  Good{bytes: P.Bytes}
  Bad{code: P.Bytes}

def reply(+bs: P.Bytes) -> Reply:
  match bs:
    case Con{1,rest}:
      Good{rest}
    case Con{0,code}:
      Bad{code}
    case _:
      Bad{B.utf8("HOST_TRANSPORT")}
def receive(+result: Reply, yes: @+bytes: P.Bytes -> State, no: @+bytes: P.Bytes -> State) -> State:
  match result:
    case Good{bytes}:
      yes(bytes)
    case Bad{code}:
      no(code)
def call(+op: U32, +fields: P.Bytes, next: Reply -> State) -> State:
  HostWait{Con{op,fields},bs => next(reply(bs))}
def lookup(+key: P.Bytes, +handles: List<&2,Handle>) -> Maybe<&2,Handle>:
  match handles:
    case Nil{}:
      None{}
    case Con{+h,rest}:
      Handle{k,a,c,p} = h
      P.choose(Maybe<&2,Handle>,P.equal(key,k),u => Some{h},u => lookup(key,rest))
def remove(+key: P.Bytes, +handles: List<&2,Handle>) -> List<&2,Handle>:
  match handles:
    case Nil{}:
      Nil{}
    case Con{+h,rest}:
      Handle{k,a,c,p} = h
      P.choose(List<&2,Handle>,P.equal(key,k),u => rest,u => Con{h,remove(key,rest)})
def inspect(+db: Database, +event: U32, +payload: P.Bytes, next: Reply -> State) -> State:
  Database{limits,state,handles} = db
  call(9,Con{event,P.packet(payload,state)},next)
def serve(+db: Database) -> State:
  ReadHeader{db}
def initial_removed(+db: Database, +result: Reply) -> State:
  receive(result,unused => inspect(db,0,Nil{},done => serve(db)),code => HostExit{1})
def initial_run(+result: Reply, +limits: P.Limits) -> State:
  match result:
    case Good{Con{1,+state}}:
      P.Limits{m,s,r} = limits
      P.choose(State,P.fits(state,s),
        u => call(7,B.utf8("initial"),removed => initial_removed(Database{limits,state,Nil{}},removed)),
        u => HostExit{1})
    case _:
      HostExit{1}
def initialized_bytes(+bytes: P.Bytes) -> State:
  match bytes:
    case Con{a,Con{b,Con{c,Con{d,Con{e,Con{f,Con{g,Con{h,Con{i,Con{j,Con{k,Con{l,Con{m,Con{n,Con{o,Con{p,Con{q,Con{r,Con{s,Con{t,Con{u,Con{v,Con{w,Con{x,Nil{}}}}}}}}}}}}}}}}}}}}}}}}}:
      limits : P.Limits = P.Limits{B.Number64{T.word(a,b,c,d),T.word(e,f,g,h)},B.Number64{T.word(i,j,k,l),T.word(m,n,o,p)},B.Number64{T.word(q,r,s,t),T.word(u,v,w,x)}}
      call(5,P.packet(B.utf8("initial"),Nil{}),result => initial_run(result,limits))
    case _:
      HostExit{1}
def initialized(+result: Reply) -> State:
  receive(result,bytes => initialized_bytes(bytes),code => HostExit{1})
def terminal(status: S.Status) -> State:
  call(2,P.error(status),ignored => HostExit{0})
def emit(+db: Database, +response: P.Bytes) -> State:
  SendResponse{db,response}
def complete_published(+publication: P.Publication, +limits: P.Limits, +handles: List<&2,Handle>) -> State:
  P.Publication{state,response} = publication
  +updated : Database = Database{limits,state,handles}
  inspect(updated,1,Nil{},done => emit(updated,response))
def complete(+db: Database, +proposal: P.Proposal) -> State:
  Database{limits,old,handles} = db
  complete_published(P.publish(old,proposal),limits,handles)
def normal_error(+db: Database, status: S.Status) -> State:
  complete(db,P.HostReady{P.error(status),None{}})

# 3 ordinary; 0 prepare; 1 prepared execution; 2 invalidate.
def error(+db: Database, +code: P.Bytes) -> State:
  complete(db,P.HostReady{P.failure(code),None{}})
def cleanup_error(+db: Database, +artifact: P.Bytes, +code: P.Bytes) -> State:
  call(7,artifact,result => receive(result,unused => error(db,code),cleanup_code => error(db,cleanup_code)))
def execution_complete(+db: Database, +result: Reply) -> State:
  Database{limits,state,handles} = db
  receive(result,output => complete(db,P.proposal(output,limits)),code => error(db,code))
def executed(+db: Database, +artifact: P.Bytes, +output: Reply) -> State:
  # Successful removal is required before validation/publication.
  call(7,artifact,result => receive(result,unused => execution_complete(db,output),code => error(db,code)))
def random_handle(+db: Database, +artifact: P.Bytes, +code: P.Bytes, +proof: P.Bytes) -> State:
  RandomHandle{db,artifact,code,proof}
def built_checked(+db: Database, +op: U32, +body: P.Bytes, +artifact: P.Bytes, +code: P.Bytes, +proof: P.Bytes) -> State:
  Database{limits,state,handles} = db
  P.choose(State,U32.is_eq(op,0),u => random_handle(db,artifact,code,proof),
    u => call(5,P.packet(artifact,P.packet(state,body)),out => executed(db,artifact,out)))
def build_bound(+limits: P.Limits, +op: U32, +parts: T.Parts) -> Bool:
  P.Limits{m,s,r} = limits
  T.Parts{bound,mode} = parts
  P.equal(bound,B.concatenate(P.size_bytes(m),B.concatenate(P.size_bytes(s),P.size_bytes(r)))) &&
    (Bool.not(U32.is_eq(op,0)) || P.equal(mode,B.utf8("universal")))
def build_matches(+report: P.Bytes, +limits: P.Limits, +op: U32) -> Bool:
  P.optional(T.Parts,Bool,T.cut(report,B.Number64{0,24},Nil{}),parts => build_bound(limits,op,parts),u => False{})
def built(+db: Database, +op: U32, +body: P.Bytes, +artifact: P.Bytes, +code: P.Bytes, +proof: P.Bytes, +result: Reply) -> State:
  Database{+limits,state,handles} = db
  receive(result,report => P.choose(State,build_matches(report,limits,op),
    u => built_checked(db,op,body,artifact,code,proof),
    u => cleanup_error(db,artifact,B.utf8("HOST_TRANSPORT"))),
    error_code => cleanup_error(db,artifact,error_code))
def allocate(+db: Database, +op: U32, +body: P.Bytes, +metadata: P.Bytes, +code: P.Bytes, +proof: P.Bytes) -> State:
  call(3,Nil{},result => receive(result,
    artifact => call(4,Con{op,P.packet(artifact,metadata)},result => built(db,op,body,artifact,code,proof,result)),
    error_code => error(db,error_code)))
def control_bound(+response: P.Bytes, +limit: B.Number64, +parts: T.Parts) -> Maybe<&2,P.Bytes>:
  T.Parts{body,rest} = parts
  P.choose(Maybe<&2,P.Bytes>,P.fits(body,limit),u => Some{response},u => None{})
def control(+db: Database, +status: String, +value: D.Value) -> Maybe<&2,P.Bytes>:
  Database{P.Limits{m,s,r},state,handles} = db
  +response = P.response(status,value)
  P.optional(T.Parts,Maybe<&2,P.Bytes>,T.separate(response),parts => control_bound(response,r,parts),u => None{})
def prepared_run(+db: Database, +key: P.Bytes, +artifact: P.Bytes, +code: P.Bytes, +proof: P.Bytes, +body: P.Bytes) -> State:
  Database{limits,state,handles} = db
  inspect(db,3,P.packet(key,P.packet(code,proof)),done =>
    call(5,P.packet(artifact,P.packet(state,body)),out => execution_complete(db,out)))
def invalidate(+db: Database, +key: P.Bytes, +artifact: P.Bytes, +response: P.Bytes) -> State:
  Database{limits,state,handles} = db
  +updated : Database = Database{limits,state,remove(key,handles)}
  call(7,artifact,result => receive(result,unused => complete(updated,P.HostReady{response,None{}}),
    error_code => error(updated,error_code)))
def resolved(+db: Database, +op: U32, +body: P.Bytes, +handle: Handle) -> State:
  Handle{key,+artifact,code,proof} = handle
  P.choose(State,U32.is_eq(op,2),
    u => P.optional(P.Bytes,State,control(db,"invalidated",D.VAbsent{}),response => invalidate(db,key,artifact,response),
      u => normal_error(db,S.Limit{})),
    u => call(11,artifact,result => receive(result,unused => prepared_run(db,key,artifact,code,proof,body),
      error_code => error(db,error_code))))
def prepared(+db: Database, +op: U32, +body: P.Bytes, +key: P.Bytes) -> State:
  Database{limits,state,handles} = db
  P.optional(Handle,State,lookup(key,handles),h => resolved(db,op,body,h),u => error(db,B.utf8("HANDLE")))
def route(+db: Database, +op: U32, +body: P.Bytes, +metadata: P.Bytes, +code: P.Bytes, +proof: P.Bytes) -> State:
  P.choose(State,U32.is_eq(op,1) || U32.is_eq(op,2),
    u => P.choose(State,P.equal(proof,Nil{}),u => prepared(db,op,body,code),u => normal_error(db,S.Input{})),
    u => inspect(db,2,metadata,done => allocate(db,op,body,metadata,code,proof)))
def auth_proof(+db: Database, +op: U32, +body: P.Bytes, +metadata: P.Bytes, +code: P.Bytes, +parts: T.Parts) -> State:
  T.Parts{proof,rest} = parts
  P.optional(T.Parts,State,T.separate(rest),unused => route(db,op,body,metadata,code,proof),
    u => error(db,B.utf8("HOST_TRANSPORT")))
def auth_code(+db: Database, +op: U32, +body: P.Bytes, +metadata: P.Bytes, +parts: T.Parts) -> State:
  T.Parts{code,rest} = parts
  P.optional(T.Parts,State,T.separate(rest),parts => auth_proof(db,op,body,metadata,code,parts),
    u => error(db,B.utf8("HOST_TRANSPORT")))
def authenticated(+result: Reply, +db: Database, +op: U32, +body: P.Bytes) -> State:
  match result:
    case Bad{code}:
      error(db,code)
    case Good{Con{0,response}}:
      complete(db,P.HostReady{response,None{}})
    case Good{Con{1,+metadata}}:
      P.optional(T.Parts,State,T.separate(metadata),parts => auth_code(db,op,body,metadata,parts),
        u => error(db,B.utf8("HOST_TRANSPORT")))
    case _:
      error(db,B.utf8("HOST_TRANSPORT"))
def decoded(+result: Reply, +db: Database, +op: U32, +body: P.Bytes) -> State:
  match result:
    case Bad{code}:
      error(db,code)
    case Good{Con{0,response}}:
      complete(db,P.HostReady{response,None{}})
    case Good{Con{1,unused}}:
      Database{limits,state,handles} = db
      call(5,P.packet(B.utf8("authenticate"),P.packet(state,body)),out => authenticated(out,db,op,body))
    case _:
      error(db,B.utf8("HOST_TRANSPORT"))
def decode(+db: Database, +op: U32, +body: P.Bytes) -> State:
  Database{limits,state,handles} = db
  call(5,P.packet(B.utf8("decode"),P.packet(state,body)),out => decoded(out,db,op,body))
def extension(+db: Database, +body: P.Bytes) -> State:
  match body:
    case Con{7,Con{+op,rest}}:
      P.choose(State,U32.is_le(op,2),u => decode(db,op,rest),u => normal_error(db,S.Input{}))
    case Con{7,Nil{}}:
      normal_error(db,S.Input{})
    case _:
      decode(db,3,body)
def body_decision(+db: Database, +size: B.Number64, +body: P.Bytes) -> State:
  P.choose(State,P.equal(P.unwrap(B.length64(B.length(body))),P.size_bytes(size)),
    u => extension(db,body),u => terminal(S.Input{}))
def received_body(+db: Database, +size: B.Number64, +result: Reply) -> State:
  receive(result,body => body_decision(db,size,body),code => HostExit{1})
def receive_header(+db: Database, +header: P.Header) -> State:
  match header:
    case P.End{}:
      HostExit{0}
    case P.Terminal{status}:
      terminal(status)
    case P.Body{+size}:
      call(1,P.size_bytes(size),result => received_body(db,size,result))
def header_decision(+db: Database, +bytes: P.Bytes) -> State:
  Database{P.Limits{m,s,r},state,handles} = db
  receive_header(db,P.header(bytes,m))
def received_header(+db: Database, +result: Reply) -> State:
  receive(result,bytes => header_decision(db,bytes),code => HostExit{1})
def registered(+db: Database, +key: P.Bytes, +artifact: P.Bytes, +code: P.Bytes, +proof: P.Bytes, +response: P.Bytes) -> State:
  Database{limits,state,handles} = db
  complete(Database{limits,state,Con{Handle{key,artifact,code,proof},handles}},P.HostReady{response,None{}})
def ascii(+bytes: P.Bytes) -> String:
  match bytes:
    case Nil{}:
      SNil{}
    case Con{h,t}:
      SCon{Chr{h},ascii(t)}
def register(+db: Database, +key: P.Bytes, +artifact: P.Bytes, +code: P.Bytes, +proof: P.Bytes) -> State:
  P.optional(P.Bytes,State,control(db,"prepared",D.VText{ascii(key)}),
    response => call(6,artifact,result => receive(result,
      unused => registered(db,key,artifact,code,proof,response),error_code => cleanup_error(db,artifact,error_code))),
    u => call(7,artifact,ignored => normal_error(db,S.Limit{})))
def candidate(+db: Database, +artifact: P.Bytes, +code: P.Bytes, +proof: P.Bytes, +key: P.Bytes) -> State:
  Database{limits,state,handles} = db
  P.optional(Handle,State,lookup(key,handles),h => random_handle(db,artifact,code,proof),
    u => register(db,key,artifact,code,proof))
def random_received(+db: Database, +artifact: P.Bytes, +code: P.Bytes, +proof: P.Bytes, result: Reply) -> State:
  receive(result,key => candidate(db,artifact,code,proof,key),error_code => cleanup_error(db,artifact,error_code))
def emitted(db: Database, result: Reply) -> State:
  receive(result,unused => serve(db),code => HostExit{0})
def step(state: State) -> E.Task<State>:
  match state:
    case Boot{}:
      E.Exchange{[0],bs => initialized(reply(bs))}
    case HostWait{bytes,next}:
      E.Exchange{bytes,next}
    case ReadHeader{db}:
      E.Exchange{Con{1,B.be64(0,8)},bs => received_header(db,reply(bs))}
    case SendResponse{db,response}:
      E.Exchange{Con{2,response},bs => emitted(db,reply(bs))}
    case RandomHandle{db,artifact,code,proof}:
      E.Exchange{[8],bs => random_received(db,artifact,code,proof,reply(bs))}
    case HostExit{code}:
      E.Stop{code}
