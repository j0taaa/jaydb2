# Concrete representation checks, not client certificates or native sessions.
import Base
import ./Data.bend as D
import ./Model.bend as M
import ./Client.bend as Client
import ./DirectoryProof.bend as DP
import ./Configuration.bend as C
import ./Requirements.bend as R
import ./Semantics.bend as S

def six() -> List<&2,Maybe<&2,String>>:
  [Some{"six"},Some{"five"},Some{"four"},Some{"three"},Some{"two"},Some{"one"}]

def after_delete() -> List<&2,Maybe<&2,String>>:
  [Some{"six"},None{},Some{"four"},None{},Some{"two"},Some{"one"}]

law six_ids:
  {DP.active_keys(M.Alice{},M.mask(six())) ==
    ["alice/aaaaaz","alice/aaaaz","alice/aaaz","alice/aaz","alice/az","alice/z"] : List<&2,String>}
def six_ids(): {==}

law delete_two_ids:
  {Client.removed(M.Alice{},Client.removed(M.Alice{},M.mask(six()),"alice/aaaaz"),"alice/aaz") ==
    M.mask(after_delete()) : String}
def delete_two_ids(): {==}

law survivors_keep_ids:
  {DP.active_keys(M.Alice{},M.mask(after_delete())) ==
    ["alice/aaaaaz","alice/aaaz","alice/az","alice/z"] : List<&2,String>}
def survivors_keep_ids(): {==}

law next_id_does_not_reuse_tombstones:
  {Client.key(M.Alice{},M.mask(after_delete())) == "alice/aaaaaaz" : String}
def next_id_does_not_reuse_tombstones(): {==}

law six_fit_existing_state_limit:
  {R.structure(C.config(),M.state(six(),[Some{"Bob private"}])) == True{} : Bool}
def six_fit_existing_state_limit(): {==}

law proposed_exact_state:
  M.Coherent(M.state(six(),[Some{"Bob private"}]))
def proposed_exact_state():
  M.Exact{six(),[Some{"Bob private"}],{==}}

def args1(command:String,arg:String) -> D.Value:
  D.VList{D.VText{command},D.VList{D.VText{arg},D.VListEmpty{}}}

def five() -> List<&2,Maybe<&2,String>>:
  [Some{"five"},Some{"four"},Some{"three"},Some{"two"},Some{"one"}]

# These evaluate the actual client actions/reference interpreter, bypassing
# admission. They establish runtime shape, NOT universal client safety.
law sixth_create_reference_state:
  {S.state_execution_trace(S.execute(4n,Client.program(),C.schema(),M.state(five(),Nil{}),D.Context{"alice","user"},args1("create","six"))) == M.state(six(),Nil{}) : D.State}
def sixth_create_reference_state(): {==}

def removed_first() -> List<&2,Maybe<&2,String>>:
  [Some{"six"},None{},Some{"four"},Some{"three"},Some{"two"},Some{"one"}]

law first_delete_reference_state:
  {S.state_execution_trace(S.execute(4n,Client.program(),C.schema(),M.state(six(),Nil{}),D.Context{"alice","user"},args1("remove","alice/aaaaz"))) == M.state(removed_first(),Nil{}) : D.State}
def first_delete_reference_state(): {==}

law second_delete_reference_state:
  {S.state_execution_trace(S.execute(4n,Client.program(),C.schema(),M.state(removed_first(),Nil{}),D.Context{"alice","user"},args1("remove","alice/aaz"))) == M.state(after_delete(),Nil{}) : D.State}
def second_delete_reference_state(): {==}

def response(p:S.Trace) -> Maybe<&2,S.Response>:
  match p:
    case S.Prefix{w,ts}: None{}
    case S.Final{w,ts,r}: Some{r}

law list_after_deletion_reference_response:
  {response(S.execute(10n,Client.program(),C.schema(),M.state(after_delete(),Nil{}),D.Context{"alice","user"},D.VList{D.VText{"list"},D.VListEmpty{}})) ==
    Some{S.Response{S.Success{},D.VList{D.fields_value(M.fields(M.Alice{},"alice/aaaaaz","six")),
      D.VList{D.fields_value(M.fields(M.Alice{},"alice/aaaz","four")),
        D.VList{D.fields_value(M.fields(M.Alice{},"alice/az","two")),
          D.VList{D.fields_value(M.fields(M.Alice{},"alice/z","one")),D.VListEmpty{}}}}}}} : Maybe<&2,S.Response>}
def list_after_deletion_reference_response(): {==}
