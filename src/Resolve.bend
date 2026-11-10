# Shared ordinary/prepared execution input. Preparation/invalidation are small
# registry commands to add at milestone 5, not a second transaction theorem.
import Base
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Semantics.bend as S
import ../contract/PreparedRegistry.bend as G
import ./Prepared.bend as Prepared
import ./Gate.bend as K

type Input is Data:
  Direct{request: P.Request}
  Registered{request: P.Request}

type Selection is Data:
  Denied{status: S.Status}
  Selected{request: P.Request}

def proof(r: P.Request) -> String:
  P.Request{credential, code, arguments, proof} = r
  proof

def found(result: Maybe<&2, G.Entry>, raw: P.Request) -> Selection:
  match result:
    case None{}: Denied{S.Failure{}}
    case Some{+entry}:
      Selected{Prepared.resolve_request(raw, G.code(entry), G.proof(entry))}

def proof_checked(empty: Bool, +instance: String, entries: List<&2, G.Entry>,
  +raw: P.Request) -> Selection:
  match empty:
    case False{}: Denied{S.Input{}}
    case True{}: found(G.lookup(instance, K.code(raw), entries), raw)

def authenticated(authentication: Maybe<&2, D.Context>, instance: String,
  entries: List<&2, G.Entry>, +raw: P.Request) -> Selection:
  match authentication:
    case None{}: Denied{S.Authentication{}}
    case Some{ctx}: proof_checked(String.eq(proof(raw), ""), instance, entries, raw)

# The selected request reaches Gate with a sound admission oracle. A cached
# universal certificate specializes at lookup under the same T1 binding.
def select(instance: String, +s: D.State, entries: List<&2, G.Entry>, input: Input) -> Selection:
  match input:
    case Direct{r}: Selected{r}
    case Registered{+raw}:
      authenticated(D.authenticate(s, K.credential(raw)), instance, entries, raw)
