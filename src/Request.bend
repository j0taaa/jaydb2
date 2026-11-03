# Exact public envelope shape. Validation does not interpret code or proof.
import Base
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P

def choose(ok: Bool, request: P.Request) -> Maybe<&2, P.Request>:
  match ok:
    case False{}:
      None{}
    case True{}:
      Some{request}

def form(v: D.Value) -> Maybe<&2, P.Request>:
  match v:
    case D.VRecord{n0, arguments,
      D.VRecord{n1, D.VText{code},
        D.VRecord{n2, D.VText{credential},
          D.VRecord{n3, D.VText{proof}, D.VRecordEmpty{}}}}}:
      choose(String.eq(n0, "arguments") && String.eq(n1, "code") &&
        String.eq(n2, "credential") && String.eq(n3, "proof"),
        P.Request{credential, code, arguments, proof})
    case _:
      None{}

def validate(ok: Bool, result: Maybe<&2, P.Request>) -> Maybe<&2, P.Request>:
  match ok:
    case False{}:
      None{}
    case True{}:
      result

def extract(+v: D.Value) -> Maybe<&2, P.Request>:
  validate(D.value_valid(v), form(v))

law form_reconstructs_request:
  for r: P.Request
  {form(P.request_value(r)) == Some{r} : Maybe<&2, P.Request>}

def form_reconstructs_request(r):
  match r:
    case P.Request{credential, code, arguments, proof}:
      {==}
