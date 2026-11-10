# Concrete tasks application, real policy, real proof and actual Core functions.
import Base
import ../../contract/Data.bend as D
import ../../contract/Semantics.bend as S
import ../../contract/Requirements.bend as R
import ../../contract/Logic.bend as L
import ../../contract/Protocol.bend as P
import ../../contract/Theorems.bend as G
import ../../src/Core.bend as N
import ../../src/Gate.bend as K
import ./tasks/Configuration.bend as App
import ./tasks/Client.bend as Client
import ./tasks/ClientProof.bend as ClientProof
import ./tasks/Bindings.bend as Bindings
import ./tasks/Instance.bend as Instance
import ./tasks/Seed.bend as Seed
import ./tasks/Policy.bend as Policy

def saved() -> D.State:
  D.State{[D.Table{"alice", [D.Row{"t1", Client.fields("alice", "t1", "Buy bread", False{})}]},
    D.Table{"bob", Nil{}}], [
      D.Row{"alice", [D.Field{"credential", D.VText{"alice-token"}},
        D.Field{"id", D.VText{"alice"}}, D.Field{"kind", D.VText{"user"}}]},
      D.Row{"bob", [D.Field{"credential", D.VText{"bob-token"}},
        D.Field{"id", D.VText{"bob"}}, D.Field{"kind", D.VText{"user"}}]}]}

def result() -> Maybe<&2, N.Conclusion>:
  K.finish(N.traverse(2n,
    N.start(Client.program(), Instance.context(), Instance.arguments(), Seed.state()),
    App.schema()), App.config(), Seed.state())

def PublishedSuccess(result: Maybe<&2, N.Conclusion>) -> Type:
  match result:
    case Some{N.Conclusion{state, response, bytes}}:
      L.E<{state == saved() : D.State},
        {response == S.Response{S.Success{}, D.VText{"t1"}} : S.Response}>
    case None{}: Empty

law authenticated:
  {D.authenticate(Seed.state(), "alice-token") == Some{Instance.context()} : Maybe<&2, D.Context>}
def authenticated(): {==}

# Result must be Some and carry a changed root; None cannot pass this law.
law publishes_success:
  PublishedSuccess(result())
def publishes_success():
  L.Both{{==}, {==}}

law final_state_valid:
  R.Valid(App.config(), saved())
def final_state_valid():
  L.Both{{==}, L.Both{Policy.Both{Policy.Both{Policy.Both{{==}, {==}}, Unit{}},
    Policy.Both{Unit{}, Unit{}}}, Unit{}}}

def request() -> P.Request:
  P.Request{"alice-token", Bindings.code(), Instance.arguments(), Bindings.proof_source()}

def accept(c: S.Configuration, r: P.Request, ctx: D.Context) -> K.Verdict:
  K.Accept{Client.program()}

law exact_gate:
  {K.begin(App.config(), Seed.state(), request(), accept) ==
    K.Started{Instance.context(),
      N.start(Client.program(), Instance.context(), Instance.arguments(), Seed.state())} : K.Entry}
def exact_gate(): {==}

# Actual logical oracle premise for this configuration/request, for ALL ctx.
# The source/frontend binding of this fixture's oracle is still external T1.
law exact_oracle_sound:
  G.OracleSoundness(App.config(), request(), accept)
def exact_oracle_sound(ctx):
  +ctx = ctx
  L.Both{
    s => valid => identity => n => ClientProof.certify(ctx, Instance.arguments(), Bindings.code(), s, valid, identity, n),
    s => Bindings.terminates(s, ctx, Instance.arguments())}
