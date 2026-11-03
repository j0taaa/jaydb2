import Base
import ./Dados.bend as D
import ./Semantica.bend as S
import ./Logica.bend as L
import ./Requisitos.bend as R
import ./Terminacao.bend as T
import ./Policy.bend as P
import ./Proofs.bend as H
import ./Configuration.bend as C
import ./Client.bend as Client
import ./Instance.bend as I
import ./Bindings.bend as B

def titulo_seguro(+id: String, tipo: String, +key: String, titulo: Maybe<&2, String>) ->
  H.Segura(2n, D.Contexto{id, tipo}, Client.continuar_titulo(id, key, titulo)):
  match titulo:
    case None{}: Unit{}
    case Some{texto}: L.Ambos{{==}, r => Unit{}}

def concluir_seguro(+id: String, tipo: String, +key: String, titulo: Maybe<&2, String>) ->
  H.Segura(2n, D.Contexto{id, tipo}, Client.concluir_titulo(id, key, titulo)):
  match titulo:
    case None{}: Unit{}
    case Some{texto}: L.Ambos{P.Ambos{{==}, {==}}, r => Unit{}}

def salvo_seguro(n: Nat, ctx: D.Contexto, cancelar: Bool, key: String) ->
  H.Segura(Succ{n}, ctx, Client.salvo(cancelar, key)):
  match cancelar:
    case False{}: Unit{}
    case True{}: Unit{}

def pedido_seguro(ctx: D.Contexto, p: Client.Pedido) ->
  H.Segura(3n, ctx, Client.pedido(D.contexto_id(ctx), p)):
  match ctx p:
    case D.Contexto{id, tipo} Client.Listar{}: L.Ambos{{==}, r => Unit{}}
    case D.Contexto{+id, tipo} Client.Ver{key}:
      L.Ambos{{==}, r => titulo_seguro(id, tipo, key, Client.texto_recebido(r))}
    case D.Contexto{+id, +tipo} Client.Salvar{+key, titulo, feita, +cancelar}:
      L.Ambos{P.Ambos{{==}, {==}}, r => salvo_seguro(1n, D.Contexto{id, tipo}, cancelar, key)}
    case D.Contexto{+id, tipo} Client.Concluir{key}:
      L.Ambos{{==}, r => concluir_seguro(id, tipo, key, Client.texto_recebido(r))}
    case D.Contexto{id, tipo} Client.Remover{key}: L.Ambos{{==}, r => Unit{}}
    case D.Contexto{id, tipo} Client.Invalido{}: Unit{}

def programa_seguro(+ctx: D.Contexto, args: D.Valor) -> H.Segura(3n, ctx, S.iniciar(Client.programa(), ctx, args)):
  match ctx:
    case D.Contexto{id, tipo}: pedido_seguro(D.Contexto{id, tipo}, Client.analisar(args))

def donos_iniciais(-s: D.Estado, valido: R.Valido(C.config(), s)) -> P.Donos(s):
  match valido:
    case L.Ambos{estrutura, L.Ambos{donos, restante}}: donos

# O lema parametrizado evita reavaliar a reificacao concreta dos argumentos
# dentro de toda a demonstracao; o alvo continua sendo o certificado original.
def certificar(+ctx: D.Contexto, +args: D.Valor, -codigo: String, +s: D.Estado,
  valido: R.Valido(C.config(), s), identidade: {D.contexto_presente(s, ctx) == True{} : Bool}, +n: Nat) ->
  R.SegurancaPercurso(S.executar(n, Client.programa(), C.esquema(), s, ctx, args), C.config(), s, ctx, codigo, args):
  H.percurso(S.executar(n, Client.programa(), C.esquema(), s, ctx, args),
    C.esquema(), C.limites(), C.ambiente(), s, ctx, codigo, args,
    H.recuar(ctx, S.executar(n, Client.programa(), C.esquema(), s, ctx, args),
      T.observar(n, S.iniciar(Client.programa(), ctx, args), C.esquema(), s, Nil{}),
      Equal.sym(S.Percurso, T.observar(n, S.iniciar(Client.programa(), ctx, args), C.esquema(), s, Nil{}),
        S.executar(n, Client.programa(), C.esquema(), s, ctx, args),
        T.referencia(n, S.iniciar(Client.programa(), ctx, args), C.esquema(), s)),
      H.segura(3n, n, S.iniciar(Client.programa(), ctx, args), ctx, C.esquema(), s, Nil{},
        programa_seguro(ctx, args), P.Ambos{donos_iniciais(s, valido), P.Ambos{identidade, Unit{}}})))

def B.certificado(s, valido, identidade, n):
  certificar(I.contexto(), I.argumentos(), B.codigo(), s, valido, identidade, n)

def B.termina(s, ctx, args):
  +ctx = ctx
  +args = args
  T.programa_finito(3n, Client.programa(), C.esquema(), s, ctx, args,
    H.finita(3n, S.iniciar(Client.programa(), ctx, args), ctx, programa_seguro(ctx, args)))
