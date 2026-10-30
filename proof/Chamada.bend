# Composicao da chamada autenticada nas funcoes reais de Nucleo.
# Nao pressupoe preparacao fiel nem publicacao valida; nao afirma Contrato do host.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Interface.bend as I
import ../contrato/Logica.bend as L
import ../contrato/Protocolo.bend as P
import ../contrato/Requisitos.bend as R
import ../contrato/Semantica.bend as S
import ../src/Nucleo.bend as N
import ./Fundamentos.bend as F
import ./CodecSomasOrdem.bend as O
import ./Maquina.bend as M
import ./Preparacao.bend as Q
import ./Publicacao.bend as U
import ./Seguranca.bend as G

def representado_casos(q: Maybe<&2, B.Numero64>, -n: Nat,
  exato: {B.nat64(n) == q : Maybe<&2, B.Numero64>},
  h: {P.representavel_resultado(B.numero64_bytes(q)) == True{} : Bool}) -> O.NumeroRepresentado<B.nat64(n)>:
  match q:
    case None{}:
      F.absurdo_booleano(O.NumeroRepresentado<B.nat64(n)>, h)
    case Some{numero}:
      O.Representado{numero, exato}

def representado(+n: Nat, h: {P.representavel_resultado(B.comprimento64(n)) == True{} : Bool}) ->
  O.NumeroRepresentado<B.nat64(n)>:
  representado_casos(B.nat64(n), n, {==}, h)

def limite_representado(l: S.Limites, h: {R.limites_validos(l) == True{} : Bool}) ->
  O.NumeroRepresentado<B.nat64(R.limite_resposta(l))>:
  match l:
    case S.Limites{+msg, +est, +resp}:
      +a = R.cabe_erro(resp, S.Entrada{})
      +b = R.cabe_erro(resp, S.Autenticacao{})
      +c = R.cabe_erro(resp, S.Certificado{})
      +d = R.cabe_erro(resp, S.Dados{})
      +e = R.cabe_erro(resp, S.Limite{})
      +f = R.cabe_erro(resp, S.Falha{})
      +prefixo = Q.prefixo_limites(msg, est, resp)
      +h5 = F.e_booleano_esquerda(prefixo && a && b && c && d && e, f, h)
      +h4 = F.e_booleano_esquerda(prefixo && a && b && c && d, e, h5)
      +h3 = F.e_booleano_esquerda(prefixo && a && b && c, d, h4)
      +h2 = F.e_booleano_esquerda(prefixo && a && b, c, h3)
      +h1 = F.e_booleano_esquerda(prefixo && a, b, h2)
      representado(resp, F.e_booleano_direita(
        P.representavel_resultado(B.comprimento64(msg)) && P.representavel_resultado(B.comprimento64(est)),
        P.representavel_resultado(B.comprimento64(resp)), F.e_booleano_esquerda(prefixo, a, h1)))

def enquadrar_medido(+v: D.Valor, +bs: List<&2, U32>,
  codificado: {P.codificar(v) == Some{bs} : Maybe<&2, List<&2, U32>>},
  medida: O.NumeroRepresentado<B.nat64(B.comprimento(bs))>) ->
  &bytes: List<&2, U32> -> P.Mensagem(v, bytes):
  match medida:
    case O.Representado{B.Numero64{+alto, +baixo}, medido}:
      (B.concatenar(B.be64(alto, baixo), bs),
        (%Equal.sym(Maybe<&2, List<&2, U32>>, P.codificar(v), Some{bs}, codificado) : {P.enquadrar_resultado(_) == Some{B.concatenar(B.be64(alto, baixo), bs)} : Maybe<&2, List<&2, U32>>}
          %Equal.sym(Maybe<&2, B.Numero64>, B.nat64(B.comprimento(bs)), Some{B.Numero64{alto, baixo}}, medido) : {P.concatenar_opcional(B.numero64_bytes(_), Some{bs}) ==
            Some{B.concatenar(B.be64(alto, baixo), bs)} : Maybe<&2, List<&2, U32>>}
          {==}))

def enquadrar_limitado(q: Maybe<&2, List<&2, U32>>, +v: D.Valor, +limite: Nat,
  codificado: {P.codificar(v) == q : Maybe<&2, List<&2, U32>>},
  teto: O.NumeroRepresentado<B.nat64(limite)>,
  cabe: {R.cabe_resultado(q, limite) == True{} : Bool}) ->
  &bytes: List<&2, U32> -> P.Mensagem(v, bytes):
  match q:
    case None{}:
      F.absurdo_booleano((&bytes: List<&2, U32> -> P.Mensagem(v, bytes)), cabe)
    case Some{+bs}:
      match teto:
        case O.Representado{numero, medido}:
          enquadrar_medido(v, bs, codificado,
            O.nat64_representabilidade_fechada_para_baixo(B.comprimento(bs), limite, numero, medido, cabe))

law resposta_preparavel_tem_enquadramento:
  for +v: D.Valor
  for +l: S.Limites
  for valido: {R.limites_validos(l) == True{} : Bool}
  for cabe: {R.cabe(R.limite_resposta(l), v) == True{} : Bool}
  exs bytes: List<&2, U32>
  P.Mensagem(v, bytes)
def resposta_preparavel_tem_enquadramento(v, l, valido, cabe):
  enquadrar_limitado(P.codificar(v), v, R.limite_resposta(l), {==}, limite_representado(l, valido), cabe)

# A finalizacao tecnica nao examina a lista de leis. A igualdade conserva o alvo real.
law finalizar_independe_da_lista_de_leis:
  for proposta: S.Resposta
  for -e: D.Esquema
  for -leis: S.Leis
  for -lim: S.Limites
  for -amb: String
  for -w: D.Estado
  {R.finalizar(proposta, S.Configuracao{e, leis, lim, amb}, w) ==
    R.finalizar(proposta, S.Configuracao{e, S.NenhumaLei{}, lim, amb}, w) : S.Resposta}
def finalizar_independe_da_lista_de_leis(proposta, e, leis, lim, amb, w):
  match proposta:
    case S.Resposta{S.Sucesso{}, v}: {==}
    case S.Resposta{S.Recusa{}, v}: {==}
    case S.Resposta{S.Entrada{}, v}: {==}
    case S.Resposta{S.Autenticacao{}, v}: {==}
    case S.Resposta{S.Certificado{}, v}: {==}
    case S.Resposta{S.Dados{}, v}: {==}
    case S.Resposta{S.Limite{}, v}: {==}
    case S.Resposta{S.Falha{}, v}: {==}

def preparar_enquadrado(-c: S.Configuracao, +w: D.Estado, +ts: List<&2, S.Evento>, -proposta: S.Resposta,
  +r: S.Resposta, finalizada: {R.finalizar(proposta, c, w) == r : S.Resposta},
  mensagem: &bytes: List<&2, U32> -> P.Mensagem(S.resposta_valor(r), bytes)) ->
  &preparada: N.Preparada -> {N.preparar(N.Parada{w, ts, proposta}, c) == Some{preparada} : Maybe<&2, N.Preparada>}:
  match mensagem:
    case (bytes, enquadrado):
      (N.Preparada{w, ts, r, bytes},
        Equal.trans(Maybe<&2, N.Preparada>, N.preparar(N.Parada{w, ts, proposta}, c),
          N.preparar_resposta(r, w, ts), Some{N.Preparada{w, ts, r, bytes}},
          Equal.cong(S.Resposta, Maybe<&2, N.Preparada>, resposta => N.preparar_resposta(resposta, w, ts),
            R.finalizar(proposta, c, w), r, finalizada),
          Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, N.Preparada>,
            q => N.preparar_bytes(q, w, ts, r), P.enquadrar(S.resposta_valor(r)), Some{bytes}, enquadrado)))

def preparar_configurada(+e: D.Esquema, -leis: S.Leis, +lim: S.Limites, +amb: String,
  +w: D.Estado, +ts: List<&2, S.Evento>, +proposta: S.Resposta,
  +valida: {R.configuracao_valida(S.Configuracao{e, leis, lim, amb}) == True{} : Bool}) ->
  &preparada: N.Preparada ->
    {N.preparar(N.Parada{w, ts, proposta}, S.Configuracao{e, leis, lim, amb}) == Some{preparada} : Maybe<&2, N.Preparada>}:
  +limites = Q.limites_da_configuracao(S.Configuracao{e, S.NenhumaLei{}, lim, amb}, valida)
  +r = R.finalizar(proposta, S.Configuracao{e, S.NenhumaLei{}, lim, amb}, w)
  F.com_par(
    (&preparada: N.Preparada -> {N.preparar(N.Parada{w, ts, proposta}, S.Configuracao{e, leis, lim, amb}) == Some{preparada} : Maybe<&2, N.Preparada>}),
    I.ErroFixo(r), {R.cabe(R.limite_resposta(lim), S.resposta_valor(r)) == True{} : Bool},
    Q.finalizar_garante_payload_e_tamanho(proposta, S.Configuracao{e, S.NenhumaLei{}, lim, amb}, w, limites),
    payload => cabe => preparar_enquadrado(S.Configuracao{e, leis, lim, amb}, w, ts, proposta, r,
      finalizar_independe_da_lista_de_leis(proposta, e, leis, lim, amb, w),
      resposta_preparavel_tem_enquadramento(S.resposta_valor(r), lim, limites, cabe)))

law finalizacao_tem_preparacao_real:
  for c: S.Configuracao
  for +w: D.Estado
  for +ts: List<&2, S.Evento>
  for +proposta: S.Resposta
  for +valida: {R.configuracao_valida(c) == True{} : Bool}
  exs preparada: N.Preparada
  {N.preparar(N.Parada{w, ts, proposta}, c) == Some{preparada} : Maybe<&2, N.Preparada>}
def finalizacao_tem_preparacao_real(c, w, ts, proposta, valida):
  match c:
    case S.Configuracao{e, leis, lim, amb}:
      preparar_configurada(e, leis, lim, amb, w, ts, proposta, valida)

# Usa os campos tecnicos copiaveis; a lista REAL de leis fica apenas nos indices.
def preparacao_configurada_fiel(+e: D.Esquema, -leis: S.Leis, +lim: S.Limites, +amb: String,
  +w: D.Estado, +ts: List<&2, S.Evento>, +proposta: S.Resposta, +preparada: N.Preparada,
  obtida: {N.preparar(N.Parada{w, ts, proposta}, S.Configuracao{e, leis, lim, amb}) == Some{preparada} : Maybe<&2, N.Preparada>}) ->
  Q.Fiel(w, ts, R.finalizar(proposta, S.Configuracao{e, leis, lim, amb}, w), preparada):
  +r = R.finalizar(proposta, S.Configuracao{e, S.NenhumaLei{}, lim, amb}, w)
  +igual = finalizar_independe_da_lista_de_leis(proposta, e, leis, lim, amb, w)
  %Equal.sym(S.Resposta, R.finalizar(proposta, S.Configuracao{e, leis, lim, amb}, w), r, igual) :
    Q.Fiel(w, ts, _, preparada)
  Q.preparar_bytes_fiel(P.enquadrar(S.resposta_valor(r)), w, ts, r, preparada, {==},
    Equal.trans(Maybe<&2, N.Preparada>, N.preparar_resposta(r, w, ts),
      N.preparar(N.Parada{w, ts, proposta}, S.Configuracao{e, leis, lim, amb}), Some{preparada},
      Equal.sym(Maybe<&2, N.Preparada>,
        N.preparar(N.Parada{w, ts, proposta}, S.Configuracao{e, leis, lim, amb}), N.preparar_resposta(r, w, ts),
        Equal.cong(S.Resposta, Maybe<&2, N.Preparada>, resposta => N.preparar_resposta(resposta, w, ts),
          R.finalizar(proposta, S.Configuracao{e, leis, lim, amb}, w), r, igual)), obtida))

def ConclusaoIntegral(-c: S.Configuracao, -s: D.Estado, -w: D.Estado,
  -ts: List<&2, S.Evento>, -proposta: S.Resposta) -> Type:
  &preparada: N.Preparada ->
    L.E<{N.preparar(N.Parada{w, ts, proposta}, c) == Some{preparada} : Maybe<&2, N.Preparada>},
      L.E<Q.Fiel(w, ts, R.finalizar(proposta, c, w), preparada),
        R.Valido(c, U.publicado(N.concluir(preparada, s)))>>

def duplicar_igualdade(-A: Data, -x: A, -y: A, igualdade: {x == y : A}) ->
  L.E<{x == y : A}, {x == y : A}>:
  %igualdade : L.E<{x == _ : A}, {x == _ : A}>
  L.Ambos{{==}, {==}}

def concluir_configurada(+e: D.Esquema, leis: S.Leis, +lim: S.Limites, +amb: String,
  -codigo: String, p: S.Programa, +ctx: D.Contexto, +args: D.Valor,
  certificado: R.Certifica(S.Configuracao{e, leis, lim, amb}, codigo, p, ctx, args),
  +s: D.Estado, valido: R.Valido(S.Configuracao{e, leis, lim, amb}, s), cred: String,
  aut: {D.autenticar(s, cred) == Some{ctx} : Maybe<&2, D.Contexto>}, +n: Nat,
  +w: D.Estado, +ts: List<&2, S.Evento>, +proposta: S.Resposta,
  obtido: {N.percorrer(n, N.iniciar(p, ctx, args, s), e) == S.Final{w, ts, proposta} : S.Percurso},
  resultado: &preparada: N.Preparada ->
    {N.preparar(N.Parada{w, ts, proposta}, S.Configuracao{e, leis, lim, amb}) == Some{preparada} : Maybe<&2, N.Preparada>}) ->
  ConclusaoIntegral(S.Configuracao{e, leis, lim, amb}, s, w, ts, proposta):
  match resultado:
    case (original, obtida):
      +preparada = (original : N.Preparada)
      F.com_par(ConclusaoIntegral(S.Configuracao{e, leis, lim, amb}, s, w, ts, proposta),
        {N.preparar(N.Parada{w, ts, proposta}, S.Configuracao{e, leis, lim, amb}) == Some{preparada} : Maybe<&2, N.Preparada>},
        {N.preparar(N.Parada{w, ts, proposta}, S.Configuracao{e, leis, lim, amb}) == Some{preparada} : Maybe<&2, N.Preparada>},
        duplicar_igualdade(Maybe<&2, N.Preparada>,
          N.preparar(N.Parada{w, ts, proposta}, S.Configuracao{e, leis, lim, amb}), Some{preparada}, obtida),
        confirmada => guardada =>
          F.com_par(ConclusaoIntegral(S.Configuracao{e, leis, lim, amb}, s, w, ts, proposta),
            {preparada == N.Preparada{w, ts, R.finalizar(proposta, S.Configuracao{e, leis, lim, amb}, w), Q.bytes_preparados(preparada)} : N.Preparada},
            {P.enquadrar(S.resposta_valor(R.finalizar(proposta, S.Configuracao{e, leis, lim, amb}, w))) == Some{Q.bytes_preparados(preparada)} : Maybe<&2, List<&2, U32>>},
            preparacao_configurada_fiel(e, leis, lim, amb, w, ts, proposta, preparada, confirmada),
            +igual => +mensagem =>
              (preparada, L.Ambos{guardada, L.Ambos{L.Ambos{igual, mensagem},
                U.conclusao_de_preparacao_certificada_e_valida(S.Configuracao{e, leis, lim, amb}, codigo, p, ctx, args,
                  certificado, s, valido, cred, aut, n, w, ts, proposta, obtido, preparada, L.Ambos{igual, mensagem})}})))

# Recebe o resultado da funcao real, nao fidelidade nem validade da conclusao.
# Maquina.terminacao_da_referencia_implica_terminacao_incremental fornece tal percurso.
law chamada_autenticada_prepara_e_conclui:
  for c: S.Configuracao
  for -codigo: String
  for p: S.Programa
  for +ctx: D.Contexto
  for +args: D.Valor
  for certificado: R.Certifica(c, codigo, p, ctx, args)
  for +s: D.Estado
  for valido: R.Valido(c, s)
  for cred: String
  for aut: {D.autenticar(s, cred) == Some{ctx} : Maybe<&2, D.Contexto>}
  for +n: Nat
  for +w: D.Estado
  for +ts: List<&2, S.Evento>
  for +proposta: S.Resposta
  for obtido: {N.percorrer(n, N.iniciar(p, ctx, args, s), S.esquema(c)) == S.Final{w, ts, proposta} : S.Percurso}
  for valida: {R.configuracao_valida(c) == True{} : Bool}
  ConclusaoIntegral(c, s, w, ts, proposta)
def chamada_autenticada_prepara_e_conclui(c, codigo, p, ctx, args, certificado, s, valido, cred, aut,
  n, w, ts, proposta, obtido, valida):
  match c:
    case S.Configuracao{+e, leis, +lim, +amb}:
      concluir_configurada(e, leis, lim, amb, codigo, p, ctx, args, certificado, s, valido, cred, aut,
        n, w, ts, proposta, obtido, preparar_configurada(e, leis, lim, amb, w, ts, proposta, valida))

law conclusao_sem_sucesso_conserva_estado_inicial:
  for preparada: N.Preparada
  for -s: D.Estado
  for sem_sucesso: {U.status_sucesso(U.resposta(preparada)) == False{} : Bool}
  {U.publicado(N.concluir(preparada, s)) == s : D.Estado}
def conclusao_sem_sucesso_conserva_estado_inicial(preparada, s, sem_sucesso):
  match preparada:
    case N.Preparada{w, ts, r, bs}:
      U.todo_status_sem_sucesso_preserva_publicado(r, s, w, sem_sucesso)
