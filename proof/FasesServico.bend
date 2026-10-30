# Invariantes estruturais do fim gerado pelo protocolo.
import Base
import ./Publicacao.bend as U
import ./Preparacao.bend as Preparacao
import ./Chamada.bend as Chamada
import ./Proposta.bend as Proposta
import ./Configuracao.bend as Configuracao
import ../src/Configuracao.bend as Config
import ../contrato/Requisitos.bend as R
import ./ProtocoloServico.bend as Q
import ./RotasServico.bend as H
import ./PrimitivasServico.bend as M
import ../src/Estado.bend as Estado
import ../contrato/Protocolo.bend as Protocolo
import ../src/Codec.bend as C
import ../contrato/Dados.bend as D
import ../contrato/Semantica.bend as S
import ../contrato/Logica.bend as L
import ../contrato/Interface.bend as I
import ../contrato/LAWS.bend as K
import ../contrato/Recursos.bend as X
import ./Fundamentos.bend as F
import ../src/Nucleo.bend as N

type Tipo is Data:
  RecusaInicial{}
  InspecaoExterna{}
  EfeitoExterno{}
  InicioComProva{}
  Inicializacao{}
  Publicacao{}
  Conclusao{}
  Completa{}
  Interrompida{}

def classificar(q: Q.Quadro, tipo: Tipo) -> Bool:
  match q tipo:
    case Q.InicialRecusada{status} RecusaInicial{}: True{}
    case Q.Inspecao{descricao} InspecaoExterna{}: True{}
    case Q.Efeito{descricao} EfeitoExterno{}: True{}
    case Q.Iniciada{s} Inicializacao{}: True{}
    case Q.Iniciada{s} InicioComProva{}: True{}
    case Q.InicialAceita{} InicioComProva{}: True{}
    case Q.Publicada{s} Publicacao{}: True{}
    case Q.Concluida{r, s, f} Conclusao{}: True{}
    case Q.Entregue{bs} Completa{}: True{}
    case Q.Interrompida{bs} Interrompida{}: True{}
    case _ _: False{}

def desse_tipo(tipo: Tipo, q: Q.Quadro) -> Bool:
  classificar(q, tipo)

def ausente(+tipo: Tipo, xs: List<&2, Q.Quadro>) -> Bool:
  match xs:
    case Nil{}: True{}
    case Con{q, resto}: Bool.not(desse_tipo(tipo, q)) && ausente(tipo, resto)

law ausente_exclui_consulta:
  for +tipo: Tipo
  for xs: List<&2, Q.Quadro>
  for n: Nat
  for +q: Q.Quadro
  for h: {ausente(tipo, xs) == True{} : Bool}
  for alvo: {desse_tipo(tipo, q) == True{} : Bool}
  for consulta: {Q.consultar(xs, n) == Some{q} : Maybe<&2, Q.Quadro>}
  Empty
def ausente_exclui_consulta(tipo, xs, n, q, h, alvo, consulta):
  match xs n:
    case Nil{} _:
      F.nenhum_nao_algum(Q.Quadro, q, consulta)
    case Con{+a, t} 0n:
      F.falso_nao_verdadeiro(Equal.trans(Bool, False{}, desse_tipo(tipo, a), True{},
        Equal.sym(Bool, desse_tipo(tipo, a), False{}, F.negacao_verdadeira(desse_tipo(tipo, a),
          F.e_booleano_esquerda(Bool.not(desse_tipo(tipo, a)), ausente(tipo, t), h))),
        Equal.trans(Bool, desse_tipo(tipo, a), desse_tipo(tipo, q), True{},
          Equal.cong(Q.Quadro, Bool, x => desse_tipo(tipo, x), a, q,
            F.algum_injetivo(Q.Quadro, a, q, consulta)), alvo)))
    case Con{a, t} 1n+k:
      ausente_exclui_consulta(tipo, t, k, q,
        F.e_booleano_direita(Bool.not(desse_tipo(tipo, a)), ausente(tipo, t), h), alvo, consulta)

law depois_entrega_sem_macros:
  for tipo: Tipo
  for fecha: Bool
  for -s: D.Estado
  for proxima: Bool
  {ausente(tipo, H.depois_entrega(fecha, s, proxima)) == True{} : Bool}
def depois_entrega_sem_macros(tipo, fecha, s, proxima):
  match fecha proxima:
    case True{} _: {==}
    case False{} True{}: {==}
    case False{} False{}: {==}

law entrega_sem_publicacao:
  for -s: D.Estado
  for -bs: List<&2, U32>
  for fecha: Bool
  for entrega: H.Entrega
  {ausente(Publicacao{}, H.render_entrega(s, bs, fecha, entrega)) == True{} : Bool}
def entrega_sem_publicacao(s, bs, fecha, entrega):
  match entrega:
    case H.Completa{proxima}: depois_entrega_sem_macros(Publicacao{}, fecha, s, proxima)
    case H.Quebrada{prefixo}: {==}
    case H.PendenteEntrega{}: {==}

law entrega_sem_conclusao:
  for -s: D.Estado
  for -bs: List<&2, U32>
  for fecha: Bool
  for entrega: H.Entrega
  {ausente(Conclusao{}, H.render_entrega(s, bs, fecha, entrega)) == True{} : Bool}
def entrega_sem_conclusao(s, bs, fecha, entrega):
  match entrega:
    case H.Completa{proxima}: depois_entrega_sem_macros(Conclusao{}, fecha, s, proxima)
    case H.Quebrada{prefixo}: {==}
    case H.PendenteEntrega{}: {==}

law entrega_quebrada_nunca_completa:
  for -s: D.Estado
  for -bs: List<&2, U32>
  for -fecha: Bool
  for -prefixo: List<&2, U32>
  {ausente(Completa{}, H.render_entrega(s, bs, fecha, H.Quebrada{prefixo})) == True{} : Bool}
def entrega_quebrada_nunca_completa(s, bs, fecha, prefixo): {==}

law entrega_completa_nunca_quebrada:
  for -s: D.Estado
  for -bs: List<&2, U32>
  for fecha: Bool
  for proxima: Bool
  {ausente(Interrompida{}, H.render_entrega(s, bs, fecha, H.Completa{proxima})) == True{} : Bool}
def entrega_completa_nunca_quebrada(s, bs, fecha, proxima):
  depois_entrega_sem_macros(Interrompida{}, fecha, s, proxima)


def estado_publicacao(q: Q.Quadro) -> Maybe<&2, D.Estado>:
  match q:
    case Q.Publicada{s}: Some{s}
    case _: None{}

def publicadas_iguais(+a: D.Estado, -b: D.Estado,
  h: {Some{Q.Publicada{a}} == Some{Q.Publicada{b}} : Maybe<&2, Q.Quadro>}) -> {b == a : D.Estado}:
  Equal.sym(D.Estado, a, b, F.algum_injetivo(D.Estado, a, b,
    Equal.cong(Q.Quadro, Maybe<&2, D.Estado>, estado_publicacao, Q.Publicada{a}, Q.Publicada{b},
      F.algum_injetivo(Q.Quadro, Q.Publicada{a}, Q.Publicada{b}, h))))

def sucesso_publica_uma_vez(+s: D.Estado, +v: D.Valor, +bs: List<&2, U32>,
  +fecha: Bool, +entrega: H.Entrega, n: Nat, +w: D.Estado,
  consulta: {Q.consultar(H.render_conclusao(N.Conclusao{s, S.Resposta{S.Sucesso{}, v}, bs}, fecha, entrega), n) ==
    Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}) -> L.E<{n == 1n : Nat}, {w == s : D.Estado}>:
  match n:
    case 0n:
      L.ex_falso(L.E<{0n == 1n : Nat}, {w == s : D.Estado}>,
        ausente_exclui_consulta(Publicacao{}, [Q.Preparada{S.Resposta{S.Sucesso{}, v}, bs}], 0n,
          Q.Publicada{w}, {==}, {==}, consulta))
    case 1n+k:
      match k:
        case 0n: L.Ambos{{==}, publicadas_iguais(s, w, consulta)}
        case 1n+j:
          match j:
            case 0n:
              L.ex_falso(L.E<{2n == 1n : Nat}, {w == s : D.Estado}>,
                ausente_exclui_consulta(Publicacao{}, [Q.Concluida{S.Resposta{S.Sucesso{}, v}, s, fecha}], 0n,
                  Q.Publicada{w}, {==}, {==}, consulta))
            case 1n+z:
              L.ex_falso(L.E<{3n+z == 1n : Nat}, {w == s : D.Estado}>,
                ausente_exclui_consulta(Publicacao{}, H.render_entrega(s, bs, fecha, entrega), z,
                  Q.Publicada{w}, entrega_sem_publicacao(s, bs, fecha, entrega), {==}, consulta))

def resposta_nao_publica(+s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>,
  +fecha: Bool, +entrega: H.Entrega,
  h: {U.status_sucesso(r) == False{} : Bool}) ->
  {ausente(Publicacao{}, H.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega)) == True{} : Bool}:
  match r:
    case S.Resposta{S.Sucesso{}, v}:
      F.absurdo_booleano(
        {ausente(Publicacao{}, H.render_conclusao(N.Conclusao{s, S.Resposta{S.Sucesso{}, v}, bs}, fecha, entrega)) == True{} : Bool},
        Equal.sym(Bool, True{}, False{}, h))
    case S.Resposta{S.Recusa{}, v}: entrega_sem_publicacao(s, bs, fecha, entrega)
    case S.Resposta{S.Entrada{}, v}: entrega_sem_publicacao(s, bs, fecha, entrega)
    case S.Resposta{S.Autenticacao{}, v}: entrega_sem_publicacao(s, bs, fecha, entrega)
    case S.Resposta{S.Certificado{}, v}: entrega_sem_publicacao(s, bs, fecha, entrega)
    case S.Resposta{S.Dados{}, v}: entrega_sem_publicacao(s, bs, fecha, entrega)
    case S.Resposta{S.Limite{}, v}: entrega_sem_publicacao(s, bs, fecha, entrega)
    case S.Resposta{S.Falha{}, v}: entrega_sem_publicacao(s, bs, fecha, entrega)

def nao_ha_publicacao(+s: D.Estado, +r: S.Resposta, +bs: List<&2, U32>, +fecha: Bool, +entrega: H.Entrega,
  n: Nat, +w: D.Estado, sem: {U.status_sucesso(r) == False{} : Bool},
  consulta: {Q.consultar(H.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega), n) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}) ->
  L.E<{n == 1n : Nat}, {w == s : D.Estado}>:
  L.ex_falso(L.E<{n == 1n : Nat}, {w == s : D.Estado}>,
    ausente_exclui_consulta(Publicacao{}, H.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega), n,
      Q.Publicada{w}, resposta_nao_publica(s, r, bs, fecha, entrega, sem), {==}, consulta))

law publicacao_no_fim_e_unica:
  for +conclusao: N.Conclusao
  for +fecha: Bool
  for +entrega: H.Entrega
  for n: Nat
  for +w: D.Estado
  for consulta: {Q.consultar(H.render_conclusao(conclusao, fecha, entrega), n) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}
  L.E<{n == 1n : Nat}, {w == U.publicado(conclusao) : D.Estado}>
def publicacao_no_fim_e_unica(conclusao, fecha, entrega, n, w, consulta):
  match conclusao:
    case N.Conclusao{s, S.Resposta{S.Sucesso{}, v}, bs}:
      sucesso_publica_uma_vez(s, v, bs, fecha, entrega, n, w, consulta)
    case N.Conclusao{s, S.Resposta{S.Recusa{}, v}, bs}:
      nao_ha_publicacao(s, S.Resposta{S.Recusa{}, v}, bs, fecha, entrega, n, w, {==}, consulta)
    case N.Conclusao{s, S.Resposta{S.Entrada{}, v}, bs}:
      nao_ha_publicacao(s, S.Resposta{S.Entrada{}, v}, bs, fecha, entrega, n, w, {==}, consulta)
    case N.Conclusao{s, S.Resposta{S.Autenticacao{}, v}, bs}:
      nao_ha_publicacao(s, S.Resposta{S.Autenticacao{}, v}, bs, fecha, entrega, n, w, {==}, consulta)
    case N.Conclusao{s, S.Resposta{S.Certificado{}, v}, bs}:
      nao_ha_publicacao(s, S.Resposta{S.Certificado{}, v}, bs, fecha, entrega, n, w, {==}, consulta)
    case N.Conclusao{s, S.Resposta{S.Dados{}, v}, bs}:
      nao_ha_publicacao(s, S.Resposta{S.Dados{}, v}, bs, fecha, entrega, n, w, {==}, consulta)
    case N.Conclusao{s, S.Resposta{S.Limite{}, v}, bs}:
      nao_ha_publicacao(s, S.Resposta{S.Limite{}, v}, bs, fecha, entrega, n, w, {==}, consulta)
    case N.Conclusao{s, S.Resposta{S.Falha{}, v}, bs}:
      nao_ha_publicacao(s, S.Resposta{S.Falha{}, v}, bs, fecha, entrega, n, w, {==}, consulta)

law marca_unica_entre_partes_ausentes:
  for +tipo: Tipo
  for antes: List<&2, Q.Quadro>
  for +depois: List<&2, Q.Quadro>
  for +marca: Q.Quadro
  for n: Nat
  for +q: Q.Quadro
  for sem_antes: {ausente(tipo, antes) == True{} : Bool}
  for sem_depois: {ausente(tipo, depois) == True{} : Bool}
  for alvo: {desse_tipo(tipo, q) == True{} : Bool}
  for consulta: {Q.consultar(Q.concatenar(antes, Con{marca, depois}), n) == Some{q} : Maybe<&2, Q.Quadro>}
  L.E<{n == Q.tamanho(antes) : Nat}, {q == marca : Q.Quadro}>
def marca_unica_entre_partes_ausentes(tipo, antes, depois, marca, n, q, sem_antes, sem_depois, alvo, consulta):
  match antes n:
    case Nil{} 0n:
      L.Ambos{{==}, Equal.sym(Q.Quadro, marca, q, F.algum_injetivo(Q.Quadro, marca, q, consulta))}
    case Nil{} 1n+k:
      L.ex_falso(L.E<{1n+k == 0n : Nat}, {q == marca : Q.Quadro}>,
        ausente_exclui_consulta(tipo, depois, k, q, sem_depois, alvo, consulta))
    case Con{+a, t} 0n:
      L.ex_falso(L.E<{0n == Q.tamanho(Con{a, t}) : Nat}, {q == marca : Q.Quadro}>,
        ausente_exclui_consulta(tipo, [a], 0n, q,
          F.e_booleano_intro(Bool.not(desse_tipo(tipo, a)), True{},
            F.e_booleano_esquerda(Bool.not(desse_tipo(tipo, a)), ausente(tipo, t), sem_antes), {==}), alvo, consulta))
    case Con{a, +t} 1n+k:
      F.com_par(L.E<{1n+k == Q.tamanho(Con{a, t}) : Nat}, {q == marca : Q.Quadro}>,
        {k == Q.tamanho(t) : Nat}, {q == marca : Q.Quadro},
        marca_unica_entre_partes_ausentes(tipo, t, depois, marca, k, q,
          F.e_booleano_direita(Bool.not(desse_tipo(tipo, a)), ausente(tipo, t), sem_antes), sem_depois, alvo, consulta),
        lugar => igual => L.Ambos{Equal.cong(Nat, Nat, x => 1n+x, k, Q.tamanho(t), lugar), igual})

law publicacao_nao_conclui:
  for r: S.Resposta
  for -s: D.Estado
  {ausente(Conclusao{}, H.render_publicacao(r, s)) == True{} : Bool}
def publicacao_nao_conclui(r, s):
  match r:
    case S.Resposta{S.Sucesso{}, v}: {==}
    case S.Resposta{S.Recusa{}, v}: {==}
    case S.Resposta{S.Entrada{}, v}: {==}
    case S.Resposta{S.Autenticacao{}, v}: {==}
    case S.Resposta{S.Certificado{}, v}: {==}
    case S.Resposta{S.Dados{}, v}: {==}
    case S.Resposta{S.Limite{}, v}: {==}
    case S.Resposta{S.Falha{}, v}: {==}

law conclusao_no_fim_e_unica:
  for +s: D.Estado
  for +r: S.Resposta
  for +bs: List<&2, U32>
  for +fecha: Bool
  for +entrega: H.Entrega
  for n: Nat
  for +outra: Q.Quadro
  for tipo: {desse_tipo(Conclusao{}, outra) == True{} : Bool}
  for consulta: {Q.consultar(H.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega), n) == Some{outra} : Maybe<&2, Q.Quadro>}
  L.E<{n == Q.tamanho(Con{Q.Preparada{r, bs}, H.render_publicacao(r, s)}) : Nat},
    {outra == Q.Concluida{r, s, fecha} : Q.Quadro}>
def conclusao_no_fim_e_unica(s, r, bs, fecha, entrega, n, outra, tipo, consulta):
  marca_unica_entre_partes_ausentes(Conclusao{}, Con{Q.Preparada{r, bs}, H.render_publicacao(r, s)},
    H.render_entrega(s, bs, fecha, entrega), Q.Concluida{r, s, fecha}, n, outra,
    publicacao_nao_conclui(r, s), entrega_sem_conclusao(s, bs, fecha, entrega), tipo, consulta)

law entrega_completa_e_unica:
  for +s: D.Estado
  for +bs: List<&2, U32>
  for +fecha: Bool
  for +proxima: Bool
  for n: Nat
  for +q: Q.Quadro
  for tipo: {desse_tipo(Completa{}, q) == True{} : Bool}
  for consulta: {Q.consultar(H.render_entrega(s, bs, fecha, H.Completa{proxima}), n) == Some{q} : Maybe<&2, Q.Quadro>}
  L.E<{n == 0n : Nat}, {q == Q.Entregue{bs} : Q.Quadro}>
def entrega_completa_e_unica(s, bs, fecha, proxima, n, q, tipo, consulta):
  marca_unica_entre_partes_ausentes(Completa{}, Nil{}, H.depois_entrega(fecha, s, proxima), Q.Entregue{bs}, n, q,
    {==}, depois_entrega_sem_macros(Completa{}, fecha, s, proxima), tipo, consulta)

law entrega_interrompida_e_unica:
  for -s: D.Estado
  for -bs: List<&2, U32>
  for -fecha: Bool
  for +prefixo: List<&2, U32>
  for n: Nat
  for +q: Q.Quadro
  for tipo: {desse_tipo(Interrompida{}, q) == True{} : Bool}
  for consulta: {Q.consultar(H.render_entrega(s, bs, fecha, H.Quebrada{prefixo}), n) == Some{q} : Maybe<&2, Q.Quadro>}
  L.E<{n == 0n : Nat}, {q == Q.Interrompida{prefixo} : Q.Quadro}>
def entrega_interrompida_e_unica(s, bs, fecha, prefixo, n, q, tipo, consulta):
  marca_unica_entre_partes_ausentes(Interrompida{}, Nil{}, [Q.Fechada{}], Q.Interrompida{prefixo}, n, q,
    {==}, {==}, tipo, consulta)

law concatenar_ausencia:
  for +tipo: Tipo
  for xs: List<&2, Q.Quadro>
  for +ys: List<&2, Q.Quadro>
  for hx: {ausente(tipo, xs) == True{} : Bool}
  for hy: {ausente(tipo, ys) == True{} : Bool}
  {ausente(tipo, Q.concatenar(xs, ys)) == True{} : Bool}
def concatenar_ausencia(tipo, xs, ys, hx, hy):
  match xs:
    case Nil{}: hy
    case Con{+h, +t}:
      F.com_par({ausente(tipo, Q.concatenar(Con{h, t}, ys)) == True{} : Bool},
        {Bool.not(desse_tipo(tipo, h)) == True{} : Bool}, {ausente(tipo, t) == True{} : Bool},
        F.e_booleano_separar(Bool.not(desse_tipo(tipo, h)), ausente(tipo, t), hx),
        cabeca => cauda => F.e_booleano_intro(Bool.not(desse_tipo(tipo, h)), ausente(tipo, Q.concatenar(t, ys)),
          cabeca, concatenar_ausencia(tipo, t, ys, cauda, hy)))

def interna_nao_macro(-tipo: Tipo, q: Q.Quadro, h: {M.interna(q) == True{} : Bool}) ->
  {desse_tipo(tipo, q) == False{} : Bool}:
  match q:
    case Q.Codificada{v, bs}: {==}
    case Q.Decodificada{bs, v}: {==}
    case Q.Guardada{s, bs, a}: {==}
    case Q.Conferida{pos, n}: {==}
    case Q.Construida{pos, n}: {==}
    case Q.Lida{a, n, d}: {==}
    case Q.Configurada{}: F.absurdo_booleano({desse_tipo(tipo, Q.Configurada{}) == False{} : Bool}, h)
    case Q.InicialAceita{}: F.absurdo_booleano({desse_tipo(tipo, Q.InicialAceita{}) == False{} : Bool}, h)
    case Q.Iniciada{s}: F.absurdo_booleano({desse_tipo(tipo, Q.Iniciada{s}) == False{} : Bool}, h)
    case Q.InicialRecusada{s}: F.absurdo_booleano({desse_tipo(tipo, Q.InicialRecusada{s}) == False{} : Bool}, h)
    case Q.Recebida{r}: F.absurdo_booleano({desse_tipo(tipo, Q.Recebida{r}) == False{} : Bool}, h)
    case Q.Autenticada{r, ctx}: F.absurdo_booleano({desse_tipo(tipo, Q.Autenticada{r, ctx}) == False{} : Bool}, h)
    case Q.Aceita{r, ctx}: F.absurdo_booleano({desse_tipo(tipo, Q.Aceita{r, ctx}) == False{} : Bool}, h)
    case Q.Rejeitada{r, ctx}: F.absurdo_booleano({desse_tipo(tipo, Q.Rejeitada{r, ctx}) == False{} : Bool}, h)
    case Q.Comecada{r, ctx}: F.absurdo_booleano({desse_tipo(tipo, Q.Comecada{r, ctx}) == False{} : Bool}, h)
    case Q.Avaliada{r, ctx, p}: F.absurdo_booleano({desse_tipo(tipo, Q.Avaliada{r, ctx, p}) == False{} : Bool}, h)
    case Q.Operada{e, s, o, r}: F.absurdo_booleano({desse_tipo(tipo, Q.Operada{e, s, o, r}) == False{} : Bool}, h)
    case Q.Preparada{r, bs}: F.absurdo_booleano({desse_tipo(tipo, Q.Preparada{r, bs}) == False{} : Bool}, h)
    case Q.Publicada{s}: F.absurdo_booleano({desse_tipo(tipo, Q.Publicada{s}) == False{} : Bool}, h)
    case Q.Visivel{s}: F.absurdo_booleano({desse_tipo(tipo, Q.Visivel{s}) == False{} : Bool}, h)
    case Q.Falhou{etapa, id, fatal}: F.absurdo_booleano({desse_tipo(tipo, Q.Falhou{etapa, id, fatal}) == False{} : Bool}, h)
    case Q.Concluida{r, s, f}: F.absurdo_booleano({desse_tipo(tipo, Q.Concluida{r, s, f}) == False{} : Bool}, h)
    case Q.Entregue{bs}: F.absurdo_booleano({desse_tipo(tipo, Q.Entregue{bs}) == False{} : Bool}, h)
    case Q.Interrompida{bs}: F.absurdo_booleano({desse_tipo(tipo, Q.Interrompida{bs}) == False{} : Bool}, h)
    case Q.Fechada{}: F.absurdo_booleano({desse_tipo(tipo, Q.Fechada{}) == False{} : Bool}, h)
    case Q.Seguinte{a, b}: F.absurdo_booleano({desse_tipo(tipo, Q.Seguinte{a, b}) == False{} : Bool}, h)
    case Q.Inspecao{d}: F.absurdo_booleano({desse_tipo(tipo, Q.Inspecao{d}) == False{} : Bool}, h)
    case Q.Efeito{d}: F.absurdo_booleano({desse_tipo(tipo, Q.Efeito{d}) == False{} : Bool}, h)

def internas_sem_macros(+tipo: Tipo, xs: List<&2, Q.Quadro>, h: M.Internas(xs)) ->
  {ausente(tipo, xs) == True{} : Bool}:
  match xs h:
    case Nil{} _: {==}
    case Con{+q, +t} L.Ambos{cabeca, cauda}:
      F.e_booleano_intro(Bool.not(desse_tipo(tipo, q)), ausente(tipo, t),
        Equal.cong(Bool, Bool, Bool.not, desse_tipo(tipo, q), False{}, interna_nao_macro(tipo, q, cabeca)),
        internas_sem_macros(tipo, t, cauda))

law primitiva_sem_macros:
  for +tipo: Tipo
  for +p: M.Primitiva
  {ausente(tipo, M.expandir(p)) == True{} : Bool}
def primitiva_sem_macros(tipo, p):
  internas_sem_macros(tipo, M.expandir(p), M.expandir_internas(p))

law primitivas_sem_macros:
  for +tipo: Tipo
  for +ps: List<&2, M.Primitiva>
  {ausente(tipo, M.expandir_primitivas(ps)) == True{} : Bool}
def primitivas_sem_macros(tipo, ps):
  internas_sem_macros(tipo, M.expandir_primitivas(ps), M.primitivas_so_geram_internas(ps))

law execucao_sem_macros:
  for +tipo: Tipo
  for +r: Protocolo.Requisicao
  for +ctx: D.Contexto
  for xs: List<&2, Q.QuadroExec>
  {ausente(tipo, Q.expandir_exec(r, ctx, xs)) == True{} : Bool}
def execucao_sem_macros(tipo, r, ctx, xs):
  match xs:
    case Nil{}: {==}
    case Con{Q.Avaliacao{percurso}, t}: execucao_sem_macros(tipo, r, ctx, t)
    case Con{Q.Operacao{e, s, o, resultado}, t}: execucao_sem_macros(tipo, r, ctx, t)

def micro_entrada_sem_macros(tipo: Tipo, m: H.Micro) ->
  {ausente(tipo, H.micro_entrada(m)) == True{} : Bool}:
  match m:
    case H.Micro{a, b, c, d}: primitivas_sem_macros(tipo, a)

def micro_autenticacao_sem_macros(tipo: Tipo, m: H.Micro) ->
  {ausente(tipo, H.micro_autenticacao(m)) == True{} : Bool}:
  match m:
    case H.Micro{a, b, c, d}: primitivas_sem_macros(tipo, b)

def micro_execucao_sem_macros(tipo: Tipo, m: H.Micro) ->
  {ausente(tipo, H.micro_execucao(m)) == True{} : Bool}:
  match m:
    case H.Micro{a, b, c, d}: primitivas_sem_macros(tipo, c)

def micro_saida_sem_macros(tipo: Tipo, m: H.Micro) ->
  {ausente(tipo, H.micro_saida(m)) == True{} : Bool}:
  match m:
    case H.Micro{a, b, c, d}: primitivas_sem_macros(tipo, d)

def recebida_sem_macros(+tipo: Tipo, +m: H.Micro, +r: Protocolo.Requisicao) ->
  {ausente(tipo, H.render_recebida(m, r)) == True{} : Bool}:
  concatenar_ausencia(tipo, H.micro_entrada(m), [Q.Recebida{r}], micro_entrada_sem_macros(tipo, m), {==})

def autenticada_sem_macros(+tipo: Tipo, +m: H.Micro, +r: Protocolo.Requisicao, +ctx: D.Contexto) ->
  {ausente(tipo, H.render_autenticada(m, r, ctx)) == True{} : Bool}:
  concatenar_ausencia(tipo, H.render_recebida(m, r), Q.concatenar(H.micro_autenticacao(m), [Q.Autenticada{r, Some{ctx}}]),
    recebida_sem_macros(tipo, m, r),
    concatenar_ausencia(tipo, H.micro_autenticacao(m), [Q.Autenticada{r, Some{ctx}}], micro_autenticacao_sem_macros(tipo, m), {==}))

def verificada_sem_macros(+tipo: Tipo, +m: H.Micro, +r: Protocolo.Requisicao, +ctx: D.Contexto) ->
  {ausente(tipo, H.render_verificada(m, r, ctx)) == True{} : Bool}:
  concatenar_ausencia(tipo, H.render_autenticada(m, r, ctx), [Q.Aceita{r, ctx}], autenticada_sem_macros(tipo, m, r, ctx), {==})

def comecada_sem_macros(+tipo: Tipo, +m: H.Micro, +r: Protocolo.Requisicao, +ctx: D.Contexto) ->
  {ausente(tipo, H.render_comecada(m, r, ctx)) == True{} : Bool}:
  concatenar_ausencia(tipo, H.render_verificada(m, r, ctx), Q.concatenar(H.micro_execucao(m), [Q.Comecada{r, ctx}]),
    verificada_sem_macros(tipo, m, r, ctx),
    concatenar_ausencia(tipo, H.micro_execucao(m), [Q.Comecada{r, ctx}], micro_execucao_sem_macros(tipo, m), {==}))

def execucao_host_sem_macros(+tipo: Tipo, +m: H.Micro, +r: Protocolo.Requisicao, +ctx: D.Contexto,
  +exec: List<&2, Q.QuadroExec>) ->
  {ausente(tipo, H.render_execucao(m, r, ctx, exec)) == True{} : Bool}:
  concatenar_ausencia(tipo, H.render_comecada(m, r, ctx), Q.expandir_exec(r, ctx, exec),
    comecada_sem_macros(tipo, m, r, ctx), execucao_sem_macros(tipo, r, ctx, exec))

law fase_anterior_sem_macros:
  for +tipo: Tipo
  for +m: H.Micro
  for fase: H.FaseAntes
  {ausente(tipo, H.render_fase(m, fase)) == True{} : Bool}
def fase_anterior_sem_macros(tipo, m, fase):
  match fase:
    case H.AntesEntrada{}: micro_entrada_sem_macros(tipo, m)
    case H.AposReceber{r}: recebida_sem_macros(tipo, m, r)
    case H.AposAutenticar{r, ctx}: autenticada_sem_macros(tipo, m, r, ctx)
    case H.AposVerificar{r, ctx}: verificada_sem_macros(tipo, m, r, ctx)
    case H.Executando{r, ctx, exec}: execucao_host_sem_macros(tipo, m, r, ctx, exec)
    case H.AposPreparar{+r, +ctx, +exec, N.Preparada{w, ts, +rp, +bs}}:
      concatenar_ausencia(tipo, H.render_execucao(m, r, ctx, exec),
        Q.concatenar(H.micro_saida(m), [Q.Preparada{rp, bs}]),
        execucao_host_sem_macros(tipo, m, r, ctx, exec),
        concatenar_ausencia(tipo, H.micro_saida(m), [Q.Preparada{rp, bs}], micro_saida_sem_macros(tipo, m), {==}))

law deslocamento_preserva_antes:
  for prefixo: Nat
  for -a: Nat
  for -b: Nat
  for menor: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(Nat.add(prefixo, a), Nat.add(prefixo, b)) == True{} : Bool}
def deslocamento_preserva_antes(prefixo, a, b, menor):
  match prefixo:
    case 0n: menor
    case 1n+k: deslocamento_preserva_antes(k, a, b, menor)

law preparo_antes_da_publicacao_no_fim:
  for +conclusao: N.Conclusao
  for +fecha: Bool
  for +entrega: H.Entrega
  for n: Nat
  for +w: D.Estado
  for consulta: {Q.consultar(H.render_conclusao(conclusao, fecha, entrega), n) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}
  exs r: S.Resposta
  exs bs: List<&2, U32>
  exs u: Nat
  L.E<{Nat.is_lt(u, n) == True{} : Bool},
    {Q.consultar(H.render_conclusao(conclusao, fecha, entrega), u) == Some{Q.Preparada{r, bs}} : Maybe<&2, Q.Quadro>}>
def preparo_antes_da_publicacao_no_fim(conclusao, fecha, entrega, n, w, consulta):
  match conclusao:
    case N.Conclusao{+s, +r, +bs}:
      F.com_par(
        (&r0: S.Resposta -> &bytes: List<&2, U32> -> &u: Nat ->
          L.E<{Nat.is_lt(u, n) == True{} : Bool},
            {Q.consultar(H.render_conclusao(N.Conclusao{s, r, bs}, fecha, entrega), u) == Some{Q.Preparada{r0, bytes}} : Maybe<&2, Q.Quadro>}>),
        {n == 1n : Nat}, {w == s : D.Estado},
        publicacao_no_fim_e_unica(N.Conclusao{s, r, bs}, fecha, entrega, n, w, consulta),
        lugar => estado =>
          (r, bs, 0n, L.Ambos{
            (%Equal.sym(Nat, n, 1n, lugar) : {Nat.is_lt(0n, _) == True{} : Bool} {==}), {==}}))

# Origem operacional da visibilidade: nenhum invariante do banco e assumido.
def SemPublicacaoAntes(-xs: List<&2, Q.Quadro>, -t: Nat) -> Type:
  @u: Nat -> @w: D.Estado -> {Nat.is_lt(u, t) == True{} : Bool} ->
    {Q.consultar(xs, u) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>} -> Empty

def Origem(-xs: List<&2, Q.Quadro>, -t: Nat, -inicial: D.Estado, -visivel: D.Estado) -> Type:
  L.Ou<L.E<{visivel == inicial : D.Estado}, SemPublicacaoAntes(xs, t)>,
    (&u: Nat -> L.E<{Nat.is_lt(u, t) == True{} : Bool},
      {Q.consultar(xs, u) == Some{Q.Publicada{visivel}} : Maybe<&2, Q.Quadro>}>)>

def nunca_antes_zero(u: Nat, menor: {Nat.is_lt(u, 0n) == True{} : Bool}) -> Empty:
  match u:
    case 0n: F.falso_nao_verdadeiro(menor)
    case 1n+k: F.falso_nao_verdadeiro(menor)

def antes_zero(-xs: List<&2, Q.Quadro>) -> SemPublicacaoAntes(xs, 0n):
  u => w => menor => consulta => nunca_antes_zero(u, menor)

def antes_vazio(-t: Nat) -> SemPublicacaoAntes(Nil{}, t):
  u => w => menor => consulta => F.nenhum_nao_algum(Q.Quadro, Q.Publicada{w}, consulta)

def ausencia_frente(u: Nat, +q: Q.Quadro, +xs: List<&2, Q.Quadro>, +t: Nat,
  nao: {desse_tipo(Publicacao{}, q) == False{} : Bool}, resto: SemPublicacaoAntes(xs, t), +w: D.Estado,
  menor: {Nat.is_lt(u, 1n+t) == True{} : Bool},
  consulta: {Q.consultar(Con{q, xs}, u) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}) -> Empty:
  match u:
    case 0n:
      F.falso_nao_verdadeiro(Equal.trans(Bool, False{}, desse_tipo(Publicacao{}, q), True{},
        Equal.sym(Bool, desse_tipo(Publicacao{}, q), False{}, nao),
        Equal.cong(Q.Quadro, Bool, x => desse_tipo(Publicacao{}, x), q, Q.Publicada{w},
          F.algum_injetivo(Q.Quadro, q, Q.Publicada{w}, consulta))))
    case 1n+v: resto(v, w, menor, consulta)

def prolongar_ausencia(+q: Q.Quadro, +xs: List<&2, Q.Quadro>, +t: Nat,
  nao: {desse_tipo(Publicacao{}, q) == False{} : Bool}, resto: SemPublicacaoAntes(xs, t)) ->
  SemPublicacaoAntes(Con{q, xs}, 1n+t):
  u => w => menor => consulta => ausencia_frente(u, q, xs, t, nao, resto, w, menor, consulta)

# A origem tambem registra inicializacao; o fold permanece o estado calculado.
def OrigemGeral(-xs: List<&2, Q.Quadro>, -t: Nat,
  -inicial: Maybe<&2, D.Estado>, -visivel: D.Estado) -> Type:
  L.Ou<L.E<{inicial == Some{visivel} : Maybe<&2, D.Estado>}, SemPublicacaoAntes(xs, t)>,
    L.Ou<(&u: Nat -> L.E<{Nat.is_lt(u, t) == True{} : Bool},
      {Q.consultar(xs, u) == Some{Q.Publicada{visivel}} : Maybe<&2, Q.Quadro>}>),
      (&u: Nat -> L.E<{Nat.is_lt(u, t) == True{} : Bool},
        {Q.consultar(xs, u) == Some{Q.Iniciada{visivel}} : Maybe<&2, Q.Quadro>}>)>>

def prolongar_origem(+q: Q.Quadro, +xs: List<&2, Q.Quadro>, +t: Nat,
  -inicial: Maybe<&2, D.Estado>, +visivel: D.Estado,
  nao: {desse_tipo(Publicacao{}, q) == False{} : Bool}, origem: OrigemGeral(xs, t, inicial, visivel)) ->
  OrigemGeral(Con{q, xs}, 1n+t, inicial, visivel):
  match origem:
    case L.Esquerda{L.Ambos{igual, nenhuma}}:
      L.Esquerda{L.Ambos{igual, prolongar_ausencia(q, xs, t, nao, nenhuma)}}
    case L.Direita{L.Esquerda{(u, L.Ambos{menor, consulta})}}:
      L.Direita{L.Esquerda{(1n+u, L.Ambos{menor, consulta})}}
    case L.Direita{L.Direita{(u, L.Ambos{menor, consulta})}}:
      L.Direita{L.Direita{(1n+u, L.Ambos{menor, consulta})}}

def origem_publicada(+xs: List<&2, Q.Quadro>, +t: Nat, -inicial: Maybe<&2, D.Estado>,
  +publicado: D.Estado, +visivel: D.Estado, origem: OrigemGeral(xs, t, Some{publicado}, visivel)) ->
  OrigemGeral(Con{Q.Publicada{publicado}, xs}, 1n+t, inicial, visivel):
  match origem:
    case L.Esquerda{L.Ambos{igual, nenhuma}}:
      L.Direita{L.Esquerda{(0n, L.Ambos{{==}, Equal.cong(D.Estado, Maybe<&2, Q.Quadro>, w => Some{Q.Publicada{w}},
        publicado, visivel, F.algum_injetivo(D.Estado, publicado, visivel, igual))})}}
    case L.Direita{L.Esquerda{(u, L.Ambos{menor, consulta})}}:
      L.Direita{L.Esquerda{(1n+u, L.Ambos{menor, consulta})}}
    case L.Direita{L.Direita{(u, L.Ambos{menor, consulta})}}:
      L.Direita{L.Direita{(1n+u, L.Ambos{menor, consulta})}}

def origem_iniciada(+xs: List<&2, Q.Quadro>, +t: Nat, -inicial: Maybe<&2, D.Estado>,
  +seed: D.Estado, +visivel: D.Estado, origem: OrigemGeral(xs, t, Some{seed}, visivel)) ->
  OrigemGeral(Con{Q.Iniciada{seed}, xs}, 1n+t, inicial, visivel):
  match origem:
    case L.Esquerda{L.Ambos{igual, nenhuma}}:
      L.Direita{L.Direita{(0n, L.Ambos{{==}, Equal.cong(D.Estado, Maybe<&2, Q.Quadro>, w => Some{Q.Iniciada{w}},
        seed, visivel, F.algum_injetivo(D.Estado, seed, visivel, igual))})}}
    case L.Direita{L.Esquerda{(u, L.Ambos{menor, consulta})}}:
      L.Direita{L.Esquerda{(1n+u, L.Ambos{menor, consulta})}}
    case L.Direita{L.Direita{(u, L.Ambos{menor, consulta})}}:
      L.Direita{L.Direita{(1n+u, L.Ambos{menor, consulta})}}

law origem_geral_do_estado_visivel:
  for t: Nat
  for +xs: List<&2, Q.Quadro>
  for +inicial: Maybe<&2, D.Estado>
  for +visivel: D.Estado
  for visto: {Q.estado_em(xs, t, inicial) == Some{visivel} : Maybe<&2, D.Estado>}
  OrigemGeral(xs, t, inicial, visivel)
def origem_geral_do_estado_visivel(t, xs, inicial, visivel, visto):
  match t:
    case 0n:
      L.Esquerda{L.Ambos{
        Equal.trans(Maybe<&2, D.Estado>, inicial, Q.estado_em(xs, 0n, inicial), Some{visivel},
          Equal.sym(Maybe<&2, D.Estado>, Q.estado_em(xs, 0n, inicial), inicial,
            Q.estado_antes_do_primeiro_passo(xs, inicial)), visto), antes_zero(xs)}}
    case 1n+ +k:
      match xs:
        case Nil{}: L.Esquerda{L.Ambos{visto, antes_vazio(1n+k)}}
        case Con{q, +resto}:
          match q:
            case Q.Publicada{+w}:
              origem_publicada(resto, k, inicial, w, visivel, origem_geral_do_estado_visivel(k, resto, Some{w}, visivel, visto))
            case Q.Iniciada{+w}:
              origem_iniciada(resto, k, inicial, w, visivel, origem_geral_do_estado_visivel(k, resto, Some{w}, visivel, visto))
            case Q.Configurada{}:
              prolongar_origem(Q.Configurada{}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.InicialAceita{}:
              prolongar_origem(Q.InicialAceita{}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.InicialRecusada{+status}:
              prolongar_origem(Q.InicialRecusada{status}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Codificada{+v, +bs}:
              prolongar_origem(Q.Codificada{v, bs}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Decodificada{+bs, +v}:
              prolongar_origem(Q.Decodificada{bs, v}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Guardada{+s, +bs, +a}:
              prolongar_origem(Q.Guardada{s, bs, a}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Conferida{+p, +n}:
              prolongar_origem(Q.Conferida{p, n}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Construida{+p, +n}:
              prolongar_origem(Q.Construida{p, n}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Lida{+a, +n, +d}:
              prolongar_origem(Q.Lida{a, n, d}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Recebida{+r}:
              prolongar_origem(Q.Recebida{r}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Autenticada{+r, +ctx}:
              prolongar_origem(Q.Autenticada{r, ctx}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Aceita{+r, +ctx}:
              prolongar_origem(Q.Aceita{r, ctx}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Rejeitada{+r, +ctx}:
              prolongar_origem(Q.Rejeitada{r, ctx}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Comecada{+r, +ctx}:
              prolongar_origem(Q.Comecada{r, ctx}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Avaliada{+r, +ctx, +percurso}:
              prolongar_origem(Q.Avaliada{r, ctx, percurso}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Operada{+e, +s, +o, +r}:
              prolongar_origem(Q.Operada{e, s, o, r}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Preparada{+r, +bs}:
              prolongar_origem(Q.Preparada{r, bs}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Visivel{+s}:
              prolongar_origem(Q.Visivel{s}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Falhou{+etapa, +id, +fatal}:
              prolongar_origem(Q.Falhou{etapa, id, fatal}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Concluida{+r, +s, +fecha}:
              prolongar_origem(Q.Concluida{r, s, fecha}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Entregue{+bs}:
              prolongar_origem(Q.Entregue{bs}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Interrompida{+bs}:
              prolongar_origem(Q.Interrompida{bs}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Fechada{}:
              prolongar_origem(Q.Fechada{}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Seguinte{+a, +b}:
              prolongar_origem(Q.Seguinte{a, b}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Inspecao{+d}:
              prolongar_origem(Q.Inspecao{d}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))
            case Q.Efeito{+d}:
              prolongar_origem(Q.Efeito{d}, resto, k, inicial, visivel, {==},
                origem_geral_do_estado_visivel(k, resto, inicial, visivel, visto))

def origem_sem_reiniciar(+xs: List<&2, Q.Quadro>, +t: Nat, +inicial: D.Estado, +visivel: D.Estado,
  sem_iniciar: {ausente(Inicializacao{}, xs) == True{} : Bool}, origem: OrigemGeral(xs, t, Some{inicial}, visivel)) ->
  Origem(xs, t, inicial, visivel):
  match origem:
    case L.Esquerda{L.Ambos{igual, nenhuma}}:
      L.Esquerda{L.Ambos{Equal.sym(D.Estado, inicial, visivel, F.algum_injetivo(D.Estado, inicial, visivel, igual)), nenhuma}}
    case L.Direita{L.Esquerda{ocorrencia}}: L.Direita{ocorrencia}
    case L.Direita{L.Direita{(u, L.Ambos{menor, consulta})}}:
      L.ex_falso(Origem(xs, t, inicial, visivel),
        ausente_exclui_consulta(Inicializacao{}, xs, u, Q.Iniciada{visivel}, sem_iniciar, {==}, consulta))

law origem_do_estado_visivel:
  for +t: Nat
  for +xs: List<&2, Q.Quadro>
  for +inicial: D.Estado
  for +visivel: D.Estado
  for sem_iniciar: {ausente(Inicializacao{}, xs) == True{} : Bool}
  for visto: {Q.estado_em(xs, t, Some{inicial}) == Some{visivel} : Maybe<&2, D.Estado>}
  Origem(xs, t, inicial, visivel)
def origem_do_estado_visivel(t, xs, inicial, visivel, sem_iniciar, visto):
  origem_sem_reiniciar(xs, t, inicial, visivel, sem_iniciar, origem_geral_do_estado_visivel(t, xs, Some{inicial}, visivel, visto))

# A inicializacao gerada so instala o seed, apos a sua codificacao real.
def estado_iniciada(q: Q.Quadro) -> Maybe<&2, D.Estado>:
  match q:
    case Q.Iniciada{s}: Some{s}
    case _: None{}

def iniciadas_iguais(+a: D.Estado, -b: D.Estado,
  h: {Some{Q.Iniciada{a}} == Some{Q.Iniciada{b}} : Maybe<&2, Q.Quadro>}) -> {b == a : D.Estado}:
  Equal.sym(D.Estado, a, b, F.algum_injetivo(D.Estado, a, b,
    Equal.cong(Q.Quadro, Maybe<&2, D.Estado>, estado_iniciada, Q.Iniciada{a}, Q.Iniciada{b},
      F.algum_injetivo(Q.Quadro, Q.Iniciada{a}, Q.Iniciada{b}, h))))

def inicial_sem_publicacao(resultado: Maybe<&2, List<&2, U32>>, -s: D.Estado) ->
  {ausente(Publicacao{}, H.render_inicial(resultado, s)) == True{} : Bool}:
  match resultado:
    case None{}: {==}
    case Some{bs}: {==}

def inicial_so_inicia_seed(+resultado: Maybe<&2, List<&2, U32>>, +s: D.Estado, n: Nat, +w: D.Estado,
  h: {Q.consultar(H.render_inicial(resultado, s), n) == Some{Q.Iniciada{w}} : Maybe<&2, Q.Quadro>}) ->
  {w == s : D.Estado}:
  match resultado:
    case None{}:
      L.ex_falso({w == s : D.Estado}, ausente_exclui_consulta(Inicializacao{}, H.render_inicial(None{}, s), n,
        Q.Iniciada{w}, {==}, {==}, h))
    case Some{+bs}:
      match n:
        case 0n:
          L.ex_falso({w == s : D.Estado}, ausente_exclui_consulta(Inicializacao{},
            [Q.Codificada{D.estado_valor(s), Some{bs}}], 0n, Q.Iniciada{w}, {==}, {==}, h))
        case 1n+k:
          match k:
            case 0n:
              L.ex_falso({w == s : D.Estado}, ausente_exclui_consulta(Inicializacao{},
                [Q.Guardada{s, bs, s}], 0n, Q.Iniciada{w}, {==}, {==}, h))
            case 1n+j:
              match j:
                case 0n: iniciadas_iguais(s, w, h)
                case 1n+z: L.ex_falso({w == s : D.Estado}, F.nenhum_nao_algum(Q.Quadro, Q.Iniciada{w}, h))

law retirar_prefixo_ausente:
  for +tipo: Tipo
  for antes: List<&2, Q.Quadro>
  for +depois: List<&2, Q.Quadro>
  for n: Nat
  for +q: Q.Quadro
  for sem: {ausente(tipo, antes) == True{} : Bool}
  for alvo: {desse_tipo(tipo, q) == True{} : Bool}
  for obtida: {Q.consultar(Q.concatenar(antes, depois), n) == Some{q} : Maybe<&2, Q.Quadro>}
  exs u: Nat
  {Q.consultar(depois, u) == Some{q} : Maybe<&2, Q.Quadro>}
def retirar_prefixo_ausente(tipo, antes, depois, n, q, sem, alvo, obtida):
  match antes n:
    case Nil{} _: (n, obtida)
    case Con{+a, t} 0n:
      L.ex_falso((&u: Nat -> {Q.consultar(depois, u) == Some{q} : Maybe<&2, Q.Quadro>}),
        ausente_exclui_consulta(tipo, [a], 0n, q,
          F.e_booleano_intro(Bool.not(desse_tipo(tipo, a)), True{},
            F.e_booleano_esquerda(Bool.not(desse_tipo(tipo, a)), ausente(tipo, t), sem), {==}), alvo, obtida))
    case Con{a, t} 1n+k:
      retirar_prefixo_ausente(tipo, t, depois, k, q,
        F.e_booleano_direita(Bool.not(desse_tipo(tipo, a)), ausente(tipo, t), sem), alvo, obtida)

def inicializacao_sem_publicacao(+m: H.Micro, +s: D.Estado) ->
  {ausente(Publicacao{}, H.render(m, s, H.InicialOk{})) == True{} : Bool}:
  concatenar_ausencia(Publicacao{}, H.micro_saida(m), H.render_inicial(Protocolo.codificar(D.estado_valor(s)), s),
    micro_saida_sem_macros(Publicacao{}, m), inicial_sem_publicacao(Protocolo.codificar(D.estado_valor(s)), s))

def sufixo_inicia_seed(+resultado: Maybe<&2, List<&2, U32>>, +s: D.Estado, +w: D.Estado,
  h: &u: Nat -> {Q.consultar(H.render_inicial(resultado, s), u) == Some{Q.Iniciada{w}} : Maybe<&2, Q.Quadro>}) ->
  {w == s : D.Estado}:
  match h:
    case (u, consulta): inicial_so_inicia_seed(resultado, s, u, w, consulta)

def prefixo_inicia_seed(+m: H.Micro, +s: D.Estado, +w: D.Estado,
  h: &u: Nat -> {Q.consultar(Q.concatenar(H.micro_saida(m), H.render_inicial(Protocolo.codificar(D.estado_valor(s)), s)), u) ==
    Some{Q.Iniciada{w}} : Maybe<&2, Q.Quadro>}) -> {w == s : D.Estado}:
  match h:
    case (u, consulta):
      sufixo_inicia_seed(Protocolo.codificar(D.estado_valor(s)), s, w,
        retirar_prefixo_ausente(Inicializacao{}, H.micro_saida(m), H.render_inicial(Protocolo.codificar(D.estado_valor(s)), s),
          u, Q.Iniciada{w}, micro_saida_sem_macros(Inicializacao{}, m), {==}, consulta))

def inicializacao_so_inicia_seed(+m: H.Micro, +s: D.Estado, t: Nat, +w: D.Estado,
  h: {Q.consultar(H.render(m, s, H.InicialOk{}), t) == Some{Q.Iniciada{w}} : Maybe<&2, Q.Quadro>}) ->
  {w == s : D.Estado}:
  prefixo_inicia_seed(m, s, w, retirar_prefixo_ausente(Inicializacao{}, [Q.Configurada{}, Q.InicialAceita{}],
    Q.concatenar(H.micro_saida(m), H.render_inicial(Protocolo.codificar(D.estado_valor(s)), s)), t, Q.Iniciada{w}, {==}, {==}, h))

def origem_inicializacao(+t: Nat, +m: H.Micro, +s: D.Estado, +w: D.Estado,
  origem: OrigemGeral(H.render(m, s, H.InicialOk{}), t, None{}, w)) -> Origem(H.render(m, s, H.InicialOk{}), t, s, w):
  match origem:
    case L.Esquerda{L.Ambos{igual, nenhuma}}:
      L.ex_falso(Origem(H.render(m, s, H.InicialOk{}), t, s, w), F.nenhum_nao_algum(D.Estado, w, igual))
    case L.Direita{L.Esquerda{(u, L.Ambos{menor, consulta})}}:
      L.ex_falso(Origem(H.render(m, s, H.InicialOk{}), t, s, w),
        ausente_exclui_consulta(Publicacao{}, H.render(m, s, H.InicialOk{}), u, Q.Publicada{w}, inicializacao_sem_publicacao(m, s), {==}, consulta))
    case L.Direita{L.Direita{(u, L.Ambos{menor, consulta})}}:
      L.Esquerda{L.Ambos{inicializacao_so_inicia_seed(m, s, u, w, consulta),
        v => s2 => anterior => publicada => ausente_exclui_consulta(Publicacao{}, H.render(m, s, H.InicialOk{}), v,
          Q.Publicada{s2}, inicializacao_sem_publicacao(m, s), {==}, publicada)}}

law origem_do_estado_inicializado:
  for +t: Nat
  for +m: H.Micro
  for +s: D.Estado
  for +w: D.Estado
  for visto: {Q.estado_em(H.render(m, s, H.InicialOk{}), t, None{}) == Some{w} : Maybe<&2, D.Estado>}
  Origem(H.render(m, s, H.InicialOk{}), t, s, w)
def origem_do_estado_inicializado(t, m, s, w, visto):
  origem_inicializacao(t, m, s, w, origem_geral_do_estado_visivel(t, H.render(m, s, H.InicialOk{}), None{}, w, visto))

# Lifting da representacao: os dois mapas sao eliminacao/introducao de
# consultas da MESMA fonte fechada, nao hipoteses sobre a Lei6.
def contradizer_publicacao_anterior(-a: I.Ambiente, -k: String, -x: I.Cenario,
  -xs: List<&2, Q.Quadro>, -t: Nat, sem: SemPublicacaoAntes(xs, t),
  extrair: @u: Nat -> @s: D.Estado -> I.Acontece(a, k, x, u, I.Publicou{s}) ->
    {Q.consultar(xs, u) == Some{Q.Publicada{s}} : Maybe<&2, Q.Quadro>},
  +s: D.Estado, anterior: I.Antes(a, k, x, t, I.Publicou{s})) -> Empty:
  match anterior:
    case (+u, L.Ambos{ordem, fato}): sem(u, s, ordem, extrair(u, s, fato))

law origem_para_regra6:
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for -t: Nat
  for -xs: List<&2, Q.Quadro>
  for +s: D.Estado
  for origem: Origem(xs, t, I.inicial(x), s)
  for introduzir: @u: Nat -> @w: D.Estado ->
    {Q.consultar(xs, u) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>} -> I.Acontece(a, k, x, u, I.Publicou{w})
  for extrair: @u: Nat -> @w: D.Estado -> I.Acontece(a, k, x, u, I.Publicou{w}) ->
    {Q.consultar(xs, u) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}
  K.Regra6(I.EstadoVisivel{s}, a, k, x, t)
def origem_para_regra6(a, k, x, t, xs, s, origem, introduzir, extrair):
  match origem:
    case L.Esquerda{L.Ambos{igual, nenhuma}}:
      L.Esquerda{L.Ambos{igual, w => anterior => contradizer_publicacao_anterior(a, k, x, xs, t, nenhuma, extrair, w, anterior)}}
    case L.Direita{(+u, L.Ambos{ordem, consulta})}:
      L.Direita{(u, L.Ambos{ordem, introduzir(u, s, consulta)})}

# Conteudo da preparacao obtido da funcao real; a causa da resposta continua
# sendo demonstrada separadamente no ramo de execucao/erro que a produziu.
def DadosPreparados(-c: S.Configuracao, -p: N.Preparada) -> Type:
  L.E<I.ErroFixo(U.resposta(p)),
    L.E<Protocolo.Mensagem(S.resposta_valor(U.resposta(p)), Preparacao.bytes_preparados(p)),
      {R.cabe(R.limite_resposta(S.limites(c)), S.resposta_valor(U.resposta(p))) == True{} : Bool}>>

def unir_preparacao(-c: S.Configuracao, -w: D.Estado, -ts: List<&2, S.Evento>,
  -r: S.Resposta, -bs: List<&2, U32>, payload: Preparacao.Preparavel(S.limites(c), r),
  mensagem: Protocolo.Mensagem(S.resposta_valor(r), bs)) -> DadosPreparados(c, N.Preparada{w, ts, r, bs}):
  match payload:
    case L.Ambos{valor, tamanho}: L.Ambos{valor, L.Ambos{mensagem, tamanho}}

def dados_da_preparacao(~c: S.Configuracao, +w: D.Estado, +ts: List<&2, S.Evento>,
  +proposta: S.Resposta, +p: N.Preparada,
  fiel: Preparacao.Fiel(w, ts, R.finalizar(proposta, c, w), p),
  limites: {R.limites_validos(S.limites(c)) == True{} : Bool}) -> DadosPreparados(c, p):
  match fiel:
    case L.Ambos{igual, mensagem}:
      %Equal.sym(N.Preparada, p, N.Preparada{w, ts, R.finalizar(proposta, c, w), Preparacao.bytes_preparados(p)}, igual) : DadosPreparados(c, _)
      unir_preparacao(c, w, ts, R.finalizar(proposta, c, w), Preparacao.bytes_preparados(p),
        Preparacao.finalizar_garante_payload_e_tamanho(proposta, c, w, limites), mensagem)

law preparar_real_garante_payload_mensagem_e_tamanho:
  for ~c: S.Configuracao
  for +w: D.Estado
  for +ts: List<&2, S.Evento>
  for +proposta: S.Resposta
  for +p: N.Preparada
  for obtida: {N.preparar(N.Parada{w, ts, proposta}, c) == Some{p} : Maybe<&2, N.Preparada>}
  for limites: {R.limites_validos(S.limites(c)) == True{} : Bool}
  DadosPreparados(c, p)
def preparar_real_garante_payload_mensagem_e_tamanho(c, w, ts, proposta, p, obtida, limites):
  dados_da_preparacao(c, w, ts, proposta, p,
    Preparacao.preparar_preserva_resposta_estado_eventos_e_bytes(N.Parada{w, ts, proposta}, c, p, obtida), limites)

# Localizacao dos marcos no sufixo; o prefixo e o gerado por Micro/execucao.
def parte_apos_prefixo(+tipo: Tipo, +antes: List<&2, Q.Quadro>, -depois: List<&2, Q.Quadro>,
  -t: Nat, +q: Q.Quadro, sem: {ausente(tipo, antes) == True{} : Bool},
  alvo: {desse_tipo(tipo, q) == True{} : Bool}, parte: Q.Parte(antes, depois, t, q)) ->
  &u: Nat -> L.E<{t == Nat.add(Q.tamanho(antes), u) : Nat},
    {Q.consultar(depois, u) == Some{q} : Maybe<&2, Q.Quadro>}>:
  match parte:
    case L.Esquerda{(u, L.Ambos{pos, consulta})}:
      L.ex_falso((&u: Nat -> L.E<{t == Nat.add(Q.tamanho(antes), u) : Nat},
        {Q.consultar(depois, u) == Some{q} : Maybe<&2, Q.Quadro>}>),
        ausente_exclui_consulta(tipo, antes, u, q, sem, alvo, consulta))
    case L.Direita{ocorrencia}: ocorrencia

def localizar_no_sufixo(+tipo: Tipo, +antes: List<&2, Q.Quadro>, -depois: List<&2, Q.Quadro>,
  +t: Nat, +q: Q.Quadro, sem: {ausente(tipo, antes) == True{} : Bool},
  alvo: {desse_tipo(tipo, q) == True{} : Bool},
  consulta: {Q.consultar(Q.concatenar(antes, depois), t) == Some{q} : Maybe<&2, Q.Quadro>}) ->
  &u: Nat -> L.E<{t == Nat.add(Q.tamanho(antes), u) : Nat},
    {Q.consultar(depois, u) == Some{q} : Maybe<&2, Q.Quadro>}>:
  parte_apos_prefixo(tipo, antes, depois, t, q, sem, alvo, Q.dividir_consulta(antes, depois, t, q, consulta))

def publicacao_localizada(+antes: List<&2, Q.Quadro>, +conclusao: N.Conclusao, +fecha: Bool, +entrega: H.Entrega,
  -t: Nat, +w: D.Estado, parte: &u: Nat -> L.E<{t == Nat.add(Q.tamanho(antes), u) : Nat},
    {Q.consultar(H.render_conclusao(conclusao, fecha, entrega), u) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}>) ->
  L.E<{t == Nat.add(Q.tamanho(antes), 1n) : Nat}, {w == U.publicado(conclusao) : D.Estado}>:
  match parte:
    case (u, L.Ambos{pos, consulta}):
      F.com_par(L.E<{t == Nat.add(Q.tamanho(antes), 1n) : Nat}, {w == U.publicado(conclusao) : D.Estado}>,
        {u == 1n : Nat}, {w == U.publicado(conclusao) : D.Estado},
        publicacao_no_fim_e_unica(conclusao, fecha, entrega, u, w, consulta),
        local => estado => L.Ambos{Equal.trans(Nat, t, Nat.add(Q.tamanho(antes), u), Nat.add(Q.tamanho(antes), 1n),
          pos, Equal.cong(Nat, Nat, z => Nat.add(Q.tamanho(antes), z), u, 1n, local)), estado})

law publicacao_unica_apos_prefixo:
  for +antes: List<&2, Q.Quadro>
  for +conclusao: N.Conclusao
  for +fecha: Bool
  for +entrega: H.Entrega
  for +t: Nat
  for +w: D.Estado
  for sem: {ausente(Publicacao{}, antes) == True{} : Bool}
  for consulta: {Q.consultar(Q.concatenar(antes, H.render_conclusao(conclusao, fecha, entrega)), t) ==
    Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}
  L.E<{t == Nat.add(Q.tamanho(antes), 1n) : Nat}, {w == U.publicado(conclusao) : D.Estado}>
def publicacao_unica_apos_prefixo(antes, conclusao, fecha, entrega, t, w, sem, consulta):
  publicacao_localizada(antes, conclusao, fecha, entrega, t, w,
    localizar_no_sufixo(Publicacao{}, antes, H.render_conclusao(conclusao, fecha, entrega), t, Q.Publicada{w}, sem, {==}, consulta))

# A conclusao atomica e uma consequencia da ordem gerada e de N.concluir.
def nenhuma_publicacao_real(-a: I.Ambiente, -k: String, -x: I.Cenario, +xs: List<&2, Q.Quadro>,
  sem: {ausente(Publicacao{}, xs) == True{} : Bool},
  extrair: @u: Nat -> @w: D.Estado -> I.Acontece(a, k, x, u, I.Publicou{w}) ->
    {Q.consultar(xs, u) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}) -> K.NenhumaPublicacao(a, k, x):
  +u => +w => fato => ausente_exclui_consulta(Publicacao{}, xs, u, Q.Publicada{w}, sem, {==}, extrair(u, w, fato))

def conclusao_sem_publicacao_real(-a: I.Ambiente, -k: String, -x: I.Cenario,
  +antes: List<&2, Q.Quadro>, +s: D.Estado, +w: D.Estado, +ts: List<&2, S.Evento>, +r: S.Resposta,
  +bs: List<&2, U32>, +entrega: H.Entrega,
  sem: {ausente(Publicacao{}, antes) == True{} : Bool},
  inicial: {s == I.inicial(x) : D.Estado},
  status: {U.status_sucesso(r) == False{} : Bool},
  extrair: @u: Nat -> @v: D.Estado -> I.Acontece(a, k, x, u, I.Publicou{v}) ->
    {Q.consultar(Q.concatenar(antes, H.render_final(N.Preparada{w, ts, r, bs}, s, False{}, entrega)), u) == Some{Q.Publicada{v}} : Maybe<&2, Q.Quadro>}) ->
  L.E<{U.publicado(N.concluir(N.Preparada{w, ts, r, bs}, s)) == I.inicial(x) : D.Estado}, K.NenhumaPublicacao(a, k, x)>:
  F.com_par(L.E<{U.publicado(N.concluir(N.Preparada{w, ts, r, bs}, s)) == I.inicial(x) : D.Estado}, K.NenhumaPublicacao(a, k, x)>,
    {U.status_sucesso(r) == False{} : Bool}, {U.status_sucesso(r) == False{} : Bool},
    Chamada.duplicar_igualdade(Bool, U.status_sucesso(r), False{}, status),
    conserva => nenhuma =>
    L.Ambos{Equal.trans(D.Estado, S.publica(r, s, w), s, I.inicial(x),
      U.todo_status_sem_sucesso_preserva_publicado(r, s, w, conserva), inicial),
      nenhuma_publicacao_real(a, k, x, Q.concatenar(antes, H.render_final(N.Preparada{w, ts, r, bs}, s, False{}, entrega)),
        concatenar_ausencia(Publicacao{}, antes, H.render_final(N.Preparada{w, ts, r, bs}, s, False{}, entrega), sem,
          resposta_nao_publica(S.publica(r, s, w), r, bs, False{}, entrega, nenhuma)), extrair)})

def indice_conclusao(+antes: List<&2, Q.Quadro>, preparada: N.Preparada, s: D.Estado) -> Nat:
  N.Preparada{w, ts, +r, bs} = preparada
  Nat.add(Q.tamanho(antes), Q.tamanho(Con{Q.Preparada{r, bs}, H.render_publicacao(r, S.publica(r, s, w))}))

law conclusao_atomica_real:
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for +s: D.Estado
  for inicial: {s == I.inicial(x) : D.Estado}
  for +antes: List<&2, Q.Quadro>
  for +preparada: N.Preparada
  for +entrega: H.Entrega
  for sem: {ausente(Publicacao{}, antes) == True{} : Bool}
  for introduzir: @u: Nat -> @w: D.Estado ->
    {Q.consultar(Q.concatenar(antes, H.render_final(preparada, s, False{}, entrega)), u) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>} ->
    I.Acontece(a, k, x, u, I.Publicou{w})
  for extrair: @u: Nat -> @w: D.Estado -> I.Acontece(a, k, x, u, I.Publicou{w}) ->
    {Q.consultar(Q.concatenar(antes, H.render_final(preparada, s, False{}, entrega)), u) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}
  K.ConclusaoAtomica(U.resposta(preparada), a, k, x, indice_conclusao(antes, preparada, s),
    U.publicado(N.concluir(preparada, s)))
def conclusao_atomica_real(a, k, x, s, inicial, antes, preparada, entrega, sem, introduzir, extrair):
  match preparada:
    case N.Preparada{+w, ts, S.Resposta{S.Sucesso{}, +v}, +bs}:
      (Nat.add(Q.tamanho(antes), 1n), L.Ambos{Q.ordem_deslocada(Q.tamanho(antes), 1n, 2n, {==}),
        introduzir(Nat.add(Q.tamanho(antes), 1n), w,
          Q.consultar_apos_prefixo(antes, H.render_conclusao(N.Conclusao{w, S.Resposta{S.Sucesso{}, v}, bs}, False{}, entrega), 1n))})
    case N.Preparada{w, ts, S.Resposta{S.Recusa{}, v}, bs}:
      conclusao_sem_publicacao_real(a, k, x, antes, s, w, ts, S.Resposta{S.Recusa{}, v}, bs, entrega, sem, inicial, {==}, extrair)
    case N.Preparada{w, ts, S.Resposta{S.Entrada{}, v}, bs}:
      conclusao_sem_publicacao_real(a, k, x, antes, s, w, ts, S.Resposta{S.Entrada{}, v}, bs, entrega, sem, inicial, {==}, extrair)
    case N.Preparada{w, ts, S.Resposta{S.Autenticacao{}, v}, bs}:
      conclusao_sem_publicacao_real(a, k, x, antes, s, w, ts, S.Resposta{S.Autenticacao{}, v}, bs, entrega, sem, inicial, {==}, extrair)
    case N.Preparada{w, ts, S.Resposta{S.Certificado{}, v}, bs}:
      conclusao_sem_publicacao_real(a, k, x, antes, s, w, ts, S.Resposta{S.Certificado{}, v}, bs, entrega, sem, inicial, {==}, extrair)
    case N.Preparada{w, ts, S.Resposta{S.Dados{}, v}, bs}:
      conclusao_sem_publicacao_real(a, k, x, antes, s, w, ts, S.Resposta{S.Dados{}, v}, bs, entrega, sem, inicial, {==}, extrair)
    case N.Preparada{w, ts, S.Resposta{S.Limite{}, v}, bs}:
      conclusao_sem_publicacao_real(a, k, x, antes, s, w, ts, S.Resposta{S.Limite{}, v}, bs, entrega, sem, inicial, {==}, extrair)
    case N.Preparada{w, ts, S.Resposta{S.Falha{}, v}, bs}:
      conclusao_sem_publicacao_real(a, k, x, antes, s, w, ts, S.Resposta{S.Falha{}, v}, bs, entrega, sem, inicial, {==}, extrair)

# O atendimento nao pode instalar outra instancia: apenas InicialOk o faz.
def entrega_sem_inicio(-s: D.Estado, -bs: List<&2, U32>, fecha: Bool, entrega: H.Entrega) ->
  {ausente(InicioComProva{}, H.render_entrega(s, bs, fecha, entrega)) == True{} : Bool}:
  match entrega:
    case H.Completa{proxima}: depois_entrega_sem_macros(InicioComProva{}, fecha, s, proxima)
    case H.Quebrada{prefixo}: {==}
    case H.PendenteEntrega{}: {==}

def publicacao_sem_inicio(r: S.Resposta, -s: D.Estado) ->
  {ausente(InicioComProva{}, H.render_publicacao(r, s)) == True{} : Bool}:
  match r:
    case S.Resposta{S.Sucesso{}, v}: {==}
    case S.Resposta{S.Recusa{}, v}: {==}
    case S.Resposta{S.Entrada{}, v}: {==}
    case S.Resposta{S.Autenticacao{}, v}: {==}
    case S.Resposta{S.Certificado{}, v}: {==}
    case S.Resposta{S.Dados{}, v}: {==}
    case S.Resposta{S.Limite{}, v}: {==}
    case S.Resposta{S.Falha{}, v}: {==}

def conclusao_sem_inicio(conclusao: N.Conclusao, +fecha: Bool, +entrega: H.Entrega) ->
  {ausente(InicioComProva{}, H.render_conclusao(conclusao, fecha, entrega)) == True{} : Bool}:
  match conclusao:
    case N.Conclusao{+s, +r, +bs}:
      concatenar_ausencia(InicioComProva{}, H.render_publicacao(r, s),
        Con{Q.Concluida{r, s, fecha}, H.render_entrega(s, bs, fecha, entrega)},
        publicacao_sem_inicio(r, s), entrega_sem_inicio(s, bs, fecha, entrega))

def erro_enquadrado_sem_inicio(resultado: Maybe<&2, List<&2, U32>>, +r: S.Resposta,
  +s: D.Estado, +fecha: Bool, +entrega: H.Entrega) ->
  {ausente(InicioComProva{}, H.render_erro_enquadrado(resultado, r, s, fecha, entrega)) == True{} : Bool}:
  match resultado:
    case None{}: {==}
    case Some{bs}: entrega_sem_inicio(s, bs, fecha, entrega)

def erro_sem_inicio(+status: S.Status, +s: D.Estado, +fecha: Bool, +entrega: H.Entrega) ->
  {ausente(InicioComProva{}, H.render_erro(status, s, fecha, entrega)) == True{} : Bool}:
  erro_enquadrado_sem_inicio(Protocolo.enquadrar(S.resposta_valor(S.resposta_erro(status))), S.resposta_erro(status), s, fecha, entrega)

def falha_sem_inicio(+s: D.Estado, +etapa: X.Etapa, +id: String, fatal: Bool, +entrega: H.Entrega) ->
  {ausente(InicioComProva{}, H.render_falha(s, etapa, id, fatal, entrega)) == True{} : Bool}:
  match fatal:
    case True{}: {==}
    case False{}: erro_sem_inicio(S.Falha{}, s, False{}, entrega)

def fatal_publicada_sem_inicio(conclusao: N.Conclusao, +etapa: X.Etapa, +id: String) ->
  {ausente(InicioComProva{}, H.render_fatal_publicada(conclusao, etapa, id)) == True{} : Bool}:
  match conclusao:
    case N.Conclusao{+s, +r, bs}:
      concatenar_ausencia(InicioComProva{}, H.render_publicacao(r, s), [Q.Falhou{etapa, id, True{}}, Q.Fechada{}], publicacao_sem_inicio(r, s), {==})

law caso_sem_inicio:
  for +m: H.Micro
  for +s: D.Estado
  for +caso: H.Caso
  for atendimento: {H.inicia(caso) == False{} : Bool}
  {ausente(InicioComProva{}, H.render(m, s, caso)) == True{} : Bool}
def caso_sem_inicio(m, s, caso, atendimento):
  match caso:
    case H.InicialOk{}:
      F.absurdo_booleano({ausente(InicioComProva{}, H.render(m, s, H.InicialOk{})) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, atendimento))
    case H.InicialRecusa{status}: {==}
    case H.InicialFalha{aceita, etapa, id, fatal}:
      match aceita:
        case True{}:
          F.absurdo_booleano({ausente(InicioComProva{}, H.render(m, s, H.InicialFalha{True{}, etapa, id, fatal})) == True{} : Bool},
            Equal.sym(Bool, True{}, False{}, atendimento))
        case False{}: {==}
    case H.SemResposta{}: {==}
    case H.EntradaRecusa{+erro, +fecha, +entrega}:
      concatenar_ausencia(InicioComProva{}, H.micro_entrada(m), H.render_erro(H.status_entrada(erro), s, fecha, entrega),
        micro_entrada_sem_macros(InicioComProva{}, m), erro_sem_inicio(H.status_entrada(erro), s, fecha, entrega))
    case H.AutRecusa{+r, +entrega}:
      concatenar_ausencia(InicioComProva{}, H.render_recebida(m, r), Q.concatenar(H.micro_autenticacao(m),
        Con{Q.Autenticada{r, None{}}, H.render_erro(S.Autenticacao{}, s, False{}, entrega)}), recebida_sem_macros(InicioComProva{}, m, r),
        concatenar_ausencia(InicioComProva{}, H.micro_autenticacao(m), Con{Q.Autenticada{r, None{}}, H.render_erro(S.Autenticacao{}, s, False{}, entrega)},
          micro_autenticacao_sem_macros(InicioComProva{}, m), erro_sem_inicio(S.Autenticacao{}, s, False{}, entrega)))
    case H.GateRecusa{+r, +ctx, +entrega}:
      concatenar_ausencia(InicioComProva{}, H.render_autenticada(m, r, ctx), Con{Q.Rejeitada{r, ctx}, H.render_erro(S.Certificado{}, s, False{}, entrega)},
        autenticada_sem_macros(InicioComProva{}, m, r, ctx), erro_sem_inicio(S.Certificado{}, s, False{}, entrega))
    case H.Executada{+r, +ctx, +exec, +p, +entrega}:
      concatenar_ausencia(InicioComProva{}, H.render_execucao(m, r, ctx, exec), Q.concatenar(H.micro_saida(m), H.render_final(p, s, False{}, entrega)),
        execucao_host_sem_macros(InicioComProva{}, m, r, ctx, exec),
        concatenar_ausencia(InicioComProva{}, H.micro_saida(m), H.render_final(p, s, False{}, entrega), micro_saida_sem_macros(InicioComProva{}, m),
          conclusao_sem_inicio(N.concluir(p, s), False{}, entrega)))
    case H.FalhaAntes{+fase, +etapa, +id, +fatal, +entrega}:
      concatenar_ausencia(InicioComProva{}, H.render_fase(m, fase), H.render_falha(s, etapa, id, fatal, entrega),
        fase_anterior_sem_macros(InicioComProva{}, m, fase), falha_sem_inicio(s, etapa, id, fatal, entrega))
    case H.FatalAposPublicacao{+r, +ctx, +exec, +p, +etapa, +id}:
      concatenar_ausencia(InicioComProva{}, H.render_execucao(m, r, ctx, exec), Q.concatenar(H.micro_saida(m), H.render_fatal_publicada(N.concluir(p, s), etapa, id)),
        execucao_host_sem_macros(InicioComProva{}, m, r, ctx, exec),
        concatenar_ausencia(InicioComProva{}, H.micro_saida(m), H.render_fatal_publicada(N.concluir(p, s), etapa, id), micro_saida_sem_macros(InicioComProva{}, m),
          fatal_publicada_sem_inicio(N.concluir(p, s), etapa, id)))
    case H.Pendente{fase}: fase_anterior_sem_macros(InicioComProva{}, m, fase)
    case H.InicialPendente{aceita}:
      match aceita:
        case True{}:
          F.absurdo_booleano({ausente(InicioComProva{}, H.render(m, s, H.InicialPendente{True{}})) == True{} : Bool},
            Equal.sym(Bool, True{}, False{}, atendimento))
        case False{}: {==}

law atendimento_sem_inicio_com_prova:
  for ~c: S.Configuracao
  for +recepcao: X.Recepcao
  for +estado: List<&2, U32>
  for +s: D.Estado
  for +dados: H.DadosFerramentas
  for +m: H.Micro
  {ausente(InicioComProva{}, H.gerar(c, recepcao, estado, s, dados, m)) == True{} : Bool}
def atendimento_sem_inicio_com_prova(c, recepcao, estado, s, dados, m):
  caso_sem_inicio(m, s, H.decidir(c, recepcao, estado, dados), H.atendimento_nao_inicia(c, recepcao, estado, dados))

# Progresso da inicializacao: o ponto e gerado, nao postulado por Processavel.
law inicializacao_codificada_tem_instancia:
  for ~c: S.Configuracao
  for +id: String
  for +s: D.Estado
  for +m: H.Micro
  for +bs: List<&2, U32>
  for configurada: {Config.valida(c, id) == True{} : Bool}
  for codificada: {Protocolo.codificar(D.estado_valor(s)) == Some{bs} : Maybe<&2, List<&2, U32>>}
  exs t: Nat
  {Q.consultar(H.gerar_inicial(c, id, s, H.Aceitou{}, m), t) == Some{Q.Iniciada{s}} : Maybe<&2, Q.Quadro>}
def inicializacao_codificada_tem_instancia(c, id, s, m, bs, configurada, codificada):
  (2n+Nat.add(Q.tamanho(H.micro_saida(m)), 2n),
    Equal.trans(Maybe<&2, Q.Quadro>,
      Q.consultar(H.gerar_inicial(c, id, s, H.Aceitou{}, m), 2n+Nat.add(Q.tamanho(H.micro_saida(m)), 2n)),
      Q.consultar(H.render(m, s, H.InicialOk{}), 2n+Nat.add(Q.tamanho(H.micro_saida(m)), 2n)), Some{Q.Iniciada{s}},
      Equal.cong(Bool, Maybe<&2, Q.Quadro>, ok => Q.consultar(H.render(m, s, H.decidir_inicial_casos(ok, H.Aceitou{})),
        2n+Nat.add(Q.tamanho(H.micro_saida(m)), 2n)), Config.valida(c, id), True{}, configurada),
      Equal.trans(Maybe<&2, Q.Quadro>,
        Q.consultar(Q.concatenar(H.micro_saida(m), H.render_inicial(Protocolo.codificar(D.estado_valor(s)), s)), Nat.add(Q.tamanho(H.micro_saida(m)), 2n)),
        Q.consultar(H.render_inicial(Protocolo.codificar(D.estado_valor(s)), s), 2n), Some{Q.Iniciada{s}},
        Q.consultar_apos_prefixo(H.micro_saida(m), H.render_inicial(Protocolo.codificar(D.estado_valor(s)), s), 2n),
        Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, Q.Quadro>, resultado => Q.consultar(H.render_inicial(resultado, s), 2n),
          Protocolo.codificar(D.estado_valor(s)), Some{bs}, codificada))))

def iniciar_seed_codificado(~c: S.Configuracao, +id: String, +s: D.Estado, +m: H.Micro,
  configurada: {Config.valida(c, id) == True{} : Bool},
  montada: Proposta.Montada(Protocolo.codificar(D.estado_valor(s)), Nil{})) ->
  &t: Nat -> {Q.consultar(H.gerar_inicial(c, id, s, H.Aceitou{}, m), t) == Some{Q.Iniciada{s}} : Maybe<&2, Q.Quadro>}:
  match montada:
    case (bs, pacote, L.Ambos{codificada, resto}): inicializacao_codificada_tem_instancia(c, id, s, m, bs, configurada, codificada)

law seed_valido_tem_instancia_apos_aprovacao:
  for ~c: S.Configuracao
  for +id: String
  for +s: D.Estado
  for +m: H.Micro
  for configurada: {Config.valida(c, id) == True{} : Bool}
  for valido: R.Valido(c, s)
  exs t: Nat
  {Q.consultar(H.gerar_inicial(c, id, s, H.Aceitou{}, m), t) == Some{Q.Iniciada{s}} : Maybe<&2, Q.Quadro>}
def seed_valido_tem_instancia_apos_aprovacao(c, id, s, m, configurada, valido):
  F.com_par((&t: Nat -> {Q.consultar(H.gerar_inicial(c, id, s, H.Aceitou{}, m), t) == Some{Q.Iniciada{s}} : Maybe<&2, Q.Quadro>}),
    {Config.valida(c, id) == True{} : Bool}, {Config.valida(c, id) == True{} : Bool},
    Chamada.duplicar_igualdade(Bool, Config.valida(c, id), True{}, configurada),
    oficial => inicia =>
      iniciar_seed_codificado(c, id, s, m, inicia,
        Proposta.sucesso_valido_tem_proposta_real(c, s, D.VAusente{}, Nil{},
          L.e_esquerda({R.configuracao_valida(c) == True{} : Bool}, {S.ambiente(c) == id : String},
            Configuracao.aceita_exige_estrutura_e_identidade_exatas(c, id, oficial)), valido)))

# Somente o ramo de configuracao valida e juizo Aceitou emite esses marcos.
def verdadeiro_se_falso_impossivel(b: Bool, impossivel: {b == False{} : Bool} -> Empty) -> {b == True{} : Bool}:
  match b:
    case False{}: L.ex_falso({False{} == True{} : Bool}, impossivel({==}))
    case True{}: {==}

def consulta_de_inicio_exige_marca(+m: H.Micro, +s: D.Estado, +caso: H.Caso, +t: Nat, +q: Q.Quadro,
  tipo: {desse_tipo(InicioComProva{}, q) == True{} : Bool},
  consulta: {Q.consultar(H.render(m, s, caso), t) == Some{q} : Maybe<&2, Q.Quadro>}) -> {H.inicia(caso) == True{} : Bool}:
  verdadeiro_se_falso_impossivel(H.inicia(caso), nao =>
    ausente_exclui_consulta(InicioComProva{}, H.render(m, s, caso), t, q, caso_sem_inicio(m, s, caso, nao), tipo, consulta))

def marca_inicial_exige_valida(resultado: H.ResultadoInicial, +valida: Bool,
  marca: {H.inicia(H.decidir_aceitou_inicial(resultado, valida)) == True{} : Bool}) -> {valida == True{} : Bool}:
  match resultado:
    case H.Finalizada{}:
      match valida:
        case False{}: F.absurdo_booleano({False{} == True{} : Bool}, marca)
        case True{}: {==}
    case H.FalhouInicial{aceita, etapa, id, fatal}: F.e_booleano_direita(aceita, valida, marca)
    case H.PendenteInicial{aceita}: F.e_booleano_direita(aceita, valida, marca)

def marca_inicial_exige_juizo(+valida: Bool, +juizo: H.Juizo, +resultado: H.ResultadoInicial,
  marca: {H.inicia(H.decidir_juizo_inicial(juizo, resultado, valida)) == True{} : Bool}) ->
  L.E<{valida == True{} : Bool}, {juizo == H.Aceitou{} : H.Juizo}>:
  match juizo:
    case H.Aceitou{}: L.Ambos{marca_inicial_exige_valida(resultado, valida, marca), {==}}
    case H.Recusou{}: F.absurdo_booleano(L.E<{valida == True{} : Bool}, {H.Recusou{} == H.Aceitou{} : H.Juizo}>, marca)
    case H.ErroJuizo{id, fatal}: F.absurdo_booleano(L.E<{valida == True{} : Bool}, {H.ErroJuizo{id, fatal} == H.Aceitou{} : H.Juizo}>, marca)
    case H.PendenteJuizo{}: F.absurdo_booleano(L.E<{valida == True{} : Bool}, {H.PendenteJuizo{} == H.Aceitou{} : H.Juizo}>, marca)

def inicio_resultado_exige_configuracao_e_juizo_aceitos(+m: H.Micro, +s: D.Estado,
  +valida: Bool, +juizo: H.Juizo, +resultado: H.ResultadoInicial, +t: Nat, +q: Q.Quadro,
  tipo: {desse_tipo(InicioComProva{}, q) == True{} : Bool},
  consulta: {Q.consultar(H.render(m, s, H.decidir_juizo_inicial(juizo, resultado, valida)), t) == Some{q} : Maybe<&2, Q.Quadro>}) ->
  L.E<{valida == True{} : Bool}, {juizo == H.Aceitou{} : H.Juizo}>:
  marca_inicial_exige_juizo(valida, juizo, resultado,
    consulta_de_inicio_exige_marca(m, s, H.decidir_juizo_inicial(juizo, resultado, valida), t, q, tipo, consulta))

law inicio_exige_configuracao_e_juizo_aceitos:
  for +m: H.Micro
  for +s: D.Estado
  for valida: Bool
  for +juizo: H.Juizo
  for +t: Nat
  for +q: Q.Quadro
  for tipo: {desse_tipo(InicioComProva{}, q) == True{} : Bool}
  for consulta: {Q.consultar(H.render(m, s, H.decidir_inicial_casos(valida, juizo)), t) == Some{q} : Maybe<&2, Q.Quadro>}
  L.E<{valida == True{} : Bool}, {juizo == H.Aceitou{} : H.Juizo}>
def inicio_exige_configuracao_e_juizo_aceitos(m, s, valida, juizo, t, q, tipo, consulta):
  inicio_resultado_exige_configuracao_e_juizo_aceitos(m, s, valida, juizo, H.Finalizada{}, t, q, tipo, consulta)

def inicial_aceita_antes_da_parte(+m: H.Micro, +s: D.Estado, -t: Nat, -w: D.Estado,
  parte: &u: Nat -> L.E<{t == 2n+u : Nat},
    {Q.consultar(Q.concatenar(H.micro_saida(m), H.render_inicial(Protocolo.codificar(D.estado_valor(s)), s)), u) == Some{Q.Iniciada{w}} : Maybe<&2, Q.Quadro>}>) ->
  &a: Nat -> L.E<{Nat.is_lt(a, t) == True{} : Bool},
    {Q.consultar(H.render(m, s, H.InicialOk{}), a) == Some{Q.InicialAceita{}} : Maybe<&2, Q.Quadro>}>:
  match parte:
    case (u, L.Ambos{pos, consulta}):
      (1n, L.Ambos{(%Equal.sym(Nat, t, 2n+u, pos) : {Nat.is_lt(1n, _) == True{} : Bool} {==}), {==}})

law instancia_so_comeca_apos_prova_inicial:
  for +m: H.Micro
  for +s: D.Estado
  for +t: Nat
  for +w: D.Estado
  for consulta: {Q.consultar(H.render(m, s, H.InicialOk{}), t) == Some{Q.Iniciada{w}} : Maybe<&2, Q.Quadro>}
  exs a: Nat
  L.E<{Nat.is_lt(a, t) == True{} : Bool},
    {Q.consultar(H.render(m, s, H.InicialOk{}), a) == Some{Q.InicialAceita{}} : Maybe<&2, Q.Quadro>}>
def instancia_so_comeca_apos_prova_inicial(m, s, t, w, consulta):
  inicial_aceita_antes_da_parte(m, s, t, w,
    localizar_no_sufixo(Inicializacao{}, [Q.Configurada{}, Q.InicialAceita{}],
      Q.concatenar(H.micro_saida(m), H.render_inicial(Protocolo.codificar(D.estado_valor(s)), s)), t, Q.Iniciada{w}, {==}, {==}, consulta))

def excluir_origem_sem_store(+xs: List<&2, Q.Quadro>, +t: Nat, +w: D.Estado,
  sem_publicar: {ausente(Publicacao{}, xs) == True{} : Bool},
  sem_iniciar: {ausente(Inicializacao{}, xs) == True{} : Bool}, origem: OrigemGeral(xs, t, None{}, w)) -> Empty:
  match origem:
    case L.Esquerda{L.Ambos{igual, nenhuma}}: F.nenhum_nao_algum(D.Estado, w, igual)
    case L.Direita{L.Esquerda{(u, L.Ambos{ordem, consulta})}}:
      ausente_exclui_consulta(Publicacao{}, xs, u, Q.Publicada{w}, sem_publicar, {==}, consulta)
    case L.Direita{L.Direita{(u, L.Ambos{ordem, consulta})}}:
      ausente_exclui_consulta(Inicializacao{}, xs, u, Q.Iniciada{w}, sem_iniciar, {==}, consulta)

def sem_store_nao_ha_estado(+xs: List<&2, Q.Quadro>, +t: Nat, +w: D.Estado,
  sem_publicar: {ausente(Publicacao{}, xs) == True{} : Bool},
  sem_iniciar: {ausente(Inicializacao{}, xs) == True{} : Bool},
  visto: {Q.estado_em(xs, t, None{}) == Some{w} : Maybe<&2, D.Estado>}) -> Empty:
  excluir_origem_sem_store(xs, t, w, sem_publicar, sem_iniciar, origem_geral_do_estado_visivel(t, xs, None{}, w, visto))

def prefixo_inicial_sem_store(+m: H.Micro, aceita: Bool) ->
  L.E<{ausente(Publicacao{}, H.prefixo_inicial(m, aceita)) == True{} : Bool},
    {ausente(Inicializacao{}, H.prefixo_inicial(m, aceita)) == True{} : Bool}>:
  match aceita:
    case False{}: L.Ambos{{==}, {==}}
    case True{}: L.Ambos{micro_saida_sem_macros(Publicacao{}, m), micro_saida_sem_macros(Inicializacao{}, m)}

# Um worker inicial que falha ou fica pendente nunca instala a instancia.
def falha_inicial_sem_instancia(+m: H.Micro, +s: D.Estado, +aceita: Bool, +etapa: X.Etapa, +id: String, +fatal: Bool) ->
  {ausente(Inicializacao{}, H.render(m, s, H.InicialFalha{aceita, etapa, id, fatal})) == True{} : Bool}:
  concatenar_ausencia(Inicializacao{}, H.prefixo_inicial(m, aceita),
    [Q.Falhou{etapa, id, fatal}, Q.InicialRecusada{S.Falha{}}],
    L.e_direita({ausente(Publicacao{}, H.prefixo_inicial(m, aceita)) == True{} : Bool},
      {ausente(Inicializacao{}, H.prefixo_inicial(m, aceita)) == True{} : Bool}, prefixo_inicial_sem_store(m, aceita)), {==})

def pendencia_inicial_sem_instancia(+m: H.Micro, +s: D.Estado, +aceita: Bool) ->
  {ausente(Inicializacao{}, H.render(m, s, H.InicialPendente{aceita})) == True{} : Bool}:
  L.e_direita({ausente(Publicacao{}, H.prefixo_inicial(m, aceita)) == True{} : Bool},
    {ausente(Inicializacao{}, H.prefixo_inicial(m, aceita)) == True{} : Bool}, prefixo_inicial_sem_store(m, aceita))

def prefixo_inicial_nao_tem_estado(+m: H.Micro, +aceita: Bool, +resto: List<&2, Q.Quadro>, +t: Nat, +w: D.Estado,
  sem_pub: {ausente(Publicacao{}, resto) == True{} : Bool}, sem_inicio: {ausente(Inicializacao{}, resto) == True{} : Bool},
  visto: {Q.estado_em(Con{Q.Configurada{}, Q.concatenar(H.prefixo_inicial(m, aceita), resto)}, t, None{}) == Some{w} : Maybe<&2, D.Estado>}) -> Empty:
  F.com_par(Empty, {ausente(Publicacao{}, H.prefixo_inicial(m, aceita)) == True{} : Bool},
    {ausente(Inicializacao{}, H.prefixo_inicial(m, aceita)) == True{} : Bool}, prefixo_inicial_sem_store(m, aceita),
    publicacao => inicio => sem_store_nao_ha_estado(Con{Q.Configurada{}, Q.concatenar(H.prefixo_inicial(m, aceita), resto)}, t, w,
      concatenar_ausencia(Publicacao{}, H.prefixo_inicial(m, aceita), resto, publicacao, sem_pub),
      concatenar_ausencia(Inicializacao{}, H.prefixo_inicial(m, aceita), resto, inicio, sem_inicio), visto))

def prefixo_inicial_direto_nao_tem_estado(+m: H.Micro, +aceita: Bool, +t: Nat, +w: D.Estado,
  visto: {Q.estado_em(Con{Q.Configurada{}, H.prefixo_inicial(m, aceita)}, t, None{}) == Some{w} : Maybe<&2, D.Estado>}) -> Empty:
  F.com_par(Empty, {ausente(Publicacao{}, H.prefixo_inicial(m, aceita)) == True{} : Bool},
    {ausente(Inicializacao{}, H.prefixo_inicial(m, aceita)) == True{} : Bool}, prefixo_inicial_sem_store(m, aceita),
    publicacao => inicio => sem_store_nao_ha_estado(Con{Q.Configurada{}, H.prefixo_inicial(m, aceita)}, t, w, publicacao, inicio, visto))

def origem_do_resultado_inicial_casos(+m: H.Micro, +s: D.Estado, +juizo: H.Juizo, +resultado: H.ResultadoInicial, +valida: Bool, +t: Nat, +w: D.Estado,
  visto: {Q.estado_em(H.render(m, s, H.decidir_juizo_inicial(juizo, resultado, valida)), t, None{}) == Some{w} : Maybe<&2, D.Estado>}) ->
  Origem(H.render(m, s, H.decidir_juizo_inicial(juizo, resultado, valida)), t, s, w):
  match juizo:
    case H.Aceitou{}:
      match resultado:
        case H.Finalizada{}:
          match valida:
            case False{}: L.ex_falso(Origem(H.render(m, s, H.InicialRecusa{S.Dados{}}), t, s, w), sem_store_nao_ha_estado([Q.Configurada{}, Q.InicialRecusada{S.Dados{}}], t, w, {==}, {==}, visto))
            case True{}: origem_do_estado_inicializado(t, m, s, w, visto)
        case H.FalhouInicial{+aceita, +etapa, +id, +fatal}:
          L.ex_falso(Origem(H.render(m, s, H.InicialFalha{aceita && valida, etapa, id, fatal}), t, s, w),
            prefixo_inicial_nao_tem_estado(m, aceita && valida, [Q.Falhou{etapa, id, fatal}, Q.InicialRecusada{S.Falha{}}], t, w, {==}, {==}, visto))
        case H.PendenteInicial{+aceita}:
          L.ex_falso(Origem(H.render(m, s, H.InicialPendente{aceita && valida}), t, s, w), prefixo_inicial_direto_nao_tem_estado(m, aceita && valida, t, w, visto))
    case H.Recusou{}: L.ex_falso(Origem(H.render(m, s, H.InicialRecusa{S.Certificado{}}), t, s, w), sem_store_nao_ha_estado([Q.Configurada{}, Q.InicialRecusada{S.Certificado{}}], t, w, {==}, {==}, visto))
    case H.ErroJuizo{+id, +fatal}:
      L.ex_falso(Origem(H.render(m, s, H.InicialFalha{False{}, X.Verificar{}, id, fatal}), t, s, w), sem_store_nao_ha_estado([Q.Configurada{}, Q.Falhou{X.Verificar{}, id, fatal}, Q.InicialRecusada{S.Falha{}}], t, w, {==}, {==}, visto))
    case H.PendenteJuizo{}: L.ex_falso(Origem(H.render(m, s, H.InicialPendente{False{}}), t, s, w), sem_store_nao_ha_estado([Q.Configurada{}], t, w, {==}, {==}, visto))

def origem_do_estado_inicial_casos(+m: H.Micro, +s: D.Estado, +valida: Bool, +juizo: H.Juizo, +t: Nat, +w: D.Estado,
  visto: {Q.estado_em(H.render(m, s, H.decidir_inicial_casos(valida, juizo)), t, None{}) == Some{w} : Maybe<&2, D.Estado>}) ->
  Origem(H.render(m, s, H.decidir_inicial_casos(valida, juizo)), t, s, w):
  origem_do_resultado_inicial_casos(m, s, juizo, H.Finalizada{}, valida, t, w, visto)


def DoCodigo(r: S.Resposta) -> Type:
  match r:
    case S.Resposta{S.Sucesso{}, v}: Unit
    case S.Resposta{S.Recusa{}, v}: Unit
    case S.Resposta{S.Dados{}, v}: Unit
    case _: Empty

def MaquinaDoCodigo(m: N.Maquina) -> Type:
  match m:
    case N.EmCurso{w, a, ts}: Unit
    case N.Parada{w, ts, r}: DoCodigo(r)

def PercursoDoCodigo(p: S.Percurso) -> Type:
  match p:
    case S.Prefixo{w, ts}: Unit
    case S.Final{w, ts, r}: DoCodigo(r)

def operacao_nao_fabrica_status(+n: Nat, r: D.ResultadoOp, w: D.Estado,
  o: D.Operacao, k: S.Retorno -> S.Acao, ts: List<&2, S.Evento>, +e: D.Esquema,
  inducao: @m: N.Maquina -> MaquinaDoCodigo(m) -> PercursoDoCodigo(N.percorrer(n, m, e))) ->
  PercursoDoCodigo(N.percorrer(n, N.passo_maquina(S.aplicar(r, w, o, k), ts), e)):
  match r:
    case D.FalhaDados{}:
      inducao(N.Parada{w, S.acrescentar(ts, S.Evento{o, S.ErroDeDados{}}), S.resposta_erro(S.Dados{})}, Unit{})
    case D.Observado{+v}:
      inducao(N.EmCurso{w, k(S.Dado{v}), S.acrescentar(ts, S.Evento{o, S.Leitura{v}})}, Unit{})
    case D.Alterado{s}:
      inducao(N.EmCurso{s, k(S.Unidade{}), S.acrescentar(ts, S.Evento{o, S.Escrita{}})}, Unit{})

law percurso_nao_fabrica_status_do_host:
  for n: Nat
  for m: N.Maquina
  for +e: D.Esquema
  for h: MaquinaDoCodigo(m)
  PercursoDoCodigo(N.percorrer(n, m, e))

def percurso_nao_fabrica_status_do_host(n, m, e, h):
  match n m:
    case 0n N.EmCurso{w, a, ts}: Unit{}
    case 0n N.Parada{w, ts, r}: h
    case 1n+ +j N.EmCurso{+w, a, ts}:
      match a:
        case S.Terminar{v}:
          percurso_nao_fabrica_status_do_host(j, N.Parada{w, ts, S.Resposta{S.Sucesso{}, v}}, e, Unit{})
        case S.Recusar{v}:
          percurso_nao_fabrica_status_do_host(j, N.Parada{w, ts, S.Resposta{S.Recusa{}, v}}, e, Unit{})
        case S.Acessar{+o, k}: operacao_nao_fabrica_status(j, D.operar(e, w, o), w, o, k, ts, e, proxima => permitido => percurso_nao_fabrica_status_do_host(j, proxima, e, permitido))
    case 1n+j N.Parada{w, ts, r}:
      percurso_nao_fabrica_status_do_host(j, N.Parada{w, ts, r}, e, h)

def DoFinal(r: S.Resposta) -> Type:
  match r:
    case S.Resposta{S.Sucesso{}, v}: Unit
    case S.Resposta{S.Recusa{}, v}: Unit
    case S.Resposta{S.Dados{}, v}: Unit
    case S.Resposta{S.Limite{}, v}: Unit
    case _: Empty

def resposta_tecnica_so_dados_ou_limite(ok: Bool, cabe: Bool, -r: S.Resposta, h: DoFinal(r)) ->
  DoFinal(R.resposta_tecnica_casos(ok, cabe, r)):
  match ok cabe:
    case False{} _: Unit{}
    case True{} False{}: Unit{}
    case True{} True{}: h

def estado_tecnico_so_dados_ou_limite(ok: Bool, cabe: Bool, -r: S.Resposta, h: DoFinal(r)) ->
  DoFinal(R.estado_tecnico_casos(ok, cabe, r)):
  match ok cabe:
    case False{} _: Unit{}
    case True{} False{}: Unit{}
    case True{} True{}: h

law finalizar_so_acrescenta_dados_ou_limite:
  for proposta: S.Resposta
  for c: S.Configuracao
  for +w: D.Estado
  for h: DoCodigo(proposta)
  DoFinal(R.finalizar(proposta, c, w))
def finalizar_so_acrescenta_dados_ou_limite(proposta, c, w, h):
  match proposta c:
    case S.Resposta{S.Sucesso{}, +v} S.Configuracao{+e, leis, +lim, amb}:
      estado_tecnico_so_dados_ou_limite(D.estrutura(e, w), R.cabe(R.limite_estado(lim), D.estado_valor(w)),
        R.resposta_tecnica_casos(D.valor_valido(v), R.cabe(R.limite_resposta(lim), S.resposta_valor(S.Resposta{S.Sucesso{}, v})), S.Resposta{S.Sucesso{}, v}),
        resposta_tecnica_so_dados_ou_limite(D.valor_valido(v), R.cabe(R.limite_resposta(lim), S.resposta_valor(S.Resposta{S.Sucesso{}, v})), S.Resposta{S.Sucesso{}, v}, Unit{}))
    case S.Resposta{S.Recusa{}, +v} S.Configuracao{e, leis, +lim, amb}:
      resposta_tecnica_so_dados_ou_limite(D.valor_valido(v), R.cabe(R.limite_resposta(lim), S.resposta_valor(S.Resposta{S.Recusa{}, v})), S.Resposta{S.Recusa{}, v}, Unit{})
    case S.Resposta{S.Dados{}, v} S.Configuracao{e, leis, lim, amb}: Unit{}
    case S.Resposta{S.Entrada{}, v} _: match h:
    case S.Resposta{S.Autenticacao{}, v} _: match h:
    case S.Resposta{S.Certificado{}, v} _: match h:
    case S.Resposta{S.Limite{}, v} _: match h:
    case S.Resposta{S.Falha{}, v} _: match h:

def negar_inicio_implica_negar_instancia(q: Q.Quadro, h: {Bool.not(desse_tipo(InicioComProva{}, q)) == True{} : Bool}) ->
  {Bool.not(desse_tipo(Inicializacao{}, q)) == True{} : Bool}:
  match q:
    case Q.Configurada{}: {==}
    case Q.InicialAceita{}: {==}
    case Q.Iniciada{s}: h
    case Q.InicialRecusada{s}: {==}
    case Q.Codificada{v, bs}: {==}
    case Q.Decodificada{bs, v}: {==}
    case Q.Guardada{s, bs, a}: {==}
    case Q.Conferida{pos, n}: {==}
    case Q.Construida{pos, n}: {==}
    case Q.Lida{a, n, d}: {==}
    case Q.Recebida{r}: {==}
    case Q.Autenticada{r, ctx}: {==}
    case Q.Aceita{r, ctx}: {==}
    case Q.Rejeitada{r, ctx}: {==}
    case Q.Comecada{r, ctx}: {==}
    case Q.Avaliada{r, ctx, p}: {==}
    case Q.Operada{e, s, o, r}: {==}
    case Q.Preparada{r, bs}: {==}
    case Q.Publicada{s}: {==}
    case Q.Visivel{s}: {==}
    case Q.Falhou{etapa, id, fatal}: {==}
    case Q.Concluida{r, s, f}: {==}
    case Q.Entregue{bs}: {==}
    case Q.Interrompida{bs}: {==}
    case Q.Fechada{}: {==}
    case Q.Seguinte{a, b}: {==}
    case Q.Inspecao{d}: {==}
    case Q.Efeito{d}: {==}

def sem_inicio_inclui_sem_instancia(+xs: List<&2, Q.Quadro>, h: {ausente(InicioComProva{}, xs) == True{} : Bool}) ->
  {ausente(Inicializacao{}, xs) == True{} : Bool}:
  match xs:
    case Nil{}: {==}
    case Con{+q, +t}:
      F.com_par({ausente(Inicializacao{}, Con{q, t}) == True{} : Bool},
        {Bool.not(desse_tipo(InicioComProva{}, q)) == True{} : Bool}, {ausente(InicioComProva{}, t) == True{} : Bool},
        F.e_booleano_separar(Bool.not(desse_tipo(InicioComProva{}, q)), ausente(InicioComProva{}, t), h),
        cabeca => cauda => F.e_booleano_intro(Bool.not(desse_tipo(Inicializacao{}, q)), ausente(Inicializacao{}, t),
          negar_inicio_implica_negar_instancia(q, cabeca), sem_inicio_inclui_sem_instancia(t, cauda)))

law atendimento_sem_inicio:
  for ~c: S.Configuracao
  for +recepcao: X.Recepcao
  for +estado: List<&2, U32>
  for +s: D.Estado
  for +dados: H.DadosFerramentas
  for +m: H.Micro
  {ausente(Inicializacao{}, H.gerar(c, recepcao, estado, s, dados, m)) == True{} : Bool}
def atendimento_sem_inicio(c, recepcao, estado, s, dados, m):
  sem_inicio_inclui_sem_instancia(H.gerar(c, recepcao, estado, s, dados, m), atendimento_sem_inicio_com_prova(c, recepcao, estado, s, dados, m))

# Inversao da conclusao no traco completo e a Regra6 correspondente.
def conclusao_localizada(+antes: List<&2, Q.Quadro>, +estado: D.Estado, +resposta: S.Resposta,
  +bytes: List<&2, U32>, +entrega: H.Entrega, -t: Nat, +q: Q.Quadro,
  alvo: {desse_tipo(Conclusao{}, q) == True{} : Bool},
  parte: &u: Nat -> L.E<{t == Nat.add(Q.tamanho(antes), u) : Nat},
    {Q.consultar(H.render_conclusao(N.Conclusao{estado, resposta, bytes}, False{}, entrega), u) == Some{q} : Maybe<&2, Q.Quadro>}>) ->
  L.E<{t == Nat.add(Q.tamanho(antes), Q.tamanho(Con{Q.Preparada{resposta, bytes}, H.render_publicacao(resposta, estado)})) : Nat},
    {q == Q.Concluida{resposta, estado, False{}} : Q.Quadro}>:
  match parte:
    case (u, L.Ambos{pos, consulta}):
      F.com_par(
        L.E<{t == Nat.add(Q.tamanho(antes), Q.tamanho(Con{Q.Preparada{resposta, bytes}, H.render_publicacao(resposta, estado)})) : Nat},
          {q == Q.Concluida{resposta, estado, False{}} : Q.Quadro}>,
        {u == Q.tamanho(Con{Q.Preparada{resposta, bytes}, H.render_publicacao(resposta, estado)}) : Nat},
        {q == Q.Concluida{resposta, estado, False{}} : Q.Quadro},
        conclusao_no_fim_e_unica(estado, resposta, bytes, False{}, entrega, u, q, alvo, consulta),
        local => quadro => L.Ambos{Equal.trans(Nat, t, Nat.add(Q.tamanho(antes), u),
          Nat.add(Q.tamanho(antes), Q.tamanho(Con{Q.Preparada{resposta, bytes}, H.render_publicacao(resposta, estado)})), pos,
          Equal.cong(Nat, Nat, i => Nat.add(Q.tamanho(antes), i), u,
            Q.tamanho(Con{Q.Preparada{resposta, bytes}, H.render_publicacao(resposta, estado)}), local)), quadro})

def conclusao_unica_apos_prefixo(+antes: List<&2, Q.Quadro>, +s: D.Estado, +p: N.Preparada,
  +entrega: H.Entrega, +t: Nat, +q: Q.Quadro,
  sem: {ausente(Conclusao{}, antes) == True{} : Bool},
  alvo: {desse_tipo(Conclusao{}, q) == True{} : Bool},
  consulta: {Q.consultar(Q.concatenar(antes, H.render_final(p, s, False{}, entrega)), t) == Some{q} : Maybe<&2, Q.Quadro>}) ->
  L.E<{t == indice_conclusao(antes, p, s) : Nat},
    {q == Q.Concluida{U.resposta(p), U.publicado(N.concluir(p, s)), False{}} : Q.Quadro}>:
  match p:
    case N.Preparada{+w, ts, +r, +bs}:
      F.com_par(
        L.E<{t == indice_conclusao(antes, N.Preparada{w, ts, r, bs}, s) : Nat},
          {q == Q.Concluida{r, S.publica(r, s, w), False{}} : Q.Quadro}>,
        {desse_tipo(Conclusao{}, q) == True{} : Bool}, {desse_tipo(Conclusao{}, q) == True{} : Bool},
        Chamada.duplicar_igualdade(Bool, desse_tipo(Conclusao{}, q), True{}, alvo),
        local => prefixo => conclusao_localizada(antes, S.publica(r, s, w), r, bs, entrega, t, q, local,
          localizar_no_sufixo(Conclusao{}, antes, H.render_final(N.Preparada{w, ts, r, bs}, s, False{}, entrega), t, q, sem, prefixo, consulta)))

def Regra6Conclusao(-a: I.Ambiente, -k: String, -x: I.Cenario, -t: Nat, q: Q.Quadro) -> Type:
  match q:
    case Q.Concluida{r, s, fecha}: K.Regra6(I.Concluiu{r, s, fecha}, a, k, x, t)
    case _: Unit

def conclusao_regra6_de_igualdades(-a: I.Ambiente, -k: String, -x: I.Cenario,
  +s: D.Estado, +antes: List<&2, Q.Quadro>, +p: N.Preparada, -t: Nat, +q: Q.Quadro,
  igual: L.E<{t == indice_conclusao(antes, p, s) : Nat},
    {q == Q.Concluida{U.resposta(p), U.publicado(N.concluir(p, s)), False{}} : Q.Quadro}>,
  atomica: K.ConclusaoAtomica(U.resposta(p), a, k, x, indice_conclusao(antes, p, s), U.publicado(N.concluir(p, s)))) ->
  Regra6Conclusao(a, k, x, t, q):
  match igual:
    case L.Ambos{pos, quadro}:
      %Equal.sym(Nat, t, indice_conclusao(antes, p, s), pos) : Regra6Conclusao(a, k, x, _, q)
      %Equal.sym(Q.Quadro, q, Q.Concluida{U.resposta(p), U.publicado(N.concluir(p, s)), False{}}, quadro) : Regra6Conclusao(a, k, x, indice_conclusao(antes, p, s), _)
      atomica

law conclusao_refletida_obedece_regra6:
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for +s: D.Estado
  for inicial: {s == I.inicial(x) : D.Estado}
  for +antes: List<&2, Q.Quadro>
  for +p: N.Preparada
  for +entrega: H.Entrega
  for +t: Nat
  for +r: S.Resposta
  for +publicado: D.Estado
  for +fecha: Bool
  for sem_publicar: {ausente(Publicacao{}, antes) == True{} : Bool}
  for sem_concluir: {ausente(Conclusao{}, antes) == True{} : Bool}
  for consulta: {Q.consultar(Q.concatenar(antes, H.render_final(p, s, False{}, entrega)), t) == Some{Q.Concluida{r, publicado, fecha}} : Maybe<&2, Q.Quadro>}
  for introduzir: @u: Nat -> @w: D.Estado ->
    {Q.consultar(Q.concatenar(antes, H.render_final(p, s, False{}, entrega)), u) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>} -> I.Acontece(a, k, x, u, I.Publicou{w})
  for extrair: @u: Nat -> @w: D.Estado -> I.Acontece(a, k, x, u, I.Publicou{w}) ->
    {Q.consultar(Q.concatenar(antes, H.render_final(p, s, False{}, entrega)), u) == Some{Q.Publicada{w}} : Maybe<&2, Q.Quadro>}
  K.Regra6(I.Concluiu{r, publicado, fecha}, a, k, x, t)
def conclusao_refletida_obedece_regra6(a, k, x, s, inicial, antes, p, entrega, t, r, publicado, fecha,
  sem_publicar, sem_concluir, consulta, introduzir, extrair):
  conclusao_regra6_de_igualdades(a, k, x, s, antes, p, t, Q.Concluida{r, publicado, fecha},
    conclusao_unica_apos_prefixo(antes, s, p, entrega, t, Q.Concluida{r, publicado, fecha}, sem_concluir, {==}, consulta),
    conclusao_atomica_real(a, k, x, s, inicial, antes, p, entrega, sem_publicar, introduzir, extrair))

law resposta_de_programa_justifica_o_status_real:
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for -t: Nat
  for +r: S.Resposta
  for +w: D.Estado
  for status: DoFinal(r)
  for programa: I.RespostaDoPrograma(a, k, x, t, r, w)
  I.RespostaJustificada(r, a, k, x, t)
def resposta_de_programa_justifica_o_status_real(a, k, x, t, r, w, status, programa):
  match r:
    case S.Resposta{S.Sucesso{}, v}: (w, programa)
    case S.Resposta{S.Recusa{}, v}: (w, programa)
    case S.Resposta{S.Dados{}, v}: (w, programa)
    case S.Resposta{S.Limite{}, v}: L.Direita{(w, programa)}
    case S.Resposta{S.Entrada{}, v}: match status:
    case S.Resposta{S.Autenticacao{}, v}: match status:
    case S.Resposta{S.Certificado{}, v}: match status:
    case S.Resposta{S.Falha{}, v}: match status:
