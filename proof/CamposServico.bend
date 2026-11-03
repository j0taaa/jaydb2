# Testemunhas de conferencia antes dos campos gerados pelo Codec real.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../src/Estado.bend as E
import ./CodecRecusas.bend as R
import ../src/Codec.bend as C
import ../contrato/Bytes.bend as B
import ./PrimitivasServico.bend as M
import ./RotasServico.bend as Rota
import ../contrato/Semantica.bend as S
import ../contrato/Recursos.bend as X
import ../src/Nucleo.bend as N
import ./ProtocoloServico.bend as Q
import ../contrato/Logica.bend as L
import ./Fundamentos.bend as F

# Cada campo gerado possui a conferencia imediatamente anterior.
def AntesDoCampo(-qs: List<&2, Q.Quadro>, -t: Nat, -p: Nat, -n: Nat) -> Type:
  &b: Nat -> L.E<{Nat.is_lt(b, t) == True{} : Bool},
    {Q.consultar(qs, b) == Some{Q.Conferida{p, n}} : Maybe<&2, Q.Quadro>}>

def eh_campo(q: Q.Quadro) -> Bool:
  match q:
    case Q.Construida{p, n}: True{}
    case _: False{}

def conferencia_de(q: Q.Quadro) -> Q.Quadro:
  match q:
    case Q.Construida{p, n}: Q.Conferida{p, n}
    case _: Q.Conferida{0n, 0n}

def deslocar_campo(-h: Q.Quadro, -qs: List<&2, Q.Quadro>, -t: Nat,
  -p: Nat, -n: Nat, antes: AntesDoCampo(qs, t, p, n)) ->
  AntesDoCampo(Con{h, qs}, Succ{t}, p, n):
  match antes:
    case (b, L.Ambos{ordem, conferida}): (Succ{b}, L.Ambos{ordem, conferida})

def atravessar_cabeca(+h: Q.Quadro, +qs: List<&2, Q.Quadro>, t: Nat, -p: Nat, -n: Nat,
  nao: {eh_campo(h) == False{} : Bool},
  obtida: {Q.consultar(Con{h, qs}, t) == Some{Q.Construida{p, n}} : Maybe<&2, Q.Quadro>},
  cauda: @u: Nat -> {Q.consultar(qs, u) == Some{Q.Construida{p, n}} : Maybe<&2, Q.Quadro>} -> AntesDoCampo(qs, u, p, n)) ->
  AntesDoCampo(Con{h, qs}, t, p, n):
  match t:
    case 0n:
      F.absurdo_booleano(AntesDoCampo(Con{h, qs}, 0n, p, n),
        Equal.trans(Bool, False{}, eh_campo(h), True{},
          Equal.sym(Bool, eh_campo(h), False{}, nao),
          Equal.cong(Q.Quadro, Bool, eh_campo, h, Q.Construida{p, n},
            F.algum_injetivo(Q.Quadro, h, Q.Construida{p, n}, obtida))))
    case 1n+u: deslocar_campo(h, qs, u, p, n, cauda(u, obtida))

def atravessar_par(+p0: Nat, +n0: Nat, +qs: List<&2, Q.Quadro>, t: Nat, -p: Nat, -n: Nat,
  obtida: {Q.consultar(Con{Q.Conferida{p0, n0}, Con{Q.Construida{p0, n0}, qs}}, t) == Some{Q.Construida{p, n}} : Maybe<&2, Q.Quadro>},
  cauda: @u: Nat -> {Q.consultar(qs, u) == Some{Q.Construida{p, n}} : Maybe<&2, Q.Quadro>} -> AntesDoCampo(qs, u, p, n)) ->
  AntesDoCampo(Con{Q.Conferida{p0, n0}, Con{Q.Construida{p0, n0}, qs}}, t, p, n):
  match t:
    case 0n:
      F.absurdo_booleano(AntesDoCampo(Con{Q.Conferida{p0, n0}, Con{Q.Construida{p0, n0}, qs}}, 0n, p, n),
        Equal.cong(Q.Quadro, Bool, eh_campo, Q.Conferida{p0, n0}, Q.Construida{p, n},
          F.algum_injetivo(Q.Quadro, Q.Conferida{p0, n0}, Q.Construida{p, n}, obtida)))
    case 1n+u:
      match u:
        case 0n:
          (0n, L.Ambos{{==}, Equal.cong(Q.Quadro, Maybe<&2, Q.Quadro>, q => Some{conferencia_de(q)},
            Q.Construida{p0, n0}, Q.Construida{p, n}, F.algum_injetivo(Q.Quadro,
              Q.Construida{p0, n0}, Q.Construida{p, n}, obtida))})
        case 1n+v:
          deslocar_campo(Q.Conferida{p0, n0}, Con{Q.Construida{p0, n0}, qs}, Succ{v}, p, n,
            deslocar_campo(Q.Construida{p0, n0}, qs, v, p, n, cauda(v, obtida)))

# A concatenacao preserva a testemunha anterior, inclusive entre fases.
def CamposSeguros(-qs: List<&2, Q.Quadro>) -> Type:
  @t: Nat -> @p: Nat -> @n: Nat ->
    {Q.consultar(qs, t) == Some{Q.Construida{p, n}} : Maybe<&2, Q.Quadro>} -> AntesDoCampo(qs, t, p, n)

def campo_na_esquerda(+xs: List<&2, Q.Quadro>, -ys: List<&2, Q.Quadro>, -t: Nat,
  -p: Nat, -n: Nat, antes: AntesDoCampo(xs, t, p, n)) -> AntesDoCampo(Q.concatenar(xs, ys), t, p, n):
  match antes:
    case (+b, L.Ambos{ordem, consulta}):
      (b, L.Ambos{ordem, Q.consulta_prefixo(xs, ys, b, Q.Conferida{p, n}, consulta)})

def campo_na_direita(+xs: List<&2, Q.Quadro>, -ys: List<&2, Q.Quadro>, -t: Nat,
  -p: Nat, -n: Nat, antes: AntesDoCampo(ys, t, p, n)) ->
  AntesDoCampo(Q.concatenar(xs, ys), Nat.add(Q.tamanho(xs), t), p, n):
  match antes:
    case (b, L.Ambos{ordem, consulta}):
      (Nat.add(Q.tamanho(xs), b), L.Ambos{Q.ordem_deslocada(Q.tamanho(xs), b, t, ordem),
        Equal.trans(Maybe<&2, Q.Quadro>, Q.consultar(Q.concatenar(xs, ys), Nat.add(Q.tamanho(xs), b)),
          Q.consultar(ys, b), Some{Q.Conferida{p, n}}, Q.consultar_apos_prefixo(xs, ys, b), consulta)})

def campo_da_parte(+xs: List<&2, Q.Quadro>, +ys: List<&2, Q.Quadro>, +t: Nat,
  +p: Nat, +n: Nat, a: CamposSeguros(xs), b: CamposSeguros(ys),
  parte: Q.Parte(xs, ys, t, Q.Construida{p, n})) -> AntesDoCampo(Q.concatenar(xs, ys), t, p, n):
  match parte:
    case L.Esquerda{(i, L.Ambos{pos, consulta})}:
      %Equal.sym(Nat, t, i, pos) : AntesDoCampo(Q.concatenar(xs, ys), _, p, n)
      campo_na_esquerda(xs, ys, i, p, n, a(i, p, n, consulta))
    case L.Direita{(i, L.Ambos{pos, consulta})}:
      %Equal.sym(Nat, t, Nat.add(Q.tamanho(xs), i), pos) : AntesDoCampo(Q.concatenar(xs, ys), _, p, n)
      campo_na_direita(xs, ys, i, p, n, b(i, p, n, consulta))

law concatenar_campos_seguros:
  for +xs: List<&2, Q.Quadro>
  for +ys: List<&2, Q.Quadro>
  for a: CamposSeguros(xs)
  for b: CamposSeguros(ys)
  CamposSeguros(Q.concatenar(xs, ys))
def concatenar_campos_seguros(xs, ys, a, b):
  +t => +p => +n => consulta =>
    campo_da_parte(xs, ys, t, p, n, a, b, Q.dividir_consulta(xs, ys, t, Q.Construida{p, n}, consulta))

def campos_vazios(t: Nat, -p: Nat, -n: Nat,
  consulta: {Q.consultar(Nil{}, t) == Some{Q.Construida{p, n}} : Maybe<&2, Q.Quadro>}) ->
  AntesDoCampo(Nil{}, t, p, n):
  match t:
    case 0n: L.ex_falso(AntesDoCampo(Nil{}, 0n, p, n), F.nenhum_nao_algum(Q.Quadro, Q.Construida{p, n}, consulta))
    case 1n+k: L.ex_falso(AntesDoCampo(Nil{}, 1n+k, p, n), F.nenhum_nao_algum(Q.Quadro, Q.Construida{p, n}, consulta))

def vazio_seguro() -> CamposSeguros(Nil{}):
  t => p => n => consulta => campos_vazios(t, p, n, consulta)

def sem_campo(+h: Q.Quadro, nao: {eh_campo(h) == False{} : Bool}) -> CamposSeguros([h]):
  t => p => n => consulta => atravessar_cabeca(h, Nil{}, t, p, n, nao, consulta,
    u => obtida => campos_vazios(u, p, n, obtida))

def construir_campos(c: C.Conferencia, +pos: Nat, +q: Nat) -> CamposSeguros(M.construir(c, pos, q)):
  match c:
    case C.Cabe{}: t => p => n => consulta => atravessar_par(pos, q, Nil{}, t, p, n, consulta,
      u => obtida => campos_vazios(u, p, n, obtida))
    case C.Curto{}: vazio_seguro()
    case C.Grande{}: vazio_seguro()

def abertura_campos(c: C.Conferencia, pronto: Bool, +pos: Nat, +q: Nat) ->
  CamposSeguros(M.abrir_campo(c, pronto, pos, q)):
  match c pronto:
    case C.Cabe{} True{}: construir_campos(C.Cabe{}, pos, q)
    case C.Cabe{} False{}: sem_campo(Q.Conferida{pos, q}, {==})
    case C.Curto{} _: vazio_seguro()
    case C.Grande{} _: vazio_seguro()

def quadro_campo_seguro(+pos: Nat, +f: C.Finalidade, +alto: U32, +baixo: U32,
  +pilha: C.Pilha, +corpo: B.Numero64, +teto: B.Numero64) ->
  CamposSeguros(M.quadro_campo(pos, f, alto, baixo, pilha, corpo, teto)):
  abertura_campos(M.conferencia(f, alto, baixo, pilha, corpo, teto),
    M.abrir_nome_valido(f, alto, baixo), pos, M.quantidade(alto, baixo))

def tag_campos(tag: Nat, +pos: Nat) -> CamposSeguros(M.quadro_tag(tag, pos)):
  match tag:
    case 0n: construir_campos(C.Cabe{}, pos, 1n)
    case 1n: construir_campos(C.Cabe{}, pos, 1n)
    case 2n: construir_campos(C.Cabe{}, pos, 1n)
    case 3n+k: vazio_seguro()

def palavra_campos(f: C.Finalidade, +alto: U32, +baixo: U32, +pilha: C.Pilha,
  +corpo: B.Numero64, +teto: B.Numero64, +pos: Nat) ->
  CamposSeguros(M.quadro_palavra(f, alto, baixo, pilha, corpo, teto, pos)):
  match f:
    case C.Inteiro{}: construir_campos(C.Cabe{}, pos, 8n)
    case C.Texto{}: quadro_campo_seguro(pos, C.Texto{}, alto, baixo, pilha, corpo, teto)
    case C.NomeTexto{}: quadro_campo_seguro(pos, C.NomeTexto{}, alto, baixo, pilha, corpo, teto)
    case C.ContaLista{}: quadro_campo_seguro(pos, C.ContaLista{}, alto, baixo, pilha, corpo, teto)
    case C.ContaRegistro{}: quadro_campo_seguro(pos, C.ContaRegistro{}, alto, baixo, pilha, corpo, teto)

def passo_campos(m: C.Maquina, +b: U32, +corpo: B.Numero64, +teto: B.Numero64, +pos: Nat) ->
  CamposSeguros(M.quadro_passo(m, b, corpo, teto, pos)):
  match m:
    case C.Tag{pilha}: tag_campos(U32.to_nat(b), pos)
    case C.Palavra{f, 0n, alto, +baixo, pilha}:
      palavra_campos(f, (alto * 256 + U32.shrn(baixo, 24n) : U32), (baixo * 256 + b : U32), pilha, corpo, teto, pos)
    case C.Palavra{f, 1n+k, alto, baixo, pilha}: vazio_seguro()
    case C.TagNome{pilha}: vazio_seguro()
    case C.Conteudo{nome, ultimo, q, u, texto, pilha}: vazio_seguro()
    case C.Pronto{v}: vazio_seguro()
    case C.Invalido{}: vazio_seguro()
    case C.Acima{}: vazio_seguro()

law codec_confere_antes_de_construir:
  for bs: List<&2, U32>
  for +m: C.Maquina
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +pos: Nat
  CamposSeguros(M.quadros_codec(bs, m, corpo, teto, pos))
def codec_confere_antes_de_construir(bs, m, corpo, teto, pos):
  match bs:
    case Nil{}: vazio_seguro()
    case Con{+b, +resto}:
      concatenar_campos_seguros(M.quadro_passo(m, b, C.diminuir64(corpo), C.diminuir64(teto), pos),
        M.quadros_codec(resto, C.passo(m, b, C.diminuir64(corpo), C.diminuir64(teto)), C.diminuir64(corpo), C.diminuir64(teto), Succ{pos}),
        passo_campos(m, b, C.diminuir64(corpo), C.diminuir64(teto), pos),
        codec_confere_antes_de_construir(resto, C.passo(m, b, C.diminuir64(corpo), C.diminuir64(teto)), C.diminuir64(corpo), C.diminuir64(teto), Succ{pos}))

def admitida_campos(ok: Bool, +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64) ->
  CamposSeguros(M.decodificacao_admitida(ok, bs, corpo, teto)):
  match ok:
    case False{}: vazio_seguro()
    case True{}:
      concatenar_campos_seguros(M.quadros_codec(bs, C.Tag{C.Raiz{}}, corpo, teto, 0n),
        [Q.Decodificada{bs, R.opcional(C.decodificar(bs, teto))}],
        codec_confere_antes_de_construir(bs, C.Tag{C.Raiz{}}, corpo, teto, 0n),
        sem_campo(Q.Decodificada{bs, R.opcional(C.decodificar(bs, teto))}, {==}))

def medida_campos(q: Maybe<&2, B.Numero64>, +bs: List<&2, U32>, +teto: B.Numero64) ->
  CamposSeguros(M.decodificacao_medida(q, bs, teto)):
  match q:
    case None{}: vazio_seguro()
    case Some{+corpo}: admitida_campos(C.menor_igual64(corpo, teto) && B.octetos_validos(bs), bs, corpo, teto)

def abstracao_campos(q: Maybe<&2, D.Estado>, +s: D.Estado, +bs: List<&2, U32>) ->
  CamposSeguros(M.guardar_abstracao(q, s, bs)):
  match q:
    case None{}: vazio_seguro()
    case Some{a}: sem_campo(Q.Guardada{s, bs, a}, {==})

def armazenamento_campos(q: Maybe<&2, List<&2, U32>>, +e: D.Esquema, +s: D.Estado) ->
  CamposSeguros(M.guardar_bytes(q, e, s)):
  match q:
    case None{}: vazio_seguro()
    case Some{bs}: abstracao_campos(E.decodificar(D.estado_valor(s), e), s, bs)

def conferencia_no_prefixo(+corte: Nat, +qs: List<&2, Q.Quadro>, +t: Nat,
  -p: Nat, -n: Nat, dentro: {Nat.is_lt(t, corte) == True{} : Bool}, antes: AntesDoCampo(qs, t, p, n)) ->
  AntesDoCampo(Q.primeiros(corte, qs), t, p, n):
  match antes:
    case (+b, L.Ambos{+ordem, consulta}):
      (b, L.Ambos{ordem, Equal.trans(Maybe<&2, Q.Quadro>, Q.consultar(Q.primeiros(corte, qs), b), Q.consultar(qs, b), Some{Q.Conferida{p, n}},
        Q.consulta_antes_do_corte_e_conservada(corte, qs, b, Q.menor_transitivo(b, t, corte, ordem, dentro)), consulta)})

law primeiros_conservam_campos_seguros:
  for +corte: Nat
  for +qs: List<&2, Q.Quadro>
  for seguros: CamposSeguros(qs)
  CamposSeguros(Q.primeiros(corte, qs))
def primeiros_conservam_campos_seguros(corte, qs, seguros):
  +t => +p => +n => +consulta =>
    conferencia_no_prefixo(corte, qs, t, p, n,
      Q.consulta_no_prefixo_respeita_corte(corte, qs, t, Q.Construida{p, n}, consulta),
      seguros(t, p, n, Q.consulta_no_prefixo_e_real(corte, qs, t, Q.Construida{p, n}, consulta)))

law primitiva_confere_antes_de_construir:
  for q: M.Primitiva
  CamposSeguros(M.expandir(q))
def primitiva_confere_antes_de_construir(q):
  match q:
    case M.Prefixo{+n, +p}: primeiros_conservam_campos_seguros(n, M.expandir(p), primitiva_confere_antes_de_construir(p))
    case M.Codificar{+v}: sem_campo(Q.Codificada{v, P.codificar(v)}, {==})
    case M.Decodificar{+bs, +teto}: medida_campos(B.nat64(B.comprimento(bs)), bs, teto)
    case M.Guardar{e, +s}: armazenamento_campos(P.codificar(D.estado_valor(s)), e, s)
    case M.Ler{a, cap, b, d}: sem_campo(Q.Lida{a, b, d}, {==})

law primitivas_conferem_antes_de_construir:
  for xs: List<&2, M.Primitiva>
  CamposSeguros(M.expandir_primitivas(xs))
def primitivas_conferem_antes_de_construir(xs):
  match xs:
    case Nil{}: vazio_seguro()
    case Con{+h, +t}:
      concatenar_campos_seguros(M.expandir(h), M.expandir_primitivas(t),
        primitiva_confere_antes_de_construir(h), primitivas_conferem_antes_de_construir(t))

# Os quadros das outras fases nao constroem campos do protocolo.
def SemCampos(xs: List<&2, Q.Quadro>) -> Type:
  match xs:
    case Nil{}: Unit
    case Con{h, t}: L.E<{eh_campo(h) == False{} : Bool}, SemCampos(t)>

def lista_sem_campos(xs: List<&2, Q.Quadro>, provas: SemCampos(xs)) -> CamposSeguros(xs):
  match xs provas:
    case Nil{} _: vazio_seguro()
    case Con{+h, +t} L.Ambos{cabeca, cauda}:
      concatenar_campos_seguros([h], t, sem_campo(h, cabeca), lista_sem_campos(t, cauda))

def execucao_sem_campos(+r: P.Requisicao, +ctx: D.Contexto, xs: List<&2, Q.QuadroExec>) ->
  SemCampos(Q.expandir_exec(r, ctx, xs)):
  match xs:
    case Nil{}: Unit{}
    case Con{Q.Avaliacao{percurso}, t}: L.Ambos{{==}, execucao_sem_campos(r, ctx, t)}
    case Con{Q.Operacao{e, s, o, resultado}, t}: L.Ambos{{==}, execucao_sem_campos(r, ctx, t)}

def micro_entrada(m: Rota.Micro) -> CamposSeguros(Rota.micro_entrada(m)):
  match m:
    case Rota.Micro{a, b, c, d}: primitivas_conferem_antes_de_construir(a)
def micro_autenticacao(m: Rota.Micro) -> CamposSeguros(Rota.micro_autenticacao(m)):
  match m:
    case Rota.Micro{a, b, c, d}: primitivas_conferem_antes_de_construir(b)
def micro_execucao(m: Rota.Micro) -> CamposSeguros(Rota.micro_execucao(m)):
  match m:
    case Rota.Micro{a, b, c, d}: primitivas_conferem_antes_de_construir(c)
def micro_saida(m: Rota.Micro) -> CamposSeguros(Rota.micro_saida(m)):
  match m:
    case Rota.Micro{a, b, c, d}: primitivas_conferem_antes_de_construir(d)

def recebida_campos(+m: Rota.Micro, +r: P.Requisicao) -> CamposSeguros(Rota.render_recebida(m, r)):
  concatenar_campos_seguros(Rota.micro_entrada(m), [Q.Recebida{r}], micro_entrada(m), sem_campo(Q.Recebida{r}, {==}))

def autenticada_campos(+m: Rota.Micro, +r: P.Requisicao, +ctx: D.Contexto) -> CamposSeguros(Rota.render_autenticada(m, r, ctx)):
  concatenar_campos_seguros(Rota.render_recebida(m, r), Q.concatenar(Rota.micro_autenticacao(m), [Q.Autenticada{r, Some{ctx}}]),
    recebida_campos(m, r), concatenar_campos_seguros(Rota.micro_autenticacao(m), [Q.Autenticada{r, Some{ctx}}],
      micro_autenticacao(m), sem_campo(Q.Autenticada{r, Some{ctx}}, {==})))

def verificada_campos(+m: Rota.Micro, +r: P.Requisicao, +ctx: D.Contexto) -> CamposSeguros(Rota.render_verificada(m, r, ctx)):
  concatenar_campos_seguros(Rota.render_autenticada(m, r, ctx), [Q.Aceita{r, ctx}],
    autenticada_campos(m, r, ctx), sem_campo(Q.Aceita{r, ctx}, {==}))

def comecada_campos(+m: Rota.Micro, +r: P.Requisicao, +ctx: D.Contexto) -> CamposSeguros(Rota.render_comecada(m, r, ctx)):
  concatenar_campos_seguros(Rota.render_verificada(m, r, ctx), Q.concatenar(Rota.micro_execucao(m), [Q.Comecada{r, ctx}]),
    verificada_campos(m, r, ctx), concatenar_campos_seguros(Rota.micro_execucao(m), [Q.Comecada{r, ctx}],
      micro_execucao(m), sem_campo(Q.Comecada{r, ctx}, {==})))

def execucao_campos(+m: Rota.Micro, +r: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>) ->
  CamposSeguros(Rota.render_execucao(m, r, ctx, xs)):
  concatenar_campos_seguros(Rota.render_comecada(m, r, ctx), Q.expandir_exec(r, ctx, xs),
    comecada_campos(m, r, ctx), lista_sem_campos(Q.expandir_exec(r, ctx, xs), execucao_sem_campos(r, ctx, xs)))

def concatenar_sem_campos(xs: List<&2, Q.Quadro>, -ys: List<&2, Q.Quadro>, a: SemCampos(xs), b: SemCampos(ys)) ->
  SemCampos(Q.concatenar(xs, ys)):
  match xs a:
    case Nil{} _: b
    case Con{h, t} L.Ambos{cabeca, cauda}: L.Ambos{cabeca, concatenar_sem_campos(t, ys, cauda, b)}

def depois_entrega_sem_campos(fecha: Bool, -s: D.Estado, proxima: Bool) ->
  SemCampos(Rota.depois_entrega(fecha, s, proxima)):
  match fecha proxima:
    case True{} _: L.Ambos{{==}, Unit{}}
    case False{} True{}: L.Ambos{{==}, Unit{}}
    case False{} False{}: Unit{}

def entrega_sem_campos(+s: D.Estado, +bs: List<&2, U32>, +fecha: Bool, entrega: Rota.Entrega) ->
  SemCampos(Rota.render_entrega(s, bs, fecha, entrega)):
  match entrega:
    case Rota.Completa{proxima}: L.Ambos{{==}, depois_entrega_sem_campos(fecha, s, proxima)}
    case Rota.Quebrada{prefixo}: L.Ambos{{==}, L.Ambos{{==}, Unit{}}}
    case Rota.PendenteEntrega{}: Unit{}

def publicacao_sem_campos(r: S.Resposta, -s: D.Estado) -> SemCampos(Rota.render_publicacao(r, s)):
  match r:
    case S.Resposta{S.Sucesso{}, v}: L.Ambos{{==}, Unit{}}
    case S.Resposta{S.Recusa{}, v}: Unit{}
    case S.Resposta{S.Entrada{}, v}: Unit{}
    case S.Resposta{S.Autenticacao{}, v}: Unit{}
    case S.Resposta{S.Certificado{}, v}: Unit{}
    case S.Resposta{S.Dados{}, v}: Unit{}
    case S.Resposta{S.Limite{}, v}: Unit{}
    case S.Resposta{S.Falha{}, v}: Unit{}

def conclusao_sem_campos(conclusao: N.Conclusao, +fecha: Bool, entrega: Rota.Entrega) ->
  SemCampos(Rota.render_conclusao(conclusao, fecha, entrega)):
  match conclusao:
    case N.Conclusao{+s, +r, +bs}:
      L.Ambos{{==}, concatenar_sem_campos(Rota.render_publicacao(r, s),
        Con{Q.Concluida{r, s, fecha}, Rota.render_entrega(s, bs, fecha, entrega)},
        publicacao_sem_campos(r, s), L.Ambos{{==}, entrega_sem_campos(s, bs, fecha, entrega)})}

def erro_enquadrado_sem_campos(q: Maybe<&2, List<&2, U32>>, +r: S.Resposta,
  +s: D.Estado, +fecha: Bool, entrega: Rota.Entrega) ->
  SemCampos(Rota.render_erro_enquadrado(q, r, s, fecha, entrega)):
  match q:
    case None{}: Unit{}
    case Some{+bs}:
      L.Ambos{{==}, L.Ambos{{==}, entrega_sem_campos(s, bs, fecha, entrega)}}

def erro_sem_campos(+status: S.Status, +s: D.Estado, +fecha: Bool, entrega: Rota.Entrega) ->
  SemCampos(Rota.render_erro(status, s, fecha, entrega)):
  erro_enquadrado_sem_campos(P.enquadrar(S.resposta_valor(S.resposta_erro(status))), S.resposta_erro(status), s, fecha, entrega)

def quadro_preparado_sem_campo(p: N.Preparada) -> CamposSeguros([Rota.quadro_preparada(p)]):
  match p:
    case N.Preparada{w, ts, +r, +bs}: sem_campo(Q.Preparada{r, bs}, {==})

def fase_campos(+m: Rota.Micro, fase: Rota.FaseAntes) -> CamposSeguros(Rota.render_fase(m, fase)):
  match fase:
    case Rota.AntesEntrada{}: micro_entrada(m)
    case Rota.AposReceber{r}: recebida_campos(m, r)
    case Rota.AposAutenticar{r, ctx}: autenticada_campos(m, r, ctx)
    case Rota.AposVerificar{r, ctx}: verificada_campos(m, r, ctx)
    case Rota.Executando{r, ctx, xs}: execucao_campos(m, r, ctx, xs)
    case Rota.AposPreparar{+r, +ctx, +xs, +p}:
      concatenar_campos_seguros(Rota.render_execucao(m, r, ctx, xs), Q.concatenar(Rota.micro_saida(m), [Rota.quadro_preparada(p)]),
        execucao_campos(m, r, ctx, xs), concatenar_campos_seguros(Rota.micro_saida(m), [Rota.quadro_preparada(p)],
          micro_saida(m), quadro_preparado_sem_campo(p)))


def inicial_sem_campos(q: Maybe<&2, List<&2, U32>>, -s: D.Estado) -> SemCampos(Rota.render_inicial(q, s)):
  match q:
    case None{}: L.Ambos{{==}, Unit{}}
    case Some{bs}: L.Ambos{{==}, L.Ambos{{==}, L.Ambos{{==}, Unit{}}}}

def falha_fim_sem_campos(+s: D.Estado, fatal: Bool, entrega: Rota.Entrega) -> SemCampos(Rota.render_falha_fim(s, fatal, entrega)):
  match fatal:
    case True{}: L.Ambos{{==}, Unit{}}
    case False{}: erro_sem_campos(S.Falha{}, s, False{}, entrega)

def falha_sem_campos(+s: D.Estado, etapa: X.Etapa, id: String, +fatal: Bool, entrega: Rota.Entrega) ->
  SemCampos(Rota.render_falha(s, etapa, id, fatal, entrega)):
  L.Ambos{{==}, falha_fim_sem_campos(s, fatal, entrega)}

def fatal_publicada_sem_campos(c: N.Conclusao, etapa: X.Etapa, id: String) ->
  SemCampos(Rota.render_fatal_publicada(c, etapa, id)):
  match c:
    case N.Conclusao{+s, +r, bs}:
      L.Ambos{{==}, concatenar_sem_campos(Rota.render_publicacao(r, s), [Q.Falhou{etapa, id, True{}}, Q.Fechada{}],
        publicacao_sem_campos(r, s), L.Ambos{{==}, L.Ambos{{==}, Unit{}}})}

def prefixo_inicial_campos(+m: Rota.Micro, aceita: Bool) -> CamposSeguros(Rota.prefixo_inicial(m, aceita)):
  match aceita:
    case True{}: concatenar_campos_seguros([Q.InicialAceita{}], Rota.micro_saida(m), sem_campo(Q.InicialAceita{}, {==}), micro_saida(m))
    case False{}: vazio_seguro()

law todas_fases_conferem_campos_antes_de_construir:
  for +m: Rota.Micro
  for +s: D.Estado
  for caso: Rota.Caso
  CamposSeguros(Rota.render_caso(m, s, caso))
def todas_fases_conferem_campos_antes_de_construir(m, s, caso):
  match caso:
    case Rota.InicialOk{}:
      concatenar_campos_seguros([Q.InicialAceita{}], Q.concatenar(Rota.micro_saida(m), Rota.render_inicial(P.codificar(D.estado_valor(s)), s)),
        sem_campo(Q.InicialAceita{}, {==}), concatenar_campos_seguros(Rota.micro_saida(m), Rota.render_inicial(P.codificar(D.estado_valor(s)), s),
          micro_saida(m), lista_sem_campos(Rota.render_inicial(P.codificar(D.estado_valor(s)), s), inicial_sem_campos(P.codificar(D.estado_valor(s)), s))))
    case Rota.InicialRecusa{+status}: sem_campo(Q.InicialRecusada{status}, {==})
    case Rota.InicialFalha{+aceita, +etapa, +id, +fatal}:
      concatenar_campos_seguros(Rota.prefixo_inicial(m, aceita), [Q.Falhou{etapa, id, fatal}, Q.InicialRecusada{S.Falha{}}],
        prefixo_inicial_campos(m, aceita), lista_sem_campos([Q.Falhou{etapa, id, fatal}, Q.InicialRecusada{S.Falha{}}], L.Ambos{{==}, L.Ambos{{==}, Unit{}}}))
    case Rota.SemResposta{}: sem_campo(Q.Fechada{}, {==})
    case Rota.EntradaRecusa{+erro, +fecha, +entrega}:
      concatenar_campos_seguros(Rota.micro_entrada(m), Rota.render_erro(Rota.status_entrada(erro), s, fecha, entrega),
        micro_entrada(m), lista_sem_campos(Rota.render_erro(Rota.status_entrada(erro), s, fecha, entrega), erro_sem_campos(Rota.status_entrada(erro), s, fecha, entrega)))
    case Rota.AutRecusa{+r, +entrega}:
      concatenar_campos_seguros(Rota.render_recebida(m, r), Q.concatenar(Rota.micro_autenticacao(m), Con{Q.Autenticada{r, None{}}, Rota.render_erro(S.Autenticacao{}, s, False{}, entrega)}),
        recebida_campos(m, r), concatenar_campos_seguros(Rota.micro_autenticacao(m), Con{Q.Autenticada{r, None{}}, Rota.render_erro(S.Autenticacao{}, s, False{}, entrega)},
          micro_autenticacao(m), lista_sem_campos(Con{Q.Autenticada{r, None{}}, Rota.render_erro(S.Autenticacao{}, s, False{}, entrega)},
            L.Ambos{{==}, erro_sem_campos(S.Autenticacao{}, s, False{}, entrega)})))
    case Rota.GateRecusa{+r, +ctx, +entrega}:
      concatenar_campos_seguros(Rota.render_autenticada(m, r, ctx), Con{Q.Rejeitada{r, ctx}, Rota.render_erro(S.Certificado{}, s, False{}, entrega)},
        autenticada_campos(m, r, ctx), lista_sem_campos(Con{Q.Rejeitada{r, ctx}, Rota.render_erro(S.Certificado{}, s, False{}, entrega)},
          L.Ambos{{==}, erro_sem_campos(S.Certificado{}, s, False{}, entrega)}))
    case Rota.Executada{+r, +ctx, +xs, +p, +entrega}:
      concatenar_campos_seguros(Rota.render_execucao(m, r, ctx, xs), Q.concatenar(Rota.micro_saida(m), Rota.render_final(p, s, False{}, entrega)),
        execucao_campos(m, r, ctx, xs), concatenar_campos_seguros(Rota.micro_saida(m), Rota.render_final(p, s, False{}, entrega),
          micro_saida(m), lista_sem_campos(Rota.render_final(p, s, False{}, entrega), conclusao_sem_campos(N.concluir(p, s), False{}, entrega))))
    case Rota.FalhaAntes{+fase, +etapa, +id, +fatal, +entrega}:
      concatenar_campos_seguros(Rota.render_fase(m, fase), Rota.render_falha(s, etapa, id, fatal, entrega),
        fase_campos(m, fase), lista_sem_campos(Rota.render_falha(s, etapa, id, fatal, entrega), falha_sem_campos(s, etapa, id, fatal, entrega)))
    case Rota.FatalAposPublicacao{+r, +ctx, +xs, +p, +etapa, +id}:
      concatenar_campos_seguros(Rota.render_execucao(m, r, ctx, xs), Q.concatenar(Rota.micro_saida(m), Rota.render_fatal_publicada(N.concluir(p, s), etapa, id)),
        execucao_campos(m, r, ctx, xs), concatenar_campos_seguros(Rota.micro_saida(m), Rota.render_fatal_publicada(N.concluir(p, s), etapa, id),
          micro_saida(m), lista_sem_campos(Rota.render_fatal_publicada(N.concluir(p, s), etapa, id), fatal_publicada_sem_campos(N.concluir(p, s), etapa, id))))
    case Rota.Pendente{fase}: fase_campos(m, fase)
    case Rota.InicialPendente{aceita}: prefixo_inicial_campos(m, aceita)

law protocolo_confere_campos_antes_de_construir:
  for +m: Rota.Micro
  for +s: D.Estado
  for +caso: Rota.Caso
  CamposSeguros(Rota.render(m, s, caso))
def protocolo_confere_campos_antes_de_construir(m, s, caso):
  concatenar_campos_seguros([Q.Configurada{}], Rota.render_caso(m, s, caso),
    sem_campo(Q.Configurada{}, {==}), todas_fases_conferem_campos_antes_de_construir(m, s, caso))
