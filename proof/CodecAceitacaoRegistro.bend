# Segmentacao integral dos campos BRUTOS de um registro realmente aceito.
# Nomes sao extraidos canonicamente; valores guardam apenas o trace local.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecPercurso.bend as R
import ./CodecAridades.bend as A
import ./CodecCanonico.bend as K
import ./CodecLimitesSequencias.bend as S
import ./CodecAceitacaoPalavra.bend as W
import ./CodecAceitacaoPrefixo.bend as X
import ./CodecAceitacaoFilhos.bend as H
import ./CodecAceitacaoLista.bend as I
import ./CodecAceitacaoNome.bend as N

# Nenhuma codificacao canonica de valor e premissa desta testemunha.
def CamposLidos(xs: List<&2, S.CampoSegmentado>, +max: Nat) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{S.CampoSegmentado{nome, valor, nb, vb}, t}:
      L.E<{D.nome_valido(nome) == True{} : Bool},
        L.E<{P.texto(nome) == Some{nb} : Maybe<&2, List<&2, U32>>},
          L.E<H.FilhoLido<valor, vb, max>, CamposLidos(t, max)>>>

type Segmentacao<-bs: List<&2, U32>, -inicio: C.Maquina, -v: D.Valor, -max: Nat> is Type:
  Segmentacao{xs: List<&2, S.CampoSegmentado>,
    bytes: {bs == S.bytes_campos(xs) : List<&2, U32>},
    entrega: {A.entregar_campos(S.campos(xs), inicio) == C.Pronto{v} : C.Maquina},
    campos: CamposLidos(xs, max)}

type EstadoRegistro is Data:
  Lendo{ultimo: Bool, restantes: B.Numero64, anterior: String, invertidos: List<&2, D.Campo>}
  Terminada{valor: D.Valor}

def maquina_registro(e: EstadoRegistro) -> C.Maquina:
  match e:
    case Lendo{u, q, anterior, xs}:
      C.TagNome{C.Nome{u, q, anterior, xs, C.Raiz{}}}
    case Terminada{v}:
      C.Pronto{v}

# A positividade do valor ja torna positivo o prefixo nome+valor.
def prefixo_campo_positivo(nb: List<&2, U32>, +vb: List<&2, U32>,
  positivo: H.BytesPositivos(vb)) -> H.BytesPositivos(B.concatenar(nb, vb)):
  match nb:
    case Nil{}:
      positivo
    case Con{b, t}:
      Unit{}

def sufixo_valido(+bs: List<&2, U32>, +pre: List<&2, U32>, +suf: List<&2, U32>,
  bytes: {bs == B.concatenar(pre, suf) : List<&2, U32>},
  validos: {B.octetos_validos(bs) == True{} : Bool}) ->
  {B.octetos_validos(suf) == True{} : Bool}:
  F.com_par({B.octetos_validos(suf) == True{} : Bool},
    {B.octetos_validos(pre) == True{} : Bool}, {B.octetos_validos(suf) == True{} : Bool},
    W.separar_octetos_validos(pre, suf,
      (%bytes : {B.octetos_validos(_) == True{} : Bool}
        validos)), prefixo_valido => resto_valido => resto_valido)

def nome_extraido_emite_campo(+u: Bool, +q: B.Numero64,
  +anterior: String, +nome: String, +invertidos: List<&2, D.Campo>,
  valido: {D.nome_valido(nome) == True{} : Bool},
  ordem: {String.is_lt(anterior, nome) == True{} : Bool}) ->
  {C.emitir_nome(C.Nome{u, q, anterior, invertidos, C.Raiz{}}, nome) ==
    C.Tag{C.Campo{u, q, nome, invertidos, C.Raiz{}}} : C.Maquina}:
  %Equal.sym(Bool, D.nome_valido(nome) && String.is_lt(anterior, nome), True{},
    F.e_booleano_intro(D.nome_valido(nome), String.is_lt(anterior, nome), valido, ordem)) :
    {C.nome_conferido(_, u, q, nome, invertidos, C.Raiz{}) ==
      C.Tag{C.Campo{u, q, nome, invertidos, C.Raiz{}}} : C.Maquina}
  {==}

def anexar_campo_lido(+bs: List<&2, U32>, +nb: List<&2, U32>, +vb: List<&2, U32>,
  +suf: List<&2, U32>, +u: Bool, +q: B.Numero64, +anterior: String,
  +invertidos: List<&2, D.Campo>, +nome: String, +h: D.Valor, -v: D.Valor, +max: Nat,
  bytes: {bs == B.concatenar(B.concatenar(nb, vb), suf) : List<&2, U32>},
  +valido: {D.nome_valido(nome) == True{} : Bool},
  ordem: {String.is_lt(anterior, nome) == True{} : Bool},
  canonico: {P.texto(nome) == Some{nb} : Maybe<&2, List<&2, U32>>},
  filho: H.FilhoLido<h, vb, max>,
  cauda: Segmentacao<suf, C.emitir(C.Campo{u, q, nome, invertidos, C.Raiz{}}, h), v, max>) ->
  Segmentacao<bs, C.TagNome{C.Nome{u, q, anterior, invertidos, C.Raiz{}}}, v, max>:
  match cauda:
    case Segmentacao{+xs, resto_bytes, entrega, campos}:
      Segmentacao{Con{S.CampoSegmentado{nome, h, nb, vb}, xs},
        Equal.trans(List<&2, U32>, bs, B.concatenar(B.concatenar(nb, vb), suf),
          B.concatenar(B.concatenar(nb, vb), S.bytes_campos(xs)), bytes,
          Equal.cong(List<&2, U32>, List<&2, U32>, t => B.concatenar(B.concatenar(nb, vb), t),
            suf, S.bytes_campos(xs), resto_bytes)),
        Equal.trans(C.Maquina,
          A.entregar_campos(S.campos(xs), A.entregar_campo(
            C.TagNome{C.Nome{u, q, anterior, invertidos, C.Raiz{}}}, D.Campo{nome, h})),
          A.entregar_campos(S.campos(xs), C.emitir(C.Campo{u, q, nome, invertidos, C.Raiz{}}, h)),
          C.Pronto{v}, A.continuar_campos(S.campos(xs), q, anterior, nome, h, invertidos,
            C.Raiz{}, valido, ordem, u), entrega),
        L.Ambos{valido, L.Ambos{canonico, L.Ambos{filho, campos}}}}

# Apenas o booleano real ultimo escolhe entre o proximo Nome e Pronto.
def continuar_apos_campo(ultimo: Bool, +q: B.Numero64, +nome: String, +h: D.Valor,
  +invertidos: List<&2, D.Campo>, +suf: List<&2, U32>, +cf: B.Numero64, +tf: B.Numero64,
  +n: Nat, -v: D.Valor, +max: Nat,
  limite_n: {Nat.is_le(B.comprimento(suf), n) == True{} : Bool},
  limite_max: {Nat.is_le(B.comprimento(suf), max) == True{} : Bool},
  validos: {B.octetos_validos(suf) == True{} : Bool},
  restante: {R.maquina(R.executar(suf,
    R.Quadro{cf, tf, C.emitir(C.Campo{ultimo, q, nome, invertidos, C.Raiz{}}, h)})) == C.Pronto{v} : C.Maquina},
  continuar: @suf: List<&2, U32> -> @cf: B.Numero64 -> @tf: B.Numero64 -> @estado: EstadoRegistro ->
    {Nat.is_le(B.comprimento(suf), n) == True{} : Bool} ->
    {Nat.is_le(B.comprimento(suf), max) == True{} : Bool} ->
    {B.octetos_validos(suf) == True{} : Bool} ->
    {R.maquina(R.executar(suf, R.Quadro{cf, tf, maquina_registro(estado)})) == C.Pronto{v} : C.Maquina} ->
    Segmentacao<suf, maquina_registro(estado), v, max>) ->
  Segmentacao<suf, C.emitir(C.Campo{ultimo, q, nome, invertidos, C.Raiz{}}, h), v, max>:
  match ultimo:
    case True{}:
      continuar(suf, cf, tf, Terminada{C.montar_registro(Con{D.Campo{nome, h}, invertidos}, D.VRegistroVazio{})},
        limite_n, limite_max, validos, restante)
    case False{}:
      continuar(suf, cf, tf, Lendo{C.um64(q), C.diminuir64(q), nome, Con{D.Campo{nome, h}, invertidos}},
        limite_n, limite_max, validos, restante)

def continuar_corte_registro(+n: Nat, +bs: List<&2, U32>, +cn: B.Numero64, +tn: B.Numero64,
  +u: Bool, +q: B.Numero64, +anterior: String, +invertidos: List<&2, D.Campo>,
  +nb: List<&2, U32>, +nome: String, +sufnome: List<&2, U32>, -v: D.Valor, +max: Nat,
  limite_n: {Nat.is_le(B.comprimento(bs), 1n+n) == True{} : Bool},
  limite_max: {Nat.is_le(B.comprimento(bs), max) == True{} : Bool},
  +bytes_nome: {bs == B.concatenar(nb, sufnome) : List<&2, U32>},
  valido: {D.nome_valido(nome) == True{} : Bool},
  ordem: {String.is_lt(anterior, nome) == True{} : Bool},
  canonico: {P.texto(nome) == Some{nb} : Maybe<&2, List<&2, U32>>},
  validos: {B.octetos_validos(sufnome) == True{} : Bool},
  corte: X.Corte<sufnome, cn, tn, C.Tag{C.Raiz{}}, C.Campo{u, q, nome, invertidos, C.Raiz{}}, v>,
  continuar: @suf: List<&2, U32> -> @cf: B.Numero64 -> @tf: B.Numero64 -> @estado: EstadoRegistro ->
    {Nat.is_le(B.comprimento(suf), n) == True{} : Bool} ->
    {Nat.is_le(B.comprimento(suf), max) == True{} : Bool} ->
    {B.octetos_validos(suf) == True{} : Bool} ->
    {R.maquina(R.executar(suf, R.Quadro{cf, tf, maquina_registro(estado)})) == C.Pronto{v} : C.Maquina} ->
    Segmentacao<suf, maquina_registro(estado), v, max>) ->
  Segmentacao<bs, C.TagNome{C.Nome{u, q, anterior, invertidos, C.Raiz{}}}, v, max>:
  match corte:
    case X.Corte{+vb, +suf, +h, +cf, +tf, +bytes_valor, local, real, restante}:
      +fora = {C.Campo{u, q, nome, invertidos, C.Raiz{}} : C.Pilha}
      +pre = B.concatenar(nb, vb)
      +bytes = Equal.trans(List<&2, U32>, bs, B.concatenar(nb, sufnome), B.concatenar(pre, suf), bytes_nome,
        Equal.trans(List<&2, U32>, B.concatenar(nb, sufnome), B.concatenar(nb, B.concatenar(vb, suf)),
          B.concatenar(pre, suf),
          Equal.cong(List<&2, U32>, List<&2, U32>, t => B.concatenar(nb, t),
            sufnome, B.concatenar(vb, suf), bytes_valor),
          Equal.sym(List<&2, U32>, B.concatenar(pre, suf), B.concatenar(nb, B.concatenar(vb, suf)),
            K.concatenacao_associativa(nb, vb, suf))))
      +local_aceito = Equal.cong(R.Quadro, C.Maquina, quadro => R.maquina(quadro),
        X.executar_local(vb, fora, R.Quadro{cn, tn, C.Tag{C.Raiz{}}}), R.Quadro{cf, tf, C.Pronto{h}}, local)
      +corte_max = H.limite_de_bytes_iguais(bs, B.concatenar(pre, suf), max, bytes, limite_max)
      anexar_campo_lido(bs, nb, vb, suf, u, q, anterior, invertidos, nome, h, v, max,
        bytes, valido, ordem, canonico,
        H.FilhoLido{cn, tn, fora, local_aceito,
          H.limite_sufixo(nb, vb, max, H.limite_prefixo(pre, suf, max, corte_max))},
        continuar_apos_campo(u, q, nome, h, invertidos, suf, cf, tf, n, v, max,
          H.sufixo_apos_prefixo_positivo(pre, suf, n,
            prefixo_campo_positivo(nb, vb, H.tag_raiz_local_aceito_tem_bytes(vb, fora, cn, tn, h, local_aceito)),
            H.limite_de_bytes_iguais(bs, B.concatenar(pre, suf), 1n+n, bytes, limite_n)),
          H.limite_sufixo(pre, suf, max, corte_max),
          sufixo_valido(sufnome, vb, suf, bytes_valor, validos), restante, continuar))

def continuar_nome_registro(+n: Nat, +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64,
  +u: Bool, +q: B.Numero64, +anterior: String, +invertidos: List<&2, D.Campo>, -v: D.Valor, +max: Nat,
  limite_n: {Nat.is_le(B.comprimento(bs), 1n+n) == True{} : Bool},
  limite_max: {Nat.is_le(B.comprimento(bs), max) == True{} : Bool},
  extraido: N.NomeExtraido<bs, corpo, teto, C.Nome{u, q, anterior, invertidos, C.Raiz{}}, v>,
  continuar: @suf: List<&2, U32> -> @cf: B.Numero64 -> @tf: B.Numero64 -> @estado: EstadoRegistro ->
    {Nat.is_le(B.comprimento(suf), n) == True{} : Bool} ->
    {Nat.is_le(B.comprimento(suf), max) == True{} : Bool} ->
    {B.octetos_validos(suf) == True{} : Bool} ->
    {R.maquina(R.executar(suf, R.Quadro{cf, tf, maquina_registro(estado)})) == C.Pronto{v} : C.Maquina} ->
    Segmentacao<suf, maquina_registro(estado), v, max>) ->
  Segmentacao<bs, C.TagNome{C.Nome{u, q, anterior, invertidos, C.Raiz{}}}, v, max>:
  match extraido:
    case N.NomeExtraido{+nb, +nome, +sufnome, alto, baixo, utf8, +cn, +tn,
      cabecalho, fatoracao, octetos_nome, resto_valido, positivo, bytes, medida,
      +valido, ordem_nome, canonico, corpo_exato, teto_exato, emissao, execucao, continuacao}:
      +ordem = {ordem_nome : {String.is_lt(anterior, nome) == True{} : Bool}}
      continuar_corte_registro(n, bs, cn, tn, u, q, anterior, invertidos, nb, nome, sufnome, v, max,
        limite_n, limite_max, fatoracao, valido, ordem, canonico, resto_valido,
        X.execucao_real_aceita_extrai_a_primeira_emissao(sufnome, cn, tn, C.Tag{C.Raiz{}},
          C.Campo{u, q, nome, invertidos, C.Raiz{}}, v, Unit{},
          (%nome_extraido_emite_campo(u, q, anterior, nome, invertidos, valido, ordem) :
            {R.maquina(R.executar(sufnome, R.Quadro{cn, tn, _})) == C.Pronto{v} : C.Maquina}
            continuacao)), continuar)

# n majoriza somente os bytes restantes; max nunca muda na recursao.
law extrair_registro_por_combustivel:
  for n: Nat
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +estado: EstadoRegistro
  for -v: D.Valor
  for +max: Nat
  for limite_n: {Nat.is_le(B.comprimento(bs), n) == True{} : Bool}
  for limite_max: {Nat.is_le(B.comprimento(bs), max) == True{} : Bool}
  for validos: {B.octetos_validos(bs) == True{} : Bool}
  for aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, maquina_registro(estado)})) == C.Pronto{v} : C.Maquina}
  Segmentacao<bs, maquina_registro(estado), v, max>
def extrair_registro_por_combustivel(n, bs, corpo, teto, estado, v, max, limite_n, limite_max, validos, aceito):
  match n bs estado:
    case _ Nil{} Lendo{u, q, anterior, xs}:
      L.ex_falso(Segmentacao<Nil{}, maquina_registro(estado), v, max>,
        F.falso_nao_verdadeiro(Equal.cong(C.Maquina, Bool, m => X.e_pronto(m), maquina_registro(estado), C.Pronto{v}, aceito)))
    case _ Nil{} Terminada{w}:
      Segmentacao{Nil{}, {==}, aceito, Unit{}}
    case 0n Con{b, t} _:
      F.absurdo_booleano(Segmentacao<bs, maquina_registro(estado), v, max>, limite_n)
    case 1n+ +menor Con{b, t} Terminada{+w}:
      L.ex_falso(Segmentacao<bs, C.Pronto{w}, v, max>, I.pronto_com_sufixo_impossivel(b, t, corpo, teto, w, v, aceito))
    case 1n+ +menor Con{b, t} Lendo{+u, +q, +anterior, +invertidos}:
      continuar_nome_registro(menor, bs, corpo, teto, u, q, anterior, invertidos, v, max, limite_n, limite_max,
        N.nome_aceito_extrai_prefixo_canonico(bs, corpo, teto, u, q, anterior, invertidos, C.Raiz{}, v, validos, aceito),
        suf => cf => tf => proximo => ln => lm => vs => aceito_resto =>
          extrair_registro_por_combustivel(menor, suf, cf, tf, proximo, v, max, ln, lm, vs, aceito_resto))

def extrair_abertura_registro(vazio: Bool, +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64,
  +q: B.Numero64, -v: D.Valor,
  validos: {B.octetos_validos(bs) == True{} : Bool},
  aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.abrir_variavel(vazio, C.ContaRegistro{}, q, C.Raiz{})})) == C.Pronto{v} : C.Maquina}) ->
  Segmentacao<bs, C.abrir_variavel(vazio, C.ContaRegistro{}, q, C.Raiz{}), v, B.comprimento(bs)>:
  match vazio:
    case True{}:
      extrair_registro_por_combustivel(B.comprimento(bs), bs, corpo, teto, Terminada{D.VRegistroVazio{}}, v, B.comprimento(bs),
        S.limite_reflexivo(B.comprimento(bs)), S.limite_reflexivo(B.comprimento(bs)), validos, aceito)
    case False{}:
      extrair_registro_por_combustivel(B.comprimento(bs), bs, corpo, teto, Lendo{C.um64(q), C.diminuir64(q), "", Nil{}}, v, B.comprimento(bs),
        S.limite_reflexivo(B.comprimento(bs)), S.limite_reflexivo(B.comprimento(bs)), validos, aceito)

law registro_aceito_extrai_todos_os_campos:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +q: B.Numero64
  for -v: D.Valor
  for validos: {B.octetos_validos(bs) == True{} : Bool}
  for aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.abrir_variavel(C.zero64(q), C.ContaRegistro{}, q, C.Raiz{})})) == C.Pronto{v} : C.Maquina}
  Segmentacao<bs, C.abrir_variavel(C.zero64(q), C.ContaRegistro{}, q, C.Raiz{}), v, B.comprimento(bs)>
def registro_aceito_extrai_todos_os_campos(bs, corpo, teto, q, v, validos, aceito):
  extrair_abertura_registro(C.zero64(q), bs, corpo, teto, q, v, validos, aceito)
