# Passo indutivo geral de registros: nomes e valores segmentados executam
# na maquina real, mantendo ordem, contagem e todos os ancestrais.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecPercurso.bend as R
import ./CodecComposicao.bend as X
import ./CodecSequencias.bend as V
import ./CodecCampos.bend as G
import ./CodecContadores.bend as N
import ./CodecPalavrasBE64.bend as H
import ./CodecTextos.bend as T
import ./CodecMinimos.bend as M
import ./CodecMinimosPilha.bend as A
import ./CodecCanonico.bend as K
import ./CodecLimitesSequencias.bend as S
import ./CodecAridades.bend as E

def registro(xs: List<&2, S.CampoSegmentado>) -> D.Valor:
  match xs:
    case Nil{}:
      D.VRegistroVazio{}
    case Con{S.CampoSegmentado{n, v, nb, vb}, t}:
      D.VRegistro{n, v, registro(t)}

def InducaoCampos(xs: List<&2, S.CampoSegmentado>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{S.CampoSegmentado{n, v, nb, vb}, t}:
      L.E<G.NomeCompleto(n, nb), L.E<V.CompletoLocal(v, vb),
        L.E<{Nat.is_le(1n, B.comprimento(vb)) == True{} : Bool},
          L.E<{Nat.is_le(Nat.mul(11n, S.quantidade_campos(t)), B.comprimento(S.bytes_campos(t))) == True{} : Bool}, InducaoCampos(t)>>>>

def NaoVazio(xs: List<&2, S.CampoSegmentado>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case Con{h, t}:
      Unit

def minimo_frame_campo(+u: Bool, +q: B.Numero64, -nome: String, -xs: List<&2, D.Campo>, +pai: C.Pilha,
  +n: Nat, +r: Nat,
  medido: {B.nat64(n) == Some{q} : Maybe<&2, B.Numero64>},
  minimo: {C.minimo_pilha(pai) == B.nat64(r) : Maybe<&2, B.Numero64>}) ->
  {C.minimo_pilha(C.Campo{u, q, nome, xs, pai}) == B.nat64(Nat.add(Nat.mul(11n, n), r)) : Maybe<&2, B.Numero64>}:
  %Equal.sym(Maybe<&2, B.Numero64>, C.minimo_pilha(pai), B.nat64(r), minimo) :
    {C.somar_pendencia(q, 11n, _) == B.nat64(Nat.add(Nat.mul(11n, n), r)) : Maybe<&2, B.Numero64>}
  A.somar_pendencia_nat64_exato(n, q, 11n, r, medido)

def compor_cauda_registro(+t: List<&2, S.CampoSegmentado>, +q: B.Numero64, +nome: String, +v: D.Valor, +bs: List<&2, U32>,
  +anterior: String, +invertidos: List<&2, D.Campo>, +pai: C.Pilha, +sufixo: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64,
  +contado: {B.nat64(1n+S.quantidade_campos(t)) == Some{q} : Maybe<&2, B.Numero64>},
  +entrada: {B.nat64(B.comprimento(B.concatenar(bs, B.concatenar(S.bytes_campos(t), sufixo)))) == Some{corpo} : Maybe<&2, B.Numero64>},
  cabe: {C.menor_igual64(corpo, teto) == True{} : Bool},
  passo: {R.executar(bs, R.Quadro{corpo, teto, C.TagNome{C.Nome{C.um64(q), C.diminuir64(q), anterior, invertidos, pai}}}) ==
    X.depois(bs, corpo, teto, C.emitir(C.Campo{C.um64(q), C.diminuir64(q), nome, invertidos, pai}, v)) : R.Quadro},
  continuar: NaoVazio(t) ->
    {B.nat64(B.comprimento(B.concatenar(S.bytes_campos(t), sufixo))) == Some{H.diminuir(B.comprimento(bs), corpo)} : Maybe<&2, B.Numero64>} ->
    {C.menor_igual64(H.diminuir(B.comprimento(bs), corpo), H.diminuir(B.comprimento(bs), teto)) == True{} : Bool} ->
    {R.executar(S.bytes_campos(t), R.Quadro{H.diminuir(B.comprimento(bs), corpo), H.diminuir(B.comprimento(bs), teto),
        C.TagNome{C.Nome{C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q)), nome, Con{D.Campo{nome, v}, invertidos}, pai}}}) ==
      X.depois(S.bytes_campos(t), H.diminuir(B.comprimento(bs), corpo), H.diminuir(B.comprimento(bs), teto), C.emitir(pai, C.montar_registro(Con{D.Campo{nome, v}, invertidos}, registro(t)))) : R.Quadro}) ->
  {R.executar(B.concatenar(bs, S.bytes_campos(t)), R.Quadro{corpo, teto, C.TagNome{C.Nome{C.um64(q), C.diminuir64(q), anterior, invertidos, pai}}}) ==
    X.depois(B.concatenar(bs, S.bytes_campos(t)), corpo, teto, C.emitir(pai, C.montar_registro(invertidos, D.VRegistro{nome, v, registro(t)}))) : R.Quadro}:
  match t:
    case Nil{}:
      +ultimo = N.um64_reflete_contagem_natural(1n, q, contado)
      +emissao = {(%Equal.sym(Bool, C.um64(q), True{}, ultimo) :
        {C.emitir(C.Campo{_, C.diminuir64(q), nome, invertidos, pai}, v) == C.emitir(pai, C.montar_registro(invertidos, D.VRegistro{nome, v, D.VRegistroVazio{}})) : C.Maquina}
        {==}) : {C.emitir(C.Campo{C.um64(q), C.diminuir64(q), nome, invertidos, pai}, v) == C.emitir(pai, C.montar_registro(invertidos, D.VRegistro{nome, v, D.VRegistroVazio{}})) : C.Maquina}}
      V.compor_dois_segmentos_reais(bs, Nil{}, corpo, teto, C.TagNome{C.Nome{C.um64(q), C.diminuir64(q), anterior, invertidos, pai}},
        C.emitir(C.Campo{C.um64(q), C.diminuir64(q), nome, invertidos, pai}, v), C.emitir(pai, C.montar_registro(invertidos, D.VRegistro{nome, v, D.VRegistroVazio{}})), passo,
        Equal.cong(C.Maquina, R.Quadro, m => X.depois(bs, corpo, teto, m),
          C.emitir(C.Campo{C.um64(q), C.diminuir64(q), nome, invertidos, pai}, v), C.emitir(pai, C.montar_registro(invertidos, D.VRegistro{nome, v, D.VRegistroVazio{}})), emissao))
    case Con{+h, +resto}:
      +ultimo = N.um64_reflete_contagem_natural(2n+S.quantidade_campos(resto), q, contado)
      +emissao = {(%Equal.sym(Bool, C.um64(q), False{}, ultimo) :
        {C.emitir(C.Campo{_, C.diminuir64(q), nome, invertidos, pai}, v) == C.TagNome{C.Nome{C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q)), nome, Con{D.Campo{nome, v}, invertidos}, pai}} : C.Maquina}
        {==}) : {C.emitir(C.Campo{C.um64(q), C.diminuir64(q), nome, invertidos, pai}, v) == C.TagNome{C.Nome{C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q)), nome, Con{D.Campo{nome, v}, invertidos}, pai}} : C.Maquina}}
      V.compor_dois_segmentos_reais(bs, S.bytes_campos(Con{h, resto}), corpo, teto, C.TagNome{C.Nome{C.um64(q), C.diminuir64(q), anterior, invertidos, pai}},
        C.TagNome{C.Nome{C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q)), nome, Con{D.Campo{nome, v}, invertidos}, pai}}, C.emitir(pai, C.montar_registro(Con{D.Campo{nome, v}, invertidos}, registro(Con{h, resto}))),
        Equal.trans(R.Quadro,
          R.executar(bs, R.Quadro{corpo, teto, C.TagNome{C.Nome{C.um64(q), C.diminuir64(q), anterior, invertidos, pai}}}),
          X.depois(bs, corpo, teto, C.emitir(C.Campo{C.um64(q), C.diminuir64(q), nome, invertidos, pai}, v)),
          X.depois(bs, corpo, teto, C.TagNome{C.Nome{C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q)), nome, Con{D.Campo{nome, v}, invertidos}, pai}}), passo,
          Equal.cong(C.Maquina, R.Quadro, m => X.depois(bs, corpo, teto, m),
            C.emitir(C.Campo{C.um64(q), C.diminuir64(q), nome, invertidos, pai}, v), C.TagNome{C.Nome{C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q)), nome, Con{D.Campo{nome, v}, invertidos}, pai}}, emissao)),
        continuar(Unit{}, V.medida_apos_segmento(bs, B.concatenar(S.bytes_campos(Con{h, resto}), sufixo), corpo, entrada), M.diminuir_repetido_preserva_ordem_dos_limites(B.comprimento(bs), corpo, teto, cabe)))

law registro_de_segmentos_compoe_execucao_real_dos_campos:
  for +xs: List<&2, S.CampoSegmentado>
  for +q: B.Numero64
  for +anterior: String
  for +invertidos: List<&2, D.Campo>
  for +pai: C.Pilha
  for +sufixo: List<&2, U32>
  for +r: Nat
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for positivo: NaoVazio(xs)
  for filhos: InducaoCampos(xs)
  for ordenados: E.CamposOrdenados(S.campos(xs), anterior)
  for +contado: {B.nat64(S.quantidade_campos(xs)) == Some{q} : Maybe<&2, B.Numero64>}
  for +minimo: {C.minimo_pilha(pai) == B.nat64(r) : Maybe<&2, B.Numero64>}
  for +reserva: {Nat.is_le(r, B.comprimento(sufixo)) == True{} : Bool}
  for +medido: {B.nat64(B.comprimento(B.concatenar(S.bytes_campos(xs), sufixo))) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {R.executar(S.bytes_campos(xs), R.Quadro{corpo, teto, C.TagNome{C.Nome{C.um64(q), C.diminuir64(q), anterior, invertidos, pai}}}) ==
    X.depois(S.bytes_campos(xs), corpo, teto, C.emitir(pai, C.montar_registro(invertidos, registro(xs)))) : R.Quadro}
def registro_de_segmentos_compoe_execucao_real_dos_campos(xs, q, anterior, invertidos, pai, sufixo, r, corpo, teto, positivo, filhos, ordenados, contado, minimo, reserva, medido, cabe):
  match xs:
    case Nil{}:
      L.ex_falso({R.Quadro{corpo, teto, C.TagNome{C.Nome{C.um64(q), C.diminuir64(q), anterior, invertidos, pai}}} == R.Quadro{corpo, teto, C.emitir(pai, C.montar_registro(invertidos, D.VRegistroVazio{}))} : R.Quadro}, positivo)
    case Con{S.CampoSegmentado{+nome, +v, +nb, +vb}, +t}:
      match filhos ordenados:
        case L.Ambos{nome_completo, L.Ambos{valor_completo, L.Ambos{positivo_v, L.Ambos{+tamanho, cauda}}}} L.Ambos{valido, L.Ambos{ordem, ordenada_cauda}}:
          +bs = B.concatenar(nb, vb)
          +restantes = N.medida_decrementada(S.quantidade_campos(t), q, N.nat64_sucessor_tem_antecessor_exato(S.quantidade_campos(t), q, contado))
          +reserva_filho = S.concatenar_segmentos_preserva_soma_dos_limites(S.bytes_campos(t), sufixo, Nat.mul(11n, S.quantidade_campos(t)), r, tamanho, reserva)
          +entrada_filho = {(%K.concatenacao_associativa(bs, S.bytes_campos(t), sufixo) :
              {B.nat64(B.comprimento(_)) == Some{corpo} : Maybe<&2, B.Numero64>}
              medido) : {B.nat64(B.comprimento(B.concatenar(bs, B.concatenar(S.bytes_campos(t), sufixo)))) == Some{corpo} : Maybe<&2, B.Numero64>}}
          minimo_campo = minimo_frame_campo(C.um64(q), C.diminuir64(q), nome, invertidos, pai, S.quantidade_campos(t), r, restantes, minimo)
          passo = G.nome_e_valor_segmentados_compoem_campo_real(nome, v, nb, vb, C.um64(q), C.diminuir64(q), anterior, invertidos, pai,
            B.concatenar(S.bytes_campos(t), sufixo), Nat.add(Nat.mul(11n, S.quantidade_campos(t)), r), corpo, teto,
            nome_completo, valor_completo, valido, ordem, positivo_v, minimo_campo, reserva_filho, entrada_filho, cabe)
          compor_cauda_registro(t, q, nome, v, bs, anterior, invertidos, pai, sufixo, corpo, teto, contado, entrada_filho, cabe, passo,
            positivo => medida_cauda => cabe_cauda =>
              registro_de_segmentos_compoe_execucao_real_dos_campos(t, C.diminuir64(q), nome, Con{D.Campo{nome, v}, invertidos}, pai, sufixo, r,
                H.diminuir(B.comprimento(bs), corpo), H.diminuir(B.comprimento(bs), teto), positivo, cauda, ordenada_cauda, restantes, minimo, reserva, medida_cauda, cabe_cauda))

law registro_aberto_compoe_todos_os_segmentos:
  for +xs: List<&2, S.CampoSegmentado>
  for +q: B.Numero64
  for +pai: C.Pilha
  for +sufixo: List<&2, U32>
  for +r: Nat
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for filhos: InducaoCampos(xs)
  for ordenados: E.CamposOrdenados(S.campos(xs), "")
  for +contado: {B.nat64(S.quantidade_campos(xs)) == Some{q} : Maybe<&2, B.Numero64>}
  for +minimo: {C.minimo_pilha(pai) == B.nat64(r) : Maybe<&2, B.Numero64>}
  for +reserva: {Nat.is_le(r, B.comprimento(sufixo)) == True{} : Bool}
  for +medido: {B.nat64(B.comprimento(B.concatenar(S.bytes_campos(xs), sufixo))) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {R.executar(S.bytes_campos(xs), R.Quadro{corpo, teto, C.abrir_variavel(C.zero64(q), C.ContaRegistro{}, q, pai)}) ==
    X.depois(S.bytes_campos(xs), corpo, teto, C.emitir(pai, registro(xs))) : R.Quadro}
def registro_aberto_compoe_todos_os_segmentos(xs, q, pai, sufixo, r, corpo, teto, filhos, ordenados, contado, minimo, reserva, medido, cabe):
  match xs:
    case Nil{}:
      %F.algum_injetivo(B.Numero64, B.Numero64{0, 0}, q, contado) :
        {R.Quadro{corpo, teto, C.abrir_variavel(C.zero64(_), C.ContaRegistro{}, q, pai)} == X.depois(Nil{}, corpo, teto, C.emitir(pai, D.VRegistroVazio{})) : R.Quadro}
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, C.zero64(q), False{}, N.zero64_reflete_contagem_natural(S.quantidade_campos(Con{h, t}), q, contado)) :
        {R.executar(S.bytes_campos(Con{h, t}), R.Quadro{corpo, teto, C.abrir_variavel(_, C.ContaRegistro{}, q, pai)}) == X.depois(S.bytes_campos(Con{h, t}), corpo, teto, C.emitir(pai, registro(Con{h, t}))) : R.Quadro}
      registro_de_segmentos_compoe_execucao_real_dos_campos(Con{h, t}, q, "", Nil{}, pai, sufixo, r, corpo, teto, Unit{}, filhos, ordenados, contado, minimo, reserva, medido, cabe)

def bytes_registro(alto: U32, baixo: U32, xs: List<&2, S.CampoSegmentado>) -> List<&2, U32>:
  Con{6, B.concatenar(B.be64(alto, baixo), S.bytes_campos(xs))}

# Este e o PASSO DE INDUCAO do construtor registro. Todos os valores dos
# filhos sao arbitrarios; a hipotese recai apenas em cada subvalor menor.
# O unico limite e o corpo/teto real, sem quota de profundidade ou aridade.
law construtor_registro_compoe_completude_local:
  for +xs: List<&2, S.CampoSegmentado>
  for +alto: U32
  for +baixo: U32
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +pai: C.Pilha
  for +sufixo: List<&2, U32>
  for +r: Nat
  for filhos: InducaoCampos(xs)
  for ordenados: E.CamposOrdenados(S.campos(xs), "")
  for canonicos: S.CamposCanonicos(xs)
  for +contado: {B.nat64(S.quantidade_campos(xs)) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>}
  for +minimo: {C.minimo_pilha(pai) == B.nat64(r) : Maybe<&2, B.Numero64>}
  for +reserva: {Nat.is_le(r, B.comprimento(sufixo)) == True{} : Bool}
  for +medido: {B.nat64(B.comprimento(B.concatenar(bytes_registro(alto, baixo, xs), sufixo))) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {R.executar(bytes_registro(alto, baixo, xs), R.Quadro{corpo, teto, C.Tag{pai}}) ==
    X.depois(bytes_registro(alto, baixo, xs), corpo, teto, C.emitir(pai, registro(xs))) : R.Quadro}
def construtor_registro_compoe_completude_local(xs, alto, baixo, corpo, teto, pai, sufixo, r, filhos, ordenados, canonicos, contado, minimo, reserva, medido, cabe):
  +medida_cauda = T.remover_prefixo_da_medida(9n, B.comprimento(B.concatenar(S.bytes_campos(xs), sufixo)), corpo, medido)
  +limite_minimo = S.concatenar_segmentos_preserva_soma_dos_limites(S.bytes_campos(xs), sufixo, Nat.mul(11n, S.quantidade_campos(xs)), r,
    S.sequencia_de_campos_canonicos_exige_onze_octetos_por_campo(xs, canonicos), reserva)
  +abertura = X.cabecalho_variavel_com_corpo_e_teto_u64_arbitrario(C.ContaRegistro{}, S.quantidade_campos(xs), r, B.comprimento(B.concatenar(S.bytes_campos(xs), sufixo)), alto, baixo, pai, corpo, teto, Unit{}, contado, minimo, medida_cauda, limite_minimo, cabe)
  V.compor_dois_segmentos_reais(Con{6, B.be64(alto, baixo)}, S.bytes_campos(xs), corpo, teto, C.Tag{pai},
    C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), C.ContaRegistro{}, B.Numero64{alto, baixo}, pai), C.emitir(pai, registro(xs)), abertura,
    registro_aberto_compoe_todos_os_segmentos(xs, B.Numero64{alto, baixo}, pai, sufixo, r, H.diminuir(9n, corpo), H.diminuir(9n, teto), filhos, ordenados, contado, minimo, reserva, medida_cauda,
      M.diminuir_repetido_preserva_ordem_dos_limites(9n, corpo, teto, cabe)))
