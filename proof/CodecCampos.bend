# Composicao efetiva do nome e do valor de um campo, com pilha ancestral.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecPercurso.bend as R
import ./CodecComposicao.bend as X
import ./CodecSequencias.bend as S
import ./CodecPalavrasBE64.bend as H
import ./CodecMinimos.bend as M
import ./CodecSomas.bend as A
import ./CodecLimitesSequencias.bend as K
import ./CodecCanonico.bend as J

def NomeCompleto(nome: String, +bs: List<&2, U32>) -> Type:
  @corpo: B.Numero64 -> @teto: B.Numero64 -> @pilha: C.Pilha ->
  @sufixo: List<&2, U32> -> @r: Nat ->
  {C.minimo_pilha(pilha) == B.nat64(r) : Maybe<&2, B.Numero64>} ->
  {Nat.is_le(r, B.comprimento(sufixo)) == True{} : Bool} ->
  {B.nat64(B.comprimento(B.concatenar(bs, sufixo))) == Some{corpo} : Maybe<&2, B.Numero64>} ->
  {C.menor_igual64(corpo, teto) == True{} : Bool} ->
  {R.executar(bs, R.Quadro{corpo, teto, C.TagNome{pilha}}) == X.depois(bs, corpo, teto, C.emitir_nome(pilha, nome)) : R.Quadro}

law minimo_nome_inclui_exatamente_valor_atual:
  for +u: Bool
  for +q: B.Numero64
  for +anterior: String
  for +nome: String
  for +xs: List<&2, D.Campo>
  for +pai: C.Pilha
  for +r: Nat
  for minimo: {C.minimo_pilha(C.Campo{u, q, nome, xs, pai}) == B.nat64(r) : Maybe<&2, B.Numero64>}
  {C.minimo_pilha(C.Nome{u, q, anterior, xs, pai}) == B.nat64(1n+r) : Maybe<&2, B.Numero64>}
def minimo_nome_inclui_exatamente_valor_atual(u, q, anterior, nome, xs, pai, r, minimo):
  %Equal.sym(Maybe<&2, B.Numero64>, C.minimo_pilha(C.Campo{u, q, nome, xs, pai}), B.nat64(r), minimo) :
    {C.somar_opcionais(Some{B.Numero64{0, 1}}, _) == B.nat64(1n+r) : Maybe<&2, B.Numero64>}
  A.somar_opcionais_nat64_exato(1n, r)

law nome_ordenado_prepara_o_valor_correto:
  for +u: Bool
  for +q: B.Numero64
  for +anterior: String
  for +nome: String
  for +xs: List<&2, D.Campo>
  for +pai: C.Pilha
  for valido: {D.nome_valido(nome) == True{} : Bool}
  for ordem: {String.is_lt(anterior, nome) == True{} : Bool}
  {C.emitir_nome(C.Nome{u, q, anterior, xs, pai}, nome) == C.Tag{C.Campo{u, q, nome, xs, pai}} : C.Maquina}
def nome_ordenado_prepara_o_valor_correto(u, q, anterior, nome, xs, pai, valido, ordem):
  %Equal.sym(Bool, D.nome_valido(nome) && String.is_lt(anterior, nome), True{}, F.e_booleano_intro(D.nome_valido(nome), String.is_lt(anterior, nome), valido, ordem)) :
    {C.nome_conferido(_, u, q, nome, xs, pai) == C.Tag{C.Campo{u, q, nome, xs, pai}} : C.Maquina}
  {==}

# Os dois callbacks sao casos da inducao: nome e SUBVALOR, nao o registro.
# Todos os limites dos dois estados Nome/Campo sao deduzidos da reserva.
law nome_e_valor_segmentados_compoem_campo_real:
  for +nome: String
  for +v: D.Valor
  for +nb: List<&2, U32>
  for +vb: List<&2, U32>
  for +u: Bool
  for +q: B.Numero64
  for +anterior: String
  for +xs: List<&2, D.Campo>
  for +pai: C.Pilha
  for +sufixo: List<&2, U32>
  for +r: Nat
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for nome_completo: NomeCompleto(nome, nb)
  for valor_completo: S.CompletoLocal(v, vb)
  for valido: {D.nome_valido(nome) == True{} : Bool}
  for ordem: {String.is_lt(anterior, nome) == True{} : Bool}
  for positivo: {Nat.is_le(1n, B.comprimento(vb)) == True{} : Bool}
  for +minimo: {C.minimo_pilha(C.Campo{u, q, nome, xs, pai}) == B.nat64(r) : Maybe<&2, B.Numero64>}
  for +reserva: {Nat.is_le(r, B.comprimento(sufixo)) == True{} : Bool}
  for +medido: {B.nat64(B.comprimento(B.concatenar(B.concatenar(nb, vb), sufixo))) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {R.executar(B.concatenar(nb, vb), R.Quadro{corpo, teto, C.TagNome{C.Nome{u, q, anterior, xs, pai}}}) ==
    X.depois(B.concatenar(nb, vb), corpo, teto, C.emitir(C.Campo{u, q, nome, xs, pai}, v)) : R.Quadro}
def nome_e_valor_segmentados_compoem_campo_real(nome, v, nb, vb, u, q, anterior, xs, pai, sufixo, r, corpo, teto, nome_completo, valor_completo, valido, ordem, positivo, minimo, reserva, medido, cabe):
  +medida_nome = {(%J.concatenacao_associativa(nb, vb, sufixo) :
      {B.nat64(B.comprimento(_)) == Some{corpo} : Maybe<&2, B.Numero64>}
      medido) : {B.nat64(B.comprimento(B.concatenar(nb, B.concatenar(vb, sufixo)))) == Some{corpo} : Maybe<&2, B.Numero64>}}
  passo_nome = nome_completo(corpo, teto, C.Nome{u, q, anterior, xs, pai}, B.concatenar(vb, sufixo), 1n+r,
    minimo_nome_inclui_exatamente_valor_atual(u, q, anterior, nome, xs, pai, r, minimo),
    K.concatenar_segmentos_preserva_soma_dos_limites(vb, sufixo, 1n, r, positivo, reserva), medida_nome, cabe)
  emissao_nome = nome_ordenado_prepara_o_valor_correto(u, q, anterior, nome, xs, pai, valido, ordem)
  S.compor_dois_segmentos_reais(nb, vb, corpo, teto, C.TagNome{C.Nome{u, q, anterior, xs, pai}}, C.Tag{C.Campo{u, q, nome, xs, pai}}, C.emitir(C.Campo{u, q, nome, xs, pai}, v),
    Equal.trans(R.Quadro,
      R.executar(nb, R.Quadro{corpo, teto, C.TagNome{C.Nome{u, q, anterior, xs, pai}}}),
      X.depois(nb, corpo, teto, C.emitir_nome(C.Nome{u, q, anterior, xs, pai}, nome)), X.depois(nb, corpo, teto, C.Tag{C.Campo{u, q, nome, xs, pai}}), passo_nome,
      Equal.cong(C.Maquina, R.Quadro, m => X.depois(nb, corpo, teto, m), C.emitir_nome(C.Nome{u, q, anterior, xs, pai}, nome), C.Tag{C.Campo{u, q, nome, xs, pai}}, emissao_nome)),
    valor_completo(H.diminuir(B.comprimento(nb), corpo), H.diminuir(B.comprimento(nb), teto), C.Campo{u, q, nome, xs, pai}, sufixo, r, minimo, reserva,
      S.medida_apos_segmento(nb, B.concatenar(vb, sufixo), corpo, medida_nome), M.diminuir_repetido_preserva_ordem_dos_limites(B.comprimento(nb), corpo, teto, cabe)))
