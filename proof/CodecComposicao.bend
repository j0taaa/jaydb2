# Composicao de segmentos na maquina REAL, conservando corpo/teto e pilha.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecPercurso.bend as R
import ./CodecPalavrasBE64.bend as H
import ./CodecTextos.bend as T
import ./CodecUTF8.bend as U
import ./CodecUTF8Inversa.bend as V
import ./CodecConteudo.bend as G
import ./CodecContadores.bend as N
import ./CodecSomasMinimos.bend as S
import ./CodecReservas.bend as Z
import ./CodecMinimos.bend as M

def depois(+bs: List<&2, U32>, corpo: B.Numero64, teto: B.Numero64, m: C.Maquina) -> R.Quadro:
  R.Quadro{H.diminuir(B.comprimento(bs), corpo), H.diminuir(B.comprimento(bs), teto), m}

# Extrair a maquina nao oculta nenhum efeito sobre os contadores.
law execucao_com_maquina_conhecida_tem_contadores_exatos:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +m: C.Maquina
  for -fim: C.Maquina
  for maquina: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, m})) == fim : C.Maquina}
  {R.executar(bs, R.Quadro{corpo, teto, m}) == depois(bs, corpo, teto, fim) : R.Quadro}
def execucao_com_maquina_conhecida_tem_contadores_exatos(bs, corpo, teto, m, fim, maquina):
  match bs:
    case Nil{}:
      Equal.cong(C.Maquina, R.Quadro, x => R.Quadro{corpo, teto, x}, m, fim, maquina)
    case Con{+b, +t}:
      %T.diminuir_comuta_com_iteracao(B.comprimento(t), corpo) :
        {R.executar(t, R.avancar(R.Quadro{corpo, teto, m}, b)) == R.Quadro{_, C.diminuir64(H.diminuir(B.comprimento(t), teto)), fim} : R.Quadro}
      %T.diminuir_comuta_com_iteracao(B.comprimento(t), teto) :
        {R.executar(t, R.avancar(R.Quadro{corpo, teto, m}, b)) == R.Quadro{H.diminuir(B.comprimento(t), C.diminuir64(corpo)), _, fim} : R.Quadro}
      execucao_com_maquina_conhecida_tem_contadores_exatos(t, C.diminuir64(corpo), C.diminuir64(teto),
        C.passo(m, b, C.diminuir64(corpo), C.diminuir64(teto)), fim, maquina)

law diminuir_por_concatenacao:
  for xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +q: B.Numero64
  {H.diminuir(B.comprimento(B.concatenar(xs, ys)), q) == H.diminuir(B.comprimento(ys), H.diminuir(B.comprimento(xs), q)) : B.Numero64}
def diminuir_por_concatenacao(xs, ys, q):
  match xs:
    case Nil{}:
      {==}
    case Con{b, +t}:
      Equal.trans(B.Numero64,
        C.diminuir64(H.diminuir(B.comprimento(B.concatenar(t, ys)), q)),
        H.diminuir(B.comprimento(B.concatenar(t, ys)), C.diminuir64(q)),
        H.diminuir(B.comprimento(ys), C.diminuir64(H.diminuir(B.comprimento(t), q))),
        Equal.sym(B.Numero64, H.diminuir(B.comprimento(B.concatenar(t, ys)), C.diminuir64(q)), C.diminuir64(H.diminuir(B.comprimento(B.concatenar(t, ys)), q)), T.diminuir_comuta_com_iteracao(B.comprimento(B.concatenar(t, ys)), q)),
        Equal.trans(B.Numero64,
          H.diminuir(B.comprimento(B.concatenar(t, ys)), C.diminuir64(q)),
          H.diminuir(B.comprimento(ys), H.diminuir(B.comprimento(t), C.diminuir64(q))),
          H.diminuir(B.comprimento(ys), C.diminuir64(H.diminuir(B.comprimento(t), q))),
          diminuir_por_concatenacao(t, ys, C.diminuir64(q)),
          Equal.cong(B.Numero64, B.Numero64, z => H.diminuir(B.comprimento(ys), z),
            H.diminuir(B.comprimento(t), C.diminuir64(q)), C.diminuir64(H.diminuir(B.comprimento(t), q)), T.diminuir_comuta_com_iteracao(B.comprimento(t), q))))

# Nome=False e Nome=True usam o mesmo transdutor; a pilha pode conter
# quaisquer ancestrais. A validade do nome/ordem e conferida por emitir_nome.
law conteudo_canonico_emite_na_pilha_original:
  for +s: String
  for +q: B.Numero64
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +nome: Bool
  for +pilha: C.Pilha
  for positivo: G.NaoVazio(B.utf8(s))
  for valido: {B.texto_valido(s) == True{} : Bool}
  for +medido: {B.nat64(B.comprimento(B.utf8(s))) == Some{q} : Maybe<&2, B.Numero64>}
  {R.executar(B.utf8(s), R.Quadro{corpo, teto, C.Conteudo{nome, C.um64(q), C.diminuir64(q), C.Inicio{}, "", pilha}}) ==
    depois(B.utf8(s), corpo, teto, C.emitir_texto(nome, s, pilha)) : R.Quadro}
def conteudo_canonico_emite_na_pilha_original(s, q, corpo, teto, nome, pilha, positivo, valido, medido):
  execucao_com_maquina_conhecida_tem_contadores_exatos(B.utf8(s), corpo, teto,
    C.Conteudo{nome, C.um64(q), C.diminuir64(q), C.Inicio{}, "", pilha}, C.emitir_texto(nome, s, pilha),
    Equal.trans(C.Maquina,
      G.processar_conteudo(B.utf8(s), q, corpo, teto, nome, C.Inicio{}, "", pilha),
      G.concluir_texto(nome, pilha, U.percorrer_texto(B.utf8(s), U.Lendo{C.Inicio{}, ""})), C.emitir_texto(nome, s, pilha),
      G.conteudo_contado_consume_exatamente_o_texto(B.utf8(s), q, corpo, teto, nome, C.Inicio{}, "", pilha, positivo, medido),
      T.concluir_transducao_aceita(nome, pilha, U.percorrer_texto(B.utf8(s), U.Lendo{C.Inicio{}, ""}), s, V.utf8_texto_valido_decodifica_exatamente(s, valido))))

def abertura_textual_maquina(+bs: List<&2, U32>, +q: B.Numero64, +corpo: B.Numero64, +teto: B.Numero64,
  +pilha: C.Pilha, -s: String,
  +medido: {B.nat64(B.comprimento(bs)) == Some{q} : Maybe<&2, B.Numero64>},
  aceito: {U.finalizar_texto(U.percorrer_texto(bs, U.Lendo{C.Inicio{}, ""})) == Some{s} : Maybe<&2, String>}) ->
  {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.abrir_variavel(C.zero64(q), C.Texto{}, q, pilha)})) == C.emitir(pilha, D.VTexto{s}) : C.Maquina}:
  match bs:
    case Nil{}:
      %F.algum_injetivo(B.Numero64, B.Numero64{0, 0}, q, medido) :
        {R.maquina(R.executar(Nil{}, R.Quadro{corpo, teto, C.abrir_variavel(C.zero64(_), C.Texto{}, q, pilha)})) == C.emitir(pilha, D.VTexto{s}) : C.Maquina}
      Equal.cong(String, C.Maquina, texto => C.emitir(pilha, D.VTexto{texto}), "", s, F.algum_injetivo(String, "", s, aceito))
    case Con{+b, +t}:
      %Equal.sym(Bool, C.zero64(q), False{}, N.zero64_reflete_contagem_natural(B.comprimento(Con{b, t}), q, medido)) :
        {R.maquina(R.executar(Con{b, t}, R.Quadro{corpo, teto, C.abrir_variavel(_, C.Texto{}, q, pilha)})) == C.emitir(pilha, D.VTexto{s}) : C.Maquina}
      Equal.trans(C.Maquina,
        G.processar_conteudo(Con{b, t}, q, corpo, teto, False{}, C.Inicio{}, "", pilha),
        G.concluir_texto(False{}, pilha, U.percorrer_texto(Con{b, t}, U.Lendo{C.Inicio{}, ""})), C.emitir(pilha, D.VTexto{s}),
        G.conteudo_contado_consume_exatamente_o_texto(Con{b, t}, q, corpo, teto, False{}, C.Inicio{}, "", pilha, Unit{}, medido),
        T.concluir_transducao_aceita(False{}, pilha, U.percorrer_texto(Con{b, t}, U.Lendo{C.Inicio{}, ""}), s, aceito))

law abertura_textual_canonica_emite_na_pilha_original:
  for +bs: List<&2, U32>
  for +q: B.Numero64
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +pilha: C.Pilha
  for -s: String
  for +medido: {B.nat64(B.comprimento(bs)) == Some{q} : Maybe<&2, B.Numero64>}
  for aceito: {U.finalizar_texto(U.percorrer_texto(bs, U.Lendo{C.Inicio{}, ""})) == Some{s} : Maybe<&2, String>}
  {R.executar(bs, R.Quadro{corpo, teto, C.abrir_variavel(C.zero64(q), C.Texto{}, q, pilha)}) ==
    depois(bs, corpo, teto, C.emitir(pilha, D.VTexto{s})) : R.Quadro}
def abertura_textual_canonica_emite_na_pilha_original(bs, q, corpo, teto, pilha, s, medido, aceito):
  execucao_com_maquina_conhecida_tem_contadores_exatos(bs, corpo, teto,
    C.abrir_variavel(C.zero64(q), C.Texto{}, q, pilha), C.emitir(pilha, D.VTexto{s}),
    abertura_textual_maquina(bs, q, corpo, teto, pilha, s, medido, aceito))


def tag(f: C.Finalidade) -> U32:
  match f:
    case C.Inteiro{}:
      3
    case C.Texto{}:
      4
    case C.NomeTexto{}:
      4
    case C.ContaLista{}:
      5
    case C.ContaRegistro{}:
      6

def inicio(f: C.Finalidade, pilha: C.Pilha) -> C.Maquina:
  match f:
    case C.NomeTexto{}:
      C.TagNome{pilha}
    case _:
      C.Tag{pilha}

def Variavel(f: C.Finalidade) -> Type:
  match f:
    case C.Inteiro{}:
      Empty
    case _:
      Unit

law tag_canonica_inicia_a_finalidade_exata:
  for +f: C.Finalidade
  for +pilha: C.Pilha
  for corpo: B.Numero64
  for teto: B.Numero64
  {C.passo(inicio(f, pilha), tag(f), corpo, teto) == C.Palavra{f, 7n, 0, 0, pilha} : C.Maquina}
def tag_canonica_inicia_a_finalidade_exata(f, pilha, corpo, teto):
  match f:
    case C.Inteiro{}:
      {==}
    case C.Texto{}:
      {==}
    case C.NomeTexto{}:
      {==}
    case C.ContaLista{}:
      {==}
    case C.ContaRegistro{}:
      {==}

law cabecalho_canonico_composto_preserva_toda_a_pilha:
  for +f: C.Finalidade
  for +alto: U32
  for +baixo: U32
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  {R.executar(Con{tag(f), B.be64(alto, baixo)}, R.Quadro{corpo, teto, inicio(f, pilha)}) ==
    R.Quadro{H.diminuir(9n, corpo), H.diminuir(9n, teto), C.concluir_palavra(f, alto, baixo, pilha, H.diminuir(9n, corpo), H.diminuir(9n, teto))} : R.Quadro}
def cabecalho_canonico_composto_preserva_toda_a_pilha(f, alto, baixo, pilha, corpo, teto):
  %Equal.sym(C.Maquina, C.passo(inicio(f, pilha), tag(f), C.diminuir64(corpo), C.diminuir64(teto)), C.Palavra{f, 7n, 0, 0, pilha},
    tag_canonica_inicia_a_finalidade_exata(f, pilha, C.diminuir64(corpo), C.diminuir64(teto))) :
    {R.executar(B.be64(alto, baixo), R.Quadro{C.diminuir64(corpo), C.diminuir64(teto), _}) ==
      R.Quadro{H.diminuir(9n, corpo), H.diminuir(9n, teto), C.concluir_palavra(f, alto, baixo, pilha, H.diminuir(9n, corpo), H.diminuir(9n, teto))} : R.Quadro}
  H.be64_conclui_palavra(f, alto, baixo, pilha, C.diminuir64(corpo), C.diminuir64(teto))

def concluir_variavel_conferida(+f: C.Finalidade, +alto: U32, +baixo: U32, +pilha: C.Pilha,
  +corpo: B.Numero64, +teto: B.Numero64, variavel: Variavel(f),
  cabe: {C.conferir(C.somar_opcionais(C.minimo_campo(f, B.Numero64{alto, baixo}), C.minimo_pilha(pilha)), corpo, teto) == C.Cabe{} : C.Conferencia}) ->
  {C.concluir_palavra(f, alto, baixo, pilha, corpo, teto) == C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), f, B.Numero64{alto, baixo}, pilha) : C.Maquina}:
  match f:
    case C.Inteiro{}:
      L.ex_falso({C.emitir(pilha, D.VInt{alto, baixo}) == C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), C.Inteiro{}, B.Numero64{alto, baixo}, pilha) : C.Maquina}, variavel)
    case C.Texto{}:
      Equal.cong(C.Conferencia, C.Maquina, c => C.abrir_conferido(c, C.Texto{}, B.Numero64{alto, baixo}, pilha),
        C.conferir(C.somar_opcionais(C.minimo_campo(C.Texto{}, B.Numero64{alto, baixo}), C.minimo_pilha(pilha)), corpo, teto), C.Cabe{}, cabe)
    case C.NomeTexto{}:
      Equal.cong(C.Conferencia, C.Maquina, c => C.abrir_conferido(c, C.NomeTexto{}, B.Numero64{alto, baixo}, pilha),
        C.conferir(C.somar_opcionais(C.minimo_campo(C.NomeTexto{}, B.Numero64{alto, baixo}), C.minimo_pilha(pilha)), corpo, teto), C.Cabe{}, cabe)
    case C.ContaLista{}:
      Equal.cong(C.Conferencia, C.Maquina, c => C.abrir_conferido(c, C.ContaLista{}, B.Numero64{alto, baixo}, pilha),
        C.conferir(C.somar_opcionais(C.minimo_campo(C.ContaLista{}, B.Numero64{alto, baixo}), C.minimo_pilha(pilha)), corpo, teto), C.Cabe{}, cabe)
    case C.ContaRegistro{}:
      Equal.cong(C.Conferencia, C.Maquina, c => C.abrir_conferido(c, C.ContaRegistro{}, B.Numero64{alto, baixo}, pilha),
        C.conferir(C.somar_opcionais(C.minimo_campo(C.ContaRegistro{}, B.Numero64{alto, baixo}), C.minimo_pilha(pilha)), corpo, teto), C.Cabe{}, cabe)

# As hipoteses sao medidas matematicas dos segmentos pendentes. Nenhuma
# delas assume uma transicao, conferencia ou aceitacao bem sucedida.
law cabecalho_variavel_limitado_abre_na_pilha_original:
  for +f: C.Finalidade
  for +n: Nat
  for +r: Nat
  for +c: Nat
  for +t: Nat
  for +alto: U32
  for +baixo: U32
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for variavel: Variavel(f)
  for medido: {B.nat64(n) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>}
  for pai: {C.minimo_pilha(pilha) == B.nat64(r) : Maybe<&2, B.Numero64>}
  for +mc: {B.nat64(c) == Some{H.diminuir(9n, corpo)} : Maybe<&2, B.Numero64>}
  for +mt: {B.nat64(t) == Some{H.diminuir(9n, teto)} : Maybe<&2, B.Numero64>}
  for +lc: {Nat.is_le(Nat.add(S.minimo_campo_natural(f, n), r), c) == True{} : Bool}
  for lt: {Nat.is_le(Nat.add(S.minimo_campo_natural(f, n), r), t) == True{} : Bool}
  {R.executar(Con{tag(f), B.be64(alto, baixo)}, R.Quadro{corpo, teto, inicio(f, pilha)}) ==
    R.Quadro{H.diminuir(9n, corpo), H.diminuir(9n, teto), C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), f, B.Numero64{alto, baixo}, pilha)} : R.Quadro}
def cabecalho_variavel_limitado_abre_na_pilha_original(f, n, r, c, t, alto, baixo, pilha, corpo, teto, variavel, medido, pai, mc, mt, lc, lt):
  Equal.trans(R.Quadro,
    R.executar(Con{tag(f), B.be64(alto, baixo)}, R.Quadro{corpo, teto, inicio(f, pilha)}),
    R.Quadro{H.diminuir(9n, corpo), H.diminuir(9n, teto), C.concluir_palavra(f, alto, baixo, pilha, H.diminuir(9n, corpo), H.diminuir(9n, teto))},
    R.Quadro{H.diminuir(9n, corpo), H.diminuir(9n, teto), C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), f, B.Numero64{alto, baixo}, pilha)},
    cabecalho_canonico_composto_preserva_toda_a_pilha(f, alto, baixo, pilha, corpo, teto),
    Equal.cong(C.Maquina, R.Quadro, m => R.Quadro{H.diminuir(9n, corpo), H.diminuir(9n, teto), m},
      C.concluir_palavra(f, alto, baixo, pilha, H.diminuir(9n, corpo), H.diminuir(9n, teto)),
      C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), f, B.Numero64{alto, baixo}, pilha),
      concluir_variavel_conferida(f, alto, baixo, pilha, H.diminuir(9n, corpo), H.diminuir(9n, teto), variavel,
        S.conferir_minimo_campo_com_pilha_por_limites_nat(f, n, r, c, t, B.Numero64{alto, baixo}, pilha, H.diminuir(9n, corpo), H.diminuir(9n, teto), medido, pai, mc, mt, lc, lt))))

law cabecalho_variavel_com_corpo_e_teto_u64_arbitrario:
  for +f: C.Finalidade
  for +n: Nat
  for +r: Nat
  for +c: Nat
  for +alto: U32
  for +baixo: U32
  for +pilha: C.Pilha
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for variavel: Variavel(f)
  for medido: {B.nat64(n) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>}
  for pai: {C.minimo_pilha(pilha) == B.nat64(r) : Maybe<&2, B.Numero64>}
  for +mc: {B.nat64(c) == Some{H.diminuir(9n, corpo)} : Maybe<&2, B.Numero64>}
  for nc: {Nat.is_le(Nat.add(S.minimo_campo_natural(f, n), r), c) == True{} : Bool}
  for ct: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {R.executar(Con{tag(f), B.be64(alto, baixo)}, R.Quadro{corpo, teto, inicio(f, pilha)}) ==
    R.Quadro{H.diminuir(9n, corpo), H.diminuir(9n, teto), C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), f, B.Numero64{alto, baixo}, pilha)} : R.Quadro}
def cabecalho_variavel_com_corpo_e_teto_u64_arbitrario(f, n, r, c, alto, baixo, pilha, corpo, teto, variavel, medido, pai, mc, nc, ct):
  Equal.trans(R.Quadro,
    R.executar(Con{tag(f), B.be64(alto, baixo)}, R.Quadro{corpo, teto, inicio(f, pilha)}),
    R.Quadro{H.diminuir(9n, corpo), H.diminuir(9n, teto), C.concluir_palavra(f, alto, baixo, pilha, H.diminuir(9n, corpo), H.diminuir(9n, teto))},
    R.Quadro{H.diminuir(9n, corpo), H.diminuir(9n, teto), C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), f, B.Numero64{alto, baixo}, pilha)},
    cabecalho_canonico_composto_preserva_toda_a_pilha(f, alto, baixo, pilha, corpo, teto),
    Equal.cong(C.Maquina, R.Quadro, m => R.Quadro{H.diminuir(9n, corpo), H.diminuir(9n, teto), m},
      C.concluir_palavra(f, alto, baixo, pilha, H.diminuir(9n, corpo), H.diminuir(9n, teto)),
      C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), f, B.Numero64{alto, baixo}, pilha),
      concluir_variavel_conferida(f, alto, baixo, pilha, H.diminuir(9n, corpo), H.diminuir(9n, teto), variavel,
        Z.conferir_minimo_composto_pelo_corpo_real(f, n, r, c, B.Numero64{alto, baixo}, pilha, H.diminuir(9n, corpo), H.diminuir(9n, teto), medido, pai, mc, nc,
          M.diminuir_repetido_preserva_ordem_dos_limites(9n, corpo, teto, ct)))))
