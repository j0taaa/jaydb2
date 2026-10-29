# Preparacao da inducao por comprimento: containers conservam os segmentos
# originais e os percursos dos filhos, sem pressupor sua canonicidade.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecPercurso.bend as R
import ./CodecAridades.bend as A
import ./CodecMontagem.bend as M
import ./CodecLimitesSequencias.bend as S
import ./CodecPalavrasBE64.bend as K
import ./CodecPrimitivos.bend as U
import ./CodecAceitacaoTags.bend as T
import ./CodecAceitacaoPalavra.bend as W
import ./CodecAceitacaoRaiz.bend as Rz
import ./CodecAceitacaoFilhos.bend as H
import ./CodecAceitacaoLista.bend as I
import ./CodecAceitacaoRegistro.bend as G

type Caso<-bs: List<&2, U32>, -v: D.Valor, -n: Nat> is Type:
  Canonico{codificacao: P.Codificacao(v, bs)}
  Lista{numero: B.Numero64, xs: List<&2, S.ValorSegmentado>,
    bytes: {bs == M.prefixo(5, numero, S.bytes_valores(xs)) : List<&2, U32>},
    entrega: {A.entregar_valores(S.valores(xs), C.abrir_variavel(C.zero64(numero), C.ContaLista{}, numero, C.Raiz{})) == C.Pronto{v} : C.Maquina},
    filhos: H.FilhosLidos(xs, n),
    octetos: {B.octetos_validos(S.bytes_valores(xs)) == True{} : Bool}}
  Registro{numero: B.Numero64, xs: List<&2, S.CampoSegmentado>,
    bytes: {bs == M.prefixo(6, numero, S.bytes_campos(xs)) : List<&2, U32>},
    entrega: {A.entregar_campos(S.campos(xs), C.abrir_variavel(C.zero64(numero), C.ContaRegistro{}, numero, C.Raiz{})) == C.Pronto{v} : C.Maquina},
    campos: G.CamposLidos(xs, n),
    octetos: {B.octetos_validos(S.bytes_campos(xs)) == True{} : Bool}}

def ampliar_filho(-v: D.Valor, +bs: List<&2, U32>, +menor: Nat, +maior: Nat,
  limite: {Nat.is_le(menor, maior) == True{} : Bool},
  filho: H.FilhoLido<v, bs, menor>) -> H.FilhoLido<v, bs, maior>:
  match filho:
    case H.FilhoLido{corpo, teto, fora, local, bound}:
      H.FilhoLido{corpo, teto, fora, local,
        S.limite_transitivo(B.comprimento(bs), menor, maior, bound, limite)}

law ampliar_filhos:
  for xs: List<&2, S.ValorSegmentado>
  for +menor: Nat
  for +maior: Nat
  for +limite: {Nat.is_le(menor, maior) == True{} : Bool}
  for filhos: H.FilhosLidos(xs, menor)
  H.FilhosLidos(xs, maior)
def ampliar_filhos(xs, menor, maior, limite, filhos):
  match xs:
    case Nil{}:
      Unit{}
    case Con{S.ValorSegmentado{v, +bs}, +t}:
      L.Ambos{filho, cauda} = filhos
      L.Ambos{ampliar_filho(v, bs, menor, maior, limite, filho),
        ampliar_filhos(t, menor, maior, limite, cauda)}

law ampliar_campos:
  for xs: List<&2, S.CampoSegmentado>
  for +menor: Nat
  for +maior: Nat
  for +limite: {Nat.is_le(menor, maior) == True{} : Bool}
  for campos: G.CamposLidos(xs, menor)
  G.CamposLidos(xs, maior)
def ampliar_campos(xs, menor, maior, limite, campos):
  match xs:
    case Nil{}:
      Unit{}
    case Con{S.CampoSegmentado{nome, v, nb, +vb}, +t}:
      L.Ambos{valido, resto} = campos
      L.Ambos{canonico, lidos} = resto
      L.Ambos{filho, cauda} = lidos
      L.Ambos{valido, L.Ambos{canonico,
        L.Ambos{ampliar_filho(v, vb, menor, maior, limite, filho),
          ampliar_campos(t, menor, maior, limite, cauda)}}}

def preparar_lista_segmentada(+n: Nat, +bs: List<&2, U32>, +numero: B.Numero64,
  +payload: List<&2, U32>, -v: D.Valor,
  fatoracao: {Con{5, bs} == M.prefixo(5, numero, payload) : List<&2, U32>},
  limite: {Nat.is_le(B.comprimento(payload), n) == True{} : Bool},
  validos: {B.octetos_validos(payload) == True{} : Bool},
  segmentacao: I.Segmentacao<payload,
    C.abrir_variavel(C.zero64(numero), C.ContaLista{}, numero, C.Raiz{}), v, B.comprimento(payload)>) ->
  Caso<Con{5, bs}, v, n>:
  match segmentacao:
    case I.Segmentacao{+xs, +bytes, entrega, filhos}:
      Lista{numero, xs,
        Equal.trans(List<&2, U32>, Con{5, bs}, M.prefixo(5, numero, payload),
          M.prefixo(5, numero, S.bytes_valores(xs)), fatoracao,
          Equal.cong(List<&2, U32>, List<&2, U32>, t => M.prefixo(5, numero, t),
            payload, S.bytes_valores(xs), bytes)),
        entrega, ampliar_filhos(xs, B.comprimento(payload), n, limite, filhos),
        (%bytes : {B.octetos_validos(_) == True{} : Bool}
          validos)}

def preparar_registro_segmentado(+n: Nat, +bs: List<&2, U32>, +numero: B.Numero64,
  +payload: List<&2, U32>, -v: D.Valor,
  fatoracao: {Con{6, bs} == M.prefixo(6, numero, payload) : List<&2, U32>},
  limite: {Nat.is_le(B.comprimento(payload), n) == True{} : Bool},
  validos: {B.octetos_validos(payload) == True{} : Bool},
  segmentacao: G.Segmentacao<payload,
    C.abrir_variavel(C.zero64(numero), C.ContaRegistro{}, numero, C.Raiz{}), v, B.comprimento(payload)>) ->
  Caso<Con{6, bs}, v, n>:
  match segmentacao:
    case G.Segmentacao{+xs, +bytes, entrega, campos}:
      Registro{numero, xs,
        Equal.trans(List<&2, U32>, Con{6, bs}, M.prefixo(6, numero, payload),
          M.prefixo(6, numero, S.bytes_campos(xs)), fatoracao,
          Equal.cong(List<&2, U32>, List<&2, U32>, t => M.prefixo(6, numero, t),
            payload, S.bytes_campos(xs), bytes)),
        entrega, ampliar_campos(xs, B.comprimento(payload), n, limite, campos),
        (%bytes : {B.octetos_validos(_) == True{} : Bool}
          validos)}

def preparar_lista_extraida(+n: Nat, +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  limite: {Nat.is_le(B.comprimento(bs), n) == True{} : Bool},
  extraida: W.PalavraExtraida<bs, C.ContaLista{}, C.Raiz{}, corpo, teto, v>) -> Caso<Con{5, bs}, v, n>:
  match extraida:
    case W.Extraida{a, b, c, d, e, f0, g, h, +payload, +alto, +baixo,
      fatoracao, octetos, resto_valido, numero, be64, +fatoracao_be64, quadro, execucao, +pronto}:
      +q = {B.Numero64{alto, baixo} : B.Numero64}
      +cpost = K.diminuir(8n, corpo)
      +tpost = K.diminuir(8n, teto)
      cabe = Rz.conferencia_aceita_e_cabe(
        C.conferir(C.somar_opcionais(C.minimo_campo(C.ContaLista{}, q), C.minimo_pilha(C.Raiz{})), cpost, tpost),
        payload, cpost, tpost, C.ContaLista{}, q, C.Raiz{}, v, pronto)
      preparar_lista_segmentada(n, bs, q, payload, v,
        Equal.cong(List<&2, U32>, List<&2, U32>, t => Con{5, t}, bs,
          B.concatenar(B.be64(alto, baixo), payload), fatoracao_be64),
        H.limite_sufixo(B.be64(alto, baixo), payload, n,
          H.limite_de_bytes_iguais(bs, B.concatenar(B.be64(alto, baixo), payload), n, fatoracao_be64, limite)),
        resto_valido,
        I.lista_aceita_extrai_todos_os_filhos(payload, cpost, tpost, q, v,
          (%cabe : {R.maquina(R.executar(payload,
            R.Quadro{cpost, tpost, C.abrir_conferido(_, C.ContaLista{}, q, C.Raiz{})})) == C.Pronto{v} : C.Maquina}
            pronto)))

def preparar_registro_extraido(+n: Nat, +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  limite: {Nat.is_le(B.comprimento(bs), n) == True{} : Bool},
  extraida: W.PalavraExtraida<bs, C.ContaRegistro{}, C.Raiz{}, corpo, teto, v>) -> Caso<Con{6, bs}, v, n>:
  match extraida:
    case W.Extraida{a, b, c, d, e, f0, g, h, +payload, +alto, +baixo,
      fatoracao, octetos, +resto_valido, numero, be64, +fatoracao_be64, quadro, execucao, +pronto}:
      +q = {B.Numero64{alto, baixo} : B.Numero64}
      +cpost = K.diminuir(8n, corpo)
      +tpost = K.diminuir(8n, teto)
      cabe = Rz.conferencia_aceita_e_cabe(
        C.conferir(C.somar_opcionais(C.minimo_campo(C.ContaRegistro{}, q), C.minimo_pilha(C.Raiz{})), cpost, tpost),
        payload, cpost, tpost, C.ContaRegistro{}, q, C.Raiz{}, v, pronto)
      preparar_registro_segmentado(n, bs, q, payload, v,
        Equal.cong(List<&2, U32>, List<&2, U32>, t => Con{6, t}, bs,
          B.concatenar(B.be64(alto, baixo), payload), fatoracao_be64),
        H.limite_sufixo(B.be64(alto, baixo), payload, n,
          H.limite_de_bytes_iguais(bs, B.concatenar(B.be64(alto, baixo), payload), n, fatoracao_be64, limite)),
        resto_valido,
        G.registro_aceito_extrai_todos_os_campos(payload, cpost, tpost, q, v, resto_valido,
          (%cabe : {R.maquina(R.executar(payload,
            R.Quadro{cpost, tpost, C.abrir_conferido(_, C.ContaRegistro{}, q, C.Raiz{})})) == C.Pronto{v} : C.Maquina}
            pronto)))

def preparar_tag(tag: Nat, +n: Nat, +b: U32, +bs: List<&2, U32>,
  +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  igual: {U32.to_nat(b) == tag : Nat},
  limite: {Nat.is_le(B.comprimento(bs), n) == True{} : Bool},
  validos: {B.octetos_validos(bs) == True{} : Bool},
  +pronto: {R.maquina(R.executar(Con{b, bs}, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})) == C.Pronto{v} : C.Maquina}) ->
  Caso<Con{b, bs}, v, n>:
  match tag:
    case 0n:
      +byte = T.u32_to_nat_injetivo(b, 0, igual)
      %Equal.sym(U32, b, 0, byte) : Caso<Con{_, bs}, v, n>
      Canonico{U.atomo_com_percurso(U.Ausencia{}, bs, corpo, teto, v,
        Rz.execucao_pronta_tem_percurso_aceito(Con{0, bs}, corpo, teto, C.Tag{C.Raiz{}}, v,
          (%byte : {R.maquina(R.executar(Con{_, bs}, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})) == C.Pronto{v} : C.Maquina}
            pronto)))}
    case 1n:
      +byte = T.u32_to_nat_injetivo(b, 1, igual)
      %Equal.sym(U32, b, 1, byte) : Caso<Con{_, bs}, v, n>
      Canonico{U.atomo_com_percurso(U.Booleano{False{}}, bs, corpo, teto, v,
        Rz.execucao_pronta_tem_percurso_aceito(Con{1, bs}, corpo, teto, C.Tag{C.Raiz{}}, v,
          (%byte : {R.maquina(R.executar(Con{_, bs}, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})) == C.Pronto{v} : C.Maquina}
            pronto)))}
    case 2n:
      +byte = T.u32_to_nat_injetivo(b, 2, igual)
      %Equal.sym(U32, b, 2, byte) : Caso<Con{_, bs}, v, n>
      Canonico{U.atomo_com_percurso(U.Booleano{True{}}, bs, corpo, teto, v,
        Rz.execucao_pronta_tem_percurso_aceito(Con{2, bs}, corpo, teto, C.Tag{C.Raiz{}}, v,
          (%byte : {R.maquina(R.executar(Con{_, bs}, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})) == C.Pronto{v} : C.Maquina}
            pronto)))}
    case 3n:
      +byte = T.u32_to_nat_injetivo(b, 3, igual)
      %Equal.sym(U32, b, 3, byte) : Caso<Con{_, bs}, v, n>
      Canonico{Rz.inteiro_com_execucao_real_e_canonico(bs, C.diminuir64(corpo), C.diminuir64(teto), v, validos,
        (%byte : {R.maquina(R.executar(Con{_, bs}, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})) == C.Pronto{v} : C.Maquina}
          pronto))}
    case 4n:
      +byte = T.u32_to_nat_injetivo(b, 4, igual)
      %Equal.sym(U32, b, 4, byte) : Caso<Con{_, bs}, v, n>
      Canonico{Rz.texto_com_execucao_real_e_canonico(bs, C.diminuir64(corpo), C.diminuir64(teto), v,
        Rz.execucao_raiz_aceita_garante_valor_valido(Con{b, bs}, corpo, teto, v, pronto), validos,
        (%byte : {R.maquina(R.executar(Con{_, bs}, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})) == C.Pronto{v} : C.Maquina}
          pronto))}
    case 5n:
      +byte = T.u32_to_nat_injetivo(b, 5, igual)
      %Equal.sym(U32, b, 5, byte) : Caso<Con{_, bs}, v, n>
      preparar_lista_extraida(n, bs, C.diminuir64(corpo), C.diminuir64(teto), v, limite,
        W.palavra_aceita_extrai_be64_e_execucao_restante(bs, C.ContaLista{}, C.Raiz{},
          C.diminuir64(corpo), C.diminuir64(teto), v, validos,
          (%byte : {R.maquina(R.executar(Con{_, bs}, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})) == C.Pronto{v} : C.Maquina}
            pronto)))
    case 6n:
      +byte = T.u32_to_nat_injetivo(b, 6, igual)
      %Equal.sym(U32, b, 6, byte) : Caso<Con{_, bs}, v, n>
      preparar_registro_extraido(n, bs, C.diminuir64(corpo), C.diminuir64(teto), v, limite,
        W.palavra_aceita_extrai_be64_e_execucao_restante(bs, C.ContaRegistro{}, C.Raiz{},
          C.diminuir64(corpo), C.diminuir64(teto), v, validos,
          (%byte : {R.maquina(R.executar(Con{_, bs}, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})) == C.Pronto{v} : C.Maquina}
            pronto)))
    case 7n+p:
      L.ex_falso(Caso<Con{b, bs}, v, n>, R.entrada_nao_decodificada(v,
        Equal.trans(C.Resultado, C.Entrada{},
          C.percorrer(bs, C.diminuir64(corpo), C.diminuir64(teto), C.Invalido{}), C.Decodificado{v},
          Equal.sym(C.Resultado,
            C.percorrer(bs, C.diminuir64(corpo), C.diminuir64(teto), C.Invalido{}), C.Entrada{},
            R.invalido_absorve_todo_sufixo(bs, C.diminuir64(corpo), C.diminuir64(teto))),
          Rz.execucao_pronta_tem_percurso_aceito(bs, C.diminuir64(corpo), C.diminuir64(teto), C.Invalido{}, v,
            (%igual : {R.maquina(R.executar(bs,
              R.Quadro{C.diminuir64(corpo), C.diminuir64(teto), C.ler_tag(_, C.Raiz{})})) == C.Pronto{v} : C.Maquina}
              pronto)))))

# n e o predecessor do majorante da raiz. Todo filho extraido recebe esse
# mesmo n, inclusive quando o payload e vazio.
law preparar_raiz:
  for +n: Nat
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for -v: D.Valor
  for limite: {Nat.is_le(B.comprimento(bs), 1n+n) == True{} : Bool}
  for validos: {B.octetos_validos(bs) == True{} : Bool}
  for pronto: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})) == C.Pronto{v} : C.Maquina}
  Caso<bs, v, n>
def preparar_raiz(n, bs, corpo, teto, v, limite, validos, pronto):
  match bs:
    case Nil{}:
      L.ex_falso(Caso<Nil{}, v, n>, A.tag_nao_e_pronto(C.Raiz{}, v, pronto))
    case Con{+b, +t}:
      preparar_tag(U32.to_nat(b), n, b, t, corpo, teto, v, {==}, limite,
        F.e_booleano_direita(U32.is_le(b, 255), B.octetos_validos(t), validos), pronto)
