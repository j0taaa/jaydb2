# Extracao da primeira emissao do Conteudo real, antes de executar o sufixo.
# A pilha e arbitraria: emitir_texto pode fechar varios ancestrais.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecContadores.bend as N
import ./CodecConteudo.bend as G
import ./CodecUTF8.bend as U
import ./CodecUTF8InversaTexto.bend as I
import ./CodecPercurso.bend as R

def pronto(m: C.Maquina) -> Bool:
  match m:
    case C.Pronto{v}:
      True{}
    case _:
      False{}

def invalido_nao_termina_pronto(-A: Type, +bs: List<&2, U32>,
  +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.Invalido{}})) == C.Pronto{v} : C.Maquina}) -> A:
  L.ex_falso(A, F.falso_nao_verdadeiro(Equal.cong(C.Maquina, Bool, m => pronto(m), C.Invalido{}, C.Pronto{v},
    Equal.trans(C.Maquina, C.Invalido{}, R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.Invalido{}})), C.Pronto{v},
      Equal.sym(C.Maquina, R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.Invalido{}})), C.Invalido{},
        G.executar_invalido_permanece_invalido(bs, corpo, teto)), aceito))))

# n conta os bytes ANTERIORES ao byte que emite. O teste do ultimo byte
# e extraido da execucao, inclusive quando o estado inicial nao e normalizado.
def ultimos_antes(n: Nat, ultimo: Bool, +q: B.Numero64) -> Bool:
  match n:
    case 0n:
      ultimo
    case 1n+p:
      Bool.not(ultimo) && ultimos_antes(p, C.um64(q), C.diminuir64(q))

law ultimos_antes_reconstituem_o_protocolo_contado:
  for n: Nat
  for +q: B.Numero64
  {ultimos_antes(n, C.um64(q), C.diminuir64(q)) == N.ultimos(1n+n, q) : Bool}
def ultimos_antes_reconstituem_o_protocolo_contado(n, q):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Bool, Bool, r => Bool.not(C.um64(q)) && r,
        ultimos_antes(p, C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q))), N.ultimos(1n+p, C.diminuir64(q)),
        ultimos_antes_reconstituem_o_protocolo_contado(p, C.diminuir64(q)))

# Snapshot imediatamente ANTES da emissao. Nao presume que a emissao
# produz Pronto nem que o sufixo e vazio. O escalar final e isolado.
type EmissaoConteudo<-bs: List<&2, U32>, -corpo: B.Numero64, -teto: B.Numero64,
  -nome: Bool, -ultimo: Bool, -q: B.Numero64, -u: C.Unicode,
  -invertido: String, -pilha: C.Pilha, -v: D.Valor> is Type:
  EmissaoConteudo{antes: List<&2, U32>, byte: U32, sufixo: List<&2, U32>,
    corpo_antes: B.Numero64, teto_antes: B.Numero64, q_antes: B.Numero64,
    unicode_antes: C.Unicode, invertido_antes: String, codigo: U32,
    divisao: {bs == B.concatenar(antes, Con{byte, sufixo}) : List<&2, U32>},
    contagem: {ultimos_antes(B.comprimento(antes), ultimo, q) == True{} : Bool},
    snapshot: {R.executar(antes, R.Quadro{corpo, teto, C.Conteudo{nome, ultimo, q, u, invertido, pilha}}) ==
      R.Quadro{corpo_antes, teto_antes, C.Conteudo{nome, True{}, q_antes, unicode_antes, invertido_antes, pilha}} : R.Quadro},
    escalar: {C.passo_utf8(unicode_antes, byte) == C.Caractere{codigo} : C.Escalar},
    transducao: {U.percorrer_texto(antes, U.Lendo{u, invertido}) == U.Lendo{unicode_antes, invertido_antes} : U.Texto},
    continuacao: {R.maquina(R.executar(sufixo,
      R.Quadro{C.diminuir64(corpo_antes), C.diminuir64(teto_antes),
        C.emitir_texto(nome, String.reverse(SCon{Chr{codigo}, invertido_antes}), pilha)})) == C.Pronto{v} : C.Maquina}}

# Acrescenta um byte que ainda nao emitiu, conservando o snapshot e a
# continuacao obtidos pela hipotese de inducao sobre a cauda dos bytes.
def preceder_emissao(+b: U32, +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64,
  +nome: Bool, +q: B.Numero64, +u: C.Unicode, +invertido: String, +pilha: C.Pilha,
  +proximo: C.Unicode, +texto: String, -v: D.Valor,
  passo: {C.guardar_escalar(C.passo_utf8(u, b), False{}, nome, q, invertido, pilha) ==
    C.Conteudo{nome, C.um64(q), C.diminuir64(q), proximo, texto, pilha} : C.Maquina},
  transicao: {U.passo_texto(U.Lendo{u, invertido}, b) == U.Lendo{proximo, texto} : U.Texto},
  emissao: EmissaoConteudo<bs, C.diminuir64(corpo), C.diminuir64(teto), nome,
    C.um64(q), C.diminuir64(q), proximo, texto, pilha, v>) ->
  EmissaoConteudo<Con{b, bs}, corpo, teto, nome, False{}, q, u, invertido, pilha, v>:
  match emissao:
    case EmissaoConteudo{+antes, +byte, +sufixo, +ca, +ta, +qa, +ua, +ia, +cp,
      divisao, contagem, snapshot, escalar, transducao, continuacao}:
      EmissaoConteudo{Con{b, antes}, byte, sufixo, ca, ta, qa, ua, ia, cp,
        Equal.cong(List<&2, U32>, List<&2, U32>, r => Con{b, r}, bs, B.concatenar(antes, Con{byte, sufixo}), divisao),
        contagem,
        (%Equal.sym(C.Maquina,
          C.guardar_escalar(C.passo_utf8(u, b), False{}, nome, q, invertido, pilha),
          C.Conteudo{nome, C.um64(q), C.diminuir64(q), proximo, texto, pilha}, passo) :
          {R.executar(antes, R.Quadro{C.diminuir64(corpo), C.diminuir64(teto), _}) ==
            R.Quadro{ca, ta, C.Conteudo{nome, True{}, qa, ua, ia, pilha}} : R.Quadro}
          snapshot),
        escalar,
        (%Equal.sym(U.Texto, U.passo_texto(U.Lendo{u, invertido}, b), U.Lendo{proximo, texto}, transicao) :
          {U.percorrer_texto(antes, _) == U.Lendo{ua, ia} : U.Texto}
          transducao),
        continuacao}

def extrair_passo_conteudo(+e: C.Escalar, ultimo: Bool,
  +b: U32, +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64,
  +nome: Bool, +q: B.Numero64, +u: C.Unicode, +invertido: String, +pilha: C.Pilha, -v: D.Valor,
  +escalar: {C.passo_utf8(u, b) == e : C.Escalar},
  aceito: {R.maquina(R.executar(bs, R.Quadro{C.diminuir64(corpo), C.diminuir64(teto),
    C.guardar_escalar(e, ultimo, nome, q, invertido, pilha)})) == C.Pronto{v} : C.Maquina},
  continuar: @proximo: C.Unicode -> @texto: String ->
    {R.maquina(R.executar(bs, R.Quadro{C.diminuir64(corpo), C.diminuir64(teto),
      C.Conteudo{nome, C.um64(q), C.diminuir64(q), proximo, texto, pilha}})) == C.Pronto{v} : C.Maquina} ->
    EmissaoConteudo<bs, C.diminuir64(corpo), C.diminuir64(teto), nome,
      C.um64(q), C.diminuir64(q), proximo, texto, pilha, v>) ->
  EmissaoConteudo<Con{b, bs}, corpo, teto, nome, ultimo, q, u, invertido, pilha, v>:
  match e ultimo:
    case C.UTFInvalido{} +ultimo:
      invalido_nao_termina_pronto(EmissaoConteudo<Con{b, bs}, corpo, teto, nome, ultimo, q, u, invertido, pilha, v>,
        bs, C.diminuir64(corpo), C.diminuir64(teto), v, aceito)
    case C.Parcial{proximo} True{}:
      invalido_nao_termina_pronto(EmissaoConteudo<Con{b, bs}, corpo, teto, nome, True{}, q, u, invertido, pilha, v>,
        bs, C.diminuir64(corpo), C.diminuir64(teto), v, aceito)
    case C.Caractere{+cp} True{}:
      EmissaoConteudo{[], b, bs, corpo, teto, q, u, invertido, cp, {==}, {==}, {==}, escalar, {==}, aceito}
    case C.Caractere{+cp} False{}:
      preceder_emissao(b, bs, corpo, teto, nome, q, u, invertido, pilha, C.Inicio{}, SCon{Chr{cp}, invertido}, v,
        Equal.cong(C.Escalar, C.Maquina, x => C.guardar_escalar(x, False{}, nome, q, invertido, pilha),
          C.passo_utf8(u, b), C.Caractere{cp}, escalar),
        Equal.cong(C.Escalar, U.Texto, x => U.juntar(x, invertido), C.passo_utf8(u, b), C.Caractere{cp}, escalar),
        continuar(C.Inicio{}, SCon{Chr{cp}, invertido}, aceito))
    case C.Parcial{+proximo} False{}:
      preceder_emissao(b, bs, corpo, teto, nome, q, u, invertido, pilha, proximo, invertido, v,
        Equal.cong(C.Escalar, C.Maquina, x => C.guardar_escalar(x, False{}, nome, q, invertido, pilha),
          C.passo_utf8(u, b), C.Parcial{proximo}, escalar),
        Equal.cong(C.Escalar, U.Texto, x => U.juntar(x, invertido), C.passo_utf8(u, b), C.Parcial{proximo}, escalar),
        continuar(proximo, invertido, aceito))

law execucao_conteudo_aceita_isola_a_emissao:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +nome: Bool
  for +ultimo: Bool
  for +q: B.Numero64
  for +u: C.Unicode
  for +invertido: String
  for +pilha: C.Pilha
  for -v: D.Valor
  for aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto,
    C.Conteudo{nome, ultimo, q, u, invertido, pilha}})) == C.Pronto{v} : C.Maquina}
  EmissaoConteudo<bs, corpo, teto, nome, ultimo, q, u, invertido, pilha, v>
def execucao_conteudo_aceita_isola_a_emissao(bs, corpo, teto, nome, ultimo, q, u, invertido, pilha, v, aceito):
  match bs:
    case Nil{}:
      L.ex_falso(EmissaoConteudo<Nil{}, corpo, teto, nome, ultimo, q, u, invertido, pilha, v>,
        F.falso_nao_verdadeiro(Equal.cong(C.Maquina, Bool, m => pronto(m),
          C.Conteudo{nome, ultimo, q, u, invertido, pilha}, C.Pronto{v}, aceito)))
    case Con{+b, +tail}:
      extrair_passo_conteudo(C.passo_utf8(u, b), ultimo, b, tail, corpo, teto, nome, q, u, invertido, pilha, v, {==}, aceito,
        proximo => texto => aceita_cauda => execucao_conteudo_aceita_isola_a_emissao(tail,
          C.diminuir64(corpo), C.diminuir64(teto), nome, C.um64(q), C.diminuir64(q), proximo, texto, pilha, v, aceita_cauda))

law comprimento_ate_o_byte_final:
  for +antes: List<&2, U32>
  for +byte: U32
  {B.comprimento(B.concatenar(antes, [byte])) == 1n+B.comprimento(antes) : Nat}
def comprimento_ate_o_byte_final(antes, byte):
  match antes:
    case Nil{}:
      {==}
    case Con{h, +t}:
      Equal.cong(Nat, Nat, n => 1n+n, B.comprimento(B.concatenar(t, [byte])), 1n+B.comprimento(t),
        comprimento_ate_o_byte_final(t, byte))

law dividir_antes_e_depois_do_byte_final:
  for antes: List<&2, U32>
  for +byte: U32
  for +sufixo: List<&2, U32>
  {B.concatenar(antes, Con{byte, sufixo}) == B.concatenar(B.concatenar(antes, [byte]), sufixo) : List<&2, U32>}
def dividir_antes_e_depois_do_byte_final(antes, byte, sufixo):
  match antes:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, bs => Con{h, bs},
        B.concatenar(t, Con{byte, sufixo}), B.concatenar(B.concatenar(t, [byte]), sufixo),
        dividir_antes_e_depois_do_byte_final(t, byte, sufixo))

def prefixo_ate_o_byte_final_tem_bytes(antes: List<&2, U32>, byte: U32) -> G.NaoVazio(B.concatenar(antes, [byte])):
  match antes:
    case Nil{}:
      Unit{}
    case Con{h, t}:
      Unit{}

law transducao_textual_de_concatenacao:
  for xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +t: U.Texto
  {U.percorrer_texto(B.concatenar(xs, ys), t) == U.percorrer_texto(ys, U.percorrer_texto(xs, t)) : U.Texto}
def transducao_textual_de_concatenacao(xs, ys, t):
  match xs:
    case Nil{}:
      {==}
    case Con{b, tail}:
      transducao_textual_de_concatenacao(tail, ys, U.passo_texto(t, b))

def protocolo_conteudo(n: Nat, ultimo: Bool, q: B.Numero64) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      ultimos_antes(p, ultimo, q)

law protocolo_conteudo_normalizado_reconstitui_ultimos:
  for n: Nat
  for +q: B.Numero64
  {protocolo_conteudo(n, C.um64(q), C.diminuir64(q)) == N.ultimos(n, q) : Bool}
def protocolo_conteudo_normalizado_reconstitui_ultimos(n, q):
  match n:
    case 0n:
      {==}
    case 1n+p:
      ultimos_antes_reconstituem_o_protocolo_contado(p, q)

law protocolo_conteudo_aceito_reconstroi_contagem_original:
  for +conteudo: List<&2, U32>
  for +q: B.Numero64
  for conferido: {protocolo_conteudo(B.comprimento(conteudo), C.um64(q), C.diminuir64(q)) == True{} : Bool}
  {B.nat64(B.comprimento(conteudo)) == Some{q} : Maybe<&2, B.Numero64>}
def protocolo_conteudo_aceito_reconstroi_contagem_original(conteudo, q, conferido):
  N.ultimos_aceitos_reconstroem_a_contagem_original(B.comprimento(conteudo), q,
    Equal.trans(Bool, N.ultimos(B.comprimento(conteudo), q),
      protocolo_conteudo(B.comprimento(conteudo), C.um64(q), C.diminuir64(q)), True{},
      Equal.sym(Bool, protocolo_conteudo(B.comprimento(conteudo), C.um64(q), C.diminuir64(q)),
        N.ultimos(B.comprimento(conteudo), q), protocolo_conteudo_normalizado_reconstitui_ultimos(B.comprimento(conteudo), q)), conferido))

# Forma utilizavel pelo soundness: bytes do conteudo, texto recodificado,
# quadro apos emitir_texto e execucao do sufixo sao testemunhas conjuntas.
# ultimo/q continuam arbitrarios; o protocolo e uma CONCLUSAO da aceitacao.
type PrefixoTextoAceito<-bs: List<&2, U32>, -corpo: B.Numero64, -teto: B.Numero64,
  -nome: Bool, -ultimo: Bool, -q: B.Numero64, -pilha: C.Pilha, -v: D.Valor> is Type:
  PrefixoTextoAceito{conteudo: List<&2, U32>, sufixo: List<&2, U32>, texto: String,
    corpo_emissao: B.Numero64, teto_emissao: B.Numero64,
    divisao: {bs == B.concatenar(conteudo, sufixo) : List<&2, U32>},
    positivo: G.NaoVazio(conteudo),
    bytes: {B.utf8(texto) == conteudo : List<&2, U32>},
    transducao: {U.finalizar_texto(U.percorrer_texto(conteudo, U.Lendo{C.Inicio{}, ""})) == Some{texto} : Maybe<&2, String>},
    protocolo: {protocolo_conteudo(B.comprimento(conteudo), ultimo, q) == True{} : Bool},
    emissao: {R.executar(conteudo, R.Quadro{corpo, teto, C.Conteudo{nome, ultimo, q, C.Inicio{}, "", pilha}}) ==
      R.Quadro{corpo_emissao, teto_emissao, C.emitir_texto(nome, texto, pilha)} : R.Quadro},
    continuacao: {R.maquina(R.executar(sufixo,
      R.Quadro{corpo_emissao, teto_emissao, C.emitir_texto(nome, texto, pilha)})) == C.Pronto{v} : C.Maquina}}

def transducao_ate_emissao(+antes: List<&2, U32>, +byte: U32,
  +u: C.Unicode, +invertido: String, +cp: U32,
  transducao: {U.percorrer_texto(antes, U.Lendo{C.Inicio{}, ""}) == U.Lendo{u, invertido} : U.Texto},
  escalar: {C.passo_utf8(u, byte) == C.Caractere{cp} : C.Escalar}) ->
  {U.finalizar_texto(U.percorrer_texto(B.concatenar(antes, [byte]), U.Lendo{C.Inicio{}, ""})) ==
    Some{String.reverse(SCon{Chr{cp}, invertido})} : Maybe<&2, String>}:
  %Equal.sym(U.Texto, U.percorrer_texto(B.concatenar(antes, [byte]), U.Lendo{C.Inicio{}, ""}),
    U.percorrer_texto([byte], U.percorrer_texto(antes, U.Lendo{C.Inicio{}, ""})),
    transducao_textual_de_concatenacao(antes, [byte], U.Lendo{C.Inicio{}, ""})) :
    {U.finalizar_texto(_) == Some{String.reverse(SCon{Chr{cp}, invertido})} : Maybe<&2, String>}
  %Equal.sym(U.Texto, U.percorrer_texto(antes, U.Lendo{C.Inicio{}, ""}), U.Lendo{u, invertido}, transducao) :
    {U.finalizar_texto(U.percorrer_texto([byte], _)) == Some{String.reverse(SCon{Chr{cp}, invertido})} : Maybe<&2, String>}
  Equal.cong(C.Escalar, Maybe<&2, String>, e => U.finalizar_texto(U.juntar(e, invertido)),
    C.passo_utf8(u, byte), C.Caractere{cp}, escalar)

def executar_ate_emissao(+antes: List<&2, U32>, +byte: U32,
  +corpo: B.Numero64, +teto: B.Numero64, +nome: Bool, +ultimo: Bool, +q: B.Numero64, +pilha: C.Pilha,
  +ca: B.Numero64, +ta: B.Numero64, +qa: B.Numero64, +ua: C.Unicode, +ia: String, +cp: U32,
  snapshot: {R.executar(antes, R.Quadro{corpo, teto, C.Conteudo{nome, ultimo, q, C.Inicio{}, "", pilha}}) ==
    R.Quadro{ca, ta, C.Conteudo{nome, True{}, qa, ua, ia, pilha}} : R.Quadro},
  escalar: {C.passo_utf8(ua, byte) == C.Caractere{cp} : C.Escalar}) ->
  {R.executar(B.concatenar(antes, [byte]), R.Quadro{corpo, teto, C.Conteudo{nome, ultimo, q, C.Inicio{}, "", pilha}}) ==
    R.Quadro{C.diminuir64(ca), C.diminuir64(ta), C.emitir_texto(nome, String.reverse(SCon{Chr{cp}, ia}), pilha)} : R.Quadro}:
  %Equal.sym(R.Quadro,
    R.executar(B.concatenar(antes, [byte]), R.Quadro{corpo, teto, C.Conteudo{nome, ultimo, q, C.Inicio{}, "", pilha}}),
    R.executar([byte], R.executar(antes, R.Quadro{corpo, teto, C.Conteudo{nome, ultimo, q, C.Inicio{}, "", pilha}})),
    R.execucao_de_concatenacao(antes, [byte], R.Quadro{corpo, teto, C.Conteudo{nome, ultimo, q, C.Inicio{}, "", pilha}})) :
    {_ == R.Quadro{C.diminuir64(ca), C.diminuir64(ta), C.emitir_texto(nome, String.reverse(SCon{Chr{cp}, ia}), pilha)} : R.Quadro}
  %Equal.sym(R.Quadro,
    R.executar(antes, R.Quadro{corpo, teto, C.Conteudo{nome, ultimo, q, C.Inicio{}, "", pilha}}),
    R.Quadro{ca, ta, C.Conteudo{nome, True{}, qa, ua, ia, pilha}}, snapshot) :
    {R.executar([byte], _) == R.Quadro{C.diminuir64(ca), C.diminuir64(ta), C.emitir_texto(nome, String.reverse(SCon{Chr{cp}, ia}), pilha)} : R.Quadro}
  Equal.cong(C.Escalar, R.Quadro,
    e => R.Quadro{C.diminuir64(ca), C.diminuir64(ta), C.guardar_escalar(e, True{}, nome, qa, ia, pilha)},
    C.passo_utf8(ua, byte), C.Caractere{cp}, escalar)

def recodificar_emissao(+bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64,
  +nome: Bool, +ultimo: Bool, +q: B.Numero64, +pilha: C.Pilha, -v: D.Valor,
  evento: EmissaoConteudo<bs, corpo, teto, nome, ultimo, q, C.Inicio{}, "", pilha, v>) ->
  PrefixoTextoAceito<bs, corpo, teto, nome, ultimo, q, pilha, v>:
  match evento:
    case EmissaoConteudo{+antes, +byte, +sufixo, +ca, +ta, +qa, +ua, +ia, +cp,
      divisao, contagem, snapshot, +escalar, transducao, continuacao}:
      +conteudo = B.concatenar(antes, [byte])
      +texto = String.reverse(SCon{Chr{cp}, ia})
      +transduzido = transducao_ate_emissao(antes, byte, ua, ia, cp, transducao, escalar)
      PrefixoTextoAceito{conteudo, sufixo, texto, C.diminuir64(ca), C.diminuir64(ta),
        Equal.trans(List<&2, U32>, bs, B.concatenar(antes, Con{byte, sufixo}), B.concatenar(conteudo, sufixo),
          divisao, dividir_antes_e_depois_do_byte_final(antes, byte, sufixo)),
        prefixo_ate_o_byte_final_tem_bytes(antes, byte),
        I.utf8_entrada_aceita_recodifica_exatamente(conteudo, texto, transduzido), transduzido,
        (%Equal.sym(Nat, B.comprimento(conteudo), 1n+B.comprimento(antes), comprimento_ate_o_byte_final(antes, byte)) :
          {protocolo_conteudo(_, ultimo, q) == True{} : Bool}
          contagem),
        executar_ate_emissao(antes, byte, corpo, teto, nome, ultimo, q, pilha, ca, ta, qa, ua, ia, cp, snapshot, escalar),
        continuacao}

law conteudo_aceito_extrai_prefixo_textual:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +nome: Bool
  for +ultimo: Bool
  for +q: B.Numero64
  for +pilha: C.Pilha
  for -v: D.Valor
  for aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto,
    C.Conteudo{nome, ultimo, q, C.Inicio{}, "", pilha}})) == C.Pronto{v} : C.Maquina}
  PrefixoTextoAceito<bs, corpo, teto, nome, ultimo, q, pilha, v>
def conteudo_aceito_extrai_prefixo_textual(bs, corpo, teto, nome, ultimo, q, pilha, v, aceito):
  recodificar_emissao(bs, corpo, teto, nome, ultimo, q, pilha, v,
    execucao_conteudo_aceita_isola_a_emissao(bs, corpo, teto, nome, ultimo, q, C.Inicio{}, "", pilha, v, aceito))

# q e a contagem ORIGINAL do cabecalho, nao uma medida presumida.
# O protocolo reconstruido acima demonstra que nat64 do conteudo e Some q.
type ConteudoContadoAceito<-bs: List<&2, U32>, -corpo: B.Numero64, -teto: B.Numero64,
  -nome: Bool, -q: B.Numero64, -pilha: C.Pilha, -v: D.Valor> is Type:
  ConteudoContadoAceito{conteudo: List<&2, U32>, sufixo: List<&2, U32>, texto: String,
    corpo_emissao: B.Numero64, teto_emissao: B.Numero64,
    divisao: {bs == B.concatenar(conteudo, sufixo) : List<&2, U32>},
    positivo: G.NaoVazio(conteudo),
    bytes: {B.utf8(texto) == conteudo : List<&2, U32>},
    medida: {B.nat64(B.comprimento(conteudo)) == Some{q} : Maybe<&2, B.Numero64>},
    transducao: {U.finalizar_texto(U.percorrer_texto(conteudo, U.Lendo{C.Inicio{}, ""})) == Some{texto} : Maybe<&2, String>},
    emissao: {R.executar(conteudo, R.Quadro{corpo, teto,
      C.Conteudo{nome, C.um64(q), C.diminuir64(q), C.Inicio{}, "", pilha}}) ==
      R.Quadro{corpo_emissao, teto_emissao, C.emitir_texto(nome, texto, pilha)} : R.Quadro},
    continuacao: {R.maquina(R.executar(sufixo,
      R.Quadro{corpo_emissao, teto_emissao, C.emitir_texto(nome, texto, pilha)})) == C.Pronto{v} : C.Maquina}}

def medir_prefixo_extraido(-bs: List<&2, U32>, -corpo: B.Numero64, -teto: B.Numero64,
  -nome: Bool, +q: B.Numero64, -pilha: C.Pilha, -v: D.Valor,
  extraido: PrefixoTextoAceito<bs, corpo, teto, nome, C.um64(q), C.diminuir64(q), pilha, v>) ->
  ConteudoContadoAceito<bs, corpo, teto, nome, q, pilha, v>:
  match extraido:
    case PrefixoTextoAceito{+conteudo, sufixo, texto, ca, ta, divisao, positivo, bytes, transducao, protocolo, emissao, continuacao}:
      ConteudoContadoAceito{conteudo, sufixo, texto, ca, ta, divisao, positivo, bytes,
        protocolo_conteudo_aceito_reconstroi_contagem_original(conteudo, q, protocolo), transducao, emissao, continuacao}

law conteudo_contado_aceito_reconstroi_prefixo_texto_e_contagem:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +nome: Bool
  for +q: B.Numero64
  for +pilha: C.Pilha
  for -v: D.Valor
  for aceito: {R.maquina(R.executar(bs, R.Quadro{corpo, teto,
    C.Conteudo{nome, C.um64(q), C.diminuir64(q), C.Inicio{}, "", pilha}})) == C.Pronto{v} : C.Maquina}
  ConteudoContadoAceito<bs, corpo, teto, nome, q, pilha, v>
def conteudo_contado_aceito_reconstroi_prefixo_texto_e_contagem(bs, corpo, teto, nome, q, pilha, v, aceito):
  medir_prefixo_extraido(bs, corpo, teto, nome, q, pilha, v,
    conteudo_aceito_extrai_prefixo_textual(bs, corpo, teto, nome, C.um64(q), C.diminuir64(q), pilha, v, aceito))
