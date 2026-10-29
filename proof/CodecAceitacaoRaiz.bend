# Interfaces de soundness para a inducao: o percurso pode iniciar com
# quaisquer contadores. Validade e canonicidade nao sao novas premissas
# ocultas da API publica; a primeira e derivada do proprio percurso.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./Codec.bend as V
import ./CodecPercurso.bend as R
import ./CodecPalavrasBE64.bend as H
import ./CodecTextoAceito.bend as T
import ./CodecPrimitivos.bend as A
import ./CodecUTF8InversaTexto.bend as U
import ./CodecAceitacaoPalavra.bend as W

law execucao_pronta_tem_percurso_aceito:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +m: C.Maquina
  for -v: D.Valor
  for pronto: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, m})) == C.Pronto{v} : C.Maquina}
  {C.percorrer(bs, corpo, teto, m) == C.Decodificado{v} : C.Resultado}
def execucao_pronta_tem_percurso_aceito(bs, corpo, teto, m, v, pronto):
  Equal.trans(C.Resultado, C.percorrer(bs, corpo, teto, m), R.finalizar_quadro(R.executar(bs, R.Quadro{corpo, teto, m})), C.Decodificado{v},
    R.percurso_e_execucao_integral(bs, R.Quadro{corpo, teto, m}),
    Equal.cong(C.Maquina, C.Resultado, x => C.finalizar(x), R.maquina(R.executar(bs, R.Quadro{corpo, teto, m})), C.Pronto{v}, pronto))

law execucao_raiz_aceita_garante_valor_valido:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for -v: D.Valor
  for pronto: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})) == C.Pronto{v} : C.Maquina}
  {D.valor_valido(v) == True{} : Bool}
def execucao_raiz_aceita_garante_valor_valido(bs, corpo, teto, v, pronto):
  %execucao_pronta_tem_percurso_aceito(bs, corpo, teto, C.Tag{C.Raiz{}}, v, pronto) : V.ResultadoValido(_)
  V.percorrer_preserva_validade(bs, corpo, teto, C.Tag{C.Raiz{}}, Unit{})

law conferencia_aceita_e_cabe:
  for c: C.Conferencia
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +f: C.Finalidade
  for +n: B.Numero64
  for +p: C.Pilha
  for -v: D.Valor
  for pronto: {R.maquina(R.executar(bs, R.Quadro{corpo, teto, C.abrir_conferido(c, f, n, p)})) == C.Pronto{v} : C.Maquina}
  {c == C.Cabe{} : C.Conferencia}
def conferencia_aceita_e_cabe(c, bs, corpo, teto, f, n, p, v, pronto):
  match c:
    case C.Cabe{}:
      {==}
    case C.Curto{}:
      L.ex_falso({C.Curto{} == C.Cabe{} : C.Conferencia}, R.entrada_nao_decodificada(v,
        Equal.trans(C.Resultado, C.Entrada{}, C.percorrer(bs, corpo, teto, C.Invalido{}), C.Decodificado{v},
          Equal.sym(C.Resultado, C.percorrer(bs, corpo, teto, C.Invalido{}), C.Entrada{}, R.invalido_absorve_todo_sufixo(bs, corpo, teto)),
          execucao_pronta_tem_percurso_aceito(bs, corpo, teto, C.Invalido{}, v, pronto))))
    case C.Grande{}:
      L.ex_falso({C.Grande{} == C.Cabe{} : C.Conferencia}, R.limite_nao_decodificado(v,
        Equal.trans(C.Resultado, C.Limite{}, C.percorrer(bs, corpo, teto, C.Acima{}), C.Decodificado{v},
          Equal.sym(C.Resultado, C.percorrer(bs, corpo, teto, C.Acima{}), C.Limite{}, R.acima_absorve_todo_sufixo(bs, corpo, teto)),
          execucao_pronta_tem_percurso_aceito(bs, corpo, teto, C.Acima{}, v, pronto))))

def inteiro_extraido_e_canonico(+bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  extraido: W.PalavraExtraida<bs, C.Inteiro{}, C.Raiz{}, corpo, teto, v>) -> P.Codificacao(v, Con{3, bs}):
  match extraido:
    case W.Extraida{a, b, c, d, e, f0, g, h, +suf, +alto, +baixo, fatoracao, octetos, resto_valido, numero, be64, +fatoracao_be64, quadro, execucao, pronto}:
      F.com_par(P.Codificacao(v, Con{3, bs}), {suf == Nil{} : List<&2, U32>}, {v == D.VInt{alto, baixo} : D.Valor},
        A.pronto_aceito_exige_sufixo_vazio_e_valor_exato(suf, H.diminuir(8n, corpo), H.diminuir(8n, teto), D.VInt{alto, baixo}, v,
          execucao_pronta_tem_percurso_aceito(suf, H.diminuir(8n, corpo), H.diminuir(8n, teto), C.Pronto{D.VInt{alto, baixo}}, v, pronto)),
        fim => valor =>
          (%Equal.sym(D.Valor, v, D.VInt{alto, baixo}, valor) : P.Codificacao(_, Con{3, bs})
           %Equal.sym(List<&2, U32>, bs, B.concatenar(B.be64(alto, baixo), suf), fatoracao_be64) : P.Codificacao(D.VInt{alto, baixo}, Con{3, _})
           %Equal.sym(List<&2, U32>, suf, Nil{}, fim) : P.Codificacao(D.VInt{alto, baixo}, Con{3, B.concatenar(B.be64(alto, baixo), _)})
           %Equal.sym(List<&2, U32>, B.concatenar(B.be64(alto, baixo), Nil{}), B.be64(alto, baixo), U.concatenar_vazio_direita(B.be64(alto, baixo))) :
             P.Codificacao(D.VInt{alto, baixo}, Con{3, _})
           {==}))

law inteiro_com_execucao_real_e_canonico:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for -v: D.Valor
  for validos: {B.octetos_validos(bs) == True{} : Bool}
  for pronto: {R.maquina(R.executar(bs, W.inicio(C.Inteiro{}, C.Raiz{}, corpo, teto))) == C.Pronto{v} : C.Maquina}
  P.Codificacao(v, Con{3, bs})
def inteiro_com_execucao_real_e_canonico(bs, corpo, teto, v, validos, pronto):
  inteiro_extraido_e_canonico(bs, corpo, teto, v,
    W.palavra_aceita_extrai_be64_e_execucao_restante(bs, C.Inteiro{}, C.Raiz{}, corpo, teto, v, validos, pronto))

def texto_extraido_e_canonico(+bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64, -v: D.Valor,
  valido: {D.valor_valido(v) == True{} : Bool},
  extraido: W.PalavraExtraida<bs, C.Texto{}, C.Raiz{}, corpo, teto, v>) -> P.Codificacao(v, Con{4, bs}):
  match extraido:
    case W.Extraida{+a, +b, +c, +d, +e, +f0, +g, +h, +suf, alto, baixo, +fatoracao, +octetos, resto_valido, numero, be64, fatoracao_be64, quadro, execucao, pronto}:
      %Equal.sym(List<&2, U32>, bs, B.concatenar([a, b, c, d, e, f0, g, h], suf), fatoracao) : P.Codificacao(v, Con{4, _})
      T.recodificar_texto_com_cabecalho(a, b, c, d, e, f0, g, h, suf, v, valido, octetos,
        T.analisar_cabecalho_textual(a, b, c, d, e, f0, g, h, suf, corpo, teto, v, octetos,
          execucao_pronta_tem_percurso_aceito(B.concatenar([a, b, c, d, e, f0, g, h], suf), corpo, teto, C.Palavra{C.Texto{}, 7n, 0, 0, C.Raiz{}}, v,
            (%fatoracao : {R.maquina(R.executar(_, W.inicio(C.Texto{}, C.Raiz{}, corpo, teto))) == C.Pronto{v} : C.Maquina}
              Equal.trans(C.Maquina, R.maquina(R.executar(bs, W.inicio(C.Texto{}, C.Raiz{}, corpo, teto))),
                R.maquina(R.executar(suf, W.apos_palavra(C.Texto{}, alto, baixo, C.Raiz{}, corpo, teto))), C.Pronto{v},
                Equal.cong(R.Quadro, C.Maquina, q => R.maquina(q), R.executar(bs, W.inicio(C.Texto{}, C.Raiz{}, corpo, teto)),
                  R.executar(suf, W.apos_palavra(C.Texto{}, alto, baixo, C.Raiz{}, corpo, teto)),
                  Equal.sym(R.Quadro, R.executar(suf, W.apos_palavra(C.Texto{}, alto, baixo, C.Raiz{}, corpo, teto)),
                    R.executar(bs, W.inicio(C.Texto{}, C.Raiz{}, corpo, teto)), execucao)), pronto)))))

law texto_com_execucao_real_e_canonico:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for -v: D.Valor
  for valido: {D.valor_valido(v) == True{} : Bool}
  for validos: {B.octetos_validos(bs) == True{} : Bool}
  for pronto: {R.maquina(R.executar(bs, W.inicio(C.Texto{}, C.Raiz{}, corpo, teto))) == C.Pronto{v} : C.Maquina}
  P.Codificacao(v, Con{4, bs})
def texto_com_execucao_real_e_canonico(bs, corpo, teto, v, valido, validos, pronto):
  texto_extraido_e_canonico(bs, corpo, teto, v, valido,
    W.palavra_aceita_extrai_be64_e_execucao_restante(bs, C.Texto{}, C.Raiz{}, corpo, teto, v, validos, pronto))
