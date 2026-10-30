# Autenticacao e admissao do mesmo protocolo gerado. As denotacoes sao as
# declaracoes fechadas checadas; a ordem dos fatos e demonstrada aqui.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Interface.bend as I
import ../contrato/LAWS.bend as K
import ../contrato/Logica.bend as L
import ../contrato/Protocolo.bend as P
import ../contrato/Semantica.bend as S
import ../contrato/Recursos.bend as X
import ../src/Nucleo.bend as N
import ./FonteServico.bend as Fonte
import ./RotasServico.bend as R
import ./ProtocoloServico.bend as Q
import ./PrimitivasServico.bend as M
import ./Lei5Servico.bend as Cinco
import ./Fundamentos.bend as F
import ./Chamada.bend as Chamada
import ./Publicacao.bend as Publicacao
import ../src/Configuracao.bend as Config
import ./CenariosServico.bend as Cenarios
import ./HistoricoServico.bend as Historico
import ./ModeloServico.bend as Modelo
import ./CodecSomas.bend as A

# Conteudo separado de cronologia: nao e uma Regra3/4 recebida.
def Conteudo(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado,
  +origem: Fonte.JuizoSintatico, q: Q.Quadro) -> Type:
  match q:
    case Q.Autenticada{r, ctx}: {ctx == D.autenticar(s, I.credencial(r)) : Maybe<&2, D.Contexto>}
    case Q.Aceita{r, ctx}: I.CertificadoValido(Fonte.ambiente(fonte), c, r, ctx, Fonte.programa(fonte, origem))
    case Q.Rejeitada{r, ctx}: I.SemCertificado(Fonte.ambiente(fonte), c, r, ctx)
    case Q.Comecada{r, ctx}: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}
    case _: Unit

def Antes(-xs: List<&2, Q.Quadro>, -t: Nat, -q: Q.Quadro) -> Type:
  &u: Nat -> L.E<{Nat.is_lt(u, t) == True{} : Bool}, {Q.consultar(xs, u) == Some{q} : Maybe<&2, Q.Quadro>}>

def Ordem(-xs: List<&2, Q.Quadro>, -t: Nat, q: Q.Quadro) -> Type:
  match q:
    case Q.Autenticada{r, ctx}: Antes(xs, t, Q.Recebida{r})
    case Q.Aceita{r, ctx}: Antes(xs, t, Q.Autenticada{r, Some{ctx}})
    case Q.Rejeitada{r, ctx}: Antes(xs, t, Q.Autenticada{r, Some{ctx}})
    case Q.Comecada{r, ctx}: L.E<Antes(xs, t, Q.Autenticada{r, Some{ctx}}), Antes(xs, t, Q.Aceita{r, ctx})>
    case _: Unit

def Dados(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado,
  +origem: Fonte.JuizoSintatico, -xs: List<&2, Q.Quadro>, -t: Nat, +q: Q.Quadro) -> Type:
  L.E<Conteudo(fonte, c, s, origem, q), Ordem(xs, t, q)>

def Validacao(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado,
  +origem: Fonte.JuizoSintatico, +xs: List<&2, Q.Quadro>) -> Type:
  @t: Nat -> @q: Q.Quadro -> {Q.consultar(xs, t) == Some{q} : Maybe<&2, Q.Quadro>} -> Dados(fonte, c, s, origem, xs, t, q)

def neutra(q: Q.Quadro) -> Bool:
  match q:
    case Q.Autenticada{r, ctx}: False{}
    case Q.Aceita{r, ctx}: False{}
    case Q.Rejeitada{r, ctx}: False{}
    case Q.Comecada{r, ctx}: False{}
    case _: True{}

def Neutras(xs: List<&2, Q.Quadro>) -> Type:
  match xs:
    case Nil{}: Unit
    case Con{h, t}: L.E<{neutra(h) == True{} : Bool}, Neutras(t)>

def neutras_concatenadas(+xs: List<&2, Q.Quadro>, -ys: List<&2, Q.Quadro>, a: Neutras(xs), b: Neutras(ys)) -> Neutras(Q.concatenar(xs, ys)):
  match xs a:
    case Nil{} _: b
    case Con{h, t} L.Ambos{cabeca, cauda}: L.Ambos{cabeca, neutras_concatenadas(t, ys, cauda, b)}

def consulta_prefixo(+xs: List<&2, Q.Quadro>, -ys: List<&2, Q.Quadro>, +t: Nat, -q: Q.Quadro,
  presente: {Q.consultar(xs, t) == Some{q} : Maybe<&2, Q.Quadro>}) -> {Q.consultar(Q.concatenar(xs, ys), t) == Some{q} : Maybe<&2, Q.Quadro>}:
  F.com_par({Q.consultar(Q.concatenar(xs, ys), t) == Some{q} : Maybe<&2, Q.Quadro>},
    {Q.consultar(xs, t) == Some{q} : Maybe<&2, Q.Quadro>}, {Q.consultar(xs, t) == Some{q} : Maybe<&2, Q.Quadro>},
    Q.igualdade_reabrivel(Maybe<&2, Q.Quadro>, Q.consultar(xs, t), Some{q}, presente), uma => duas =>
      Equal.trans(Maybe<&2, Q.Quadro>, Q.consultar(Q.concatenar(xs, ys), t), Q.consultar(xs, t), Some{q},
        Q.consultar_dentro_prefixo(xs, ys, t, Q.posicao_presente_dentro(xs, t, q, uma)), duas))

def antes_prefixo(+xs: List<&2, Q.Quadro>, -ys: List<&2, Q.Quadro>, -t: Nat, -q: Q.Quadro, antes: Antes(xs, t, q)) -> Antes(Q.concatenar(xs, ys), t, q):
  match antes:
    case (+u, L.Ambos{ordem, consulta}): (u, L.Ambos{ordem, consulta_prefixo(xs, ys, u, q, consulta)})

def ordem_prefixo(+xs: List<&2, Q.Quadro>, -ys: List<&2, Q.Quadro>, -t: Nat, q: Q.Quadro, ordem: Ordem(xs, t, q)) -> Ordem(Q.concatenar(xs, ys), t, q):
  match q:
    case Q.Autenticada{r, ctx}: antes_prefixo(xs, ys, t, Q.Recebida{r}, ordem)
    case Q.Aceita{r, ctx}: antes_prefixo(xs, ys, t, Q.Autenticada{r, Some{ctx}}, ordem)
    case Q.Rejeitada{r, ctx}: antes_prefixo(xs, ys, t, Q.Autenticada{r, Some{ctx}}, ordem)
    case Q.Comecada{r, ctx}:
      match ordem:
        case L.Ambos{aut, cert}: L.Ambos{antes_prefixo(xs, ys, t, Q.Autenticada{r, Some{ctx}}, aut), antes_prefixo(xs, ys, t, Q.Aceita{r, ctx}, cert)}
    case Q.Configurada{}: Unit{}
    case Q.InicialAceita{}: Unit{}
    case Q.Iniciada{a0}: Unit{}
    case Q.InicialRecusada{a0}: Unit{}
    case Q.Codificada{a0, a1}: Unit{}
    case Q.Decodificada{a0, a1}: Unit{}
    case Q.Guardada{a0, a1, a2}: Unit{}
    case Q.Conferida{a0, a1}: Unit{}
    case Q.Construida{a0, a1}: Unit{}
    case Q.Lida{a0, a1, a2}: Unit{}
    case Q.Recebida{a0}: Unit{}
    case Q.Avaliada{a0, a1, a2}: Unit{}
    case Q.Operada{a0, a1, a2, a3}: Unit{}
    case Q.Preparada{a0, a1}: Unit{}
    case Q.Publicada{a0}: Unit{}
    case Q.Visivel{a0}: Unit{}
    case Q.Falhou{a0, a1, a2}: Unit{}
    case Q.Concluida{a0, a1, a2}: Unit{}
    case Q.Entregue{a0}: Unit{}
    case Q.Interrompida{a0}: Unit{}
    case Q.Fechada{}: Unit{}
    case Q.Seguinte{a0, a1}: Unit{}
    case Q.Inspecao{a0}: Unit{}
    case Q.Efeito{a0}: Unit{}

def dados_prefixo(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, +origem: Fonte.JuizoSintatico,
  +xs: List<&2, Q.Quadro>, -ys: List<&2, Q.Quadro>, -t: Nat, +q: Q.Quadro, dados: Dados(fonte, c, s, origem, xs, t, q)) -> Dados(fonte, c, s, origem, Q.concatenar(xs, ys), t, q):
  match dados:
    case L.Ambos{conteudo, ordem}: L.Ambos{conteudo, ordem_prefixo(xs, ys, t, q, ordem)}

# A lista neutra prova ausencia dos quatro marcos, sem um segundo parser.
def neutra_consultada(xs: List<&2, Q.Quadro>, t: Nat, +q: Q.Quadro, provas: Neutras(xs),
  consulta: {Q.consultar(xs, t) == Some{q} : Maybe<&2, Q.Quadro>}) -> {neutra(q) == True{} : Bool}:
  match xs t:
    case Nil{} _: L.ex_falso({neutra(q) == True{} : Bool}, F.nenhum_nao_algum(Q.Quadro, q, consulta))
    case Con{+h, cauda} 0n:
      F.com_par({neutra(q) == True{} : Bool}, {neutra(h) == True{} : Bool}, Neutras(cauda), provas, cabeca => resto =>
        %F.algum_injetivo(Q.Quadro, h, q, consulta) : {neutra(_) == True{} : Bool} cabeca)
    case Con{h, cauda} 1n+k:
      F.com_par({neutra(q) == True{} : Bool}, {neutra(h) == True{} : Bool}, Neutras(cauda), provas, cabeca => resto => neutra_consultada(cauda, k, q, resto, consulta))

def dados_neutros(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, +origem: Fonte.JuizoSintatico,
  -xs: List<&2, Q.Quadro>, -t: Nat, q: Q.Quadro, h: {neutra(q) == True{} : Bool}) -> Dados(fonte, c, s, origem, xs, t, q):
  match q:
    case Q.Configurada{}: L.Ambos{Unit{}, Unit{}}
    case Q.InicialAceita{}: L.Ambos{Unit{}, Unit{}}
    case Q.Iniciada{a0}: L.Ambos{Unit{}, Unit{}}
    case Q.InicialRecusada{a0}: L.Ambos{Unit{}, Unit{}}
    case Q.Codificada{a0, a1}: L.Ambos{Unit{}, Unit{}}
    case Q.Decodificada{a0, a1}: L.Ambos{Unit{}, Unit{}}
    case Q.Guardada{a0, a1, a2}: L.Ambos{Unit{}, Unit{}}
    case Q.Conferida{a0, a1}: L.Ambos{Unit{}, Unit{}}
    case Q.Construida{a0, a1}: L.Ambos{Unit{}, Unit{}}
    case Q.Lida{a0, a1, a2}: L.Ambos{Unit{}, Unit{}}
    case Q.Recebida{a0}: L.Ambos{Unit{}, Unit{}}
    case Q.Autenticada{a0, a1}: F.absurdo_booleano(Dados(fonte, c, s, origem, xs, t, Q.Autenticada{a0, a1}), h)
    case Q.Aceita{a0, a1}: F.absurdo_booleano(Dados(fonte, c, s, origem, xs, t, Q.Aceita{a0, a1}), h)
    case Q.Rejeitada{a0, a1}: F.absurdo_booleano(Dados(fonte, c, s, origem, xs, t, Q.Rejeitada{a0, a1}), h)
    case Q.Comecada{a0, a1}: F.absurdo_booleano(Dados(fonte, c, s, origem, xs, t, Q.Comecada{a0, a1}), h)
    case Q.Avaliada{a0, a1, a2}: L.Ambos{Unit{}, Unit{}}
    case Q.Operada{a0, a1, a2, a3}: L.Ambos{Unit{}, Unit{}}
    case Q.Preparada{a0, a1}: L.Ambos{Unit{}, Unit{}}
    case Q.Publicada{a0}: L.Ambos{Unit{}, Unit{}}
    case Q.Visivel{a0}: L.Ambos{Unit{}, Unit{}}
    case Q.Falhou{a0, a1, a2}: L.Ambos{Unit{}, Unit{}}
    case Q.Concluida{a0, a1, a2}: L.Ambos{Unit{}, Unit{}}
    case Q.Entregue{a0}: L.Ambos{Unit{}, Unit{}}
    case Q.Interrompida{a0}: L.Ambos{Unit{}, Unit{}}
    case Q.Fechada{}: L.Ambos{Unit{}, Unit{}}
    case Q.Seguinte{a0, a1}: L.Ambos{Unit{}, Unit{}}
    case Q.Inspecao{a0}: L.Ambos{Unit{}, Unit{}}
    case Q.Efeito{a0}: L.Ambos{Unit{}, Unit{}}

def validar_neutras(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, +origem: Fonte.JuizoSintatico,
  +xs: List<&2, Q.Quadro>, h: Neutras(xs)) -> Validacao(fonte, c, s, origem, xs):
  +t => +q => consulta => dados_neutros(fonte, c, s, origem, xs, t, q, neutra_consultada(xs, t, q, h, consulta))

def caso_concat_neutra(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, +origem: Fonte.JuizoSintatico,
  +xs: List<&2, Q.Quadro>, +ys: List<&2, Q.Quadro>, +t: Nat, +q: Q.Quadro,
  a: Validacao(fonte, c, s, origem, xs), b: Neutras(ys), parte: Q.Parte(xs, ys, t, q)) -> Dados(fonte, c, s, origem, Q.concatenar(xs, ys), t, q):
  match parte:
    case L.Esquerda{(+u, L.Ambos{posicao, consulta})}:
      %Equal.sym(Nat, t, u, posicao) : Dados(fonte, c, s, origem, Q.concatenar(xs, ys), _, q)
      dados_prefixo(fonte, c, s, origem, xs, ys, u, q, a(u, q, consulta))
    case L.Direita{(+u, L.Ambos{posicao, consulta})}:
      dados_neutros(fonte, c, s, origem, Q.concatenar(xs, ys), t, q, neutra_consultada(ys, u, q, b, consulta))

def anexar_neutras(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, +origem: Fonte.JuizoSintatico,
  +xs: List<&2, Q.Quadro>, +ys: List<&2, Q.Quadro>, a: Validacao(fonte, c, s, origem, xs), b: Neutras(ys)) -> Validacao(fonte, c, s, origem, Q.concatenar(xs, ys)):
  +t => +q => consulta => caso_concat_neutra(fonte, c, s, origem, xs, ys, t, q, a, b, Q.dividir_consulta(xs, ys, t, q, consulta))

def marca_da_parte(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, +origem: Fonte.JuizoSintatico,
  +xs: List<&2, Q.Quadro>, +marca: Q.Quadro, -t: Nat, +q: Q.Quadro, u: Nat,
  dado: Dados(fonte, c, s, origem, Q.concatenar(xs, [marca]), Nat.add(Q.tamanho(xs), 0n), marca),
  posicao: {t == Nat.add(Q.tamanho(xs), u) : Nat}, consulta: {Q.consultar([marca], u) == Some{q} : Maybe<&2, Q.Quadro>}) -> Dados(fonte, c, s, origem, Q.concatenar(xs, [marca]), t, q):
  match u:
    case 0n:
      %Equal.sym(Nat, t, Nat.add(Q.tamanho(xs), 0n), posicao) : Dados(fonte, c, s, origem, Q.concatenar(xs, [marca]), _, q)
      %F.algum_injetivo(Q.Quadro, marca, q, consulta) : Dados(fonte, c, s, origem, Q.concatenar(xs, [marca]), Nat.add(Q.tamanho(xs), 0n), _)
      dado
    case 1n+k:
      L.ex_falso(Dados(fonte, c, s, origem, Q.concatenar(xs, [marca]), t, q), F.nenhum_nao_algum(Q.Quadro, q, consulta))

def caso_anexar_marca(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, +origem: Fonte.JuizoSintatico,
  +xs: List<&2, Q.Quadro>, +marca: Q.Quadro, +t: Nat, +q: Q.Quadro,
  a: Validacao(fonte, c, s, origem, xs), dado: Dados(fonte, c, s, origem, Q.concatenar(xs, [marca]), Nat.add(Q.tamanho(xs), 0n), marca),
  parte: Q.Parte(xs, [marca], t, q)) -> Dados(fonte, c, s, origem, Q.concatenar(xs, [marca]), t, q):
  match parte:
    case L.Esquerda{(+u, L.Ambos{posicao, consulta})}:
      %Equal.sym(Nat, t, u, posicao) : Dados(fonte, c, s, origem, Q.concatenar(xs, [marca]), _, q)
      dados_prefixo(fonte, c, s, origem, xs, [marca], u, q, a(u, q, consulta))
    case L.Direita{(u, L.Ambos{posicao, consulta})}:
      marca_da_parte(fonte, c, s, origem, xs, marca, t, q, u, dado, posicao, consulta)

def anexar_marca(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, +origem: Fonte.JuizoSintatico,
  +xs: List<&2, Q.Quadro>, +marca: Q.Quadro, a: Validacao(fonte, c, s, origem, xs),
  dado: Dados(fonte, c, s, origem, Q.concatenar(xs, [marca]), Nat.add(Q.tamanho(xs), 0n), marca)) -> Validacao(fonte, c, s, origem, Q.concatenar(xs, [marca])):
  +t => +q => consulta => caso_anexar_marca(fonte, c, s, origem, xs, marca, t, q, a, dado, Q.dividir_consulta(xs, [marca], t, q, consulta))

def consulta_da_marca(+xs: List<&2, Q.Quadro>, -q: Q.Quadro) ->
  {Q.consultar(Q.concatenar(xs, [q]), Nat.add(Q.tamanho(xs), 0n)) == Some{q} : Maybe<&2, Q.Quadro>}:
  Q.consultar_apos_prefixo(xs, [q], 0n)

def antes_da_marca(+xs: List<&2, Q.Quadro>, -q: Q.Quadro, -marca: Q.Quadro, +u: Nat,
  consulta: {Q.consultar(xs, u) == Some{q} : Maybe<&2, Q.Quadro>}) -> Antes(Q.concatenar(xs, [marca]), Nat.add(Q.tamanho(xs), 0n), q):
  F.com_par(Antes(Q.concatenar(xs, [marca]), Nat.add(Q.tamanho(xs), 0n), q),
    {Q.consultar(xs, u) == Some{q} : Maybe<&2, Q.Quadro>}, {Q.consultar(xs, u) == Some{q} : Maybe<&2, Q.Quadro>},
    Q.igualdade_reabrivel(Maybe<&2, Q.Quadro>, Q.consultar(xs, u), Some{q}, consulta), uma => duas =>
      (u, L.Ambos{(%Equal.sym(Nat, Nat.add(Q.tamanho(xs), 0n), Q.tamanho(xs), A.nat_somar_zero_direita(Q.tamanho(xs))) : {Nat.is_lt(u, _) == True{} : Bool}
        Q.posicao_presente_dentro(xs, u, q, uma)), consulta_prefixo(xs, [marca], u, q, duas)}))

def interna_neutra(q: Q.Quadro, h: {M.interna(q) == True{} : Bool}) -> {neutra(q) == True{} : Bool}:
  match q:
    case Q.Configurada{}: {==}
    case Q.InicialAceita{}: {==}
    case Q.Iniciada{a0}: {==}
    case Q.InicialRecusada{a0}: {==}
    case Q.Codificada{a0, a1}: {==}
    case Q.Decodificada{a0, a1}: {==}
    case Q.Guardada{a0, a1, a2}: {==}
    case Q.Conferida{a0, a1}: {==}
    case Q.Construida{a0, a1}: {==}
    case Q.Lida{a0, a1, a2}: {==}
    case Q.Recebida{a0}: {==}
    case Q.Autenticada{a0, a1}: F.absurdo_booleano({neutra(Q.Autenticada{a0, a1}) == True{} : Bool}, h)
    case Q.Aceita{a0, a1}: F.absurdo_booleano({neutra(Q.Aceita{a0, a1}) == True{} : Bool}, h)
    case Q.Rejeitada{a0, a1}: F.absurdo_booleano({neutra(Q.Rejeitada{a0, a1}) == True{} : Bool}, h)
    case Q.Comecada{a0, a1}: F.absurdo_booleano({neutra(Q.Comecada{a0, a1}) == True{} : Bool}, h)
    case Q.Avaliada{a0, a1, a2}: {==}
    case Q.Operada{a0, a1, a2, a3}: {==}
    case Q.Preparada{a0, a1}: {==}
    case Q.Publicada{a0}: {==}
    case Q.Visivel{a0}: {==}
    case Q.Falhou{a0, a1, a2}: {==}
    case Q.Concluida{a0, a1, a2}: {==}
    case Q.Entregue{a0}: {==}
    case Q.Interrompida{a0}: {==}
    case Q.Fechada{}: {==}
    case Q.Seguinte{a0, a1}: {==}
    case Q.Inspecao{a0}: {==}
    case Q.Efeito{a0}: {==}

def internas_neutras(xs: List<&2, Q.Quadro>, provas: M.Internas(xs)) -> Neutras(xs):
  match xs provas:
    case Nil{} _: Unit{}
    case Con{+q, +t} L.Ambos{cabeca, cauda}: L.Ambos{interna_neutra(q, cabeca), internas_neutras(t, cauda)}

def micro_entrada_neutra(m: R.Micro) -> Neutras(R.micro_entrada(m)):
  match m:
    case R.Micro{+a, b, c, d}: internas_neutras(M.expandir_primitivas(a), M.primitivas_so_geram_internas(a))
def micro_autenticacao_neutra(m: R.Micro) -> Neutras(R.micro_autenticacao(m)):
  match m:
    case R.Micro{a, +b, c, d}: internas_neutras(M.expandir_primitivas(b), M.primitivas_so_geram_internas(b))
def micro_execucao_neutra(m: R.Micro) -> Neutras(R.micro_execucao(m)):
  match m:
    case R.Micro{a, b, +c, d}: internas_neutras(M.expandir_primitivas(c), M.primitivas_so_geram_internas(c))
def micro_saida_neutra(m: R.Micro) -> Neutras(R.micro_saida(m)):
  match m:
    case R.Micro{a, b, c, +d}: internas_neutras(M.expandir_primitivas(d), M.primitivas_so_geram_internas(d))

def execucao_neutra(+r: P.Requisicao, +ctx: D.Contexto, xs: List<&2, Q.QuadroExec>) -> Neutras(Q.expandir_exec(r, ctx, xs)):
  match xs:
    case Nil{}: Unit{}
    case Con{Q.Avaliacao{p}, t}: L.Ambos{{==}, execucao_neutra(r, ctx, t)}
    case Con{Q.Operacao{e, s, o, r2}, t}: L.Ambos{{==}, execucao_neutra(r, ctx, t)}

def depois_entrega_neutra(fecha: Bool, -s: D.Estado, proxima: Bool) -> Neutras(R.depois_entrega(fecha, s, proxima)):
  match fecha proxima:
    case True{} _: L.Ambos{{==}, Unit{}}
    case False{} True{}: L.Ambos{{==}, Unit{}}
    case False{} False{}: Unit{}

def entrega_neutra(-s: D.Estado, -bs: List<&2, U32>, +fecha: Bool, entrega: R.Entrega) -> Neutras(R.render_entrega(s, bs, fecha, entrega)):
  match entrega:
    case R.Completa{proxima}: L.Ambos{{==}, depois_entrega_neutra(fecha, s, proxima)}
    case R.Quebrada{prefixo}: L.Ambos{{==}, L.Ambos{{==}, Unit{}}}
    case R.PendenteEntrega{}: Unit{}

def publicacao_neutra(r: S.Resposta, -s: D.Estado) -> Neutras(R.render_publicacao(r, s)):
  match r:
    case S.Resposta{S.Entrada{}, v}: Unit{}
    case S.Resposta{S.Autenticacao{}, v}: Unit{}
    case S.Resposta{S.Certificado{}, v}: Unit{}
    case S.Resposta{S.Dados{}, v}: Unit{}
    case S.Resposta{S.Limite{}, v}: Unit{}
    case S.Resposta{S.Falha{}, v}: Unit{}
    case S.Resposta{S.Recusa{}, v}: Unit{}
    case S.Resposta{S.Sucesso{}, v}: L.Ambos{{==}, Unit{}}

def conclusao_neutra(conclusao: N.Conclusao, +fecha: Bool, entrega: R.Entrega) -> Neutras(R.render_conclusao(conclusao, fecha, entrega)):
  match conclusao:
    case N.Conclusao{+s, +r, +bs}: L.Ambos{{==}, neutras_concatenadas(R.render_publicacao(r, s), Con{Q.Concluida{r, s, fecha}, R.render_entrega(s, bs, fecha, entrega)},
      publicacao_neutra(r, s), L.Ambos{{==}, entrega_neutra(s, bs, fecha, entrega)})}

def erro_enquadrado_neutro(resultado: Maybe<&2, List<&2, U32>>, -r: S.Resposta, -s: D.Estado, +fecha: Bool, entrega: R.Entrega) -> Neutras(R.render_erro_enquadrado(resultado, r, s, fecha, entrega)):
  match resultado:
    case None{}: Unit{}
    case Some{+bs}: L.Ambos{{==}, L.Ambos{{==}, entrega_neutra(s, bs, fecha, entrega)}}

def erro_neutro(+status: S.Status, -s: D.Estado, +fecha: Bool, entrega: R.Entrega) -> Neutras(R.render_erro(status, s, fecha, entrega)):
  erro_enquadrado_neutro(P.enquadrar(S.resposta_valor(S.resposta_erro(status))), S.resposta_erro(status), s, fecha, entrega)

def falha_fim_neutro(+s: D.Estado, fatal: Bool, entrega: R.Entrega) -> Neutras(R.render_falha_fim(s, fatal, entrega)):
  match fatal:
    case True{}: L.Ambos{{==}, Unit{}}
    case False{}: erro_neutro(S.Falha{}, s, False{}, entrega)

def falha_neutra(+s: D.Estado, -etapa: X.Etapa, -id: String, +fatal: Bool, entrega: R.Entrega) -> Neutras(R.render_falha(s, etapa, id, fatal, entrega)):
  L.Ambos{{==}, falha_fim_neutro(s, fatal, entrega)}

def fatal_neutra(conclusao: N.Conclusao, -etapa: X.Etapa, -id: String) -> Neutras(R.render_fatal_publicada(conclusao, etapa, id)):
  match conclusao:
    case N.Conclusao{+s, +r, bs}: L.Ambos{{==}, neutras_concatenadas(R.render_publicacao(r, s), [Q.Falhou{etapa, id, True{}}, Q.Fechada{}], publicacao_neutra(r, s), L.Ambos{{==}, L.Ambos{{==}, Unit{}}})}

def inicial_neutra(bs: Maybe<&2, List<&2, U32>>, -s: D.Estado) -> Neutras(R.render_inicial(bs, s)):
  match bs:
    case None{}: L.Ambos{{==}, Unit{}}
    case Some{bs}: L.Ambos{{==}, L.Ambos{{==}, L.Ambos{{==}, Unit{}}}}

def prefixo_inicial_neutro(+m: R.Micro, aceita: Bool) -> Neutras(R.prefixo_inicial(m, aceita)):
  match aceita:
    case False{}: Unit{}
    case True{}: L.Ambos{{==}, micro_saida_neutra(m)}

# Os indices abaixo contam os quadros reais, inclusive os microquadros.
def recebida(+m: R.Micro, +r: P.Requisicao) -> List<&2, Q.Quadro>:
  Con{Q.Configurada{}, R.render_recebida(m, r)}
def antes_auth(+m: R.Micro, +r: P.Requisicao) -> List<&2, Q.Quadro>:
  Q.concatenar(recebida(m, r), R.micro_autenticacao(m))
def autenticada(+m: R.Micro, +r: P.Requisicao, ctx: Maybe<&2, D.Contexto>) -> List<&2, Q.Quadro>:
  Q.concatenar(recebida(m, r), Q.concatenar(R.micro_autenticacao(m), [Q.Autenticada{r, ctx}]))
def verificada(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto) -> List<&2, Q.Quadro>:
  Con{Q.Configurada{}, R.render_verificada(m, r, ctx)}
def indice_recebida(m: R.Micro) -> Nat:
  Succ{Nat.add(Q.tamanho(R.micro_entrada(m)), 0n)}
def indice_auth(+m: R.Micro, +r: P.Requisicao) -> Nat:
  Nat.add(Q.tamanho(antes_auth(m, r)), 0n)
def indice_aceita(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto) -> Nat:
  Nat.add(Q.tamanho(autenticada(m, r, Some{ctx})), 0n)

def recebida_neutra(+m: R.Micro, -r: P.Requisicao) -> Neutras(recebida(m, r)):
  L.Ambos{{==}, neutras_concatenadas(R.micro_entrada(m), [Q.Recebida{r}], micro_entrada_neutra(m), L.Ambos{{==}, Unit{}})}

def consulta_recebida(+m: R.Micro, -r: P.Requisicao) -> {Q.consultar(recebida(m, r), indice_recebida(m)) == Some{Q.Recebida{r}} : Maybe<&2, Q.Quadro>}:
  Q.consultar_apos_prefixo(R.micro_entrada(m), [Q.Recebida{r}], 0n)

def auth_associativa(+m: R.Micro, +r: P.Requisicao, -ctx: Maybe<&2, D.Contexto>) ->
  {Q.concatenar(antes_auth(m, r), [Q.Autenticada{r, ctx}]) == autenticada(m, r, ctx) : List<&2, Q.Quadro>}:
  Q.concatenar_assoc(recebida(m, r), R.micro_autenticacao(m), [Q.Autenticada{r, ctx}])

def consulta_auth(+m: R.Micro, +r: P.Requisicao, +ctx: Maybe<&2, D.Contexto>) ->
  {Q.consultar(autenticada(m, r, ctx), indice_auth(m, r)) == Some{Q.Autenticada{r, ctx}} : Maybe<&2, Q.Quadro>}:
  %auth_associativa(m, r, ctx) : {Q.consultar(_, indice_auth(m, r)) == Some{Q.Autenticada{r, ctx}} : Maybe<&2, Q.Quadro>}
  consulta_da_marca(antes_auth(m, r), Q.Autenticada{r, ctx})

def auth_validada(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, +origem: Fonte.JuizoSintatico,
  +m: R.Micro, +r: P.Requisicao, +ctx: Maybe<&2, D.Contexto>, exata: {ctx == D.autenticar(s, I.credencial(r)) : Maybe<&2, D.Contexto>}) -> Validacao(fonte, c, s, origem, autenticada(m, r, ctx)):
  %auth_associativa(m, r, ctx) : Validacao(fonte, c, s, origem, _)
  anexar_marca(fonte, c, s, origem, antes_auth(m, r), Q.Autenticada{r, ctx},
    validar_neutras(fonte, c, s, origem, antes_auth(m, r), neutras_concatenadas(recebida(m, r), R.micro_autenticacao(m), recebida_neutra(m, r), micro_autenticacao_neutra(m))),
    L.Ambos{exata, antes_da_marca(antes_auth(m, r), Q.Recebida{r}, Q.Autenticada{r, ctx}, indice_recebida(m),
      consulta_prefixo(recebida(m, r), R.micro_autenticacao(m), indice_recebida(m), Q.Recebida{r}, consulta_recebida(m, r)))})

def aceita_validada(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, +origem: Fonte.JuizoSintatico,
  +m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto,
  aut: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}, juizo: Fonte.JuizoAceito(fonte, c, r, ctx, origem)) -> Validacao(fonte, c, s, origem, verificada(m, r, ctx)):
  anexar_marca(fonte, c, s, origem, autenticada(m, r, Some{ctx}), Q.Aceita{r, ctx},
    auth_validada(fonte, c, s, origem, m, r, Some{ctx}, Equal.sym(Maybe<&2, D.Contexto>, D.autenticar(s, I.credencial(r)), Some{ctx}, aut)),
    L.Ambos{Fonte.certificado_de_juizo(fonte, c, r, ctx, origem, juizo),
      antes_da_marca(autenticada(m, r, Some{ctx}), Q.Autenticada{r, Some{ctx}}, Q.Aceita{r, ctx}, indice_auth(m, r), consulta_auth(m, r, Some{ctx}))})

def rejeita_validada(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, +origem: Fonte.JuizoSintatico,
  +m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto,
  aut: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}, juizo: Fonte.JuizoRecusado(fonte, c, r, ctx)) ->
  Validacao(fonte, c, s, origem, Q.concatenar(autenticada(m, r, Some{ctx}), [Q.Rejeitada{r, ctx}])):
  anexar_marca(fonte, c, s, origem, autenticada(m, r, Some{ctx}), Q.Rejeitada{r, ctx},
    auth_validada(fonte, c, s, origem, m, r, Some{ctx}, Equal.sym(Maybe<&2, D.Contexto>, D.autenticar(s, I.credencial(r)), Some{ctx}, aut)),
    L.Ambos{juizo, antes_da_marca(autenticada(m, r, Some{ctx}), Q.Autenticada{r, Some{ctx}}, Q.Rejeitada{r, ctx}, indice_auth(m, r), consulta_auth(m, r, Some{ctx}))})

def consulta_aceita(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto) ->
  {Q.consultar(verificada(m, r, ctx), indice_aceita(m, r, ctx)) == Some{Q.Aceita{r, ctx}} : Maybe<&2, Q.Quadro>}:
  consulta_da_marca(autenticada(m, r, Some{ctx}), Q.Aceita{r, ctx})

def antes_start(+m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto) -> List<&2, Q.Quadro>:
  Q.concatenar(verificada(m, r, ctx), R.micro_execucao(m))

def comeca_duas(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, +origem: Fonte.JuizoSintatico,
  +m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto,
  auts: L.E<{D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}, {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}>,
  juizo: Fonte.JuizoAceito(fonte, c, r, ctx, origem)) -> Validacao(fonte, c, s, origem, Con{Q.Configurada{}, R.render_comecada(m, r, ctx)}):
  match auts:
    case L.Ambos{uma, duas}:
      %Q.concatenar_assoc(verificada(m, r, ctx), R.micro_execucao(m), [Q.Comecada{r, ctx}]) : Validacao(fonte, c, s, origem, _)
      anexar_marca(fonte, c, s, origem, antes_start(m, r, ctx), Q.Comecada{r, ctx},
        anexar_neutras(fonte, c, s, origem, verificada(m, r, ctx), R.micro_execucao(m), aceita_validada(fonte, c, s, origem, m, r, ctx, uma, juizo), micro_execucao_neutra(m)),
        L.Ambos{duas, L.Ambos{
          antes_da_marca(antes_start(m, r, ctx), Q.Autenticada{r, Some{ctx}}, Q.Comecada{r, ctx}, indice_auth(m, r),
            consulta_prefixo(verificada(m, r, ctx), R.micro_execucao(m), indice_auth(m, r), Q.Autenticada{r, Some{ctx}},
              consulta_prefixo(autenticada(m, r, Some{ctx}), [Q.Aceita{r, ctx}], indice_auth(m, r), Q.Autenticada{r, Some{ctx}}, consulta_auth(m, r, Some{ctx})))),
          antes_da_marca(antes_start(m, r, ctx), Q.Aceita{r, ctx}, Q.Comecada{r, ctx}, indice_aceita(m, r, ctx),
            consulta_prefixo(verificada(m, r, ctx), R.micro_execucao(m), indice_aceita(m, r, ctx), Q.Aceita{r, ctx}, consulta_aceita(m, r, ctx)))}})

def comeca_validada(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, +origem: Fonte.JuizoSintatico,
  +m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto,
  aut: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}, juizo: Fonte.JuizoAceito(fonte, c, r, ctx, origem)) -> Validacao(fonte, c, s, origem, Con{Q.Configurada{}, R.render_comecada(m, r, ctx)}):
  comeca_duas(fonte, c, s, origem, m, r, ctx, Q.igualdade_reabrivel(Maybe<&2, D.Contexto>, D.autenticar(s, I.credencial(r)), Some{ctx}, aut), juizo)

def duas_associacoes(+xs: List<&2, Q.Quadro>, +ys: List<&2, Q.Quadro>, -q: Q.Quadro, +zs: List<&2, Q.Quadro>) ->
  {Q.concatenar(Q.concatenar(xs, Q.concatenar(ys, [q])), zs) == Q.concatenar(xs, Q.concatenar(ys, Con{q, zs})) : List<&2, Q.Quadro>}:
  Equal.trans(List<&2, Q.Quadro>, Q.concatenar(Q.concatenar(xs, Q.concatenar(ys, [q])), zs),
    Q.concatenar(xs, Q.concatenar(Q.concatenar(ys, [q]), zs)), Q.concatenar(xs, Q.concatenar(ys, Con{q, zs})),
    Q.concatenar_assoc(xs, Q.concatenar(ys, [q]), zs),
    Equal.cong(List<&2, Q.Quadro>, List<&2, Q.Quadro>, resto => Q.concatenar(xs, resto), Q.concatenar(Q.concatenar(ys, [q]), zs), Q.concatenar(ys, Con{q, zs}), Q.concatenar_assoc(ys, [q], zs)))

def continuar_auth(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, +origem: Fonte.JuizoSintatico,
  +m: R.Micro, +r: P.Requisicao, +ctx: Maybe<&2, D.Contexto>, +resto: List<&2, Q.Quadro>,
  validada: Validacao(fonte, c, s, origem, autenticada(m, r, ctx)), neutro: Neutras(resto)) ->
  Validacao(fonte, c, s, origem, Q.concatenar(recebida(m, r), Q.concatenar(R.micro_autenticacao(m), Con{Q.Autenticada{r, ctx}, resto}))):
  %duas_associacoes(recebida(m, r), R.micro_autenticacao(m), Q.Autenticada{r, ctx}, resto) : Validacao(fonte, c, s, origem, _)
  anexar_neutras(fonte, c, s, origem, autenticada(m, r, ctx), resto, validada, neutro)

def continuar_marca(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, +origem: Fonte.JuizoSintatico,
  +xs: List<&2, Q.Quadro>, +marca: Q.Quadro, +resto: List<&2, Q.Quadro>, validada: Validacao(fonte, c, s, origem, Q.concatenar(xs, [marca])), neutro: Neutras(resto)) -> Validacao(fonte, c, s, origem, Q.concatenar(xs, Con{marca, resto})):
  %Q.concatenar_assoc(xs, [marca], resto) : Validacao(fonte, c, s, origem, _)
  anexar_neutras(fonte, c, s, origem, Q.concatenar(xs, [marca]), resto, validada, neutro)

def preparada_neutra(p: N.Preparada) -> {neutra(R.quadro_preparada(p)) == True{} : Bool}:
  match p:
    case N.Preparada{w, ts, r, bs}: {==}

def exec_validada(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, +origem: Fonte.JuizoSintatico,
  +m: R.Micro, +r: P.Requisicao, +ctx: D.Contexto, +xs: List<&2, Q.QuadroExec>, aut: {D.autenticar(s, I.credencial(r)) == Some{ctx} : Maybe<&2, D.Contexto>}, juizo: Fonte.JuizoAceito(fonte, c, r, ctx, origem)) -> Validacao(fonte, c, s, origem, Con{Q.Configurada{}, R.render_execucao(m, r, ctx, xs)}):
  anexar_neutras(fonte, c, s, origem, Con{Q.Configurada{}, R.render_comecada(m, r, ctx)}, Q.expandir_exec(r, ctx, xs), comeca_validada(fonte, c, s, origem, m, r, ctx, aut, juizo), execucao_neutra(r, ctx, xs))

def fase_validada(~fonte: Fonte.Fonte, -c: S.Configuracao, +s: D.Estado, +origem: Fonte.JuizoSintatico,
  +m: R.Micro, fase: R.FaseAntes, aut: Cinco.AuthDaFase(s, fase), juizo: Fonte.JuizoDaFase(fonte, c, origem, fase)) -> Validacao(fonte, c, s, origem, Con{Q.Configurada{}, R.render_fase(m, fase)}):
  match fase:
    case R.AntesEntrada{}: validar_neutras(fonte, c, s, origem, Con{Q.Configurada{}, R.micro_entrada(m)}, L.Ambos{{==}, micro_entrada_neutra(m)})
    case R.AposReceber{+r}: validar_neutras(fonte, c, s, origem, recebida(m, r), recebida_neutra(m, r))
    case R.AposAutenticar{+r, +ctx}: auth_validada(fonte, c, s, origem, m, r, Some{ctx}, Equal.sym(Maybe<&2, D.Contexto>, D.autenticar(s, I.credencial(r)), Some{ctx}, aut))
    case R.AposVerificar{+r, +ctx}: aceita_validada(fonte, c, s, origem, m, r, ctx, aut, juizo)
    case R.Executando{+r, +ctx, +xs}: exec_validada(fonte, c, s, origem, m, r, ctx, xs, aut, juizo)
    case R.AposPreparar{+r, +ctx, +xs, +p}:
      anexar_neutras(fonte, c, s, origem, Con{Q.Configurada{}, R.render_execucao(m, r, ctx, xs)}, Q.concatenar(R.micro_saida(m), [R.quadro_preparada(p)]),
        exec_validada(fonte, c, s, origem, m, r, ctx, xs, aut, juizo),
        neutras_concatenadas(R.micro_saida(m), [R.quadro_preparada(p)], micro_saida_neutra(m), L.Ambos{preparada_neutra(p), Unit{}}))

def caso_validado(~fonte: Fonte.Fonte, -c: S.Configuracao, +s: D.Estado, +origem: Fonte.JuizoSintatico,
  +m: R.Micro, caso: R.Caso, aut: Cinco.AuthDoCaso(s, caso), juizo: Fonte.JuizoDoCaso(fonte, c, origem, caso)) -> Validacao(fonte, c, s, origem, R.render(m, s, caso)):
  match caso:
    case R.InicialOk{}:
      validar_neutras(fonte, c, s, origem, R.render(m, s, R.InicialOk{}), L.Ambos{{==}, L.Ambos{{==}, neutras_concatenadas(R.micro_saida(m), R.render_inicial(P.codificar(D.estado_valor(s)), s), micro_saida_neutra(m), inicial_neutra(P.codificar(D.estado_valor(s)), s))}})
    case R.InicialRecusa{status}: validar_neutras(fonte, c, s, origem, R.render(m, s, R.InicialRecusa{status}), L.Ambos{{==}, L.Ambos{{==}, Unit{}}})
    case R.InicialFalha{+aceita, +etapa, +id, +fatal}:
      validar_neutras(fonte, c, s, origem, R.render(m, s, R.InicialFalha{aceita, etapa, id, fatal}), L.Ambos{{==}, neutras_concatenadas(R.prefixo_inicial(m, aceita), [Q.Falhou{etapa, id, fatal}, Q.InicialRecusada{S.Falha{}}], prefixo_inicial_neutro(m, aceita), L.Ambos{{==}, L.Ambos{{==}, Unit{}}})})
    case R.SemResposta{}: validar_neutras(fonte, c, s, origem, R.render(m, s, R.SemResposta{}), L.Ambos{{==}, L.Ambos{{==}, Unit{}}})
    case R.EntradaRecusa{+erro, +fecha, +entrega}:
      validar_neutras(fonte, c, s, origem, R.render(m, s, R.EntradaRecusa{erro, fecha, entrega}), L.Ambos{{==}, neutras_concatenadas(R.micro_entrada(m), R.render_erro(R.status_entrada(erro), s, fecha, entrega), micro_entrada_neutra(m), erro_neutro(R.status_entrada(erro), s, fecha, entrega))})
    case R.AutRecusa{+r, +entrega}:
      continuar_auth(fonte, c, s, origem, m, r, None{}, R.render_erro(S.Autenticacao{}, s, False{}, entrega),
        auth_validada(fonte, c, s, origem, m, r, None{}, Equal.sym(Maybe<&2, D.Contexto>, D.autenticar(s, I.credencial(r)), None{}, aut)), erro_neutro(S.Autenticacao{}, s, False{}, entrega))
    case R.GateRecusa{+r, +ctx, +entrega}:
      continuar_marca(fonte, c, s, origem, autenticada(m, r, Some{ctx}), Q.Rejeitada{r, ctx}, R.render_erro(S.Certificado{}, s, False{}, entrega), rejeita_validada(fonte, c, s, origem, m, r, ctx, aut, juizo), erro_neutro(S.Certificado{}, s, False{}, entrega))
    case R.Executada{+r, +ctx, +xs, +p, +entrega}:
      anexar_neutras(fonte, c, s, origem, Con{Q.Configurada{}, R.render_execucao(m, r, ctx, xs)}, Q.concatenar(R.micro_saida(m), R.render_final(p, s, False{}, entrega)), exec_validada(fonte, c, s, origem, m, r, ctx, xs, aut, juizo),
        neutras_concatenadas(R.micro_saida(m), R.render_final(p, s, False{}, entrega), micro_saida_neutra(m), conclusao_neutra(N.concluir(p, s), False{}, entrega)))
    case R.FalhaAntes{+fase, +etapa, +id, +fatal, +entrega}:
      anexar_neutras(fonte, c, s, origem, Con{Q.Configurada{}, R.render_fase(m, fase)}, R.render_falha(s, etapa, id, fatal, entrega), fase_validada(fonte, c, s, origem, m, fase, aut, juizo), falha_neutra(s, etapa, id, fatal, entrega))
    case R.FatalAposPublicacao{+r, +ctx, +xs, +p, +etapa, +id}:
      anexar_neutras(fonte, c, s, origem, Con{Q.Configurada{}, R.render_execucao(m, r, ctx, xs)}, Q.concatenar(R.micro_saida(m), R.render_fatal_publicada(N.concluir(p, s), etapa, id)), exec_validada(fonte, c, s, origem, m, r, ctx, xs, aut, juizo),
        neutras_concatenadas(R.micro_saida(m), R.render_fatal_publicada(N.concluir(p, s), etapa, id), micro_saida_neutra(m), fatal_neutra(N.concluir(p, s), etapa, id)))
    case R.Pendente{fase}: fase_validada(fonte, c, s, origem, m, fase, aut, juizo)
    case R.InicialPendente{+aceita}: validar_neutras(fonte, c, s, origem, R.render(m, s, R.InicialPendente{aceita}), L.Ambos{{==}, prefixo_inicial_neutro(m, aceita)})

# Tres predecessores possiveis; todos sao fatos do mesmo trace fixo.
type Predecessor is Data:
  PedidoAnterior{r: P.Requisicao}
  AutAnterior{r: P.Requisicao, ctx: D.Contexto}
  CertAnterior{r: P.Requisicao, ctx: D.Contexto}

def quadro_anterior(pre: Predecessor) -> Q.Quadro:
  match pre:
    case PedidoAnterior{r}: Q.Recebida{r}
    case AutAnterior{r, ctx}: Q.Autenticada{r, Some{ctx}}
    case CertAnterior{r, ctx}: Q.Aceita{r, ctx}

def fato_anterior(~fonte: Fonte.Fonte, +origem: Fonte.JuizoSintatico, pre: Predecessor) -> I.Fato:
  match pre:
    case PedidoAnterior{r}: I.RecebeuRequisicao{r}
    case AutAnterior{r, ctx}: I.Autenticou{r, Some{ctx}}
    case CertAnterior{r, ctx}: I.CertificadoAceito{r, ctx, Fonte.programa(fonte, origem)}

def observacao_anterior(~fonte: Fonte.Fonte, -c: S.Configuracao, -s: D.Estado, +origem: Fonte.JuizoSintatico,
  +xs: List<&2, Q.Quadro>, +t: Nat, pre: Predecessor,
  consulta: {Q.consultar(xs, t) == Some{quadro_anterior(pre)} : Maybe<&2, Q.Quadro>}) ->
  Q.observa_servico(c, Fonte.programa(fonte, origem), Some{s}, xs, t, fato_anterior(fonte, origem, pre)):
  match pre:
    case PedidoAnterior{+r}: Q.consulta_estabelece_observacao(c, Fonte.programa(fonte, origem), xs, t, Q.Recebida{r}, I.RecebeuRequisicao{r}, consulta, {==})
    case AutAnterior{+r, +ctx}: Q.consulta_estabelece_observacao(c, Fonte.programa(fonte, origem), xs, t, Q.Autenticada{r, Some{ctx}}, I.Autenticou{r, Some{ctx}}, consulta, {==})
    case CertAnterior{+r, +ctx}: Q.consulta_estabelece_observacao(c, Fonte.programa(fonte, origem), xs, t, Q.Aceita{r, ctx}, I.CertificadoAceito{r, ctx, Fonte.programa(fonte, origem)}, consulta, {==})

def Elevar(~fonte: Fonte.Fonte, -x: I.Cenario, +origem: Fonte.JuizoSintatico, -xs: List<&2, Q.Quadro>) -> Type:
  @u: Nat -> @pre: Predecessor -> {Q.consultar(xs, u) == Some{quadro_anterior(pre)} : Maybe<&2, Q.Quadro>} ->
    I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), x, u, fato_anterior(fonte, origem, pre))

def antes_no_ambiente(~fonte: Fonte.Fonte, -x: I.Cenario, +origem: Fonte.JuizoSintatico,
  -xs: List<&2, Q.Quadro>, -t: Nat, +pre: Predecessor, elevar: Elevar(fonte, x, origem, xs), antes: Antes(xs, t, quadro_anterior(pre))) ->
  I.Antes(Fonte.ambiente(fonte), Fonte.artefato(fonte), x, t, fato_anterior(fonte, origem, pre)):
  match antes:
    case (+u, L.Ambos{ordem, consulta}): (u, L.Ambos{ordem, elevar(u, pre, consulta)})

# As funcoes abaixo consomem a unica consulta real. Nao recebem Regra3/4.
def regra3_bruta(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao,
  +origem: Fonte.JuizoSintatico, +xs: List<&2, Q.Quadro>, +t: Nat, f: I.Fato,
  valida: Validacao(fonte, c, s, origem, xs), elevar: Elevar(fonte, I.Atender{mundo, c, s, recepcao}, origem, xs),
  fato: Q.observa_servico(c, Fonte.programa(fonte, origem), Some{s}, xs, t, f)) ->
  K.Regra3(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t):
  match f:
    case I.Autenticou{+r, +ctx}:
      F.com_par(K.Regra3(I.Autenticou{r, ctx}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t),
        Conteudo(fonte, c, s, origem, Q.Autenticada{r, ctx}), Ordem(xs, t, Q.Autenticada{r, ctx}),
        valida(t, Q.Autenticada{r, ctx}, Q.observacao_quadro(c, Fonte.programa(fonte, origem), xs, t, I.Autenticou{r, ctx}, fato)),
        conteudo => ordem => L.Ambos{conteudo, antes_no_ambiente(fonte, I.Atender{mundo, c, s, recepcao}, origem, xs, t, PedidoAnterior{r}, elevar, ordem)})
    case I.ProgramaComecou{+r, +ctx, p}:
      F.com_par(K.Regra3(I.ProgramaComecou{r, ctx, p}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t),
        Conteudo(fonte, c, s, origem, Q.Comecada{r, ctx}), Ordem(xs, t, Q.Comecada{r, ctx}),
        valida(t, Q.Comecada{r, ctx}, Q.observacao_quadro(c, Fonte.programa(fonte, origem), xs, t, I.ProgramaComecou{r, ctx, p}, fato)),
        conteudo => ordem => L.Ambos{conteudo, antes_no_ambiente(fonte, I.Atender{mundo, c, s, recepcao}, origem, xs, t, AutAnterior{r, ctx}, elevar,
          L.e_esquerda(Antes(xs, t, Q.Autenticada{r, Some{ctx}}), Antes(xs, t, Q.Aceita{r, ctx}), ordem))})
    case I.ConfiguracaoEmUso{a0}: Unit{}
    case I.InspecaoNaoModelada{a0}: Unit{}
    case I.EfeitoNaoModelado{a0}: Unit{}
    case I.InstanciaIniciou{a0}: Unit{}
    case I.InicializacaoRecusada{a0}: Unit{}
    case I.ProvaInicialAceita{}: Unit{}
    case I.Codificou{a0, a1}: Unit{}
    case I.Decodificou{a0, a1}: Unit{}
    case I.Guardou{a0, a1, a2}: Unit{}
    case I.Operou{a0, a1, a2, a3}: Unit{}
    case I.ConferiuComprimento{a0, a1}: Unit{}
    case I.AlocouCampo{a0, a1}: Unit{}
    case I.LeuCorpo{a0, a1, a2}: Unit{}
    case I.RecebeuRequisicao{a0}: Unit{}
    case I.CertificadoAceito{a0, a1, a2}: Unit{}
    case I.CertificadoRejeitado{a0, a1}: Unit{}
    case I.Avaliou{a0, a1, a2, a3}: Unit{}
    case I.Preparou{a0, a1}: Unit{}
    case I.Publicou{a0}: Unit{}
    case I.EstadoVisivel{a0}: Unit{}
    case I.FalhouAmbiente{a0, a1, a2}: Unit{}
    case I.Concluiu{a0, a1, a2}: Unit{}
    case I.EntregouTudo{a0}: Unit{}
    case I.EntregaInterrompida{a0}: Unit{}
    case I.EncerrouCanal{}: Unit{}
    case I.ProximaChamada{a0, a1}: Unit{}

def fato_da_mesma_fonte(~fonte: Fonte.Fonte, -c: S.Configuracao, +origem: Fonte.JuizoSintatico,
  +xs: List<&2, Q.Quadro>, +t: Nat, +q: Q.Quadro, -f: I.Fato, -esperado: I.Fato,
  fato: Q.observa(c, Fonte.programa(fonte, origem), xs, t, f),
  consulta: {Q.consultar(xs, t) == Some{q} : Maybe<&2, Q.Quadro>}, relacao: Q.rel_fato(c, Fonte.programa(fonte, origem), q, esperado)) -> {f == esperado : I.Fato}:
  Q.observacao_unica(c, Fonte.programa(fonte, origem), xs, t, f, esperado, fato,
    Q.consulta_estabelece_observacao(c, Fonte.programa(fonte, origem), xs, t, q, esperado, consulta, relacao))

def aceita4_dados(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao,
  +origem: Fonte.JuizoSintatico, +xs: List<&2, Q.Quadro>, +t: Nat, +r: P.Requisicao, +ctx: D.Contexto, -p: S.Programa,
  dados: Dados(fonte, c, s, origem, xs, t, Q.Aceita{r, ctx}), elevar: Elevar(fonte, I.Atender{mundo, c, s, recepcao}, origem, xs),
  mesmo: {I.CertificadoAceito{r, ctx, p} == I.CertificadoAceito{r, ctx, Fonte.programa(fonte, origem)} : I.Fato}) ->
  K.Regra4(I.CertificadoAceito{r, ctx, p}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t):
  %Equal.sym(I.Fato, I.CertificadoAceito{r, ctx, p}, I.CertificadoAceito{r, ctx, Fonte.programa(fonte, origem)}, mesmo) :
    K.Regra4(_, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t)
  F.com_par(K.Regra4(I.CertificadoAceito{r, ctx, Fonte.programa(fonte, origem)}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t),
    Conteudo(fonte, c, s, origem, Q.Aceita{r, ctx}), Ordem(xs, t, Q.Aceita{r, ctx}), dados,
    conteudo => ordem => L.Ambos{antes_no_ambiente(fonte, I.Atender{mundo, c, s, recepcao}, origem, xs, t, AutAnterior{r, ctx}, elevar, ordem), conteudo})

def comeca4_dados(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao,
  +origem: Fonte.JuizoSintatico, +xs: List<&2, Q.Quadro>, +t: Nat, +r: P.Requisicao, +ctx: D.Contexto, -p: S.Programa,
  dados: Dados(fonte, c, s, origem, xs, t, Q.Comecada{r, ctx}), elevar: Elevar(fonte, I.Atender{mundo, c, s, recepcao}, origem, xs),
  mesmo: {I.ProgramaComecou{r, ctx, p} == I.ProgramaComecou{r, ctx, Fonte.programa(fonte, origem)} : I.Fato}) ->
  K.Regra4(I.ProgramaComecou{r, ctx, p}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t):
  %Equal.sym(I.Fato, I.ProgramaComecou{r, ctx, p}, I.ProgramaComecou{r, ctx, Fonte.programa(fonte, origem)}, mesmo) :
    K.Regra4(_, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t)
  F.com_par(K.Regra4(I.ProgramaComecou{r, ctx, Fonte.programa(fonte, origem)}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t),
    Conteudo(fonte, c, s, origem, Q.Comecada{r, ctx}), Ordem(xs, t, Q.Comecada{r, ctx}), dados,
    conteudo => ordem => antes_no_ambiente(fonte, I.Atender{mundo, c, s, recepcao}, origem, xs, t, CertAnterior{r, ctx}, elevar,
      L.e_direita(Antes(xs, t, Q.Autenticada{r, Some{ctx}}), Antes(xs, t, Q.Aceita{r, ctx}), ordem)))

def aceita4_consultas(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao,
  +origem: Fonte.JuizoSintatico, +xs: List<&2, Q.Quadro>, +t: Nat, +r: P.Requisicao, +ctx: D.Contexto, -p: S.Programa,
  valida: Validacao(fonte, c, s, origem, xs), elevar: Elevar(fonte, I.Atender{mundo, c, s, recepcao}, origem, xs),
  fato: Q.observa(c, Fonte.programa(fonte, origem), xs, t, I.CertificadoAceito{r, ctx, p}),
  consultas: L.E<{Q.consultar(xs, t) == Some{Q.Aceita{r, ctx}} : Maybe<&2, Q.Quadro>}, {Q.consultar(xs, t) == Some{Q.Aceita{r, ctx}} : Maybe<&2, Q.Quadro>}>) ->
  K.Regra4(I.CertificadoAceito{r, ctx, p}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t):
  match consultas:
    case L.Ambos{uma, duas}: aceita4_dados(fonte, c, mundo, s, recepcao, origem, xs, t, r, ctx, p, valida(t, Q.Aceita{r, ctx}, uma), elevar,
      fato_da_mesma_fonte(fonte, c, origem, xs, t, Q.Aceita{r, ctx}, I.CertificadoAceito{r, ctx, p}, I.CertificadoAceito{r, ctx, Fonte.programa(fonte, origem)}, fato, duas, {==}))

def comeca4_consultas(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao,
  +origem: Fonte.JuizoSintatico, +xs: List<&2, Q.Quadro>, +t: Nat, +r: P.Requisicao, +ctx: D.Contexto, -p: S.Programa,
  valida: Validacao(fonte, c, s, origem, xs), elevar: Elevar(fonte, I.Atender{mundo, c, s, recepcao}, origem, xs),
  fato: Q.observa(c, Fonte.programa(fonte, origem), xs, t, I.ProgramaComecou{r, ctx, p}),
  consultas: L.E<{Q.consultar(xs, t) == Some{Q.Comecada{r, ctx}} : Maybe<&2, Q.Quadro>}, {Q.consultar(xs, t) == Some{Q.Comecada{r, ctx}} : Maybe<&2, Q.Quadro>}>) ->
  K.Regra4(I.ProgramaComecou{r, ctx, p}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t):
  match consultas:
    case L.Ambos{uma, duas}: comeca4_dados(fonte, c, mundo, s, recepcao, origem, xs, t, r, ctx, p, valida(t, Q.Comecada{r, ctx}, uma), elevar,
      fato_da_mesma_fonte(fonte, c, origem, xs, t, Q.Comecada{r, ctx}, I.ProgramaComecou{r, ctx, p}, I.ProgramaComecou{r, ctx, Fonte.programa(fonte, origem)}, fato, duas, {==}))

def regra4_bruta(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao,
  +origem: Fonte.JuizoSintatico, +xs: List<&2, Q.Quadro>, +t: Nat, f: I.Fato,
  valida: Validacao(fonte, c, s, origem, xs), elevar: Elevar(fonte, I.Atender{mundo, c, s, recepcao}, origem, xs),
  fato: Q.observa_servico(c, Fonte.programa(fonte, origem), Some{s}, xs, t, f)) ->
  K.Regra4(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t):
  match f:
    case I.CertificadoAceito{+r, +ctx, p}:
      F.com_par(K.Regra4(I.CertificadoAceito{r, ctx, p}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t),
        Q.observa(c, Fonte.programa(fonte, origem), xs, t, I.CertificadoAceito{r, ctx, p}), Q.observa(c, Fonte.programa(fonte, origem), xs, t, I.CertificadoAceito{r, ctx, p}),
        Q.duplicar_observacao(c, Fonte.programa(fonte, origem), xs, t, I.CertificadoAceito{r, ctx, p}, fato), uma => duas =>
          aceita4_consultas(fonte, c, mundo, s, recepcao, origem, xs, t, r, ctx, p, valida, elevar, uma,
            Q.igualdade_reabrivel(Maybe<&2, Q.Quadro>, Q.consultar(xs, t), Some{Q.Aceita{r, ctx}}, Q.observacao_quadro(c, Fonte.programa(fonte, origem), xs, t, I.CertificadoAceito{r, ctx, p}, duas))))
    case I.CertificadoRejeitado{+r, +ctx}:
      F.com_par(K.Regra4(I.CertificadoRejeitado{r, ctx}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t),
        Conteudo(fonte, c, s, origem, Q.Rejeitada{r, ctx}), Ordem(xs, t, Q.Rejeitada{r, ctx}),
        valida(t, Q.Rejeitada{r, ctx}, Q.observacao_quadro(c, Fonte.programa(fonte, origem), xs, t, I.CertificadoRejeitado{r, ctx}, fato)),
        conteudo => ordem => L.Ambos{antes_no_ambiente(fonte, I.Atender{mundo, c, s, recepcao}, origem, xs, t, AutAnterior{r, ctx}, elevar, ordem), conteudo})
    case I.ProgramaComecou{+r, +ctx, p}:
      F.com_par(K.Regra4(I.ProgramaComecou{r, ctx, p}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t),
        Q.observa(c, Fonte.programa(fonte, origem), xs, t, I.ProgramaComecou{r, ctx, p}), Q.observa(c, Fonte.programa(fonte, origem), xs, t, I.ProgramaComecou{r, ctx, p}),
        Q.duplicar_observacao(c, Fonte.programa(fonte, origem), xs, t, I.ProgramaComecou{r, ctx, p}, fato), uma => duas =>
          comeca4_consultas(fonte, c, mundo, s, recepcao, origem, xs, t, r, ctx, p, valida, elevar, uma,
            Q.igualdade_reabrivel(Maybe<&2, Q.Quadro>, Q.consultar(xs, t), Some{Q.Comecada{r, ctx}}, Q.observacao_quadro(c, Fonte.programa(fonte, origem), xs, t, I.ProgramaComecou{r, ctx, p}, duas))))
    case I.ConfiguracaoEmUso{a0}: Unit{}
    case I.InspecaoNaoModelada{a0}: Unit{}
    case I.EfeitoNaoModelado{a0}: Unit{}
    case I.InstanciaIniciou{a0}: Unit{}
    case I.InicializacaoRecusada{a0}: Unit{}
    case I.ProvaInicialAceita{}: Unit{}
    case I.Codificou{a0, a1}: Unit{}
    case I.Decodificou{a0, a1}: Unit{}
    case I.Guardou{a0, a1, a2}: Unit{}
    case I.Operou{a0, a1, a2, a3}: Unit{}
    case I.ConferiuComprimento{a0, a1}: Unit{}
    case I.AlocouCampo{a0, a1}: Unit{}
    case I.LeuCorpo{a0, a1, a2}: Unit{}
    case I.RecebeuRequisicao{a0}: Unit{}
    case I.Autenticou{a0, a1}: Unit{}
    case I.Avaliou{a0, a1, a2, a3}: Unit{}
    case I.Preparou{a0, a1}: Unit{}
    case I.Publicou{a0}: Unit{}
    case I.EstadoVisivel{a0}: Unit{}
    case I.FalhouAmbiente{a0, a1, a2}: Unit{}
    case I.Concluiu{a0, a1, a2}: Unit{}
    case I.EntregouTudo{a0}: Unit{}
    case I.EntregaInterrompida{a0}: Unit{}
    case I.EncerrouCanal{}: Unit{}
    case I.ProximaChamada{a0, a1}: Unit{}

type QualLei is Data:
  AutenticacaoLei{}
  AdmissaoLei{}

def Regra(lei: QualLei, f: I.Fato, -a: I.Ambiente, -k: String, -x: I.Cenario, -t: Nat) -> Type:
  match lei:
    case AutenticacaoLei{}: K.Regra3(f, a, k, x, t)
    case AdmissaoLei{}: K.Regra4(f, a, k, x, t)

def regra_bruta(~fonte: Fonte.Fonte, ~c: S.Configuracao, lei: QualLei, +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao,
  +origem: Fonte.JuizoSintatico, +xs: List<&2, Q.Quadro>, +t: Nat, f: I.Fato,
  valida: Validacao(fonte, c, s, origem, xs), elevar: Elevar(fonte, I.Atender{mundo, c, s, recepcao}, origem, xs),
  fato: Q.observa_servico(c, Fonte.programa(fonte, origem), Some{s}, xs, t, f)) ->
  Regra(lei, f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t):
  match lei:
    case AutenticacaoLei{}: regra3_bruta(fonte, c, mundo, s, recepcao, origem, xs, t, f, valida, elevar, fato)
    case AdmissaoLei{}: regra4_bruta(fonte, c, mundo, s, recepcao, origem, xs, t, f, valida, elevar, fato)

# Uma unica chamada ao seletor existente produz a igualdade da autenticacao.
def aut_da_decisao(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado, +origem: Fonte.JuizoSintatico,
  +estado: List<&2, U32>, +dados: R.DadosFerramentas, +recepcao: X.Recepcao,
  real: Cinco.EnquadramentoReal(fonte, c, s, origem, estado, S.esquema(c), S.limites(c), dados,
    X.decidir_recepcao_em(S.limites(c), recepcao), R.preprocessamento(dados))) -> Cinco.AuthDoCaso(s, R.decidir(c, recepcao, estado, dados)):
  L.e_esquerda(Cinco.AuthDoCaso(s, R.decidir(c, recepcao, estado, dados)), Cinco.GateDoCaso(R.juizo_de(dados), R.decidir(c, recepcao, estado, dados)),
    L.e_direita(Cinco.CasoReal(fonte, c, s, origem, R.decidir(c, recepcao, estado, dados)),
      L.E<Cinco.AuthDoCaso(s, R.decidir(c, recepcao, estado, dados)), Cinco.GateDoCaso(R.juizo_de(dados), R.decidir(c, recepcao, estado, dados))>,
      Cinco.rota_real_decidida(fonte, c, s, origem, estado, dados, recepcao, real)))

def OrigemChamada(~fonte: Fonte.Fonte, ~c: S.Configuracao, +s: D.Estado, +recepcao: X.Recepcao,
  dados: Fonte.ChamadaData) -> Type:
  match dados:
    case Fonte.ChamadaData{cf, +ps, pf, tf, +estado, +ferramentas, micro}:
      L.E<Cinco.ChamadaReal(fonte, c, s, recepcao, Fonte.ChamadaData{cf, ps, pf, tf, estado, ferramentas, micro}),
        Fonte.JuizoDoCaso(fonte, c, ps, R.decidir(c, recepcao, estado, ferramentas))>

def introduzir_da_chamada(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao,
  +cf: Fonte.JuizoSintatico, +origem: Fonte.JuizoSintatico, +pf: Fonte.JuizoSintatico, +tf: Fonte.JuizoSintatico,
  +estado: List<&2, U32>, +dados: R.DadosFerramentas, +micro: R.Micro, +u: Nat, +pre: Predecessor,
  canonico: {I.Atender{mundo, c, s, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario},
  metadata: {Fonte.chamada(fonte, mundo) == Fonte.ChamadaData{cf, origem, pf, tf, estado, dados, micro} : Fonte.ChamadaData},
  consulta: {Q.consultar(R.gerar(c, recepcao, estado, s, dados, micro), u) == Some{quadro_anterior(pre)} : Maybe<&2, Q.Quadro>}) ->
  I.Acontece(Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, u, fato_anterior(fonte, origem, pre)):
  Fonte.introduzir_fato_literal(fonte, Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, u, fato_anterior(fonte, origem, pre),
    L.Ambos{{==}, L.Ambos{canonico,
      (%Equal.sym(Fonte.ChamadaData, Fonte.chamada(fonte, mundo), Fonte.ChamadaData{cf, origem, pf, tf, estado, dados, micro}, metadata) :
        Fonte.de_observacao(fonte, c, Fonte.construir_chamada(c, s, recepcao, _), u, fato_anterior(fonte, origem, pre))
      observacao_anterior(fonte, c, s, origem, R.gerar(c, recepcao, estado, s, dados, micro), u, pre, consulta))}})

def regra_da_chamada(~fonte: Fonte.Fonte, ~c: S.Configuracao, lei: QualLei,
  +mundo: Nat, +s: D.Estado, +recepcao: X.Recepcao, dados: Fonte.ChamadaData,
  +t: Nat, f: I.Fato, canonico: {I.Atender{mundo, c, s, recepcao} == Fonte.cenario(fonte, mundo) : I.Cenario},
  origens: L.E<{Fonte.chamada(fonte, mundo) == dados : Fonte.ChamadaData}, {Fonte.chamada(fonte, mundo) == dados : Fonte.ChamadaData}>,
  real: OrigemChamada(fonte, c, s, recepcao, dados), fato: Fonte.da_rota(fonte, I.Atender{mundo, c, s, recepcao}, t, f)) ->
  Regra(lei, f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Atender{mundo, c, s, recepcao}, t):
  match dados origens real:
    case Fonte.ChamadaData{+cf, +origem, +pf, +tf, +estado, +ferramentas, +micro} L.Ambos{ler, repor} L.Ambos{execucao, juizo}:
      regra_bruta(fonte, c, lei, mundo, s, recepcao, origem, R.gerar(c, recepcao, estado, s, ferramentas, micro), t, f,
        caso_validado(fonte, c, s, origem, micro, R.decidir(c, recepcao, estado, ferramentas), aut_da_decisao(fonte, c, s, origem, estado, ferramentas, recepcao, execucao), juizo),
        +u => +pre => consulta => introduzir_da_chamada(fonte, c, mundo, s, recepcao, cf, origem, pf, tf, estado, ferramentas, micro, u, pre, canonico, repor, consulta),
        (%ler : Fonte.de_observacao(fonte, c, Fonte.construir_chamada(c, s, recepcao, _), t, f) fato))

def inicial_resultado_neutro(+m: R.Micro, +s: D.Estado, j: R.Juizo, resultado: R.ResultadoInicial, +valida: Bool) -> Neutras(R.render(m, s, R.decidir_juizo_inicial(j, resultado, valida))):
  match j:
    case R.Aceitou{}:
      match resultado:
        case R.Finalizada{}:
          match valida:
            case False{}: L.Ambos{{==}, L.Ambos{{==}, Unit{}}}
            case True{}: L.Ambos{{==}, L.Ambos{{==}, neutras_concatenadas(R.micro_saida(m), R.render_inicial(P.codificar(D.estado_valor(s)), s), micro_saida_neutra(m), inicial_neutra(P.codificar(D.estado_valor(s)), s))}}
        case R.FalhouInicial{+aceita, +etapa, +id, +fatal}: L.Ambos{{==}, neutras_concatenadas(R.prefixo_inicial(m, aceita && valida), [Q.Falhou{etapa, id, fatal}, Q.InicialRecusada{S.Falha{}}], prefixo_inicial_neutro(m, aceita && valida), L.Ambos{{==}, L.Ambos{{==}, Unit{}}})}
        case R.PendenteInicial{aceita}: L.Ambos{{==}, prefixo_inicial_neutro(m, aceita && valida)}
    case R.Recusou{}: L.Ambos{{==}, L.Ambos{{==}, Unit{}}}
    case R.ErroJuizo{id, fatal}: L.Ambos{{==}, L.Ambos{{==}, L.Ambos{{==}, Unit{}}}}
    case R.PendenteJuizo{}: L.Ambos{{==}, Unit{}}

def regra3_inicial(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +pi: String,
  +xs: List<&2, Q.Quadro>, +t: Nat, f: I.Fato, neutras: Neutras(xs), fato: Q.observa_servico(c, Fonte.sem_programa(), None{}, xs, t, f)) ->
  K.Regra3(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t):
  match f:
    case I.ConfiguracaoEmUso{a0}: Unit{}
    case I.InspecaoNaoModelada{a0}: Unit{}
    case I.EfeitoNaoModelado{a0}: Unit{}
    case I.InstanciaIniciou{a0}: Unit{}
    case I.InicializacaoRecusada{a0}: Unit{}
    case I.ProvaInicialAceita{}: Unit{}
    case I.Codificou{a0, a1}: Unit{}
    case I.Decodificou{a0, a1}: Unit{}
    case I.Guardou{a0, a1, a2}: Unit{}
    case I.Operou{a0, a1, a2, a3}: Unit{}
    case I.ConferiuComprimento{a0, a1}: Unit{}
    case I.AlocouCampo{a0, a1}: Unit{}
    case I.LeuCorpo{a0, a1, a2}: Unit{}
    case I.RecebeuRequisicao{a0}: Unit{}
    case I.Autenticou{a0, a1}: F.absurdo_booleano(K.Regra3(I.Autenticou{a0, a1}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t),
      neutra_consultada(xs, t, Q.Autenticada{a0, a1}, neutras, Q.observacao_quadro(c, Fonte.sem_programa(), xs, t, I.Autenticou{a0, a1}, fato)))
    case I.CertificadoAceito{a0, a1, a2}: Unit{}
    case I.CertificadoRejeitado{a0, a1}: Unit{}
    case I.ProgramaComecou{a0, a1, a2}: F.absurdo_booleano(K.Regra3(I.ProgramaComecou{a0, a1, a2}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t),
      neutra_consultada(xs, t, Q.Comecada{a0, a1}, neutras, Q.observacao_quadro(c, Fonte.sem_programa(), xs, t, I.ProgramaComecou{a0, a1, a2}, fato)))
    case I.Avaliou{a0, a1, a2, a3}: Unit{}
    case I.Preparou{a0, a1}: Unit{}
    case I.Publicou{a0}: Unit{}
    case I.EstadoVisivel{a0}: Unit{}
    case I.FalhouAmbiente{a0, a1, a2}: Unit{}
    case I.Concluiu{a0, a1, a2}: Unit{}
    case I.EntregouTudo{a0}: Unit{}
    case I.EntregaInterrompida{a0}: Unit{}
    case I.EncerrouCanal{}: Unit{}
    case I.ProximaChamada{a0, a1}: Unit{}

def regra4_inicial(~fonte: Fonte.Fonte, ~c: S.Configuracao, +mundo: Nat, +s: D.Estado, +pi: String,
  +xs: List<&2, Q.Quadro>, +t: Nat, f: I.Fato, neutras: Neutras(xs), fato: Q.observa_servico(c, Fonte.sem_programa(), None{}, xs, t, f)) ->
  K.Regra4(f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t):
  match f:
    case I.ConfiguracaoEmUso{a0}: Unit{}
    case I.InspecaoNaoModelada{a0}: Unit{}
    case I.EfeitoNaoModelado{a0}: Unit{}
    case I.InstanciaIniciou{a0}: Unit{}
    case I.InicializacaoRecusada{a0}: Unit{}
    case I.ProvaInicialAceita{}: Unit{}
    case I.Codificou{a0, a1}: Unit{}
    case I.Decodificou{a0, a1}: Unit{}
    case I.Guardou{a0, a1, a2}: Unit{}
    case I.Operou{a0, a1, a2, a3}: Unit{}
    case I.ConferiuComprimento{a0, a1}: Unit{}
    case I.AlocouCampo{a0, a1}: Unit{}
    case I.LeuCorpo{a0, a1, a2}: Unit{}
    case I.RecebeuRequisicao{a0}: Unit{}
    case I.Autenticou{a0, a1}: Unit{}
    case I.CertificadoAceito{a0, a1, a2}: F.absurdo_booleano(K.Regra4(I.CertificadoAceito{a0, a1, a2}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t),
      neutra_consultada(xs, t, Q.Aceita{a0, a1}, neutras, Q.observacao_quadro(c, Fonte.sem_programa(), xs, t, I.CertificadoAceito{a0, a1, a2}, fato)))
    case I.CertificadoRejeitado{a0, a1}: F.absurdo_booleano(K.Regra4(I.CertificadoRejeitado{a0, a1}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t),
      neutra_consultada(xs, t, Q.Rejeitada{a0, a1}, neutras, Q.observacao_quadro(c, Fonte.sem_programa(), xs, t, I.CertificadoRejeitado{a0, a1}, fato)))
    case I.ProgramaComecou{a0, a1, a2}: F.absurdo_booleano(K.Regra4(I.ProgramaComecou{a0, a1, a2}, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t),
      neutra_consultada(xs, t, Q.Comecada{a0, a1}, neutras, Q.observacao_quadro(c, Fonte.sem_programa(), xs, t, I.ProgramaComecou{a0, a1, a2}, fato)))
    case I.Avaliou{a0, a1, a2, a3}: Unit{}
    case I.Preparou{a0, a1}: Unit{}
    case I.Publicou{a0}: Unit{}
    case I.EstadoVisivel{a0}: Unit{}
    case I.FalhouAmbiente{a0, a1, a2}: Unit{}
    case I.Concluiu{a0, a1, a2}: Unit{}
    case I.EntregouTudo{a0}: Unit{}
    case I.EntregaInterrompida{a0}: Unit{}
    case I.EncerrouCanal{}: Unit{}
    case I.ProximaChamada{a0, a1}: Unit{}

def regra_inicial(~fonte: Fonte.Fonte, ~c: S.Configuracao, lei: QualLei, +mundo: Nat, +s: D.Estado, +pi: String,
  +xs: List<&2, Q.Quadro>, +t: Nat, f: I.Fato, neutras: Neutras(xs), fato: Q.observa_servico(c, Fonte.sem_programa(), None{}, xs, t, f)) ->
  Regra(lei, f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t):
  match lei:
    case AutenticacaoLei{}: regra3_inicial(fonte, c, mundo, s, pi, xs, t, f, neutras, fato)
    case AdmissaoLei{}: regra4_inicial(fonte, c, mundo, s, pi, xs, t, f, neutras, fato)

def regra_dados_iniciais(~fonte: Fonte.Fonte, ~c: S.Configuracao, lei: QualLei,
  +mundo: Nat, +s: D.Estado, +pi: String, dados: Fonte.InicialData, +t: Nat, f: I.Fato,
  metadata: {Fonte.inicial(fonte, mundo) == dados : Fonte.InicialData}, fato: Fonte.da_rota(fonte, I.Inicializar{mundo, c, s, pi}, t, f)) ->
  Regra(lei, f, Fonte.ambiente(fonte), Fonte.artefato(fonte), I.Inicializar{mundo, c, s, pi}, t):
  match dados:
    case Fonte.InicialData{cf, sf, pf, +j, +resultado, +micro}:
      regra_inicial(fonte, c, lei, mundo, s, pi, R.gerar_resultado_inicial(c, Fonte.identidade(fonte), s, j, resultado, micro), t, f,
        inicial_resultado_neutro(micro, s, j, resultado, Config.valida(c, Fonte.identidade(fonte))),
        (%metadata : Fonte.de_observacao(fonte, c, Fonte.construir_inicial(Fonte.identidade(fonte), c, s, _), t, f) fato))

# Contratos de fonte por mundo: equacoes reais do executor/snapshot e os
# dois termos fechados julgados pelo checker. Nenhuma lei e uma premissa.
def OrigemDoMomento(~fonte: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, +mundo: Nat, momento: Cenarios.Momento) -> Type:
  match momento:
    case Cenarios.Inicializacao{}: Unit
    case Cenarios.Atendimento{+recepcao}:
      OrigemChamada(fonte, c, Historico.estado(historico(mundo), seed(Unit{})), recepcao, Fonte.chamada(fonte, mundo))

def regra_por_momento(~fonte: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~pi: String, lei: QualLei, momento: Cenarios.Momento,
  +mundo: Nat, +t: Nat, f: I.Fato,
  canonico: {Cenarios.de_momento(c, seed, historico, pi, momento, mundo) == Fonte.cenario(fonte, mundo) : I.Cenario},
  origem: OrigemDoMomento(fonte, c, seed, historico, mundo, momento),
  fato: Fonte.da_rota(fonte, Cenarios.de_momento(c, seed, historico, pi, momento, mundo), t, f)) ->
  Regra(lei, f, Fonte.ambiente(fonte), Fonte.artefato(fonte), Cenarios.de_momento(c, seed, historico, pi, momento, mundo), t):
  match momento:
    case Cenarios.Inicializacao{}:
      regra_dados_iniciais(fonte, c, lei, mundo, seed(Unit{}), pi, Fonte.inicial(fonte, mundo), t, f, {==}, fato)
    case Cenarios.Atendimento{+recepcao}:
      regra_da_chamada(fonte, c, lei, mundo, Historico.estado(historico(mundo), seed(Unit{})), recepcao, Fonte.chamada(fonte, mundo), t, f, canonico, L.Ambos{{==}, {==}}, origem, fato)

def regra_do_cenario(~base: Fonte.Fonte, ~c: S.Configuracao, ~seed: Unit -> D.Estado,
  ~historico: Nat -> List<&2, Historico.Registro>, ~momentos: Nat -> Cenarios.Momento, ~pi: String,
  lei: QualLei, x: I.Cenario, +t: Nat, f: I.Fato,
  origens: @m: Nat -> OrigemDoMomento(Modelo.fonte(base, c, seed, historico, momentos, pi), c, seed, historico, m, momentos(m)),
  fato: I.Acontece(Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momentos, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momentos, pi)), x, t, f)) ->
  Regra(lei, f, Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momentos, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momentos, pi)), x, t):
  match x:
    case I.Inicializar{+mundo, configuracao, +s, +prova}:
      match fato:
        case L.Ambos{nome, L.Ambos{igual, obs}}:
          %Equal.sym(I.Cenario, I.Inicializar{mundo, configuracao, s, prova}, Cenarios.canonico(c, seed, historico, momentos, pi, mundo),
            Equal.trans(I.Cenario, I.Inicializar{mundo, configuracao, s, prova}, Fonte.cenario(Modelo.fonte(base, c, seed, historico, momentos, pi), mundo),
              Cenarios.canonico(c, seed, historico, momentos, pi, mundo), igual, Modelo.cenario_do_modelo(base, c, seed, historico, momentos, pi, mundo))) :
            Regra(lei, f, Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momentos, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momentos, pi)), _, t)
          regra_por_momento(Modelo.fonte(base, c, seed, historico, momentos, pi), c, seed, historico, pi, lei, momentos(mundo), mundo, t, f,
            Equal.sym(I.Cenario, Fonte.cenario(Modelo.fonte(base, c, seed, historico, momentos, pi), mundo), Cenarios.canonico(c, seed, historico, momentos, pi, mundo), Modelo.cenario_do_modelo(base, c, seed, historico, momentos, pi, mundo)),
            origens(mundo), (%Modelo.cenario_do_modelo(base, c, seed, historico, momentos, pi, mundo) : Fonte.da_rota(Modelo.fonte(base, c, seed, historico, momentos, pi), _, t, f) obs))
    case I.Atender{+mundo, configuracao, +s, +recepcao}:
      match fato:
        case L.Ambos{nome, L.Ambos{igual, obs}}:
          %Equal.sym(I.Cenario, I.Atender{mundo, configuracao, s, recepcao}, Cenarios.canonico(c, seed, historico, momentos, pi, mundo),
            Equal.trans(I.Cenario, I.Atender{mundo, configuracao, s, recepcao}, Fonte.cenario(Modelo.fonte(base, c, seed, historico, momentos, pi), mundo),
              Cenarios.canonico(c, seed, historico, momentos, pi, mundo), igual, Modelo.cenario_do_modelo(base, c, seed, historico, momentos, pi, mundo))) :
            Regra(lei, f, Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momentos, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momentos, pi)), _, t)
          regra_por_momento(Modelo.fonte(base, c, seed, historico, momentos, pi), c, seed, historico, pi, lei, momentos(mundo), mundo, t, f,
            Equal.sym(I.Cenario, Fonte.cenario(Modelo.fonte(base, c, seed, historico, momentos, pi), mundo), Cenarios.canonico(c, seed, historico, momentos, pi, mundo), Modelo.cenario_do_modelo(base, c, seed, historico, momentos, pi, mundo)),
            origens(mundo), (%Modelo.cenario_do_modelo(base, c, seed, historico, momentos, pi, mundo) : Fonte.da_rota(Modelo.fonte(base, c, seed, historico, momentos, pi), _, t, f) obs))

law lei3_do_modelo:
  for ~base: Fonte.Fonte
  for ~c: S.Configuracao
  for ~seed: Unit -> D.Estado
  for ~historico: Nat -> List<&2, Historico.Registro>
  for ~momentos: Nat -> Cenarios.Momento
  for ~pi: String
  for origens: @m: Nat -> OrigemDoMomento(Modelo.fonte(base, c, seed, historico, momentos, pi), c, seed, historico, m, momentos(m))
  K.Lei3(Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momentos, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momentos, pi)))
def lei3_do_modelo(base, c, seed, historico, momentos, pi, origens):
  x => +t => f => fato => regra_do_cenario(base, c, seed, historico, momentos, pi, AutenticacaoLei{}, x, t, f, origens, fato)

law lei4_do_modelo:
  for ~base: Fonte.Fonte
  for ~c: S.Configuracao
  for ~seed: Unit -> D.Estado
  for ~historico: Nat -> List<&2, Historico.Registro>
  for ~momentos: Nat -> Cenarios.Momento
  for ~pi: String
  for origens: @m: Nat -> OrigemDoMomento(Modelo.fonte(base, c, seed, historico, momentos, pi), c, seed, historico, m, momentos(m))
  K.Lei4(Fonte.ambiente(Modelo.fonte(base, c, seed, historico, momentos, pi)), Fonte.artefato(Modelo.fonte(base, c, seed, historico, momentos, pi)))
def lei4_do_modelo(base, c, seed, historico, momentos, pi, origens):
  x => +t => f => fato => regra_do_cenario(base, c, seed, historico, momentos, pi, AdmissaoLei{}, x, t, f, origens, fato)
