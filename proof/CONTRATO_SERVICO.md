# Composição das oito leis

Alvo: construir `LAWS.Contrato(a,k)` para o serviço serial em
`server/main.rs`, com admissão em `tools/admission`, preparação em
`tools/service` e execução das funções Bend de `src`. As oito leis e a
arquitetura permanecem as atuais. Este mapa não é uma prova desse alvo.

A base `e0b3bbb` passou `make build`, `make verify-contract`, `make verify`
e `make test` antes desta composição. A aceitação dos agregados comprova os
termos neles contidos, não instancia automaticamente `Interface.Ambiente`.

| Lei | Código responsável | Provas existentes | Lacuna de composição | Contratos externos utilizados |
| --- | --- | --- | --- | --- |
| 1 — inicialização/configuração | `stage.INITIALIZE`, `assertInitialization`, `Database::initialize` | `Configuracao.aceita_satisfaz_configuracao_valida_original`; reconstrução de estado em `Representacao` | Ordenar verificação do seed e início; excluir início após recusa; conservar a configuração entre chamadas. | Verificador correto para o alvo inicial; mesmos fontes/seed no executável; transporte exato. |
| 2 — representação/operações | `Codec`, `Entrada`, `Estado`, `Transporte`, `Nucleo`; `packet`, `split`, `serve_stream` | `CodecLei2.decodificar_satisfaz_relacao_original`; `Representacao.transporte_privado_preserva_estado`; `EntradaRelacoes`; `RecepcaoLimites`; `AlocacoesComprimentos`; `Maquina.operacao_real_vincula_transicao` | Ligar os resultados a todos os fatos reais, incluindo leitura do corpo e conferência anterior à construção dos campos. | Compilação fiel; pipes preservam bytes; ligação dos fatos às chamadas reais, sem omissões. |
| 3 — identidade | `Entrada.autenticar`, `D.autenticar`; `Database::propose` | `Adaptadores.entrada_recebida_tem_identidade_autentica`; `Autenticacao.autenticacao_implica_contexto_presente` | Ordenar recebimento/autenticação/início e manter o snapshot publicado inicial nos workers. | Transporte do estado e da requisição; execução das fontes congeladas. A identidade não é uma premissa externa. |
| 4 — certificado | `assertBindings`, `assertInitialization`, `audit`, `checkBook`, `emitC` | Reificação dos argumentos; alvo exato `R.Certifica` e término; `Seguranca.certificado_cobre_execucao_autenticada` | Relacionar a fonte e a derivação com `Elabora`/`Deriva`; aceitação antes de executar; rejeição matemática distinta de falha técnica. | Correção das ferramentas oficiais; fechamento de dependências e vínculos exatos da admissão. |
| 5 — execução/observações | `Nucleo.avancar`, `Execucao.avancar`, `native/effects.c` | `Nucleo.fidelidade_de_todos_os_prefixos`; `Maquina.prefixos_da_maquina_em_ordem`; `operacao_real_vincula_transicao`; `Seguranca` | Provar ordem e exclusividade dos passos: cada operação ocupa uma única janela; nenhum passo após término; nenhuma observação omitida. | Compilação fiel; os efeitos C invocam o passo fechado segundo sua implementação; refinamento das fases concretas. |
| 6 — publicação | `Nucleo.preparar/concluir`; Rust `propose`, `checked_proposal`, `Published::finish` | `Preparacao.preparar_preserva_resposta_estado_eventos_e_bytes`; `Publicacao.conclusao_de_preparacao_certificada_e_valida`; `Chamada.chamada_autenticada_prepara_e_conclui`; rollback para todo não-sucesso | Provar a única troca do publicado após preparação/cleanup; validade preservada entre chamadas; entrega não desfaz publicação. | Refinamento das operações concretas de bytes/store para o protocolo de fases. Não assumir “publica corretamente”. |
| 7 — respostas/falhas/canal | `R.finalizar`, `Nucleo.preparar`; `Error::response`, `capture`, `serve_stream` | `Preparacao.finalizar_garante_payload_e_tamanho`; `ErrosFixos`; `Recursos`; `Transporte` | Ordenar causa/preparação/conclusão/entrega; exclusão entre entrega completa e interrompida; mapear cada falha efetiva. | Contratos de erro/EOF dos processos e canais; classificação da admissão; refinamento dos blocos do host. |
| 8 — progresso | `ProgramaTermina`, `Native.loop`, sequência serial Rust/Node | `Terminacao.finita_termina`; `Maquina.terminacao_da_referencia_implica_terminacao_incremental`; `Chamada.finalizacao_tem_preparacao_real`; completude do Codec/configuração | Progresso das fases externas; completude da admissão no fragmento fixado independentemente do resultado do candidato. | Término das ferramentas e IO quando o ambiente é processável; completude no fragmento declarado. Sem prazo ou quota física. |

## Composição a construir

A sequência de fases deve chamar as funções existentes: configuração,
recepção, autenticação, admissão, máquina incremental, preparação, publicação
e entrega. As transições devem produzir os fatos `Interface.Fato`; uma
indução de suas execuções deve estabelecer ordem, unicidade e invariantes.
Os lemas existentes estabelecem o conteúdo dos resultados dessas transições.
Não é necessário adicionar logs, observador ou novos efeitos ao servidor.

O primeiro fechamento matemático está em `Chamada.bend`: existência da
preparação real e composição do caminho autenticado e certificado nas funções
`Nucleo.iniciar/percorrer/preparar/concluir`. Sua conclusão não é
`Contrato(a,k)`; falta a sequência composta de fatos das fases do serviço.
O teorema de conclusão recebe a igualdade do percurso final efetivamente
calculado. `Maquina.terminacao_da_referencia_implica_terminacao_incremental`
fornece esse antecedente a partir da testemunha de término, em um lema
separado; não se afirma que o novo termo já compõe também essa passagem.

## Fronteira com a execução concreta

As hipóteses sobre ferramentas são preservação da semântica pelo compilador
e runtime oficiais e correção do checker/Safe/BendTT para os fontes e o
fragmento fixados. Os imports, os alvos e a seleção dos mesmos insumos são
responsabilidade da aplicação; hashes identificam bytes, não demonstram essas
hipóteses.

A ligação Rust/Node/C deve ser um refinamento operacional identificado por
bloco: bytes enviados/recebidos, fase executada, resultado das funções Bend e
store efetuado. Se essa ligação for sustentada por revisão e testes, continua
sendo hipótese explícita para a garantia aplicada ao executável, não uma
prova mecanizada do Rust. O protocolo correspondente ainda precisa ser
construído e demonstrado, antes de receber tal hipótese.

Para segurança, todo fato real deve corresponder a uma transição do protocolo.
Para a Lei 8, isso não basta: um observador vazio também satisfaria tal inclusão.
É necessário provar progresso/reflexão sob `Processavel`, que é externo e
independente da decisão do candidato. Não se pode defini-lo como “o servidor
terminou” nem presumir que uma chamada válida foi atendida.

Não constituem solução: receber `Lei1`…`Lei8` ou `Regra1`…`Regra8` como oito
callbacks, conceder publicação/execução corretas como premissas, ou aceitar uma
lista de fatos escolhida pelo candidato que possa esconder operações reais.
Não há ainda termo final de `Contrato(a,k)` para o serviço.
