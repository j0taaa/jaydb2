# Serviço com três limites lógicos

Esta é a entrada ativa após a revisão autorizada em 2026-10-29. `jaydb2.py` usa
`controller.Database`, `abi_simple.SimpleModule` e `tools/native/build_simple.py`.
Não carrega accounting, N1/N2, relógios por etapa, guardas de memória, o decoder
C alternativo ou os módulos antigos de conclusão física. Os arquivos anteriores
continuam preservados; sua existência no repositório não os torna dependências
da entrada atual.

## Caminho da chamada

1. O host lê o enquadramento e verifica o teto de mensagem.
2. Módulos Bend compilados decodificam e autenticam pelo estado publicado.
3. A admissão verifica fonte, dependências e prova contra a configuração,
   contexto e argumentos reais. A emissão recebe o mesmo Book admitido.
4. O hash do C lido pelo builder deve coincidir com a emissão; o descritor do
   módulo carregado deve identificar esse mesmo C e seu build.
5. O programa Bend executa no mesmo PID, em CPU no thread principal. O estado
   de trabalho é privado. O Codec é o programa original compilado.
6. O host obtém os bytes completos de estado e resposta, verifica o transporte,
   resolve leases, fecha o módulo temporário e remove seu diretório.
7. Um sucesso substitui uma única referência por `Published(state, response)`
   imutável. Uma recusa ou erro anterior mantém a referência anterior.
8. A entrega vem depois da publicação. Uma falha posterior conserva o par
   publicado; não há repetição automática nem deduplicação de requisições.

Os diretórios de compilação recebem configuração, fonte, prova, contexto e
argumentos; nunca recebem o estado privado da instância ou o seed de outra
requisição. O seed só participa da inicialização, é removido depois e não
entra na identidade pública.

## Ownership e falhas

Os recibos existentes de loading/lifecycle continuam necessários para não
perder um subprocesso, biblioteca ou saída quando uma exceção ocorre dentro
de uma chamada C. O registro forte precede a aquisição. Um owner pendente
impede publicação e resposta normal; o host conserva a referência para cleanup.
Esses recibos são sobre ownership, sem orçamento físico ou epoch de verificação.

Helpers usam pipes e são recolhidos antes da conclusão. O líder permanece
identificável por WNOWAIT até o encerramento do grupo, antes do reap. A pausa
de 50 ms do seletor só permite observar o fim do líder quando um descendente
mantém o pipe aberto; ela não limita a duração da chamada.

Somente mensagem, estado e resposta têm teto configurado em bytes canônicos.
Igualdade é permitida. O transporte privado usa extensões u64; a capacidade
indicada ao runtime não pré-aloca essa quantidade de memória. Falha efetiva de
alocação nativa torna o módulo inutilizável, sem fingir um `limite` físico
recuperável. Falha fatal pode encerrar a instância RAM sem resposta.

O serviço não repete uma leitura ou escrita cujo consumo ficou incerto após
uma exceção. O canal é encerrado. Um EOF ou erro de framing conhecido também
encerra aquela sessão; um consumidor confiável da API pode fornecer outro canal.
A CLI usa uma única sessão e depois fecha a instância.

## Verificação

`make test-host` verifica a publicação, rollback, ownership, pipes, sinais,
staging imutável e vínculos de emissão. Os positivos simulados são explicitamente
fixtures de fronteira. `make test-integration` admite, compila e executa Bend
real para inicialização, autenticação, certificados, framing e transações de
credenciais. `make test-native` verifica a ABI6 e o runtime geral.

A revisão do contrato e as provas estão em
[REVISAO_RECURSOS_SIMPLES.md](../../proof/REVISAO_RECURSOS_SIMPLES.md).
Os registros novos da integração ficam em
[recursos-simples-v2](../../tests/service/evidence/recursos-simples-v2/).
As primeiras tentativas com erros de fixtures e os timeouts de desenvolvimento
permanecem registradas; não são contados como aprovação.

Não há uma prova geral de `Contrato(a,k)` para o executável. A extensão da
tradução de templates dependentes e as relações completas de compilação,
runtime e host continuam obrigações abertas. Hashes ligam artefatos, mas não
substituem essas provas.
