# Admissão

O gate recebe o programa e seu certificado para uma configuração, identidade e argumentos fixados pelo host. Apenas Bend puro e terminante é admitido; metas, leis abertas, unsafe, foreign e IO externos são recusados também em definições sem uso. Dependências registradas, bytes de fonte e alvos do certificado precisam coincidir exatamente.

```js
import { admitSubmission, emitC, emitGenericC } from './index.mjs';
const admitted = await admitSubmission(hostManifest);
const report = admitted.report;
const c = emitC(admitted);
// Ou emitGenericC(admitted, {backendSha256: hashFixadoPeloHost}).
```

O handle público expõe `sources` e `report`. O Book checado fica privado no módulo e é o mesmo objeto passado ao emissor fixado. Não há API para editar declarações após a checagem; um objeto que imite o relatório não autoriza emissão. `configurationLimits(admitted)` lê somente os três tamanhos lógicos para o helper do serviço.

## Caminho de confiança

1. Preflight congela bytes e dependências autorizadas, antes de executar o frontend.
2. O checker primário original verifica a fonte. O fechamento de templates usa o elaborador original; o primário verifica o grafo final e a auditoria de capacidades é repetida.
3. Safe traduz as mesmas declarações e o BendTT verifica o payload completo.
4. A emissão usa o Book privado, sem reler fontes da submissão. Apenas um backend é escolhido para aquele handle.

Os hashes de fonte, contrato, frontend, backend e kernels estão nos locks. A configuração pública faz parte da identidade; o estado publicado não entra no diretório de compilação.

## Templates e evidências

O resolvedor de instâncias mantém as especializações físicas realmente consumidas pelo compilador. Cada `source_link` compara a árvore física com a elaboração independente de sua origem; não substitui um corpo existente para fazê-lo passar. Instâncias da Base recebem a mesma exigência.

Há dois layouts Safe compartilhando essas verificações: o físico e a extensão estrutural de tipos dependentes. A escolha é determinada pelos tipos antes do verdict. Uma rejeição do kernel nunca provoca tentativa de aceite por outra rota.

A extensão usa o corpo lógico paramétrico e relações compostas dos tipos e corpos checados. Funções têm um avaliador vivo; seus índices são apagados. Igualdades mantêm a evidência exata por J, sem funext, irrelevância de provas ou axioma novo. A execução fechada constrói suas relações; não recebe uma hipótese externa de correção do helper.

O fingerprint interno existe apenas para detectar o ponto fixo do fechamento. Não há selagem de protótipos JavaScript, getters, descritores ou suporte a um embedding que adultere estruturas internas.

O mesmo compositor abre os padrões e transporta seus endpoints por J. Para provas sobre Data monomórficos, conserva a árvore completa de matches antes do transporte, que só fecha na folha. Os resultados recursivos usados ali são fornecidos por chamadas reais no subcampo menor, preservando as evidências dos parâmetros anteriores. Domínios lineares e dependentes mantêm o fechamento imediato; nenhum verdict provoca troca de rota.

## Fronteira IO do núcleo

`admitKernel` admite os wrappers confiáveis de inicialização, leitura, autenticação e execução. As assinaturas foreign de `native/effects.bend` e os IDs de efeito precisam corresponder aos bindings do kernel; o cliente não recebe essa permissão. A inicialização exige a prova de validade do seed real, para a configuração real.

## Instalação e limites

Use os comandos do README raiz. O frontend é derivado offline das fontes oficiais fixadas; o serviço não compila um novo verificador a partir da submissão. O launcher usa stack Linux expansível e o addon Node autenticado. Não possui parâmetros de memória ou de deadline por requisição.

`verification.initialFuel` e `initialModelFuel` são controles de desenvolvimento do verificador. A exaustão aumenta o combustível sem teto; não se transforma em recusa matemática. Não há orçamento físico obrigatório.

A tradução estrutural ainda não cobre todos os tipos originais: recursão por matches que exige transportar funções lineares entre os parâmetros, grupos gerados mutuamente recursivos, reflexão opaca, quantidades simbólicas e certas renderizações podem falhar tecnicamente. O gate não declara preservação semântica geral nem `Contrato` do executável.
