# JayDB2

Banco em RAM que executa programas Bend acompanhados de provas contra as leis do administrador. O serviço atende requisições seriais por stdin/stdout, autentica pelo estado publicado e prepara estado e resposta antes de publicar uma única alteração.

O contrato ativo tem **três limites de tamanho canônico: mensagem, estado e resposta**. A retirada dos orçamentos físicos foi autorizada em 2026-10-29. A execução não exige observador de memória, prazo por etapa, contabilidade de alocações ou recuperação garantida após falta de recursos. Uma chamada cara pode ocupar a instância; uma falha fatal pode perder seus dados em RAM.

Autenticação, pureza, terminação matemática, vínculo entre programa e prova, leis sobre todos os acessos e publicação atômica continuam obrigatórios. **A correspondência geral do executável completo com o contrato ainda não foi demonstrada.** O estado atual reúne provas gerais e testes reais; há formas de templates dependentes em extensão na admissão.

## Executar

O perfil atual usa Linux x86_64, páginas de 4096 bytes, Clang 19, Python 3.12 e Node 24.19+. Bend 2.0.39, kernels, frontend e backend são fixados por hash. O runtime usa CPU no thread principal do mesmo processo, com stack Linux expansível. Helpers de verificação e compilação têm inicialização Python isolada. Opções que substituem ferramentas ou injetam carregadores externos são recusadas para preservar o ambiente verificado.

```sh
python3 tools/bootstrap.py --source /caminho/bend-2.0.39 --kernel /caminho/bendtt
python3 -m tools.service.build_loading .tools/service/loading.so
python3 -m tools.service.build_lifecycle .tools/service/lifecycle.so
node tools/admission/build-frontend.mjs --write-lock
node tools/verifier/build.mjs --write-lock
python3 jaydb2.py --configuration examples/sem-observacoes/Configuration.bend \
  --seed examples/sem-observacoes/Seed.bend
```

O bootstrap instala ferramentas locais em `.tools/`. A construção do verificador derivado requer Lean 4.34.0 e preserva o kernel original. Loader e lifecycle são preparados antes do serviço; seus recibos mantêm ownership de subprocessos, bibliotecas e saídas mesmo se Python receber uma exceção. Não se compila esses shims durante uma requisição.

O cliente produz uma mensagem canônica enquadrada em stdout:

```sh
python3 tools/client.py --codigo examples/sem-observacoes/Client.bend \
  --prova examples/sem-observacoes/ClientProof.bend --credencial demo
```

`python3 tools/client.py --decode` lê uma resposta e imprime JSON. A configuração pública registra suas dependências imutáveis e usa `Environment.identidade()`; o seed contém o estado inicial e sua prova exata de validade, permanece privado e não integra a identidade pública. O estado da instância nunca entra nos diretórios de compilação.

## Funcionamento

Código e certificado são admitidos juntos para a configuração, identidade autenticada e argumentos efetivos. O mesmo Book verificado segue para emissão. Codec, autenticação, interpretação incremental e preparação executam como Bend compilado; o runtime simples não usa um segundo parser C.

Alterações ficam privadas até a publicação. Cada sucesso publica estado e resposta completos numa única troca de referência. Recusa e erro anterior conservam o estado. Perder o canal depois da publicação não desfaz a operação; uma leitura ou escrita de consumo incerto não é repetida automaticamente.

Credenciais podem ficar vazias ou duplicadas no estado provisório se as leis permitirem. Inicialização e publicação exigem credenciais não vazias e únicas. A autenticação usa o estado publicado inicial; mudanças afetam a próxima chamada.

## Verificação e limites atuais

```sh
make verify-contract
make verify
make test-host
make test-admission
make test-native
make test-integration
```

A [revisão das provas](proof/REVISAO_RECURSOS_SIMPLES.md) registra 72 verificações oficiais do contrato revisado, wrappers, exemplos, agregados e negativos. Inclui as 692 leis gerais do Codec, com correção nos dois sentidos. O `--verdict` separado do lote legado de 222 exemplos excedeu o harness de desenvolvimento e continua explicitamente incompleto.

O [runtime simples ABI6](native/SIMPLE_RUNTIME.md) passou 13 testes com execução C real, incluindo Codec original, inteiros largos, closures e falha real de alocação. Esses resultados não substituem uma prova geral de compilação ou de `Contrato(a,k)` para o serviço. A ligação integral entre admissão, emissão, runtime, host e canal permanece em desenvolvimento.

A [especificação ativa](ESPECIFICACAO.md) e os 14 módulos em `contrato/` definem o contrato revisado. O original está preservado literalmente em [history/contrato-v1](history/contrato-v1/contrato/README.md), além do snapshot anterior à migração. Os protótipos de accounting, deadlines e conclusão física permanecem como histórico; não são carregados nem exigidos pela entrada ativa. Relatórios antigos pertencem a seus próprios contratos e hashes.

A prioridade é concluir a primeira versão funcional e depois simplificar o código ativo, preservando as garantias centrais.
