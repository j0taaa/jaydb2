# Admissão

O gate recebe o programa e seu certificado para uma configuração, identidade e argumentos fixados pelo host. Dependências registradas, bytes de fonte e alvos do certificado precisam coincidir exatamente. Metas, leis abertas, unsafe e efeitos externos do cliente são recusados, inclusive em definições sem uso.

```js
import { admitSubmission, emitC } from './index.mjs';
const admitted = await admitSubmission(hostManifest);
const c = emitC(admitted);
```

O handle público expõe `sources` e `report`. O Book checado fica privado e é o mesmo objeto entregue ao compilador oficial. Não há API para alterar declarações após a checagem. `configurationLimits(admitted)` lê os três tamanhos lógicos para o serviço.

## Ferramentas oficiais

1. Preflight fixa os bytes e as dependências autorizadas antes de executar o frontend.
2. O checker oficial Bend 2.0.39 verifica a fonte.
3. O Safe oficial traduz as declarações; o BendTT original verifica esse payload.
4. O compilador oficial emite o C do mesmo Book, sem reler fontes da submissão.

As fontes e o kernel são conferidos contra `toolchain.lock.json`. Os módulos TypeScript oficiais são carregados com remoção de sintaxe TypeScript pelo Node, sem patch semântico. O JayDB não modifica conversão, templates, quantidades, regras lógicas, combustível ou runtime do Bend.

Não existem layouts Safe alternativos, fechamento próprio de instâncias, `source_links` gerados, avaliadores estruturais ou tentativas por um segundo caminho após rejeição. Uma forma não representada pelo Safe oficial não é uma prova de falsidade; o banco não altera o tradutor para admiti-la.

Os bindings da aplicação continuam exigindo a configuração, o código, o contexto e os argumentos reais. O estado publicado não é copiado para o diretório de compilação.

## Fronteira do núcleo

`admitKernel` admite os wrappers confiáveis do JayDB. Somente suas declarações foreign registradas recebem a permissão de integração; o cliente não recebe essa capacidade. A inicialização exige uma prova de validade do seed para a configuração real. O host compila o C oficial sem reescrevê-lo e executa cada chamada num processo auxiliar, conservando a publicação no host.

Use os comandos do README raiz. Não há instalação de verificador derivado, addon de stack, orçamento físico ou prazo por requisição. Limitações próprias das ferramentas oficiais permanecem inalteradas. O gate não declara preservação semântica geral nem `Contrato` do executável completo.

O launcher usa a opção pública `node --stack_size=65536` para o Safe oficial. O perfil exige o limite hard de stack do Linux ilimitado e eleva o limite soft a ilimitado antes de executar o Node. É uma configuração de execução do auxiliar; os fontes Bend e V8 não são alterados.
