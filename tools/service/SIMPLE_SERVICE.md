# Serviço com três limites lógicos

Configuração e dependências do administrador são públicas. O arquivo escolhido
como seed é privado e só participa da inicialização; a configuração pública não
pode importá-lo, inclusive por outro nome ou caminho para o mesmo arquivo.

A entrada ativa é `./jaydb2` → `server/main.rs` → `tools/service/stage.mjs`.
O host é Rust, a admissão e a compilação são coordenadas por Node, e cada
programa compilado usa o runtime oficial do Bend. Python não participa da
execução do serviço.
A configuração contém somente `mensagem`, `estado` e `resposta`, medidos em
bytes canônicos. Igualdade com o teto é permitida. Não há orçamento físico,
observador ou prazo de execução.

## Caminho da chamada

1. O host lê o enquadramento e verifica o tamanho da mensagem.
2. Programas Bend oficiais decodificam e autenticam pelo estado publicado.
3. A admissão verifica fonte, dependências e prova com as ferramentas oficiais,
   contra a configuração, contexto e argumentos reais.
4. O mesmo Book checado é compilado pelo compilador oficial. O estágio só chama
   Clang sobre o C literal e registra hashes do C e executável.
5. O programa roda em um processo auxiliar nativo novo, em CPU e com GPU desativada.
   A proposta é privada. O Codec continua sendo o programa Bend compilado.
6. O host recebe toda a saída, recolhe o processo, valida estado/resposta e remove
   o diretório temporário antes de aceitar a proposta para publicação.
7. O sucesso substitui o par `Published { state, response }` do host serial.
   Uma recusa ou falha anterior conserva a publicação anterior.
8. A entrega vem depois. Uma falha de entrega conserva o par publicado e encerra
   o canal, sem repetição automática nem deduplicação.

Os diretórios de compilação recebem código, prova e dados públicos da admissão,
sem o estado privado. O seed participa apenas da inicialização e é removido
antes do atendimento. O estado de cada chamada atravessa pipes em RAM, nunca
um arquivo temporário de entrada.

## Ownership e falhas

O host Rust possui cada processo e seus pipes. Threads locais alimentam a
entrada e drenam stdout e stderr simultaneamente, evitando bloqueio entre
pipes. O host espera o término do filho e a leitura integral antes de aceitar
a proposta.

Não há DSO, lease, `dlclose`, registries ou runtime substituto. O encerramento
do filho libera seus recursos. Uma falha do filho devolve `falha` sem publicar,
e o host pode atender a próxima chamada. Falha de ownership incerto encerra o
uso da instância, sem repetir uma operação possivelmente consumida.

O perfil é uma CLI Linux serial com ferramentas e host confiáveis. Não promete
recuperar falhas fatais ou morte do banco. Perder
o host pode perder os dados em RAM sem resposta.

O helper Node usa apenas uma opção pública de tamanho de stack, sem addon ou
mudança no Bend. O estágio usa Clang 19 com `--no-default-config`; o programa nativo recebe as
opções oficiais `--threads 1 --gpu off`. A instalação dessas ferramentas faz
parte do ambiente confiável.

## Verificação

Os testes Rust cobrem publicação, rollback e enquadramento. `make test-native`
compila C oficial e exercita efeitos, representação e os limites reais da
toolchain. `make test-integration` admite, compila e executa transações Bend reais.
Hashes e testes identificam artefatos e sustentam os casos executados; não
substituem a demonstração das oito leis para o executável completo.
