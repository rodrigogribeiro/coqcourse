---
layout: page
title: QuickChick - Testes baseado em propriedades em Coq
permalink: /quickchick/
---

Não é incomum gastarmos muitas horas de esforço na prova
de uma propriedade incorreta, ou mesmo com suposições inadequadas.
Uma maneira para contornar essa situação é o uso de testes
baseados em propriedades para encontrar contra-exemplos de
propriedades de interesse o quanto antes.

O teste baseado em propriedades foi introduzido em Haskell com
a biblioteca Quickcheck. O Quickchick é um plug-in para Coq que
permite a construção de geradores de valores aleatórios e para
codificação de propriedades a serem testadas para esses.
O objetivo deste capítulo é apresentar o Quickchick para
depurar propriedades simples sobre listas e árvores.

## Configurando o Quickchick

Primeiro, deve-se instalar o Quickchick. Detalhes sobre como instalar esse
plug-in podem ser encontrados [aqui](https://github.com/QuickChick/QuickChick).

Além disso, devemos realizar alguns imports e configurar alguns warnings para
evitar mensagens desnecesárias. Todo desenvolvimento usando o Quickchick deve iniciar
com esses imports e configurações para correta utilização do plug-in.

```coq
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings ''-extraction-opaque-accessed,-extraction''.
Set Warnings  ''-notation-overridden,-parsing''.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.
```

# Um primeiro exemplo...

Considere a seguinte função que remove um número natural de uma lista
de números fornecida como entrada.

```coq
Fixpoint remove (x : nat) (l : list nat) : list nat :=
  match l with
    | []   => []
    | h::t => if beq_nat h x then t else h :: remove x t
  end.
```

Podemos conjecturar que, dado um número x e uma lista l, após remover
x de l, temos que x não pertence a l. Especificaremos isso usando a
seguinte propriedade.

```coq
Definition removeP (x : nat) (l : list nat) :=
  (~~ (existsb (fun y => beq_nat y x) (remove x l))).
```

Ao observamos o código anterior, não é difícil descobrir o erro. Porém,
vamos usar o QuickChick para descobrir essa falha de forma automatizada.
Internamente, o Quickchick acrescenta alguns comandos a Coq, como por
exemplo o comando QuickChick que recebe uma propriedade como entrada e
tenta encontrar um contra-exemplo.

```coq
QuickChick removeP.
```

Ao executarmos o comando anterior obtemos a seguinte saída (o resultado pode
variar de máquina para máquina):

````coq
    0
    [ 0, 0 ]
    Failed! After 17 tests and 12 shrinks
````
O resultado apresenta como contra-exemplo uma lista l = [0;0] e x = 0.
Note que esse é o caso pois a função remove apenas retira a primeira
ocorrência do elemento passado como parâmetro da lista. A última linha
do resultado mostra que foram necessários gerar 17 casos de testes aleatórios
para encontrar a falha e que 12 simplificações foram realizadas de forma a
encontrar um contra-exemplo mínimo.

Um ponto importante: o QuickChick somente consegue executar código, portanto,
propriedades (valores em Prop) não podem ser testados. Como exemplo,
a propriedade remove_spec não pode ser utilizada para testes com QuickChick.

```coq
Definition remove_spec :=
  forall x l, ~ In x (remove x l).
```

# Teste baseado em propriedades

O teste baseado em propriedades é caracterizado pelos seguintes ingredientes

* Uma propriedade executável.
* Uma instância de Show para os valores de entrada: isso é necessário
  para apresentar contra-exemplos.
* Um gerador, para produzir valores de entrada aleatórios.
* Um simplificador, para reduzir contra-exemplos.

Agora iremos apresentar esses 2 últimos ingredientes.

## Construindo geradores

A pedra fundamental do teste baseado em propriedades é a geração de entradas
aleatórias. No QuickChick, um gerador para elementos de um tipo A é um valor
de tipo G A, em que G é uma mônada. A mônada G é, basicamente, uma abstração
para encapsular o processo de geração de valores aleatórios. A mônada G é
caracterizada pelas seguintes funções:

```coq
returnGen : ?A -> G ?A
bindGen   : G ?A -> (?A -> G ?B) -> G ?B
````
Note que essas funções correspondem, exatamente, às presentes na classe de tipos
Monad em Haskell. Da mesma maneira, o QuickChick possui funções como liftM (liftGen)
, sequence (sequenceGen) e foldM (foldGen).

As seções seguintes, apresentam algumas funções e combinadores
para construir geradores.

### Geradores primitivos

Geradores primitivos para booleanos, naturais e inteiros são construídos usando a
função choose.

```coq
choose : (?A * A?) -> G ?A
````
Em que ?A é uma instância da classe ChooseFromInterval, presente na biblioteca do QuickcChick.
Podemos usar o comando Sample para gerar alguns valores aleatórios usando choose.

```coq
Sample (choose (0,10)).

[2, 7, 1, 5, 2, 5, 3, 6, 4, 10, 3]
`````
### Gerando listas de valores

Listas são pervasivas na programação funcional. Desta forma, o QuickChick possui alguns combinadores
para permitir a geração de listas de valores. Esses são o listOf e vectorOf.

```coq
listOf : G ?A -> G (list ?A).
vectorOf : nat -> G ?A -> G (list ?A).
````

De maneira simples, listOf recebe como parâmetro um gerador para elementos de um certo tipo e produz,
como resultado, um gerador para listas de elementos deste tipo.

```coq
Sample (listOf (choose (0,4))).
[ [2, 0, 4, 1, 4, 4]
, []
, [4, 3, 1, 4, 0, 2, 0]
, []
, [1, 1]
, []
, []
, [1, 1]
, [0]
, [3]
, []]
````
A diferença entre vectorOf e listOf é que o primeiro recebe como parâmetro adicional o tamanho das listas a serem geradas.

```coq
Sample (vectorOf 2 (choose (0,4))).
[ [2, 0]
, [1, 1]
, [1, 2]
, [0, 0]
, [3, 0]
, [2, 2]
, [4, 2]
, [0, 0]
, [0, 2]
, [4, 4]
, [0, 4]]
````

### Outros combinadores

O QuickChick provê uma extensa biblioteca de funções para construção de geradores para tipos de dados definidos por um
desenvolvedor. A primeira função que veremos é a função elements, que a partir de um valor x e uma lista de valores xs,
elements x xs retorna um elemento aleatório da lista (x :: xs).

```coq
elements : ?A -> list ?A -> G ?A
````

A biblioteca QuickChick fornece algumas notações para listas não vazias de elementos, conforme abaixo:


```coq
Definition genColor : G Color :=
  elems [ Red ; Green ; Blue ; Yellow ].
```

Vamos considerar um exemplo mais interessante: árvores binárias.

```coq
Inductive Tree A :=
| Leaf : Tree A
| Node : A -> Tree A -> Tree A -> Tree A.

Arguments Leaf {A}.
Arguments Node {A} _ _ _.

Instance showTree {A} `{_ : Show A} : Show (Tree A) :=
  {| show :=
       let fix aux t :=
         match t with
           | Leaf => 'Leaf'
           | Node x l r => 'Node (' ++ show x ++ ') (' ++ aux l ++ ') (' ++ aux r ++ ')'
         end
       in aux
  |}.

```
A instância para Show é definida de maneira direta e os construtores do tipo Tree possuem
significado imediato.

## Construindo simplificadores


# Estudo de caso: Inserção em árvores binárias de busca




