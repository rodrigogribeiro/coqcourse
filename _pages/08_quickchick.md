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
significado imediato. A função oneof permite a construção de um gerador a partir de diferentes geradores.

```coq
oneof : G ?A -> G (list ?A) -> G ?A
```

Usando o combinador oneof podemos construir um gerador para árvores binárias.

```coq
Fixpoint genTree {A} (g : G A) : G (Tree A) :=
  oneOf [ returnGen Leaf ;
          liftGen3 Node  g (genTree g) (genTree g) ]
```

Apesar de simples, a definição anterior possui um problema: ela não é aceita pelo
verificador de terminação de Coq que não consegue determinar que esta função
sempre termina. Uma maneira de contornar essa situação é uso de um parâmetro adicional para
controlar o número de chamadas recursivas, como o código seguinte:

```coq
Fixpoint genTreeSized {A} (sz : nat) (g : G A) : G (Tree A) :=
  match sz with
    | O => returnGen Leaf
    | S sz' => oneOf [ returnGen Leaf ;
                       liftGen3  Node g (genTreeSized sz' g) (genTreeSized sz' g)
                     ]
  end.
```

Com isso, podemos testar o gerador de árvores aleatórias.

```coq
[ Node (3) (Leaf) (Leaf)
, Node (0) (Leaf) (Node (1) (Leaf) (Leaf))
, Leaf
, Leaf
, Leaf
, Node (1) (Node (3) (Node (0) (Leaf) (Leaf)) (Leaf)) (Node (1) (Leaf) (Leaf))
, Leaf
, Leaf
, Node (0) (Node (0) (Leaf) (Node (1) (Leaf) (Leaf))) (Leaf)
, Leaf
, Node (3) (Node (3) (Node (3) (Leaf) (Leaf)) (Node (2) (Leaf) (Leaf))) (Leaf)]
````
Note que há um elevado número de árvores vazias, o que pode não ser interessante. Idealmente,
devemos gerar valores aleatórios que tenham uma boa variabilidade para garantir uma grande
cobertura do código testado. O combinador frequency permite especificar o peso de geradores.
Com isso, podemos atribuir um peso menor para folhas, gerando assim uma quantidade pequena de
árvores vazias.

```coq
frequency : G ?A -> seq (nat * G ?A) -> G ?A
```

Abaixo apresentamos a versão aprimorada do gerador de árvores binárias aleatórias e alguns valores
gerados.

```coq
Fixpoint genTreeSized' {A} (sz : nat) (g : G A) : G (Tree A) :=
  match sz with
    | O => returnGen Leaf
    | S sz' => freq [ (1,  returnGen Leaf) ;
                      (sz, liftGen3  Node g (genTreeSized' sz' g) (genTreeSized' sz' g))
                    ]
  end.

Sample (genTreeSized' 3 (choose(0,3))).

[ Node (0) (Node (2) (Leaf) (Leaf)) (Node (0) (Node (1) (Leaf) (Leaf)) (Node (1) (Leaf) (Leaf)))
, Node (1) (Leaf) (Leaf), Node (1) (Node (3) (Leaf) (Leaf)) (Node (3) (Node (1) (Leaf) (Leaf)) (Leaf))
, Node (0) (Node (3) (Leaf) (Node (1) (Leaf) (Leaf))) (Node (3) (Node (1) (Leaf) (Leaf)) (Node (3) (Leaf) (Leaf)))
, Node (3) (Leaf) (Node (2) (Node (3) (Leaf) (Leaf)) (Node (2) (Leaf) (Leaf)))
, Leaf
, Node (0) (Leaf) (Node (1) (Leaf) (Node (3) (Leaf) (Leaf)))
, Leaf
, Node (0) (Node (0) (Leaf) (Leaf)) (Node (2) (Node (0) (Leaf) (Leaf)) (Node (2) (Leaf) (Leaf)))
, Node (2) (Leaf) (Leaf), Leaf]
```

Como exemplo de uso deste gerador, vamos considerar a seguinte função que troca as subárvores direita e esquerda de uma
árvore binária.

```coq
Fixpoint mirror {A : Type} (t : Tree A) : Tree A :=
  match t with
    | Leaf => Leaf
    | Node x l r => Node x (mirror r) (mirror l)
  end.
```

e de um teste de igualdade sobre árvores binárias.

```coq
Fixpoint eq_tree (t1 t2 : Tree nat) : bool :=
  match t1, t2 with
    | Leaf, Leaf => true
    | Node x1 l1 r1, Node x2 l2 r2 =>
      beq_nat x1 x2 && eq_tree l1 l2 && eq_tree r1 r2
    | _, _ => false
  end.
````

Evidentemente, se invertermos as subárvores esquerda e direita duas vezes, o resultado é a árvore original.

```coq
Definition mirrorP (t : Tree nat) := eq_tree (mirror (mirror t)) t.
````
Usamos o seguinte comando para testar essa propriedade.

```coq
QuickChick (forAll (genTreeSized' 5 (choose (0,5))) mirrorP).
```

que produz o resultado esperado, de que nenhum contra-exemplo foi encontrado.

```coq
+++ Passed 10000 tests (0 discards)
```

Mas o que aconteceria se especificássemos a proopriedade incorreta? Vamos ver a seguinte definição errada de mirror:

```coq
Definition faultyMirrorP (t : Tree nat) := eq_tree (mirror t) t.
```

Ao executarmos o comando de testes

```coq
QuickChick (forAll (genTreeSized' 5 (choose (0,5))) faultyMirrorP).
```

Obtemos o seguinte contra-exemplo:

```coq
Node (2) (Node (3) (Node (4) (Leaf) (Node (0) (Leaf) (Leaf))) (Leaf))
         (Node (5) (Node (5) (Node (3) (Node (4) (Leaf) (Leaf)) (Leaf)) (Leaf)) (Leaf))
```

Que não ajuda muito em entender o problema, visto que esse contra-exemplo parece ser desnecessiramente grande.
Na próxima seção veremos como construir simplificadores que ajudam a reduzir o tamanho de contra-exemplos.


## Construindo simplificadores

Intuitivamente, um simplificador é um processo guloso que busca
encontrar o menor contra-exemplo, a partir de um maior, que falsifica
uma certa propriedade. Simplificadores são funções de tipo A -> list A,
que a partir de um valor x : A, produz uma lista de subtermos de x, que podem ser
usados como candidatos de contra-exemplos menores.

Abaixo apresentamos uma definição de um simplificador de árvores binárias.

```coq
Open Scope list.
Fixpoint shrinkTree {A} (s : A -> list A) (t : Tree A) : seq (Tree A) :=
  match t with
    | Leaf => []
    | Node x l r => [l] ++ [r] ++
                    map (fun x' => Node x' l r) (s x) ++
                    map (fun l' => Node x l' r) (shrinkTree s l) ++
                    map (fun r' => Node x l r') (shrinkTree s r)
  end.
````

Note que a função gera uma lista de árvores binárias, tentando simplificar as subárvores direita e esquerda
e concatenando os resultados desses processos.

Executando o teste anterior com essa função de simplificação, conseguimos um contra-exemplo bem menor.

```coq
QuickChick (forAllShrink (genTreeSized' 5 (choose (0,5))) (shrinkTree shrink) faultyMirrorP).

Node (0) (Leaf) (Node (0) (Leaf) (Leaf))
*** Failed after 1 tests and 7 shrinks. (0 discards)
```

## Juntando todas as peças

A biblioteca Haskell QuickCheck possui uma classe Arbitrary que possui duas funções
arbitrary, que gera valores aleatórios, e shrink, que simplifica valores. QuickChick possui
as classes GenSized e Shrink que fornecem geradores e simplificadores.

```coq
Instance genTree {A} `{Gen A} : GenSized (Tree A) :=
  {| arbitrarySized n := genTreeSized n arbitrary |}.

Instance shrTree {A} `{Shrink A} : Shrink (Tree A) :=
  {| shrink x := shrinkTree shrink x |}.
````

Com isso podemos simplesmente chamar o comando QuickChick para realizar os testes sobre uma propriedade de
maneira direta.

```coq
QuickChick faltyMirrorP.
````

## Gerando instâncias automaticamente

QuickChick possui facilidades para geração automática de instâncias de Arbitrary e Show, usando o comando Derive.

```coq
Derive Arbitrary for Tree.
(* genSTree is defined *)
(* shrTree0 is defined *)
Print genSTree.
Print shrTree0.

Derive Show for Tree.
(* showTree0 is defined *)
Print showTree0.
```



