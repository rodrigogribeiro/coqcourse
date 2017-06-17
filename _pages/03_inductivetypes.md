---
layout: page
title: Tipos indutivos e indução matemática
permalink: /inductivetypes/
---

## Definindo tipos indutivos

Um dos principais mecanismos para introduzir novas definições
em Coq é o uso de tipos indutivos. Um tipo indutivo é formado por
um nome (do tipo), o universo a que este tipo pertence e uma lista,
possivelmente vazia, de construtores deste tipo.

Dos conectivos e quantificadores apresentados anteriormente somente
o quantificador universal e a implicação lógica são primitivas de Coq,
todo o restante é definido em termos de tipos indutivos. A seguir, 
apresentamos a definição de tipos indutivos que representam as proposições
verdadeiro (`True`) e falso (`False`). Usamos os nomes `True1` e 
`False1` para evitar conflito de nomes com definições automaticamente 
importadas da biblioteca padrão de Coq.

```coq
Inductive True1 : Prop :=
| tt1 : True1.

Inductive False1 : Prop := .
```
As definições de `True1` e `False1` apresentam a sintaxe para definição de tipos
de dados indutivos. Toda declaração de tipo indutivo deve ser iniciada pela palavra
chave `Inductive`, seguida de um nome e do tipo (junto com um universo) deste novo tipo
e de uma lista dos construtores deste tipo indutivo.

O tipo `True1` modela uma proposição que é sempre provável. Este fato é representado por
um único construtor para este tipo, isto é, a única evidência possível para `True1` é o 
construtor  `tt1`. Por sua vez, `False1` representa uma proposição falsa, isto é uma 
proposição que não pode ser provada. Representamos a impossibilidade de demonstração
por um tipo indutivo sem construtores, isto é, um tipo que não é possível construir
um elemento que possui este tipo.

Também podemos representar a conjunção utilizando um tipos de dados indutivo. Neste
caso parametrizamos tipo definido com duas proposições, que possuem semântica imediata.

```coq
Inductive conj1 (A B : Prop) : Prop :=
| and1 : A -> B -> conj1 A B.
```
O tipo `conj1` modela a conjunção especificando, usando o construtor `and1`, que a única
maneira de se obter uma demonstração para `conj1 A B` é utilizando o construtor `and1`
e provas das proposições `A` e `B`.

### Exercício 13

Apresente uma definição apropriada para o tipo `disj1` para que este modelo o conectivo
de disjunção.

```coq
  Inductive disj1 : Prop :=.
```
## Booleanos

	
Outro exemplo simples de tipo de dados são o de valores booleanos, cuja definição apresentamos
a seguir.

```coq
  Inductive bool1 : Set :=
  | true1 : bool1
  | false1 : bool1.
```
Nesta definição podemos perceber algumas diferenças: Primeiro, este tipo é definido como
sendo pertencente ao universo `Set`. A principal diferença entre os tipos definidos no
universo `Set` e tipos definidos no universo `Prop` é que podemos realizar 
_pattern-matching_ sobre tipos `Set` e não sobre tipos em `Prop`. 

Os próximos exemplos usarão o tipo `bool` definido na biblioteca padrão de Coq. 
Importamos bibliotecas utilizando o comando `Require Import`.

```coq
  Require Import Bool.
```
  
Tipos indutivos permitem definirmos funções por casamento de padrão sobre sua estrutura. 
Porém, nem toda função sobre tais tipos é definível. Para garantir a consistência lógica, 
Coq exige que todas funções, recursivas ou não, sejam _totais_, isto é, sejam definidas
para todos os possíveis valores de seu domínio. Como um primeiro exemplo de função, 
considere a seguinte codificação da negação sobre valores de tipo `bool`. 

```coq
  Definition not_bool (b : bool) : bool :=
    match b with
    | false => true
    | true  => false
    end.
```	

O comando `Definition` inicia a declaração de uma função não recursiva. No exemplo, esta
função é chamada de [not_bool] e possui como parâmetro um valor `b : bool`. O corpo 
da função utiliza a construção `match`, que permite enumerar um conjunto de equações
para definir a função por casos. Neste exemplo, o `match` possui duas equações: uma para 
o construtor `false` e outra pra o construtor `true`. Abaixo, apresentamos a definição
da conjunção sobre valores booleanos, cujo significado é imediato.

```coq
  Definition and_bool (b1 b2 : bool) : bool :=
    match b1 , b2 with
    | true  , b2 => b2
    | false , b2 => b2
    end.
```
A única diferença desta definição em relação à sintaxe utilizada para definição da negação, 
é o uso de tuplas para realização de pattern-matching sobre mais de um parâmetro.


### Exercício 14

Apresente uma definição para os conectivos de disjunção ("ou") e exclusive-or ("xor")


Podemos executar casos de teste sobre funções definidas utilizando o comando 
`Eval compute in...` sobre uma expressão.

```coq
  Eval compute in not_bool false.
```
  
A execução do último comando produz o seguinte resultado
  
```coq
      = true
      : bool
```

Casos de teste são úteis para fornecer uma evidência inicial
da correção de uma função. Porém, pode-se considerar que uma função
está correta provando propriedades que esta deve atender.

Uma propriedade que a negação deve atender é involução, isso é `not_bool (not_bool b) = b`,
para quaisquer valores `b : bool`. Como podemos provar esse fato? Manualmente, esse fato
pode ser demonstrado por análise de caso sobre [b : bool] e o uso da definição de `not_bool`.

      Teorema: Para todo b : bool, not_bool (not_bool b) = b.
      Prova
        Suponha b : bool arbitrário.
           Considere os seguintes casos.
              caso b = true: Temos que: 
                 not_bool (not_bool true) =
                 not_bool false           = {Definição de not_bool}
                 true                     = {Definição de not_bool}
                 b                          {b = true}
              caso b = false: Temos que:   
                 not_bool (not_bool false) =
                 not_bool true             = {Definição de not_bool}
                 false                     = {Definição de not_bool}
                 b                           {b = false}
           Como os casos cobrem todas as possibilidades, temos que not_bool (not_bool b) = b.
       Como b : bool é arbitrário, temos que para todo b : bool, not_bool (not_bool b) = b.



Nesta breve demonstração manual vemos que para realizá-la em Coq precisamos de táticas 
para: 1) realizar análise de caso sobre valores de um tipo de dados indutivo; 2) realizar
computações a partir da definição de funções e 3) táticas para provar igualdades. 
A tática utilizada para realizar análise de
casos é `destruct`, que já utilizamos diversas vezes e usamos a tática `simpl` para realizar
computações sobre uma expressão utilizando definições de funções. Usamos a tática
`reflexivity` para demonstrar igualdades da forma `x = x`, para qualquer `x`. 
Abaixo apresentamos a prova de que a negação é involutiva.

```coq
  Lemma not_bool_inv : forall b : bool, not_bool (not_bool b) = b.
  Proof.
    intro b.
    destruct b.
    +
      simpl.
      reflexivity.
    +
      simpl.
      reflexivity.
  Qed.
```	 

Antes de executarmos a tática `destruct b` o estado da prova é:

```coq
      b : bool
      ============================
      not_bool (not_bool b) = b
```
Ao executarmos `destruct b` obtemos:

```coq
============================
not_bool (not_bool true) = true

subgoal 2 (ID 8) is:
not_bool (not_bool false) = false
```
      
### Exercício 15

```coq
  Lemma and_true_left : forall b, and_bool true b = b.
  Proof.
  Admitted.
```

### Exercício 16

```coq
  Lemma and_false_left : forall b, and_bool false b = false.
  Proof.
  Admitted.
```
  
### Exercício 17

```coq
  Lemma and_com : forall b b', and_bool b b' = and_bool b' b.
  Proof.
  Admitted.
```
  
### Exercício 18

```coq
  Lemma and_assocc : forall b1 b2 b3, and_bool b1 (and_bool b2 b3) = and_bool (and_bool b1 b2) b3.
  Proof.
  Admitted.
```

## Números naturais

Ao contrário de linguagens de programação tradicionais, tipos de dados númericos devem 
ser definidos utilizando tipos de dados indutivos. O tipo indutivo `nat` consiste de
uma definição recursiva do conjunto de números naturais.

```coq
Inductive nat : Set :=
| O : nat
| S : nat -> nat.
```
O construtor `O` representa o número 0 e o construtor `S` denota a operação de 
sucessor. O número `n > 0` é representado por `n` aplicações do construtor `S`
finalizadas pelo construtor `O`. Desta forma o número 3 é representado pelo valor
`S (S (S O))`.

Como a definição de números naturais é recursiva, funções sobre estes valores, usualmente
são definidas por recursão. Em Coq, todas as funções recursivas devem ser estruturalmente
recursivas, isto é só podem realizar chamadas recursivas sobre valores que são
sub-expressões do parâmetro original da função. 

Como um primeiro exemplo de função recursiva, vamos considerar a adição de números
naturais.

```coq
  Fixpoint add (n m : nat) : nat :=
    match n with
    | O    => m
    | S n' => S (add n' m)
    end.
```
Note que para definirmos uma função recursiva utilizamos o comando `Fixpoint`. A seguir,
apresentamos um caso de teste para esta função. 

```coq
  Eval compute in add 1 1.
```
o resultado é 2, como esperado. Note que Coq permite utilizar numerais para se referir
a valores de tipo `nat`. Este é um exemplo do recurso chamado de _notações_ que permite
modificarmos a sintaxe de Coq adicionando "açúcar sintático". Como exemplo da definição de
notações, vamos definir um operador para a operação de adição.


     Notation "n ':+:' m" := (add n m)(at level 40, left associativity).

O comando `Notation` define que a string entre aspas simples `:+:` irá representar a
função `add` com argumentos `n` e `m`. Note que além de especificar a sintaxe, `Notation`
define a precedência (especificada por `at level 40`) e associatividade deste operador
(no caso à esquerda). Usamos essa notação apenas para diferir de "+" que já é usado pela
biblioteca padrão de Coq.

A operação de adição possui diversas propriedades algébricas, uma destas é que o número 
0 é identidade à esquerda. O próximo teorema formaliza este fato.

```coq
Lemma zero_identity_add_left : forall n, 0 + n = n.
Proof.
    intro n.
    simpl.
    reflexivity.
Qed.
```
Essa demonstração não possui surpresas. Iniciamos introduzindo o quantificador universal
com a tática `intro n`, obtendo o seguinte estado de prova:

```coq
1 subgoal, subgoal 1 (ID 21)
  
n : nat
============================
0 + n = n
```
Na sequência utilizamos a tática `simpl` que realiza computações sobre a conclusão 
modificando o estado de prova anterior para:

```coq
1 subgoal, subgoal 1 (ID 21)
  
n : nat
============================
n = n
```

Finalmente, finalizamos a dedução utilizando a tática `reflexivity`, que prova igualdades
óbvias. Uma sequência óbvia seria demonstrar de que 0 é identidade à direita para a 
adição:

```coq
Lemma zero_identity_add_right : forall n, n + 0 = n.
Proof.
   intro n.
    simpl.
        ...
```
Porém, após a execução da tática `simpl` percebemos que o estado da prova continua 
inalterado:

```coq
1 subgoal, subgoal 1 (ID 21)
  
n : nat
============================
n + 0 = n
```
e ao tentarmos executar a tática `reflexivity`, a seguinte mensagem de
erro é exibida:

```coq
Error: In environment
n : nat
Unable to unify n with n + 0.
```
O que aconteceu de errado? A definição da função de adição está incorreta? Para 
entendermos este problema devemos entender melhor como funciona a igualdade em 
assistentes de prova baseados em teoria de tipos intuicionista.

## Igualdade em Coq 

A igualdade em teoria de tipos intuicionista é um tópico de pesquisa muito ativo.
A definição usual é a conhecida como _igualdade proposicional_ que, intuitivamente,
especifica que dois valores são iguais se estes possuem a mesma _forma normal_. 
Mas o que é uma forma normal? Dizemos que um valor está em forma normal quando este
não possui nenhuma computação pendente a ser realizada. Considere as seguintes 
expressões de tipo `nat`:
      
  - `S (S 0)`
  - `S ((S 0) + 0)`

Note que a primeira é uma forma normal, visto que representa o número 2. Por sua vez,
a segunda não é uma forma normal, pois ainda possui uma chamada da função `add` a ser
executada.

Evidentemente, apesar de sintaticamente diferentes, estas expressões denotam o mesmo
valor de tipo `nat`, a diferença é que a segunda ainda não foi completamente reduzida.
Assistentes de prova verificam a igualdade de duas expressões reduzindo-as até que estas
sejam formas normais e então as testa com respeito a igualdade sintática. Formalmente,
a igualdade proposicional é definida pelo seguinte tipo indutivo:

```coq
Inductive eq (A : Type) (x : A) : A -> Prop :=
| eq_refl : eq A x
```

O tipo `eq` é parametrizado por um tipo, `A : Type`, e um valor deste tipo, `x : A`.
Note que para diferentes valores de `x : A` existem diferentes tipos
`eq A x `. De maneira mais concreta, temos que a igualdade para `true` é representada por um valor de tipo
`eq bool true`, a igualdade de 2 é representada por `eq nat (S (S O))` e assim por diante.
Assim como acontece com números naturais, o tipo `eq A x` utiliza notações e é representado
como `x = x`. Note a igualdade proposicional possui apenas um construtor, `eq_refl`. Isto é, 
a única maneira de provarmos uma igualdade é usando a evidência `eq_refl` de tipo `x = x`.

Anteriormente tentamos provar a seguinte proposição, sem sucesso:

```coq
forall n : nat, n + 0 = n
```

O motivo da falha na prova desta proposição deve-se ao tratamento da igualdade em Coq. 
Note que a proposição

```coq 
forall n : nat, 0 + n = n
```
foi provada, pois temos que a igualdade `0 + n = n` é uma consequência direta da definição
da função `add`, cuja definição repetimos abaixo por conveniência:

```coq
Fixpoint add (n m : nat) : nat :=
	match n with
	| O    => m
	| S n' => S (add n' m)
	end.
```
A partir desta definição, podemos perceber que a forma do parâmetro
`n`_determina de maneira única o resultado desta função_. Por isso, a
prova da proposição `0 + n = n` é imediata: basta executar a função
`add`e a prova da igualdade pode ser concluída. Porém, este não é 
o caso para a igualdade `n + 0`, visto que Coq não consegue decidir como reduzir a função
`add` sem saber se `n = O` ou se `n = S n'`, para algum `n' : nat`. Uma possível solução 
para esse problema é usar a tática `destruct n` que força uma análise de casos sobre a 
estrutura do tipo de dados `nat`. 

```coq
Lemma zero_identity_add_right : forall n, n + 0 = n.
Proof.
    intro n.
    destruct n.
    +
        simpl.
	reflexivity.
    +
        simpl.
	reflexivity.
Qed.
``` 

Após o processamento da tática `destruct n`, temos o seguinte estado
de prova:

```coq 
2 subgoals, subgoal 1 (ID 28)
  
============================
0 + 0 = 0

subgoal 2 (ID 30) is:
S n + 0 = S n
```

A prova de `0 + 0 = 0` é trivial e pode ser resolvida pelas táticas `simpl`, que reduz
a conclusão a `0 = 0` e `reflexivity` que demonstra essa igualdade. Com isso, resta-nos
demonstrar o próximo caso quando `n = S n'`:

```coq
n : nat
============================
S n + 0 = S n
```

Ao executarmos a tática `simpl` o estado da prova é alterado para:

```coq
n : nat
============================
S (n + 0) = S n
```

e ao tentarmos processar a tática `reflexivity` obtemos a seguinte mensagem de erro:

```coq
Error: In environment
n : nat
Unable to unify S n with S (n + 0).
```

Note que estamos tentando provar que, a menos do construtor `S`, essa conclusão é 
exatamente a conclusão original. Observe que `S (n + 0) = S n` será verdadeiro 
se, e somente se, `(n + 0) = n`, isto é a propriedade será verdadeira para o 
sucessor de `n`, `S n`, somente quanto for verdadeira para `n`. O que precisamos
para concluir essa prova é indução matemática.

## Indução Matemática

Indução matemática é uma técnica de demonstração amplamente usada na ciência da 
computação. Em Coq, ao declararmos um novo tipo indutivo é gerado uma função 
que representa o _princípio de indução_ para aquele tipo de dados e, usualmente, 
o nome desta função é o mesmo nome do tipo de dados em questão concatenado com 
o sufixo ind. Para o tipo de dados `nat`, temos a função `nat_ind` cujo tipo
é apresentado abaixo:

```coq
Check nat_ind.
nat_ind  : forall P : nat -> Prop, 
                         P 0 ->
                        (forall n : nat, P n -> P (S n)) -> 
                        forall n : nat, P n
```
						
Esta função possui como parâmetros um predicado `P : nat -> Prop`, que é a proposição
a ser provada, uma prova de que esta proposição é verdadeira para zero, `P 0`, que
representa o caso base; e uma função de tipo `(forall n : nat, P n -> P (S n))` 
que denota o passo indutivo. Note que a ocorrência de [P n] na fórmula correspondente
ao passo indutivo representa a conhecida _hipótese de indução_, que vista sobre as 
lentes de _proposições são tipos e programas são provas_ corresponde a uma chamada
recursiva. Em um script de táticas, usamos `induction` para iniciar uma demonstração
por indução usando o princípio de indução apropriado.

Usando a tática `induction` podemos finalizar facilmente o problemático teorema 
sobre adição.

```coq
    Lemma zero_identity_add_right : forall n, n + 0 = n.
    Proof.
      intro n.
      induction n as [ | n' IHn'].
      +
        simpl.
        reflexivity.
      +
        simpl.
        rewrite IHn'.
        reflexivity.
    Qed.
```
	
Ao processarmos a tática `induction n as [ | n' IHn']`, obtemos a seguinte
configuração para o caso `n = S n'`: 

```coq
        n' : nat
        IHn' : n' + 0 = n'
        ============================
        S (n' + 0) = S n'
```
Ao especificarmos o padrão `[ | [n' IHn']]` na tática `induction` atribuímos o 
nome `n'` à variável universalmente quantificada que ocorre no passo indutivo 
e `IHn'` à hipótese de indução. Para finalizar a prova, devemos ser capazes de
utilizar a igualdade `IHn' : n' + 0 = n'`. Utilizamos a tática `rewrite IHn'`
para substituir ocorrências do lado esquerdo da igualdade `n' + 0 = n'` pelo
lado direito na conclusão e, com isso, obtemos o seguinte estado:

```coq

1 focused subgoal
(unfocused: 0), subgoal 1 (ID 37)
  
n' : nat
IHn' : n' + 0 = n'
============================
S n' = S n'
```
que pode ser imediatamente resolvido pela tática `reflexivity`. A seguir, provamos 
outro simples teorema sobre adição utilizando indução.

```coq
    Lemma add_inc : forall m n, S (m + n) = m + S n.
    Proof.
      intros m n.
      induction m as [ | m' IHm'].
      +
        simpl.
        reflexivity.
      +
        simpl.
        rewrite IHm'.
        reflexivity.
    Qed.
```
Neste último exemplo, utilizamos a tática `intros` que permite especificarmos uma 
sequência de suposições a serem adicionadas no contexto de hipóteses.
Usando os resultados anteriores, com a tática `apply`, podemos demonstrar que a 
adição é uma operação comutativa.

```coq
    Lemma add_commut : forall n m, n + m = m + n.
    Proof.
      intros n m.
      induction n as [| n' IHn'].
      +
        simpl.
        symmetry.
        apply zero_identity_add_right.
      +
        simpl.
        rewrite IHn'.
        apply add_inc.
    Qed.
```

### Exercício 19

```coq
    Lemma add_associative : forall n m p, n + (m + p) = (n + m) + p.
    Proof.
    Admitted.
```
	
### Exercício 20

A seguir apresentamos uma definição da operação de multiplicação sobre números 
naturais. 

```coq
    Fixpoint times (n m : nat) : nat :=
      match n with
      | 0    => 0
      | S n' => m + (times n' m)
      end.
```

A partir desta definição, enuncie e prove os seguintes fatos sobre a multiplicação:
        
- O número 1 é identidade à esquerda da multiplicação.
- O número 1 é identidade à direita da multiplicação.
- A operação de multiplicação é associativa.
- A operação de multiplicação é comutativa.

### Exercício 21

Defina a função `even_bool : nat -> bool` que, a partir de um número natural, retorne
verdadeiro se este é par.
	  
### Exercício 22

Prove a seguinte propriedade sobre a função `even_bool`:

```coq
    Lemma even_add_n : forall n, even_bool (n + n) = true.
    Proof.
    Admitted.
```
	
### Exercício 23

Defina a função `odd_bool : nat -> bool` que, a partir de um número natural, 
retorne verdadeirso se este é ímpar
	  
### Exercício 24

Prove a seguinte propriedade sobre a função `odd_bool`:

```coq
    Lemma odd_add_n_Sn : forall n, odd_bool (n + S n) = true.
    Proof.
    Admitted.
```	

### Exercício 25

```coq
    Lemma even_SS : forall n, even_bool n = even_bool (S (S n)).
    Proof.
    Admitted.
```	

### Exercício 26

```coq
    Lemma odd_SS : forall n, odd_bool n = odd_bool (S (S n)).
    Proof.
    Admitted.
```	

### Exercício 27

```coq
    Lemma even_bool_S : forall n, even_bool n = not_bool (even_bool (S n)).
    Proof.
    Admitted.
```	

## Listas

Listas são um dos tipos de dados mais utilizados por programadores de linguagens
funcionais. Uma possível definição é apresentada a seguir, juntamente com notações
para facilitar o uso deste tipo de dados.

```coq
    Inductive list (A : Type) : Type :=
    | nil : list A
    | cons : A -> list A -> list A.
```

     Notation "x :: l" := (cons x l)
                                   (at level 60, right associativity).
     Notation "[ ]" := nil.
     Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Alguns exemplos de listas são apresentados abaixo

```coq
    Definition list1 : list nat := 1 :: 2 :: 3 :: nil.
    Definition list2 : list nat := [1 ; 2 ; 3].
```

A seguir definimos duas funções simples sobre listas: `repeat`, que gera uma lista
contendo `n` cópias de um valor e `length`, que retorna o número de elementos
de uma lista.

```coq
    Fixpoint repeat {A : Type}(n : nat)(x : A) : list A :=
      match n with
      | O => []
      | S n' => x :: repeat n' x
      end.

    Fixpoint length {A : Type}(xs : list A) : nat :=
      match xs with
      | []        => O
      | (x :: xs) => S (length xs)
      end.
```

Em ambas as definições utilizamos a sintaxe de Coq para _parâmetros implícitos_,
isto é, parâmetros que podem ser determinados automaticamente pelo algoritmo de
verificação de tipos de Coq. A rigor, ao definirmos essas funções deveríamos 
fornecer o tipo `A : Type` como parâmetro, porém como outros argumentos dessas
funções utilizam o tipo `A`, este pode ser inferido. Declarando argumentos
como implícitos evita que os passemos em chamadas à função definida. 

Outra função útil sobre listas é a concatenação de duas listas, cuja definição
apresentamos a seguir, juntamente com uma notação apropriada.

```coq
    Fixpoint app {A : Type}(xs ys : list A) : list A :=
      match xs with
      | []        => ys
      | (x :: xs) => x :: (app xs ys)
      end.
```

     Notation "x ++ y" := (app x y)(right associativity, at level 60).

A demonstração de propriedades de funções que operam sobre listas é usualmente
feita por indução sobre a estrutura da lista. A seguir, apresentamos uma prova 
de que, para quaisquer listas `xs, ys`, `length (xs ++ ys) = length xs + length ys`.
Primeiramente, construiremos essa prova manualmente e em seguida apresentaremos 
o correspondente teorema Coq.

        Teorema: Para toda lista xs e ys, length (xs ++ ys) = length xs + length ys.
        Prova: Por indução sobre a estrutura de xs.
        
        Caso base (xs = []): 
           Suponha ys arbitrário. Temos que:
             length ([] ++ ys) = {Definição de app}
             length ys         = {Álgebra}
             0 + length ys     = {Definição de length}
             length [] + length ys.
        Passo indutivo (xs = z :: zs):
            Suponha ys, z e zs arbitrários tais que xs = z :: zs e
            que length (zs ++ ys) = length zs + length ys.
            Temos que:
               length ((z :: zs) ++ ys)   = {Definição de app}
               length (z :: (zs ++ ys))   = {Definição de length}
               S (length (zs ++ ys))      = {Hipótese de indução}
               S (length zs + length ys)  = {Definição da adição}
               S (length zs) + length ys  = {Definição de length}
               length (z :: zs) + length ys

```coq
    Lemma length_app
      : forall {A : Type}(xs ys : list A), length (xs ++ ys) = length xs + length ys.
    Proof.
      intros A xs ys.
      induction xs as [| z zs IHzs].
      +
        simpl.
        reflexivity.
      +
        simpl.
        rewrite IHzs.
        reflexivity.
    Qed.
```

 Uma função muito utilizada em programação funcional sobre é `map`, que recebe
 como parâmetro uma função e uma lista e retorna a lista resultante de se
aplicar a função passada como parâmetro a cada elemento da lista

```coq
    Fixpoint map {A B : Type}(f : A -> B)(xs : list A) : list B :=
      match xs with
      | []      => []
      | y :: ys =>  f y :: map f ys
      end.
```

Uma propriedade importante de `map` é que esta preserva o tamanho da lista
de entrada.

```coq
    Lemma map_length {A B : Type}{f : A -> B} : forall xs, length (map f xs) = length xs.
    Proof.
      intros xs.
      induction xs as [ | y ys IHys].
      +
        reflexivity.
      +
        simpl.
        rewrite IHys.
        reflexivity.
    Qed.
```

A seguir apresentamos uma função que inverte a lista de entrada.

```coq
    Fixpoint reverse {A : Type}(xs : list A) : list A :=
      match xs with
      | [] => []
      | y :: ys => reverse ys ++ [ y ]
      end.
```
	  
Evidentemente, se a implementação de `reverse` é correta, esta 
deve preservar o tamanho da lista de entrada.

```coq
    Lemma reverse_length {A : Type}: forall (xs : list A), length xs = length (reverse xs).
    Proof.
      intros xs.
      induction xs.
      +
        reflexivity.
      +
        simpl.
        rewrite length_app, add_commut.
        rewrite IHxs.
        reflexivity.
    Qed.
```
	
### Exercício 28

```coq
    Lemma repeat_length {A : Type} : forall (n : nat)(x : A), length (repeat n x) = n.
    Proof.
    Admitted.
```

### Exercício 29

```coq
    Lemma app_nil_right {A : Type} : forall (xs : list A), xs ++ [] = xs.
    Proof.
    Admitted.
```

### Exercício 30

```coq
    Lemma app_assoc {A : Type} : forall (xs ys zs : list A), xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
    Proof.
    Admitted.
```

### Exercício 31

```coq
    Lemma map_app {A B : Type}{f : A -> B}
      : forall xs ys, map f (xs ++ ys) = map f xs ++ map f ys.
    Proof.
    Admitted.
```

### Exercício 32

```coq
    Lemma reverse_app {A : Type}
      : forall (xs ys : list A), reverse (xs ++ ys) = reverse ys ++ reverse xs.
    Proof.
    Admitted.
```

### Exercício 33

```coq
    Lemma reverse_inv {A : Type}
      : forall (xs : list A), reverse (reverse xs) = xs.
    Proof.
    Admitted.
```

## Predicados indutivos e princípio de inversão

Anteriormente vimos como definir fórmulas lógicas usando conectivos e quantificadores
em Coq. Além disso, vimos que, exceto pelo quantificador universal e implicação, todos
os outros conectivos podem ser definidos utilizando tipos de dados indutivos. 
        
Agora vamos utilizar tipos indutivos para definir predicados, ou seja 
_predicados indutivos_. Como um primeiro exemplo de predicado definido indutivamente,
considere as seguintes regras que definem se um número natural é par:

- 0 é par.
- Se `n : nat` é par então `S (S n) : nat` é par.

Note que esse par de regras é recursivo, pois o fato de [S (S n)] ser par depende
de `n` ser par. Desta forma, podemos representar esse predicado sobre números naturais
pelo seguinte tipo indutivo.

```coq
Inductive even : nat -> Prop :=
| ev_zero : even 0
| ev_ss   : forall n, even n -> even (S (S n)).
```

Este tipo é ligeiramente diferente de definições anteriores: ao invés de ser
definido no universo `Set`, `Prop` ou `Type`; `even` é definido como sendo uma 
função de tipo `nat -> Prop`, isto é,  `even` é uma propriedade (predicado) 
sobre números naturais. Ao contrário da definição de listas em que o parâmetro
do tipo definido aparece a esquerda do ":", o tipo `nat` aparece a direita. 
Apesar de parecer um detalhe insignificante, na verdade, este é crucial. 
Valores que aparecem à esquerda do ":" são usualmente chamados de _parâmetros_ e
não podem variar nos tipos presentes em diferentes construtores. Por sua vez, 
valores à direita do ":" são chamados de _índices_ e estes podem possuir 
valores diferentes em construtores do tipo definido.

Usando essas regras podemos construir provas de que um dado número é par, simplesmente
usando os construtores deste tipo.

```coq
    Example eight_is_even : even 8.
    Proof.
      apply ev_ss.
      apply ev_ss.
      apply ev_ss.
      apply ev_ss.
      apply ev_zero.
    Qed.
```

### Exercício 34

```coq

Definition double (n : nat) := 2 * n.

Lemma double_even : forall n, even (double n).
Proof.
Admitted.
```

## Princípio de inversão

Os princípios de inversão são definidos na teoria de prova como teoremas que 
especificam as condições necessárias e suficientes para uma determinada proposição
ser verdadeira. Como exemplo, considere a regra de introdução da conjunção em
dedução natural:


            \Gamma |- A        \Gamma |- B
            --------------------------------
              \Gamma |- A /\ B


Esta regra especifica que, a fórmula `A /\ B` é demonstrável se e somente se 
as fórmulas `A` e `B` forem demonstráveis. Logo, podemos afirmar que se `A /\ B`
é uma fórmula verdadeira então `A` , `B` também o são. Essa noção corresponde ao
princípio de inversão pois permite-nos deduzir as premissas utilizadas para concluir
que uma certa proposição é verdadeira.

Ao utilizarmos predicados indutivos para formalizações, a inversão é uma técnica
fundamental: seja para deduzirmos premissas ou mesmo para deduzir a impossibilidade 
de um predicado, visto que se um valor não é deduzível então este é equivalente a 
uma contradição. O princípio de inversão é implementado em Coq pela tática `inversion`.
A seguir apresentamos um exemplo de uso desta tática.

```coq
    Lemma one_not_even : ~ even 1.
    Proof.
      intros Hone.
      inversion Hone.
    Qed.
```

Após o precessamento da tática `intros`, obtemos o seguinte estado de prova:

```co
        1 subgoal, subgoal 1 (ID 147)
  
        Hone : even 1
        ============================
        False
```

Ao usarmos `inversion H` a prova é finalizada. Esta tática funciona da seguinte maneira:
uma prova de `even 1` deve ser construída pelos construtores `ev_zero` ou `ev_ss`. No
caso de ser construída por `ev_zero`, temos que os tipos `even 0` e `even 1` devem ser
iguais, o que é falso. No segundo caso, temos que `even 1` deve ser igual a 
`even (S (S n))`, para algum valor de `n`, o que nos leva a tentar demonstrar que
`S 0 = S (S n)`, o que também é uma contradição, finalizando a demonstração.

Ainda sobre o predicado `even`, veremos como ele pode ser utilizado para deduzir
premissas.

```coq
    Lemma even_2_inv : forall n, even (2 + n) -> even n.
    Proof.
      intros n H.
      inversion H.
      assumption.
    Qed.
```

Após a execução da tática [inversion], temos a seguinte configuração:

```coq
        1 subgoal, subgoal 1 (ID 184)
  
        n : nat
        H : even (2 + n)
        n0 : nat
        H1 : even n
        H0 : n0 = n
        ============================
        even n
```

que possui exatamente como hipótese a premissa `even n` (devido ao construtor `ev_ss`)
que pode ser utilizada pela tática assumption para finalizar a demonstração. 
Cabe ressaltar que o uso da tática `inversion` pode gerar um grande número de
igualdades no contexto de hipóteses. Ao invés de usarmos a tática `rewrite`
para reescrevermos as igualdades geradas, usaremos a tática `subst` que
automaticamente re-escreve todas as igualdades presentes nas hipóteses.

Os próximos exemplos e  exercícios envolverão a demonstração de diversos 
fatos envolvendo a relação "menor ou igual" sobre números naturais. 
Esta pode ser definida pelo seguinte tipo indutivo:

```coq
        Inductive le (n : nat) : nat -> Prop :=
        | le_n : n <= n 
        | le_S : forall m : nat, n <= m -> n <= S m
```

Assim como fizemos anteriormente, podemos usar os construtores deste tipo
para construir provas, como no exemplo seguinte:

```coq
    Example teste_le : 3 <= 6.
    Proof.
      apply le_S.
      apply le_S.
      apply le_S.
      apply le_n.
    Qed.
```
	
Além disso, podemos usar inversão para provar contradições envolvendo esta
relação.

```coq
    Example teste_le_false : 2 <= 1 -> 1 + 1 = 10.
    Proof.
      intros H.
      inversion H.
      inversion H1.
    Qed.
```

A seguinte demonstração, mostra que 0 é menor ou igual a todo número natural.
A prova é uma simples indução sobre a estrutura de `n`.

```coq
    Lemma le_0_n : forall n, 0 <= n.
    Proof.
      intros n.
      induction n as [| n' IHn'].
      +
        apply le_n.
      +
        apply le_S.
        assumption.
    Qed.
```

### Exercício 35

```coq
Lemma le_refl : forall n, n <= n.
Proof.
Admitted.
```

Outra fato é que a relação de `<=` é preservada pelo construtor `S

```coq
    Lemma le_cong_S : forall n m, n <= m -> S n <= S m.
    Proof.
      intros n m Hnm.
      induction Hnm.
      +
        apply le_refl.
      +
        apply le_S.
        assumption.
    Qed.

    Lemma le_S_cong : forall n m, S n <= S m -> n <= m.
    Proof.
      intros n m.
      induction m as [| m' IHm'].
      +
        intros Hnm.
        inversion Hnm.
        -
          apply le_refl.
        -
          inversion H0.
      +
        intros Hnm.
        inversion Hnm.
        -
          subst.
          apply le_refl.
        -
          subst.
          apply le_S.
          apply IHm'.
          assumption.
    Qed.
```
Sabemos que a relação `<=` é uma ordem parcial sobre o conjunto dos números naturais, 
isto é, ela é reflexiva, transitiva e anti-simétrica. Os próximos
exercícios visam demonstrar essa propriedade.

### Exercício 36

```coq
Lemma le_trans : forall n m p, n <= m -> m <= p -> n <= p.
Proof.
Admitted.
```

### Exercício 37

```coq
Lemma le_antisym : forall n m, n <= m -> m <= n -> n = m.
Proof.
Admitted.
```

### Exercício 38

Considere a tarefa de projetar um predicado indutivo
`Sorted : list nat -> Prop` que constitui uma prova
de que uma certa lista de números naturais está ordenada. 
Sua definição deve utilizar o predicado `<=` e conseguir
demonstrar os casos de teste abaixo.

```coq
    Inductive Sorted : list nat -> Prop := .

    Example test_sorted1 : Sorted [].
    Proof.
    Admitted.

    Example test_sorted2 : Sorted [10].
    Proof.
    Admitted .
    
    Example test_sorted3 : Sorted [1 ; 3 ; 5 ].
    Proof.
    Admitted.
```	

Considere a seguinte definição alternativa para a relação de ordem
entre números naturais

    Reserved Notation "x '<<=' y" (at level 40, no associativity).
    
    Inductive le_alt : nat -> nat -> Prop :=
    | le_alt_zero : forall n, 0 <<= n
    | le_alt_succ : forall n m, n <<= m -> S n <<= S m
    where "x '<<=' y" := (le_alt x y).

### Exercício 39

```coq
    Lemma le_alt_refl : forall n, n <<= n.
    Proof.
    Admitted.
```

### Exercício 40

```coq
    Lemma le_alt_trans
      : forall n m p, n <<= m -> m <<= p -> n <<= p.
    Proof.
    Admitted.
```

### Exercício 41

```coq
    Lemma le_alt_antisym : forall n m, n <<= m -> m <<= n -> n = m.
    Proof.
    Admitted.
```

### Exercício 42

```coq
    Lemma le_alt_equiv_le : forall n m, n <<= m <-> n <= m.
    Proof.
    Admitted.
```
