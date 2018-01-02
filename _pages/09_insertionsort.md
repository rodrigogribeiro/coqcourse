---
layout: page
title: Estudo de caso - Formalizando o Insertion sort
permalink: /insertionsort/
---


O insertion sort é um conhecido algoritmo de ordenação que consiste em repetidamente inserir um elemento em uma lista
previamente ordenada. Uma possível implementação em Coq deste algoritmo seria:

```coq
 Fixpoint ble (x y : nat) : bool :=
    match x, y with
    | O , y => true
    | S n , S m => ble n m
    | _ , _ => false
    end.

  Fixpoint insert (x : nat)(xs : list nat) : list nat :=
    match xs with
    | [] => [ x ]
    | (y :: ys) =>
      if ble x y then x :: y :: ys else y :: (insert x ys)
    end.

  Fixpoint isort (xs : list nat) : list nat :=
    match xs with
    | [] => []
    | (x :: xs) => insert x (isort xs)
    end.
```

O objetivo desse estudo de caso é verificar a implementação deste algoritmo. Para isso, usaremos uma combinação de
testes baseados em propriedades e de provas formais.

# Usando QuickChick para verificar o insertion sort

Primeiramente, para testarmos o algoritmo acima, devemos especificar uma propriedade que atesta sua correção.
Quando um algoritmo de ordenação pode ser considerado correto? Dizemos que um algoritmo de ordenação é correto se,
a partir de uma lista xs fornecida como entrada:

* retorna uma lista xs' que é uma permutação de xs.
* xs' é ordenada.

### Exercício 63

Codifique as seguintes funções que serão utilizadas para o teste de correção do insertion sort.

```coq
Fixpoint is_sorted (xs : list nat) : bool := ...
Definition is_permutation (xs ys : list nat) := ...
```

De posse dessas funções podemos estabelecer a correção do insertion sort usando a seguinte definição:

```coq
  Definition isort_correct (xs : list nat) :=
    isort_is_sorted xs && isort_permutation xs.
```

que evidentemente pode ser testada usando o comando QuickChick:

```coq
QuickChick isort_correct.
+++ Passed 10000 tests (0 discards)
```

### Exercício 64

Outro conhecido algoritmo de ordenação é o selection sort, que consiste em, a cada passo,
colocar o menor elemento de uma lista como seu primeiro elemento. Implemente o selection sort e
codifique a propriedade de correção para testar seu algoritmo usando QuickChick.


# Provando a correção do insertion sort

Para provarmos a correção do insertion sort, devemos especificar o que significa uma lista estar ordenada e
ser uma permutação. Ao contrário de usarmos funções, o mais adequado para provas é especificarmos predicados
indutivos tanto para listas ordenadas ou permutação de duas listas.

Abaixo, segue o predicado para especificar quando uma lista está ordenada.

```coq
  Inductive sorted : list nat -> Prop :=
  | SortedNil : sorted []
  | SortedSing : forall x, sorted [ x ]
  | SortedRec : forall x y l, x <= y -> sorted (y :: l) -> sorted (x :: y :: l).
````

### Exercício 65

Prove o seguinte teorema:

```coq
  Lemma insert_sorted
    : forall l x, sorted l -> sorted (insert x l).
````

Dizemos que uma lista xs é uma permutação de ys se permutation xs ys é provável.

```coq
  Inductive permutation {A : Type}: list A -> list A -> Prop :=
    perm_nil : permutation [] []
  | perm_skip : forall (x : A) (l l' : list A),
                permutation l l' ->
                permutation (x :: l) (x :: l')
  | perm_swap : forall (x y : A) (l : list A),
                permutation (y :: x :: l) (x :: y :: l)
  | perm_trans : forall l l' l'' : list A,
                 permutation l l' ->
                 permutation l' l'' ->
                 permutation l l''.
````

### Exercício 66

Prove o seguinte teorema:

```coq
  Lemma insert_permutation
    : forall l x, permutation (x :: l) (insert x l).
```

### Exercício 67

Prove o seguinte teorema:

```coq
  Lemma isort_permutation_thm : forall l, permutation l (isort l).
```

Usando os resultados anteriores, prove o seguinte resultado de correção:

```coq
 Theorem isort_correct_thm : forall l, permutation l (isort l) /\
                                   sorted (isort l).
````

Nota: Evidentemente, será necessário provar vários lemas / teoremas auxiliares. É útil
tentar descobrir quais são os teoremas e usar QuickChick para tentar encontrar contra
exemplos para esses possíveis teoremas, antes de tentar provar.

### Exercício 68

Usando como modelo a formalização do insertion sort, formalize o algoritmo selection sort.
