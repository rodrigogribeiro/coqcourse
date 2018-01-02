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

