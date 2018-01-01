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


