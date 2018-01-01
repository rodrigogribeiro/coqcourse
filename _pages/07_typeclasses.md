---
layout: page
title: Classes de tipos em Coq
permalink: /typeclasses/
---

Classes de tipos são dos um das mais distintivas características da
linguagem Haskell. De maneira simples, classes de tipos permitem ao
programador definir novos símbolos sobrecarregados na linguagem.
Até recentemente, Coq não suportava a definição de classes de tipos.
Em versões mais recentes, esse mecanismo foi incluído e permite a
definição de funções (e também provas) sobrecarregadas, o que possibilita
uma maior reutilização de formalizações.

Neste capítulo veremos alguns exemplos de como classes de tipos são
utilizadas em Coq, sem se preocupar com detalhes aprofundados de como
estas são implementadas. O leitor interessado pode ler o seguinte
[tutorial](https://softwarefoundations.cis.upenn.edu/draft/qc-current/Typeclasses.html)
que cobre todos esses detalhes.


# Introdução às classes de tipos em Coq

Como um primeiro exemplo, vamos considerar uma classe de tipo para
converter valores em strings.

```coq
Class Show (A : Type) : Type
   :={
       show : A -> string
     }.
```
A classe de tipos _Show_ pode ser entendida como um predicado que classifica os
tipos que provêem uma função para converter valores em strings. Podemos declarar
que o tipo _bool_ satisfaz o predicado definido por _Show_ usando uma declaração
de instância, conforme a seguir (note que strings em Coq são construídas usando aspas duplas normais "",
o código abaixo usa aspas simples para evitar erros do gerador de páginas estáticas):


```coq
Instance showBool : Show bool
:={
    show := fun b:bool => if b then ''true'' else ''false''
  }.
```
A seguir mostramos um exemplo de um tipo de dados simples e de sua respectiva instância de _Show_.

```coq

Inductive color := Red | Green | Blue.

Instance showColor : Show color :=
  {
    show :=
      fun c:color =>
        match c with
        | Red => ''Red''
        | Green => ''Green''
        | Blue => ''Blue''
        end
  }.
```
Abaixo apresentamos uma instância para o tipo _nat_:

```coq

Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match n mod 10 with
           | 0 => ''0'' | 1 => ''1'' | 2 => ''2'' | 3 => ''3'' | 4 => ''4'' | 5 => ''5''
           | 6 => ''6'' | 7 => ''7'' | 8 => ''8'' | _ => ''9''
           end in
  let acc' := d ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => string_of_nat_aux time' n' acc'
      end
  end.

Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux n n ''.

Instance showNat : Show nat :=
  {
    show := string_of_nat
  }.

````

### Exercício 57

Escreva uma instância de _Show_ para pares de _nat_ e _bool_.

Usando a classe _Show_, podemos definir funções que usam _show_ anotando uma
restrição de classe no tipo da função definida.

```coq
Definition showOne {A : Type} `{Show A} (a : A) : string :=
  ''The value is '' ++ show a.
```

A anotação _{Show A}_ é uma restrição de classe que especifica que a função _showOne_ só pode ser
aplicada a tipos que são instâncias da classe _Show_. Abaixo, temos outro exemplo.

```coq
Definition showTwo {A B : Type}
           `{Show A} `{Show B} (a : A) (b : B) : string :=
  ''First is '' ++ show a ++ '' and second is '' ++ show b.
```

### Exercício 58

Porquê a restrição _{Show A}_ no tipo de _ShowOne_ é necessária? Explique com suas palavras e remova-a
para verificar se sua intuição corresponde a mensagem retornada pelo interpretador de Coq.

Evidentemente, _Show_ não é a única classe de tipos interessante. Outro exemplo é o de uma classe cujos
tipos suportam um teste de igualdade.

```coq
Class Eq A :=
  {
    eqb: A -> A -> bool;
  }.
```
e algumas instâncias simples.

```coq
Instance eqBool : Eq bool :=
  {
    eqb := fun (b c : bool) =>
       match b, c with
         | true, true => true
         | true, false => false
         | false, true => false
         | false, false => true
       end
  }.

Instance eqNat : Eq nat :=
  {
    eqb := beq_nat
  }.
```

### Exercício 59

Usualmente, a igualdade para tipos funcionais não é definida. Porém, alguns
tipos funcionais, como bool -> bool, podem ser testados para igualdade.
Escreva uma instância de Eq para o tipo bool -> bool.


# Instâncias parametrizadas

Instâncias podem ser construídas para tipos polimórficos como pares, listas, etc.
Como exemplo, apresentamos uma instância para pares de valores de tipos potencialmente
diferentes.

```coq
Instance showPair {A B : Type} `{Show A} `{Show B} : Show (A * B) :=
  {|
    show p :=
      let (a,b) := (p : A * B) in
         ''('' ++ show a ++ '','' ++ show b ++ '')''
  |}.
```

De maneira similar, podemos definir uma instância de Eq para pares.

```coq
Instance eqPair {A B : Type} `{Eq A} `{Eq B} : Eq (A * B) :=
  {|
    eqb p1 p2 :=
      let (p1a,p1b) := p1 : A * B in
      let (p2a,p2b) := p2 : A * B in
      andb (eqb p1a p2a) (eqb p1b p2b)
  |}.
```

e aqui está a instância de _Show_ para listas

```coq
Fixpoint showListAux {A : Type} (s : A -> string) (l : list A) : string :=
  match l with
    | nil => ''
    | cons h nil => s h
    | cons h t => append (append (s h) ', ') (showListAux s t)
  end.

Instance showList {A : Type} `{Show A} : Show (list A) :=
  {|
    show l := append '[' (append (showListAux show l) ']')
  |}.
```

# Hierarquias de Classes

Normalmente ornizamos classes em hierarquias. Por exemplo, podemos projetar uma classe Ord
para tipos que provêem um testes de igualdade ou de menor-que. Uma maneira de se fazer isso é,
como em Haskell, especificar que Ord é uma subclasse de Eq.

```coq
Class Ord A `{Eq A} : Type :=
  {
    le : A → A → bool
  }.
```

Abaixo apresentamos um exemplo de instância para Ord:

```coq
Instance natOrd : Ord nat :=
  {
    le := Nat.leb
  }.
```

### Exercício 60

Implemente uma instância de Ord para o tipo bool.

Usando a classe Ord, podemos implementar uma função _max_:

```coq
Definition max {A: Type} `{Eq A} `{Ord A} (x y : A) : A :=
  if le x y then y else x.
```

### Exercício 61

Qual erro apresentado por Coq ao esquecermos a restrição Ord do tipo de max?
E a restrição Eq é realmente necessária?

### Exercício 62

Defina uma instância de Ord para pares e listas.

# Conclusão

Isso conclui essa simples apresentação ao uso de classes de tipos em Coq.
O próximo capítulo irá usar os conceitos aqui apresentados para uso do
plug-in para teste baseado em propriedades de Coq, o QuickChick.

