---
layout: page
title: Programação com tipos dependentes
permalink: /dependenttypes/
---

Até o presente momento devotamos nossa atenção a usar Coq para demonstrar
simples fatos matemáticos e a explicar o uso da ferramenta. A partir deste
ponto, vamos apresentar como o uso de automação de provas e tipos indutivos
fornece um arcabouço apropriado para desenvolver programas em conjunto com
suas respectivas provas de correção.

## Subset types and friends

O primeiro tipo que pode ser utilizado para integrar provas de correção a
definição de funções é o chamado tipo _subset_, cuja definição presente 
na biblioteca de Coq apresento abaixo:

```coq
     Inductive sig (A : Type) (P : A -> Prop) : Type :=
        exist : forall x : A, P x -> sig P
```

Intuitivamente, o tipo `sig` é similar ao quantificador existencial: seu 
construtor, `exist`, recebe um valor `x : A` e uma prova de que `x` atende
a uma propriedade `P`. A diferença entre `sig` e `ex` está no universo em que
estes tipos são definidos: `sig` é definido em `Type`, enquanto `ex` é definido
em `Prop`. Essa diferença é fundamental para o processo de extração de código, 
que permite a geração de código ML ou Haskell a partir de uma formalização Coq.
Durante a extração, valores cujos tipos pertencem ao universo `Prop` são 
eliminados do código já que estes são apenas certificados de propriedades e
não influem na execução do código em questão.

Coq define a seguinte notação para o tipo `sig A P` : `{x : A | P x}`. A seguir, 
definimos uma função de adição que utiliza o tipo `sig` para combinar um
certificado de correção à declaração da função.

```coq
  Hint Constructors Plus.
  
  Definition plus_cert : forall (n m : nat), {r : nat | Plus n m r}.
```
Inicialmente, incluímos os construtores do predicado `Plus` ao hint database 
e usamos um subset type para definirmos o tipo da função `plus_cert`. 
O tipo `{r : nat | Plus n m r}` intuitivamente descreve o conjunto de valores
`r : nat` que satisfaz o predicado `Plus n m r`, isto é, este tipo descreve
um subconjunto de `nat`, por isso o nome subset type.

Para definirmos funções que envolvem tipos dependentes é comum utilizarmos
a tática `refine`, que permite especificarmos a estrutura de um termo
com _holes_, que consistem de partes a serem preenchidas posteriormente
por táticas. Holes são representados por "_" (underlines). 
      
A principal vantagem de usar a tática `refine` é que 
temos um maior controle sobre o código da função produzida, porém, 
isso demanda maior trabalho, uma vez que somos obrigados a realizar
anotações para descrever o dependências do resultado da função com 
seus parâmetros e utilizar igualdades para forçar o refinamento de parâmetros
em equações. Primeiramente, vamos considerar como expressar a relação entre
o resultado de uma função e seus parâmetros.

```coq
      refine (fix plus_cert (n m : nat) : {r | Plus n m r} :=
                match n return {r | Plus n m r} with
                | O    => exist _ m _
                | S n1 =>
                   match plus_cert n1 m with
                   | exist _ r1 _ => exist _ (S r1) _
                   end
                end) ; clear plus_cert ; auto.
    Defined.
```
Note que usamos uma anotação [return] na construção [match]. Cláusulas
[return] são usadas para declarar explicitamente a relação de dependência 
entre o tipo de resultado da função e seus parâmetros. No exemplo anterior,
o trecho [match n return {r | Plus n m r} with] especifica que a ocorrência
de [n] em [{r | Plus n m r}] deve ser igual ao valor de [n] em cada equação
considerada no casamento de padrão. Após o processamento da tática [refine],
temos as seguintes conclusões a serem provadas para concluir a definição de
[plus_cert]:

```coq
plus_cert : forall n m : nat, {r : nat | Plus n m r}
n, m : nat
============================
Plus 0 m m

subgoal 2 (ID 11) is:

plus_cert : forall n m : nat, {r : nat | Plus n m r}
n, m, n1, r1 : nat
p : Plus n1 m r1
============================
Plus (S n1) m (S r1)
```

Note que, em ambos os casos, temos a hipótese

```coq
plus_cert : forall n m : nat, {r : nat | Plus n m r}
```

isso se deve ao fato de definirmos `plus_cert` usando uma expressão `fix`, para definir 
uma função recursiva. Quando definimos uma função recursiva usando `fix`, Coq adiciona
o tipo da função definida como uma hipótese. Essa inclusão é necessária para permitir
que possamos fazer uma chamada recursiva (afinal, só podemos chamar uma função se ela
estiver definida, certo?). Porém, no contexto de automação de provas, essa hipótese
é perigosa, pois permite que façamos uma chamada recursiva sobre os parâmetros originais,
construindo, assim, um loop. Por isso, sempre ao utilizarmos `refine` para definir funções
recursivas devemos usar a tática `clear` para eliminar essa hipótese do contexto evitando
assim que esta seja usada por táticas com `auto`.

A seguir, apresentamos outro exemplo de função utilizando subset types: cálculo do
predecessor de um número natural. A função `pred_cert` possui o seguinte tipo:

```coq
Definition pred_cert : forall (n : nat), n > 0 -> {r | n = 1 + r}.
```
que a partir de um número natural `n > 0` retorna um valor `r` tal que `n = 1 + r`.

```coq
  Definition pred_cert : forall (n : nat), n > 0 -> {r | n = 1 + r}.
    refine (fun n =>
              match n return n > 0 -> {r | n = 1 + r} with
              | O => fun _ => False_rec _ _
              | S n' => fun _ => exist _ n' _
              end) ; omega.
  Defined.
```

Uma maneira de atenuar a sintaxe de definições envolvendo tipos subset é o uso de 
notações. Abaixo apresentamos notações e redefinimos `pred_cert` de
modo a usá-las.

     Notation "!" := (False_rec _ _).
     Notation "[ e ]" := (exist _ e _).

```coq
  Definition pred_cert1 : forall (n : nat), n > 0 -> {r | n = 1 + r}.
    refine (fun n =>
              match n return n > 0 -> {r | n = 1 + r} with
              | O => fun _ => !
              | S n' => fun _ => [ n' ]
              end) ; omega.
  Defined.
```

Outro tipo importante para programação com tipos dependentes em Coq é o chamado
tipo de proposições decidíveis, `sumbool`, suja definição é apresentada abaixo:

```coq
Inductive sumbool (A B : Prop) : Set :=
| left : A -> {A} + {B} 
| right : B -> {A} + {B}
```

Intuitivamente, o tipo `sumbool` captura a idéia de que uma dentre duas proposições
é verdadeira. Usando este tipo podemos definir uma função que testa igualdade de
números naturais, retornando uma prova de que os parâmetros são iguais ou não.
A seguir apresentamos essa função e notações para o uso do tipo
`sumbool`.

    Notation "'Yes'" := (left _ _).
    Notation "'No'" := (right _ _).
    Notation "'Reduce' x" := (if x then Yes else No) (at level 50).

```coq
  Definition eq_nat_dec : forall (n m : nat), {n = m} + {n <> m}.
    refine (fix eq_nat n m : {n = m} + {n <> m} :=
              match n , m with
              | O    , O    => Yes
              | S n' , S m' => Reduce (eq_nat n' m')
              | _    , _    => No
              end) ; clear eq_nat ; congruence.
  Defined.
```

A seguir, vamos utilizar a função `eq_nat_dec` em alguns casos de
teste

```coq
  Eval compute in eq_nat_dec 1 1.

   = Yes
     : {1 = 1} + {1 <> 1}

  
  Eval compute in eq_nat_dec 2 4.

   = No
     : {2 = 4} + {2 <> 4}
```

### Exercício 44

```coq
  Definition eq_bool_dec : forall (a b : bool), {a = b} + {a <> b}.
  Admitted.
```  

### Exercício 45

```coq
  Definition eq_list_dec
             {A : Type}
             (eqAdec : forall (x y : A), {x = y} + {x <> y})
    : forall (xs ys : list A), {xs = ys} + {xs <> ys}.
  Admitted.
```

O último exemplo de tipo dependente da biblioteca padrão de Coq é o tipo `sumor`, cuja
declaração apresentamos abaixo:

```coq
    Inductive sumor (A : Type) (B : Prop) : Type :=
    inleft : A -> A + {B} | inright : B -> A + {B}
```

Usualmente o tipo `sumor` é combinado com `sig` para fornecer especificações do
comportamento de funções. Em exemplos anteriores, usamos o tipo `sig` para 
especificar uma função de predecessor. Porém, as implementações não constituem
uma função total sobre o conjunto dos naturais, uma vez que para executar `pred_cert`
devemos fornecer um valor `n > 0`. Utilizando o tipo `sumor`, podemos especificar
essa função de maneira a considerar o caso de que `n = 0`. A implementação é apresentada
abaixo.

	Notation "!!" := (inright _ _).
	Notation "[|| x ||]" := (inleft _ [x]).

```coq
  Definition pred_cert_full : forall n, {r | n = 1 + r} + {n = 0}.
    refine (fun n =>
              match n return {r | n = 1 + r} + {n = 0} with
              | O => !!
              | S n' => [|| n' ||] 
              end) ; auto.
  Defined.
```

A seguir vamos considerar um exemplo mais elaborado de um programa e
sua cerficação, uma função para busca por chaves em um finite map.
Primeiramente, vamos definir uma versão aprimorada da tática `inversion`.

```coq
Ltac inverts H := inversion H ; subst ; clear H.
```

Em seguida, definimos uma seção, que é o mecanismo, similar a blocos em
linguagens imperativas, utilizado por Coq para agrupar declações em um
escopo de visibilidade.

```coq
  Section MAP.
    Variable Key : Type.
    Variable Value : Type.
    Variable eqKeyDec : forall (x y : Key), {x = y} + {x <> y}.

    Inductive Map : Type :=
    | nil : Map
    | cons : Key -> Value -> Map -> Map.
```
	
Suponhos um tipo `Key`, para representar chaves em um finite map e
uma função `eqKeyDec` para decidir a igualdade de dois valores deste
tipo. Além disso, supomos o tipo `Value` para representar valores a
serem armazenados em um map. Na sequência, declaramos o tipo `Map`,
que consiste de uma lista de formada por pares chave-valor.

O tipo `MapsTo k v m` representa provas de que uma de uma chave `k`
está associada ao valor `v` no finite map `m`. Este é definido a seguir.

```coq
    Inductive MapsTo : Key -> Value -> Map -> Prop :=
    | Here  : forall k v m, MapsTo k v (cons k v m)
    | There : forall k v m k' v', k <> k' ->
        MapsTo k v m -> MapsTo k v (cons k' v' m).

    Hint Constructors MapsTo.
```

A função `lookup` retorna o valor associado a uma chave fornecida como
parâmetro e uma prova deste fato usando o predicado `MapsTo` ou
um certificado de que tal chave não está presente no finite map
fornecido como parâmetro. Essa especificação é dada pelo tipo:

```coq
forall (k : Key)(m : Map), {v | MapsTo k v m} + {forall v, ~ MapsTo k v m}.
```

em que `{v | MapsTo k v m}` denota a prova de que `v` está associado
a chave `k` em `m`. O tipo `{forall v, ~ MapsTo k v m}` representa o
fato de que não existe valor `v` associado a `k` em `m`. A declaração
de `lookup` utiliza a tática `refine` em sua definição, que consiste
em uma busca sequencial pela chave. 

```coq
    Definition lookupMap
      : forall (k : Key)(m : Map), {v | MapsTo k v m} + {forall v, ~ MapsTo k v m}.
      refine (fix look k m : {v | MapsTo k v m} + {forall v, ~ MapsTo k v m} :=
                match m return {v | MapsTo k v m} + {forall v, ~ MapsTo k v m} with
                | nil => !!
                | cons k' v' m' =>
                  match eqKeyDec k k' with
                  | Yes => [|| v' ||]
                  | No  =>
                    match look k m' with
                    | !! => !!
                    | [|| v ||] => [|| v ||]
                    end
                  end
                end) ;
        clear look ; subst ;
          try (repeat (match goal with
                       | [H : MapsTo _ _ nil |- _] => inverts H
                       | [H : MapsTo _ _ (cons _ _ _) |- _] => inverts H
                       | [|- forall x, ~ _ ] => unfold not ; intros
                       | [ H : forall x, ~ (MapsTo _ _ _)
                         , H1 : MapsTo _ _ _ |- _] => apply H in H1
                       end)) ; auto.
     Defined.
  End MAP.
```
Note que em cada caso da equação,
utilizamos as notações definidas anteriormente para o tipo `sumor`,
que ao fim do processamento da tática `refine`, produzem as seguintes
obrigações de prova:

```coq
 ============================
  forall v : Value, ~ MapsTo k v nil

subgoal 2 (ID 74) is:
 MapsTo k' v' (cons k' v' m')
subgoal 3 (ID 71) is:
 MapsTo k v (cons k' v' m')
subgoal 4 (ID 72) is:
forall v : Value, ~ MapsTo k v (cons k' v' m')

```

que são resolvidas pela seguinte tática:

```coq
        clear look ; subst ;
          try (repeat (match goal with
                       | [H : MapsTo _ _ nil |- _] => inverts H
                       | [H : MapsTo _ _ (cons _ _ _) |- _] => inverts H
                       | [|- forall x, ~ _ ] => unfold not ; intros
                       | [ H : forall x, ~ (MapsTo _ _ _)
                         , H1 : MapsTo _ _ _ |- _] => apply H in H1
                       end)) ; auto.
```

que elimina do contexto a hipótese referente a definição função
`lookup`, usando a tática `clear` e na sequência executa diferentes
táticas de acordo com o padrão especificado em cada uma das equações
da construção `match`.

### Exercício 46

```coq
Definition insertMap : forall (k : Key)(v : Value)(m : Map), {m' | MapsTo k v m'}.
Admitted.
```

### Exercício 47

```coq
Definition removeMap : forall (k : Key)(m : Map), {m' | ~ MapsTo k v m'}.
Admitted.
```

## Listas indexadas por tamanho

Um dos exemplos clássicos para uso de tipos dependentes é a
manipulação segura de índices em listas / arranjos. Nesta seção,
veremos como o uso de tipos dependentes em Coq permite-nos
definir funções potencialmente não seguras sobre listas.

Listas indexadas por tamanho, usualmente denominadas de `vectors`,
possuem a seguinte definição em Coq.

```coq
    Inductive vector (A : Set) : nat -> Type :=
    | vnil  : vector A 0
    | vcons : forall n, A -> vector A n -> vector A (S n).
```
O tipo `vector` é parametrizado por um tipo `A : Set` e possui um
índice de tipo `nat`, que representa o número de elementos
presentes nesta lista. O construtor `vnil : vector A 0`, representa a
lista vazia e, por isso, possui como índice o valor `0`. Por sua vez,
vectors não vazios são formados pelo construtor `vcons` que
a partir de um valor de tipo `A` e uma lista de tamanho `n` produz
um vector de tamanho `S n`.

A seguir apresentamos uma função para concatenação de `vector`s.

```coq
    Fixpoint app {A : Set}{n1 n2}(ls1 : vector A n1)(ls2 : vector A n2) : vector A (n1 + n2) :=
      match ls1 with
      | vnil _ => ls2
      | vcons _ _ x ls1' => vcons _ _ x (app ls1' ls2)
      end.
```
Note que o tipo de `app` garante que o `vector` resultante tenha
tamanho igual a soma do tamanho de seus parâmetros. Para listas
convencionais este resultado foi provado por indução. No caso de
vectors, este decorre diretamente da definição da função de
concatenação.

### Exercício 48

```coq
    Fixpoint vmap {A B : Set}{n}(f : A -> B)(v : vector A n) : vector B n :=
      admit.
```

### Exercício 49

Enuncie e prove um teorema que mostra que concatenação de valores de
tipo `vector` é uma operação associativa.

Outra vantagem do tipo `vector` é por permitir especificar que a
função `head`, que obtem o primeiro elemento de uma lista, só pode ser
aplicada sobre listas não vazias.

```coq
  Definition vhead {A : Set}{n}(v : vector A (S n)) : A :=
    match v with
    | vcons _ _ x _ => x
    end.
````

Outra operação que pode ser representada de maneira segura usando
o tipo`vector` é a operação de indexação sobre listas. Para isso,
vamos utilizar o tipo `fin n`, que representa um conjunto contendo
`n` elementos.

```coq
  Inductive fin : nat -> Set :=
  | fzero : forall {n}, fin (S n)
  | fsucc : forall {n}, fin n -> fin (S n).
```

De acordo com a definição do tipo `fin`, podemos observar que não é
possível construir um valor de tipo `fin 0`, logo denota o conjunto
vazio e o tipo `fin 1`, possui exatamente um valor `fzero : fin 1`,
por sua vez, `fin 2` possui dois a valores, a saber: `fzero : fin 2` e
`fsucc fzero : fin 2`, e assim por diante.

A função `get`, usada para indexar valores de tipo `vector` é
apresentada abaixo.

```coq
Fixpoint get {A}{n}(ls : vector A n) : fin n -> A :=
    match ls with
      | vnil _ => fun idx =>
        match idx in fin n' return (match n' with
                                        | O => A
                                        | S _ => unit
                                      end) with
          | fzero => tt
          | fsucc _ => tt
        end
      | vcons _ _ x ls' => fun idx =>
        match idx in fin n' return (fin (pred n') -> A) -> A with
          | fzero => fun _ => x
          | fsucc idx' => fun get_ls' => get_ls' idx'
        end (get ls')
	end.
```
O tipo da função `get` garante:

- Esta não pode ser chamada sobre listas vazias. Isso se deve ao fato
  de que o tipo `fin 0` ser equivalente ao tipo `False`, por ser não habitado.

- Esta não pode ser chamada sobre índices maiores que o tamanho da
lista. Esta restrição está diretamente codificada pelo tipo: Note que
tanto a lista `vector A n` e o índice `fin n` possuem o mesmo tamanho,
"n", evitando acessos a posições inválidas.
