---
layout: page
title: Táticas e automação de provas
permalink: /tactics/
---

## Táticas adicionais e automação de provas

Até o presente momento, escrevemos demonstrações como scripts
de táticas que alteram o estado de uma prova até sua conclusão.
Você deve ter notado que existe um certo grau de "repetição" em 
scripts. Em provas que possuem diversos casos é usual que cada
caso inicie com o mesmo conjunto de táticas (por exemplo, introduzindo 
hipóteses), o que torna tediosa a tarefa de demonstrar fatos simples.

Nesta seção apresentaremos diversos recursos presentes em Coq que 
permitem a automação de provas. Primeiramente, falaremos sobre os
combinadores de táticas e, em seguida, apresentaremos táticas
especializadas em resolver conclusões de certos subconjuntos decidíveis
da lógica de predicados. Finalmente, apresentaremos uma introdução à 
linguagem de descrição de táticas, Ltac, que permite a escrita de novas
táticas.

## Combinadores de táticas

O primeiro combinador de táticas que utilizaremos será o ; . 
Combinar sequencialmente duas táticas `tac` e `tac'`, `tac ; tac'`, 
quando aplicada sobre um estado de prova `C` consiste em aplicar `tac`
sobre `C` e `tac'` a todas as sub-provas geradas pela aplicação de `tac`.
Se `tac` ou  `tac'` falham, toda a combinação falha. A seguir, apresentamos 
um exemplo simples desta tática.

```coq
    Theorem seq_comb
      : forall (A B : Prop), (((A -> B) -> B) -> B) -> A -> B.
    Proof.
      intros A B HImp Ha ; apply HImp ; intros Hab ; apply Hab ; assumption.
    Qed.
```

Um inconveniente da composição sequencial `tac ; tac'` é que a tática `tac'`
deve ser aplicável a todas as subprovas geradas por `tac`. Porém, é comum que
diferentes sub-casos gerados por uma tática demandem tratamento específico.
Nestas situações, podemos utilizar a composição generalizada:

        tac ; [tac1 | tac2 | ... | tacn].

que se comporta de maneira similar a composição sequencial, porém aplica a tática
`tac_i` ao i-ésimo caso gerado por `tac`. É importante ressaltar que ao utilizar
a composição generalizada devemos utilizar o número correto de subcasos gerados.
O próximo exemplo ilustra o uso deste combinador.

```coq
    Theorem chain
      : forall (A B C : Prop), (A -> B -> C) -> (A -> B) -> A -> C.
    Proof.
      intros A B C Habc Hab Ha ; apply Habc ; [ assumption | apply Hab ; assumption ].
    Qed.
```
 Outro combinador de táticas é representado por `tac || tac'` e denota o seguinte 
comportamento: se `tac` é executada com sucesso sobre o estado atual, `tac'` é 
ignorada. Somente quando `tac` falha, ocorre a execução de `tac'` sobre o 
estado de prova atual. O próximo exemplo ilustra essa tática.

```coq
    Theorem orElse_example
      : forall (A B C D : Prop), (A -> B) -> C -> ((A -> B) -> C -> (D -> B) -> D) -> A -> D.
    Proof.
      intros A B C D Hab Hc H Ha ;
        apply H ; (assumption || intro H1) ;
          apply Hab ; assumption.
    Qed.
```

Além dos operadores de composição apresentados, Coq provê as táticas `idtac` e
`fail`, que deixam o estado de prova inalterado (logo, sempre executa com sucesso) e
que sempre falha, respectivamente. Essas táticas são úteis no contexto de combinadores
por agirem como elementos neutro (`idtac`) e nulo (`fail`) para composição. 

Dois combinadores muito utéis em automação de provas são `try` e `repeat`. A tática
`try tac` comporta-se exatamente como `tac`, exceto que se `tac` falhar no estado 
de prova atual, `try tac` deixa-o inalterado. Por sua vez, a tática `repeat tac`
aplica `tac` ao estado de prova atual e a todos os sub-casos gerados por sucessivas
aplicações de `tac` até resolver a prova ou até que `tac` falhe em algum subcaso.
Note que usar a tática `repeat` sobre uma tática que não falha sem resolver completamente
a prova, leva a não terminação --- loop. A seguir apresentamos dois exemplos destes
combinadores.

```coq
    Lemma try_test
      : forall (A B C D : Prop), (A -> B -> C -> D) -> (A -> B) -> (A -> C -> D).
    Proof.
      intros A B C D H H1 HA HC.
      apply H  ; try (assumption || (apply H1 ; assumption)).
     Qed.
      
    Lemma even_100 : even 100.
    Proof.
      repeat ((apply ev_ss) || (apply ev_zero)).
    Qed.
```

## Táticas adicionais

O manual de Coq (disponível em http://coq.inria.fr) possui uma lista de
todas as táticas disponíveis na linguagem (são muitas). Aqui vamos apresentar
algumas táticas muito úteis e que podem ajudar em diversas formalizações.

### Tática `constructor`

É comum em provas sobre predicados indutivos termos que aplicar explicitamente
um construtor do predicado em questão. Coq possui uma tática que facilita 
esse processo: a tática `constructor`, que tenta aplicar algum construtor 
do tipo de dados indutivo que forma a conclusão da prova atual. Anteriormente, 
usamos `repeat ((apply ev_ss) || (apply ev_zero))` para provar `even 100`. O 
mesmo resultado pode ser obtido por `repeat constructor`.

### Tática `clear`

A utilização da tática `inversion` sobre uma hipótese pode resultar em um número
grande de igualdades. Vimos anteriormente que a tática `subst` pode ser utilizada
para reescrever essas igualdades eliminando-as do contexto de tipos. Porém, a hipótese
original sobre a qual `inversion` foi chamada permanece após sua execução. Outra tática
comumente utilizanda com `inversion` é a tática `clear` que pode ser utilizada para 
eliminar uma hipótese. Aparentemente remover hipóteses pode não parecer uma boa idéia,
porém, ao utilizarmos automação de provas, o desempenho da verificação 
realizada por Coq começa a depender seriamente do número de hipóteses. Desta forma, 
o uso da tática `clear` é altamente recomendado quando uma hipótese não é mais necessária.

### Tática `congruence`

A primeira tática que veremos consiste de um procedimento de decisão para 
igualdades envolvendo símbolos não interpretados, a tática `congruence`.
A utilidade desta tática é para eliminar casos em que surgem igualdades
contraditórias, especialmente comum em provas que envolvem análise de casos
sobre tipos indutivos. A seguir, apresentamos um exemplo simples de uso 
desta tática.

```coq
    Lemma one_not_zero : 0 <> 1.
    Proof.
      intro ; congruence.
    Qed.
```

### Tática `intuition`

A tática `intuition` realiza simplificações no estado de prova utilizando
a teoria da lógica proposicional. Diversos objetivos envolvendo tautologias
da lógica proposicional podem ser resolvidos automaticamente por `intuition`.

```coq
    Theorem orElse_example1
      : forall (A B C D : Prop), (A -> B) -> C -> ((A -> B) -> C -> (D -> B) -> D) -> A -> D.
    Proof.
      intuition.
      Qed.
```
	  
### Tática `omega`


Provas envolvendo aritmética são especialmente tediosas de serem escritas manualmente.
A tática `omega` é um procedimento de decisão completo para a aritmética de Presburguer,
que de maneira simples, são fórmulas envolvendo conectivos da lógica proposicional, 
valores inteiros adição e comparação. Abaixo repetimos uma prova anterior, `le_S_cong`,
usando a tática `omega`, que resolve-a automaticamente.

```coq
Lemma le_S_cong_omega : forall n m, S n <= S m -> n <= m.
Proof.
	intros n m ; omega.
Qed.
```

### Tática `auto`

De maneira simples, a tática `auto` resolve conclusões que podem ser provadas por
uma combinação de `assumption`, `intros` e [apply] até uma profundidade máxima 
para busca por uma solução. O valor padrão de profundidade de busca é 5. A 
seguir usamos a tática `auto` para provar um resultado provado anteriormente.

```coq
    Theorem auto_example1
      : forall (A B C D : Prop), (A -> B) -> C -> ((A -> B) -> C -> (D -> B) -> D) -> A -> D.
    Proof.
      auto.
    Qed.
```
	
A execução de `auto` nunca resulta em erro. Ou resolve completamente 
a prova ou deixa o estado de prova inalterado. Um ponto importante a 
cerca da tática `auto` é que esta utiliza os chamados _hint databases_
para determinar quais lemas serão utilizados pela tática para tentar
demonstrar conclusões. O comando

```coq
Hint Resolve thm1 thm2 ... thmn : dbname. 
```

Adiciona as táticas `apply thm1, apply thm2, ..., apply thmn` ao hint
database `dbname`. O nome `dbname` pode ser omitido e, neste caso,
assume-se que as táticas serão adicionadas ao hint database `core`.
Além de teoremas é possível adicionar construtores de um determinado
tipo de dados indutivo usando o comando

```coq
Hint Constructors ty1 ty2 ... tyn : dbname.
```

O exemplo a seguir ilustra esses comandos.

```coq
    Inductive Plus : nat -> nat -> nat -> Prop :=
    | PlusZero
      : forall m, Plus 0 m m
    | PlusSucc
      : forall n m r,
        Plus n m r ->
        Plus (S n) m (S r).
```

O tipo `Plus` representa uma possível especificação de uma função
de adição de números naturais. A seguir usamos a tática 
`repeat constructor` para construir um valor de tipo `Plus 4 3 7`.

```coq
    Example plus_4_3 : Plus 4 3 7.
    Proof.
      repeat constructor.
    Qed.

    Hint Constructors Plus.
```
Ao adicionarmos os construtores de `Plus` ao hint database,
o exemplo anterior pode ser resolvido pela tática `auto`, conforme 
apresentado a seguir.

```coq
    Example plus_4_3_auto : Plus 4 3 7.
    Proof.
      auto.
    Qed.
```

A seguir, apresentamos um teorema que mostra a relação
entre a função de soma e o predicado `Plus`.

```coq
    Lemma plus_complete : forall n m r, Plus n m r -> n + m = r.
    Proof.
      induction n ; intros m r H ; inversion H ;
        subst ; clear H ; simpl ; f_equal ; auto. 
    Qed.
```

## Programando táticas com Ltac

O uso de combinadores, táticas que proveem procedimentos de decisão 
(`omega`, `congruence`) e `auto` permite-nos resolver diversas provas
de maneira mais simples. Apesar de úteis, esses recursos não nos permitem
um controle preciso de quando táticas serão aplicadas e também não proporcionam 
maneiras para reutilização de uma tática para uso por diferentes teoremas. 
        
Uma resposta para as dificuldades citadas é a linguagem de domínio específico para
táticas, Ltac, que permite declarar novas táticas e também possui uma construção
para casamento de padrão sobre o estado atual da prova.

O próximo exemplo ilustra como podemos realizar casamento de padrão sobre o 
estado atual da prova.

```coq
    Ltac break_if :=
      match goal with
      | [ |- if ?X then _ else _ ] => destruct X
      end.
```

A palavra reservada `Ltac` inicia a definição de uma nova tática. Neste exemplo,
usamos a construção `match goal with...`, para casamento de padrão sobre o 
estado atual da prova. O `match` é formado apenas por uma equação

```coq
[ |- if ?X then _ else _ ] => destruct X 
```

que especifica que se a conclusão for da forma `if ?X then _ else _`, executaremos
a tática `destruct X`, para realizar uma análise de casos sobre o valor `X`. Padrões
como o descrito na equação anterior utilizam o símbolo de sequente, `|-`, para separar
hipóteses da conclusão do estado de prova atual.
Note que na equação anterior, não 
especificamos nenhuma hipótese logo, essa regra irá sempre ser executada independente
do estado de prova atual possuir ou não hipóteses. Isto é, padrões Ltac sobre hipóteses
possuem uma semântica similar ao quantificador existe: deve haver pelo menos uma hipótese
que satisfaça o padrão para que ele seja executado com sucesso. A seguir, utilizamos
essa tática para demonstrar um resultado simples.

```coq
    Theorem hmm : forall (a b c : bool),
        if a
        then if b
             then True
             else True
        else if c
             then True
             else True.
    Proof.
      intros; repeat break_if; constructor.
    Qed.
```
Apesar de útil, a tática `break_if` somente realiza casamento de padrão sobre a
condição se o if for o elemento sintático mais externo da conclusão. Usando 
_context patterns_ podemos selecionar um estado de prova com base em subexpressões.
A seguir, apresentamos uma tática que será executada sempre que a conclusão possuir
um `if`, mesmo que este ocorra interno a outras expressões

```coq
    Ltac break_if_inside :=
      match goal with
      | [ |- context[if ?X then _ else _] ] => destruct X
      end.

    Theorem hmm2 : forall (a b : bool),
        (if a then 42 else 42) = (if b then 42 else 42).
    Proof.
      intros; repeat break_if_inside; reflexivity.
    Qed.
```

O uso do combinador `repeat` com a construção `match` permite programar
procedimentos de decisão capazes de resolver muitos tipos de conclusões.
A seguir, apresento uma tática capaz de resolver diversas provas da 
lógica proposicional.

```coq
    Ltac simple_tauto :=
      repeat match goal with
             | [ H : ?P |- ?P ] => exact H
             | [ |- True ] => constructor
             | [ |- _ /\ _ ] => constructor
             | [ |- _ -> _ ] => intro
             | [ H : False |- _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ H : _ \/ _ |- _ ] => destruct H
             | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] => apply H1 in H2
             end.

    Lemma simple_example : forall A B C, (A -> B) -> (B -> C) -> A -> C.
    Proof.
      simple_tauto.
    Qed.
```
