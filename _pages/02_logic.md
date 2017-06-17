---
layout: page
title: Lógica em Coq
permalink: /logic/
---

Nesta seção apresentaremos como demonstrar resultados conhecidos da
lógica proposicional e de predicados utilizando Coq.

## Implicação

Vamos iniciar demonstrando alguns fatos simples envolvendo a implicação.
Para isso, vamos definir algumas variáveis proposicionais:

```coq
Variables A B C : Prop.
```

Em Coq, o comando `Variables` permite a definição de variáveis de
um determinado tipo. No código acima, declaramos `A B C` como sendo 
do tipo `Prop`, isso é, proposições. Dessa forma, temos que valores
de tipo `A B C` são, na verdade, provas de que estas proposições são
verdadeiras.

A seguir, definimos um primeiro teorema:

```coq
  Theorem first_theorem : (A -> B) -> A -> B.
  Proof.
    intro Hab.
    intro Ha.
    apply Hab.
    assumption.
  Qed.
```
Vamos analisar a estrutura deste primeiro exemplo. Inicialmente, definimos
qual resultado desejamos provar usando a palavra chave `Theorem` que
deve ser seguida de um identificador, `first_theorem` neste exemplo, para nomear este resultado. 
Após a definição do nome do teorema a ser demonstrado, definimos a fórmula lógica a 
ser provada, que em nosso exemplo consiste da tautologia `(A -> B) -> A -> B`.

Ao processarmos a declaração deste teorema, o seu IDE irá iniciar o modo de
construção interativa de provas, que exibe a seguinte configuração do estado inicial da 
prova. 

```coq
1 subgoal, subgoal 1 (ID 1)
  
A, B, C : Prop
============================
(A -> B) -> A -> B
```

A interpretação do estado de prova é bastante simples: tudo acima da linha formada por 
`===` consiste das hipóteses que podem ser utilizadas para provar a conclusão, localizada 
abaixo destas linhas. Note que essa notação é similar à utilizada para representar 
provas utilizando dedução natural.

Provas em Coq são construídas utilizando comandos chamados de _táticas_, que alteram o 
estado atual da prova. Em nosso primeiro exemplo, a primeira tática que utilizamos é 
`intro`, que permite adicionar o lado esquerdo de uma implicação ao conjunto de hipóteses,
similar à conhecida regra de introdução da implicação. Ao processarmos a tática `intro Hab`
o estado de prova é alterado para:
```coq
1 subgoal, subgoal 1 (ID 2)
  
A, B, C : Prop
Hab : A -> B
============================
A -> B
```
Note que a tática `intro` possui como parâmetro um nome a ser utilizado pela hipótese
a ser adicionada. É importante ressaltar que este deve ser um novo nome, isto é, nenhuma
outra hipótese deve possuir o mesmo nome utilizado como parâmetro para a tática `intro`.

Em seguida introduzimos a hipótese `Ha : A` utilizando a tática `intro Ha`, resultando em:

```coq
1 subgoal, subgoal 1 (ID 3)
  
A, B, C : Prop
Hab : A -> B
Ha : A
============================
B
```
      
Para concluirmos a prova, precisamos deduzir `B` a partir das hipóteses 
`Hab : A -> B` e `Ha : A`. Em dedução natural, esse passo é uma aplicação imediata
da regra de eliminação da implicação (ou _modus ponens_). Em Coq, usamos a tática 
`apply Hab`, que permite-nos deduzir `B` se obtermos uma prova de `A`. O estado de 
prova passa a ser:

```coq
1 subgoal, subgoal 1 (ID 3)
  
A, B, C : Prop
Hab : A -> B
Ha : A
============================
A
```
Note que o estado atual da prova possui como conclusão a proposição `A` que esta 
presente nas hipóteses, `Ha : A`. A tática `assumption` permite concluir uma 
demonstração caso exista uma hipótese com o mesmo tipo da conclusão. A seguinte
mensagem é apresentada por Coq para indicar que a demonstração foi concluída.

```coq
No more subgoals.
(dependent evars: (printing disabled) )
```
      
O comando `Qed` é utilizado para terminar a definição de um teorema. Outro comando
que termina uma prova é o `Admitted`, que simplesmente assume uma demonstração como
sendo verdadeira. Todos os exercícios propostos estão marcados com o comando 
`Admitted` e sua tarefa é substituí-lo por um _script_ de táticas para a construção
da prova em questão.

Isso termina o nosso primeiro exemplo.

### Exercício 1

```coq
Lemma ex1 : A -> B -> A.
Proof.
Admitted.
```

### Exercício 2

```coq
Lemma ex2 : (A -> B) -> (B -> C) -> A -> C.
Proof.
Admitted.
```

## Conjunção

Nesta seção abordaremos como construir provas utilizando conjunção. Para isso, utilizaremos
duas novas táticas: `destruct`, que permite decompor uma conjunção em suas partes e 
`split`, que divide uma conclusão `A /\ B` em duas conclusões. O exemplo a seguir mostra 
como usar essas táticas para provar que o conectivo de conjunção é comutativo.

```coq
  Lemma and_comm : A /\ B -> B /\ A.
  Proof.
    intro Hab.
    destruct Hab as [Ha Hb].
    split.
    +
      assumption.
    +
      assumption.
  Qed. 
```

  Após o processamento da tática `intro Hab, o estado da prova será:

```coq
  1 subgoal, subgoal 1 (ID 5)
  
  A, B, C : Prop
  Hab : A /\ B
  ============================
  B /\ A
  ```
  
  Para concluir essa demonstração, devemos decompor a hipótese `Hab : A /\ B` em duas hipóteses,
  `Ha : A` e `Hb : B`. A tática `destruct Hab as [Ha Hb]` realiza essa decomposição dando o nome
  `Ha` para o lado esquerdo e `Hb` para o lado direito da conjunção `A /\ B`.
  Com isso, o estado de prova passa a ser:
  
  ```coq
  1 subgoal, subgoal 1 (ID 10)
  
  A, B, C : Prop
  Ha : A
  Hb : B
  ============================
  B /\ A
  ```
  
  Na sequência, utilizamos a tática `split` que divide uma conclusão formada por uma conjunção em 
  duas provas, uma para concluir o lado esquerdo e outra para concluir o lado direito. Ao usarmos 
  a tática `split`, obteremos a seguinte configuração.

  ```coq
  2 subgoals, subgoal 1 (ID 12)
  
  A, B, C : Prop
  Ha : A
  Hb : B
  ============================
  B

  subgoal 2 (ID 13) is:
  A
  ```

  Note que foram produzidos duas provas distintas, uma cuja conclusão é `B` e outra cuja 
  conclusão é `A`. Ambas demonstrações podem ser finalizadas utilizando a tática 
  `assumption`.

  Note que o script de táticas utilizado utiliza _bullets_, uma adição recente a Coq que
  permite "marcar" o início de diferentes conclusões a serem demonstradas. Bullets podem
  ser representados pelos caracteres *, +, - .

  A seguir, apresentamos mais um exemplo que utiliza táticas para conjunção e implicação 
  lógica.

```coq
  Lemma and_assoc : A /\ (B /\ C) -> (A /\ B) /\ C.
  Proof.
    intro Habc.
    destruct Habc as [Ha [Hb Hc]].
    split.
    +
      split.
      *
        assumption.
      *
        assumption.
    +
      assumption.
  Qed.
```
O teorema `and_assoc` mostra que a conjunção é uma operação associativa. 
Ele é provado utilizando táticas já apresentadas anteriormente. A peculiaridade
deste exemplo é o uso de _padrões aninhados_ para decompor a hipótese `Habc: A /\ B /\ C`
em seus três componentes, a saber: `Ha : A`, `Hb : B` e `Hc : C`.

### Exercício 3

  ```coq
  Lemma ex3 : (A /\ B) /\ C -> A /\ (B /\ C).
  Proof.
  Admitted.
  ```

### Exercício 4

  ```coq
  Lemma ex4 : ((A /\ B) -> C) -> (A -> B -> C).
  Proof.
  Admitted.
  ```

### Exercício 5

  ```coq
  Lemma ex5 : (A -> B -> C) -> ((A /\ B) -> C).
  Proof.
  Admitted.
  ```
  
### Exercício 6

```coq
  Lemma ex6 : ((A -> B) /\ (A -> C)) -> A -> (B /\ C).
  Proof.
  Admitted.
```

##  Bi-condicional

Assim como na lógica proposicional, Coq define o conectivo bicondicional
em termos da conjunção e da implicação lógica. A fórmula `A <-> B` é equivalente
a `(A -> B) /\ (B -> A)`, conforme expresso pela seguinte definição
Coq:
```coq
Definition iff (A B : Prop) : Prop := (A -> B) /\ (B -> A).
```
A seguir apresentamos um pequeno exemplo que usa o conectivo bi-condicional e a
tática `unfold` utilizada para substituir o bicondicional por sua definição.

```coq
  Lemma and_comm_iff : (A /\ B) <-> (B /\ A).
  Proof.
    unfold iff.
    split.
    +
      apply and_comm.
    +
      intro Hba.
      destruct Hba as [Hb Ha].
      split.
      *
        assumption.
      *
        assumption.
  Qed.
```
O exemplo anterior usa a tática `unfold iff` que modifica a conclusão de
`A /\ B <-> B /\ A` para `(A /\ B -> B /\ A) /\ (B /\ A -> A /\ B)`
Além do uso da tática `unfold`, o exemplo usa um resultado previamente 
demonstrado, o teorema `and_comm`. Para isso, usamos a tática `apply` que 
permite usar um teorema cujo enunciado coincida com a conclusão da prova atual.


## Negação

 A negação, em Coq, é definida em termos da implicação lógica, isto é, a fórmula `~ A`
é equivalente a `A -> False`, em que `False` é a proposição que não pode ser provada. 
Logo, as mesmas táticas utilizadas para implicação podem ser utilizadas sobre a negação. 

A seguir apresentamos um exemplo que ilustra o uso da negação.

```coq
Lemma modus_tollens : ((A -> B) /\ ~ B) -> ~ A.
Proof.
    intro H.
    destruct H as [Hb Hnb].
    unfold not.
    unfold not in Hnb.
    intro Ha.
    apply Hnb.
    apply Hb.
    assumption.
Qed.
```
Neste exemplo, temos alguns pontos importantes: primeiramente ele utiliza a tática
`unfold` que subtitui um nome por sua definição. Em Coq, a negação é definida da seguinte
maneira:
     
```coq 
Definition not (A : Prop) : Prop := A -> False.
```

Após a execução da tática [destruct H as [Hb Hnb]], o estado da prova é

```coq
1 subgoal, subgoal 1 (ID 16)
  
A, B, C : Prop
Hb : A -> B
Hnb : ~ B
============================
~ A
```

Que possui tanto conclusão e hipótese que utiliza o conectivo de negação. Ao utilizarmos a
tática `unfold not` a fórmula `~ A` é substituída por sua definição, `A -> False`.

```coq
  Lemma contra : A -> ~ A -> B.
  Proof.
    intro Ha.
    intro Hna.
    contradiction.
  Qed.
```	
No exemplo `contra` temos uma técnica de prova comum envolvendo o conectivo de negação:
prova por contradição. Em lógica, sempre que temos um conjunto de hipóteses contraditório
podemos concluir a demonstração apelando ao princípio _ex falsum quod libet_ que permite
concluir qualquer proposição a partir da dedução de `False`.

Em Coq, podemos construir provas por contradição de diversas maneiras. A primeira que 
veremos neste curso é a tática `contradiction` que a partir de fatos contraditórios 
(por exemplo `A` e `~ A`) conclui a prova corrente.

## Disjunção

Nesta seção apresentaremos táticas para construção de provas envolvendo disjunção.
Para a utilização de hipóteses envolvendo a disjunção, utilizamos a tática 
`destruct`, que funciona de maneira similar à regra de eliminação da disjunção da
dedução natural. Para provar uma conclusão que utiliza a disjunção, devemos provar
que seu lado esquerdo (ou direito) é verdadeiro. Para isso, utilizamos as táticas
`left` and `right`, respectivamente. O próximo exemplo ilustra o uso destas táticas.

```coq
  Lemma or_comm : (A \/ B) -> (B \/ A).
  Proof.
    intro Hab.
    destruct Hab as [Ha | Hb].
    +
      right.
      assumption.
    +
      left.
      assumption.
  Qed.
```

Note que a tática `destruct` possui uma sintaxe diferente para dividir hipóteses
envolvendo uma disjunção: cada componente da disjunção deve ser separado usando
o caractere "|".

```coq
  Lemma or_assoc : A \/ (B \/ C) -> (A \/ B) \/ C.
  Proof.
    intro Habc.
    destruct Habc as [Ha | [Hb | Hc]].
    +
      left.
      left.
      assumption.
    +
      left.
      right.
      assumption.
    +
      right.
      assumption.
  Qed.
```

### Exercício 7

```coq
  Lemma ex7 : ((A \/ B) /\ ~ A) -> B.
  Proof.
  Admitted.
  ```
  
### Exercício 8

```coq
  Lemma ex8 : (A \/ (B /\ C)) -> (A \/ B) /\ (A \/ C).
  Proof.
  Admitted.
```
  
## Quantificadores universal e existencial

Para formalizarmos alguns fatos sobre a lógica de predicados devemos, primeiramente,
definir um universo de discurso e predicados sobre seus elementos. A seguir definimos
um tipo `U` para representar um conjunto não vazio (especificamos esse fato supondo 
a existência de um valor `u : U` e dois predicados definidos sobre este universo, `P` 
e `Q`.

```coq
  Hypothesis U : Set.
  Hypothesis u : U.
  Hypothesis P : U -> Prop.
  Hypothesis Q : U -> Prop.
  Hypothesis R : U -> Prop.
```
Note que definimos o tipo `U` pertencendo ao universo `Set`. Visando eliminar paradoxos,
como os presentes na teoria de conjuntos (por o exemplo, o paradoxo de Russell), a teoria
de tipos classifica tipos em termos de universos. Coq possui dois universos básicos:
`Set`, o universo que classifica tipos com os quais podemos realizar computações e 
`Prop`, o universo de proposições lógicas. Ambos `Set` e `Prop` pertencem ao universo
`Type 0`, que por sua vez pertence ao universo `Type 1` formando uma cadeia infinita 
de universos de tipos que evitam inconsistências lógicas.

O quantificador universal é representado em Coq pela palavra reservada
`forall` e o quantificador existencial por `exists`. Para o quantificador `forall` utilizaremos
as táticas `intro` para introdução deste quantificador e `apply` ou `destruct`
para eliminá-lo. O seguinte exemplo ilustra o uso destas táticas.

```coq
  Lemma forall_and : (forall x : U, P x /\ Q x) -> ((forall x : U, P x) /\ (forall x : U, Q x)).
  Proof.
    intro H.
    split.
    +
      intro y.
      destruct (H y).
      assumption.
    +
      intro y.
      destruct (H y).
      assumption.
  Qed.
```
  
Para explicarmos o uso das táticas `intro` e `destruct` neste exemplo,
vamos considerar o estado da prova após a execução da tática `split`.

```coq
2 subgoals, subgoal 1 (ID 4)
  
U : Set
u : U
P, Q : U -> Prop
H : forall x : U, P x /\ Q x
============================
forall x : U, P x

subgoal 2 (ID 5) is:
forall x : U, Q x
```

Ao executarmos `intro x`, obtemos a seguinte configuração para o primeiro componente
desta prova.

```coq
1 focused subgoal
(unfocused: 1), subgoal 1 (ID 6)
  
U : Set
u : U
P, Q : U -> Prop
H : forall x : U, P x /\ Q x
y : U
============================
P y
```

A execução da tática `intro y` incluiu no conjunto de hipóteses um elemento `y : U`
_arbitrário_, exatamente como a regra de introdução do quantificador universal presente
na dedução natural. Para eliminarmos o quantificador universal de uma fórmula devemos
obter um elemento do universo de discurso sobre o qual a fórmula que contém este 
quantificador está definida e substituir a variável quantificado por este elemento.
Este passo de substituição da variável quantificada por um elemento do universo de 
discurso pode ser realizado tanto pela tática `destruct` quanto pela tática `apply`.
No exemplo anterior, a tática `apply` não é adequada devido ao fato da fórmula em 
questão não envolver implicações. Como ela utiliza o conectivo de conjunção o uso
de `destruct` é quase obrigatório. O uso de `destruct` neste
exemplo,  `destruct (H y)` especifica que desejamos usar esta
tática sobre o resultado de substituir todas as  ocorrências
livres da variável `x` em
`forall x : U, P x /\ Q x` por `y` resultando em
`P y /\ Q y`, note que isso é exatamente o mecanismo de substituição que ocorre
durante a aplicação de funções em linguagens de programação funcional! Além deste uso 
de `destruct` e `intro`, o restante desta demonstração é imediato.

O próximo exemplo ilustra o uso da tática `apply` para eliminar o quantificador universal
de uma fórmula.

```coq
  Lemma forall_modus_ponens : ((forall x : U, P x -> Q x) /\
                               (forall y : U, Q y -> R y)) ->
                              (forall z : U, P z -> R z).
  Proof.
    intro Hpqr.
    destruct Hpqr as [Hpq Hqr].
    intro z.
    intro Hpz.
    apply Hqr.
    apply Hpq.
    assumption.
  Qed.
```
Para compreendermos este uso de `apply`, considere a configuração da prova
imediatamente antes do uso de `apply Hqr`. 

```coq
      1 subgoal, subgoal 1 (ID 10)
  
      U : Set
      u : U
      P, Q, R : U -> Prop
      Hpq : forall x : U, P x -> Q x
      Hqr : forall y : U, Q y -> R y
      z : U
      Hpz : P z
      ============================
      R z
```

Ao utilizarmos a tática `apply Hqr` o estado da prova é alterado para:
     
```coq
     U : Set
     u : U
     P, Q, R : U -> Prop
     Hpq : forall x : U, P x -> Q x
     Hqr : forall y : U, Q y -> R y
     z : U
     Hpz : P z
     ============================
     Q z
```

Note que ao aplicarmos a hipótese `Hqr : forall y : U, Q y -> R y` sobre a 
conclusão `R z`, Coq automaticamente instancia a variável `y` para `z : U` e
deixa como próximo objetivo a ser demonstrado `Q z`, o lado esquerdo da 
implicação presente na hipótese `Hqr`. Note que o uso de `apply` realiza
"dois" passos dedutivos: a eliminação do quantificador universal e a eliminação
da implicação.

O quantificador existencial é representado por `exists` e, usamos a tática
`destruct` para eliminar hipóteses envolvendo este quantificador e a tática `exists`
para provar uma conclusão que utiliza este quantificador. O próximo exemplo 
ilustra o uso destas táticas.

```coq
  Lemma ex_or : (exists x : U, P x \/ Q x) -> (exists x : U, P x) \/ (exists y : U, Q y).
  Proof.
    intro Hpq.
    destruct Hpq as [x [Hpx | Hqx]].
    +
      left.
      exists x.
      assumption.
    +
      right.
      exists x.
      assumption.
  Qed.
```

A tática `destruct Hpq as [x [Hpx | Hqx]]` ilustra como podemos combinar padrões
para decompor uma fórmula que usa o quantificador existêncial no valor que a torna
verdadeira, `x`, e nas sub-fórmulas que o compõe. Por sua vez, a tática `exists` permite
especificar a evidência que torna uma fórmula envoveldo este quantificador como verdadeira.

### Exercício 9

```coq
  Lemma ex9 : forall x : U, P x -> exists y : U, P y.
  Proof.
  Admitted.
```
### Exercício 10

```coq
  Lemma ex10 : (forall x : U, P x -> ~ Q x) -> ~ exists y : U, P y /\ Q y.
  Proof.
  Admitted.
```

### Exercício 11

```coq
  Lemma ex11 : (forall x : U, P x -> Q x) -> (forall x : U, ~ Q x) -> (forall x : U, ~ P x).
  Proof.
  Admitted.
  ```
  
### Exercício 12

Considere o seguinte argumento muito usado em livros texto sobre lógica formal:
      
      "Todo homem é mortal. Sócrates é um homem. Logo, Sócrates é mortal".

Modele este argumento e prove sua veracidade (ou refute-o) usando um teorema Coq.

