---
layout: page
title: Formalizando uma linguagem simples
permalink: /formalsemantics/
---

Uma das aplicações que popularizou o uso de assistentes de prova foi a
formalização de resultados sobre semântica formal de linguagens de
programação. Atualmente, a maioria dos trabalhos publicados sobre
semântica formal em conferências como o ACM _Principles on Programming
Languages_ usa algum assistente de prova para formalização de seus
resultados. Nesta seção utilizaremos Coq para formalizar uma pequena
linguagem de expressões.

# Sintaxe da linguagem

Um primeiro passo na formalização de uma linguagem de programação é
a definição de sua sintaxe abstrata. Abaixo apresentamos a sintaxe
considerada:

```
e ::= zero
| succ e
| true
| false
| IsZero e
| Pred e
| If e the e else e
```

A sintaxe da linguagem é formada por valores booleanos, a constante zero
e operações de sucessor, predecessor, condicionais e uma operação para
testar se um valor numérico é ou não igual a zero. Representaremos
essa sintaxe utilizando o seguinte tipo.

```coq
Inductive exp : Set :=
| Zero   : exp
| Succ   : exp -> exp
| T      : exp
| F      : exp
| Pred   : exp -> exp
| If     : exp -> exp -> exp -> exp
| IsZero : exp -> exp.
```

### Exercício 50

Modifique a sintaxe da linguagem apresentada de maneira a incluir as seguintes
operações: soma de números naturais e conjunção de valores booleanos.

# Semântica da linguagem

Para definirmos a semântica de uma linguagem de programação existem
diferentes abordagens: a operacional, a denotacional e a axiomática.
Neste curso vamos nos ater a semântica operacional por esta permitir
uma caracterização simples da execução de uma linguagem.

## Valores e formas normais

Antes de definirmos a semântica da linguagem devemos formalizar
quando a execução de uma expressão é encerrada. Definimos como
_valor_ uma expressão de acordo com a seguinte gramática:

```
bv ::= true | false

nv ::= zero | succ nv

value ::= nv | bv
```

Isto é, um valor ou é um booleano ou a constante zero aplicada a um
número arbitrário de operações de sucessor. Definimos o conceito de
valor utilizando os seguintes tipos indutivos e adicionamos os seus
construtores ao hint database para uso pela tática `auto`.

```coq
Inductive bvalue : exp -> Prop :=
| btrue  : bvalue T
| bfalse : bvalue F.

Inductive nvalue : exp -> Prop :=
| nzero  : nvalue Zero
| nsucc  : forall n, nvalue n -> nvalue (Succ n).

Inductive value : exp -> Prop :=
| Bvalue : forall e, bvalue e -> value e
| Nvalue : forall e, nvalue e -> value e.

Hint Constructors bvalue nvalue value.
```

## Semântica de passo-pequeno

A semântica de passo-pequeno da linguagem em questão é definida
por uma entre pares de expressões que representaremos usando a
seguinte notação: `e ==> e'` que denota que a expressão `e` avalia
em um passo para a expressão `e'`. A seguir representamos as regras da
semântica de expressões.

```

--------------------(ST_If_True)
If true e e' ==> e

--------------------(ST_If_True)
If false e e' ==> e'

e ==> e'
--------------------(ST_If_True)
If e e1 e2 ==> if e' e1 e2 

--------------------(ST_Pred_Zero)
Pred zero ==> zero

nvalue e
--------------------(ST_Pred_Succ)
Pred (succ e) ==> e

e ==> e'
--------------------(ST_Pred)
Pred e ==> Pred e' 


--------------------(ST_IsZero_Zero)
IsZero zero ==> true

nvalue e
--------------------(ST_IsZero_Succ)
IsZero (succ e) ==> false

e ==> e'
--------------------(ST_IsZero)
IsZero e ==> IsZero e' 
```

A seguir apresentamos o tipo de dados `step` em que cada construtor
representa uma das regras da semântica apresentada.

```
Reserved Notation "e '==>' e1" (at level 40).

Inductive step : exp -> exp -> Prop :=
| ST_If_T
  : forall e e', (If T e e') ==> e
| ST_If_F
  : forall e e', If F e e' ==> e'
| ST_If
  : forall e e' e1 e2,
    e ==> e'                ->
    If e e1 e2 ==> If e' e1 e2
| ST_Succ
  : forall e e',
    e ==> e'                ->
    (Succ e) ==> (Succ e')
| ST_Pred_Zero
  : Pred Zero ==> Zero
| ST_Pred_Succ
  : forall e,
    nvalue e         ->
    Pred (Succ e) ==> e
| ST_Pred
  : forall e e',
    e ==> e'           ->
    (Pred e) ==> (Pred e')
| ST_IsZeroZero
  : IsZero Zero ==> T
| ST_IsZeroSucc
  : forall e,
    nvalue e           ->
    IsZero (Succ e) ==> F
| ST_IsZero
  : forall e e',
    e ==> e'               -> 
    (IsZero e) ==> (IsZero e')
	where "e '==>' e1" := (step e e1).

Hint Constructors step.

```	

Usando a semântica, podemos definir o conceito de _forma normal_, que
consiste de uma expressão que não pode mais ser reduzida de acordo com
a semântica da linguagem em questão.

```coq
Definition normal_form e := ~ exists e', step e e'.
```

Note que nem toda forma normal é um valor, por exemplo `if zero then
zero else true` não pode ser reduzida e não é um valor, de acordo com
a definição dada anteriormente. Dizemos que uma expressão é `presa`
(`stuck`) se ela é uma forma normal mas não um valor.

```coq
Definition stuck e := normal_form e /\ ~ value e.
```

### Exercício 51

Modifique a definição da semântica para que suporte as
operações de soma e conjunção definidas por você na sintaxe.

Abaixo apresentamos a demonstração de uma primeira propriedade: todo
valor é uma forma normal.

```coq
Ltac inverts H := inversion H ; clear H ; subst.

Lemma value_is_nf' : forall e, value e -> normal_form e.
Proof.
  intros e Hv.
  unfold normal_form.
  intro contra.
  induction e.
  +
    inverts contra.
    inverts H.
  +
    inverts contra.
    inverts Hv.
    inverts H0.
    inverts H0.
    apply IHe.
    auto.
    inverts H.
    exists e'.
    auto.
  +
    inverts contra.
    inverts H.
  +
    inverts contra.
    inverts H.
  +
    inverts Hv.
    inverts H.
    inverts H.
  +
    inverts Hv.
    inverts H.
    inverts H.
  +
    inverts Hv.
    inverts H.
    inverts H.
Qed.
	
```

É fácil notar que a demonstração anterior possui muita repetição. Ao
processar o script tática a tática, você deve ter percebido a
existência de diversos casos contraditórios, como o estado de prova
seguinte:

```coq

  Hv : value Zero
  contra : exists e' : exp, Zero ==> e'
  ============================
  False
  
```

Note que, de acordo com a semântica, não existe `e'` tal que `Zero ==>
e'`, logo essa hipótese é contraditória e pode ser provada por
inversão. Na verdade, a maior parte dos casos presentes nesta
demonstração consiste de contradições óbvias e que podem ser
automatizadas facilmente. A tática seguinte realiza casamento de
padrão sobre o estado da prova atual de maneira a identificar esses
casos contraditórios e resolvê-los.

```coq
Ltac s :=
      match goal with
      | [ H : ex _ |- _ ] => destruct H
      | [ H : Zero ==> _ |- _] => inverts H
      | [ H : T ==> _ |- _] => inverts H
      | [ H : F ==> _ |- _] => inverts H
      | [ H : value (Pred _) |- _] => inverts H
      | [ H : bvalue (Pred _) |- _] => inverts H
      | [ H : nvalue (Pred _) |- _] => inverts H
      | [ H : value (If _ _ _) |- _] => inverts H
      | [ H : bvalue (If _ _ _) |- _] => inverts H
      | [ H : nvalue (If _ _ _) |- _] => inverts H
      | [ H : value (IsZero _) |- _] => inverts H
      | [ H : bvalue (IsZero _) |- _] => inverts H
      | [ H : nvalue (IsZero _) |- _] => inverts H
      | [ H : value (Succ _) |- _] => inverts H
      | [ H : bvalue (Succ _) |- _] => inverts H
      | [ H : nvalue (Succ _) |- _] => inverts H
      | [ H : (Succ _) ==> _ |- _ ] => inverts H
      end.
```

Usando a tática acima, a demonstração anterior pode ser reescrita como:

```coq
Lemma value_is_nf : forall e, value e -> normal_form e.
Proof.
  unfold normal_form ; intros e H contra ; induction e ;
    try (repeat s) ; eauto.
Qed.

Hint Resolve value_is_nf.
```

### Exercício 52

Modifique a tática `s` e a prova `value_is_nf` de maneira dar suporte
as modificações realizadas por você nos exercícios 50 e 51.

Uma importante propriedade da semântica é que esta é
deterministica. Esse teorema é enunciado abaixo.

```coq

Ltac s1 :=
  match goal with
  | [ H : (nvalue ?e) , H1 : ?e ==> _ |- _] =>
    apply Nvalue in H ; apply value_is_nf in H ;
    unfold normal_form in H ; apply ex_intro in H1 ; contradiction
  end.

Lemma step_deterministic
  : forall e e', e ==> e' -> forall e1, e ==> e1-> e' = e1.
Proof.
  intros e e' H ; induction H ; intros e'' H' ;
    inverts H' ; f_equal ; try repeat s ; auto ; try repeat s1.
Qed.

```

## Semântica de passo-grande


Abaixo apresentamos a definição de um predicado indutivo para a
semântica de passo-grande.


```
Reserved Notation "e '==>>' e1" (at level 40).

Inductive big_step : exp -> exp -> Prop :=
| B_Value
  : forall v, value v -> v ==>> v
| B_If_True
  : forall e e1 e11 e2,
    e ==>> T ->
    e1 ==>> e11 ->
    (If e e1 e2) ==>> e11
| B_If_False
  : forall e e1 e2 e22,
    e ==>> F ->
    e2 ==>> e22 ->
    (If e e1 e2) ==>> e22
| B_Succ
  : forall e nv,
    nvalue nv ->
    e ==>> nv ->
    (Succ e) ==>> (Succ nv)
| B_PredZero
  : forall e,
    e ==>> Zero ->
    (Pred e) ==>> Zero
| B_PredSucc
  : forall e nv,
    nvalue nv ->
    e ==>> (Succ nv) ->
    Pred e ==>> nv
| B_IsZeroZero
  : forall e,
    e ==>> Zero ->
    (IsZero e) ==>> T
| B_IsZeroSucc
  : forall e nv,
    nvalue nv ->
    e ==>> nv ->
    (IsZero e) ==>> F
where "e '==>>' e1" := (big_step e e1).
	
```

A seguir, demonstramos que a semântica de passo-grande é
determinística.

```coq
Ltac bs :=
	match goal with
	| [H : T ==>> _ |- _] => inverts H
    | [H : F ==>> _ |- _] => inverts H 
	| [H : Zero ==>> _ |- _] => inverts H
	| [H : (Succ _) ==>> _ |- _] => inverts H
	| [H : value _ |- _] => inverts H
	| [H : bvalue (Succ _) |- _] => inverts H
	| [H : nvalue (Succ _) |- _] => inverts H
	| [H : (Pred _) ==>> _ |- _] => inverts H
	| [H : bvalue (Pred _) |- _] => inverts H
	| [H : nvalue (Pred _) |- _] => inverts H
	| [H : (If _ _ _) ==>> _ |- _] => inverts H
	| [H : bvalue (If _ _ _) |- _] => inverts H
	| [H : nvalue (If _ _ _) |- _] => inverts H
	| [H : (IsZero _) ==>> _ |- _] => inverts H
	| [H : bvalue (IsZero _) |- _] => inverts H
	| [H : nvalue (IsZero _) |- _] => inverts H
	| [ IH : forall v, ?e ==>> v -> forall v', ?e ==>> v' ->
		, H : ?e ==>> _, H1 : ?e ==>> _ |- _] =>
		apply (IH _ H) in H1
	end ; subst ; try f_equal ; auto.


Lemma big_step_deterministic : forall e v, e ==>> v -> forall v', e ==>> v' -> v = v'.
Proof.
  induction e ; intros ; repeat bs.
Qed.
```

Os próximos exercícios sugerem a demonstração da equivalência entre ambas
as definições semânticas e ele utiliza o fecho reflexivo e transitivo
da semântica de passo pequeno, definido a seguir.

```
Reserved Notation "e '==>*' e1" (at level 40).

Inductive multi_step : exp -> exp -> Prop :=
| mstep_refl
  : forall e, e ==>* e
| mstep_step
  : forall e e1 e',
    e ==> e1   ->
    e1 ==>* e' ->
    e ==>* e'
where "e '==>*' e1" := (multi_step e e1).

Hint Constructors multi_step.
```

### Exercício 53

```coq
Lemma multi_step_big_step  : forall e v, value v -> e ==>* v -> e ==>> v.
Proof.
Admitted.
```

### Exercício 54

```coq
Lemma big_step_mult_step  : forall e v, value v -> e ==>> v -> e ==>* v.
Proof.
Admitted.
```

# Sistema de tipos

Nosso próximo objetivo é a formalização de um sistema de tipos para
nossa linguagem de expressões aritméticas. A principal função de um
sistema de tipos em uma linguagem de programação é evitar a execução
de programas cujo comportamento seja indefinido. Primeiramente,
definimos os tipos da linguagem de expressões.

```coq
Inductive type : Set :=
| TBool : type
| TNat  : type.
```

O sistema de tipos para a linguagem de expressões é definido como
uma relação entre expressões e tipos conforme especificado pelo
seguinte predicado indutivo.

```
Reserved Notation "e '<<-' t" (at level 40).

Inductive has_type : exp -> type -> Prop :=
| T_True
  : T <<- TBool
| T_False
  : F <<- TBool
| T_Zero
  : Zero <<- TNat
| T_Succ
  : forall e,
    e <<- TNat ->
    (Succ e) <<- TNat
| T_Pred
  : forall e,
    e <<- TNat  ->
    (Pred e) <<- TNat
| T_If
  : forall e e' e'' t,
    e <<- TBool ->
    e' <<- t    ->
    e'' <<- t   ->
    (If e e' e'') <<- t
| T_IsZero
  : forall e,
    e <<- TNat ->
    (IsZero e) <<- TBool
where "e '<<-' t" := (has_type e t).
```

### Exercício 55

```coq
Lemma bool_canonical : forall e, e <<- TBool -> value e -> bvalue e.
Proof.
Admitted.
```

### Exercício 56

```coq
Lemma nat_canonical : forall e, e <<- TNat -> value e -> nvalue e. 
Proof.
Admitted.
```

A seguir apresentamos a demonstração da propriedade de progresso, que
especifica que toda expressão bem tipada é um valor ou ainda pode
executar mais um passo.


```coq
Theorem progress : forall e t, e <<- t -> value e \/ exists e', e ==> e'.
Proof.
  induction 1 ; try solve [left ; auto] ;
    try repeat (match goal with
                | [H : _ \/ _ |- _] => destruct H
                | [H : ex _ |- _] => destruct H
                | [H : value _ |- _] => inverts H
                | [H : bvalue _ |- _] => inverts H
                | [H : T <<- _ |- _] => inverts H
                | [H : F <<- _ |- _] => inverts H
                | [H : nvalue _ |- context[(Pred _)]] => inverts H
                | [H : nvalue _ |- context[(IsZero _)]] => inverts H
                | [H : ?e <<- TBool , H1 : nvalue ?e |- _] =>
                  inverts H1 ; inverts H
                end ; try solve [ right ; eexists ; eauto ] ; auto).
Qed.
```
A prova da propriedade de progesso é realizada por indução sobre a
derivação de tipo da expressão, conforme apresentado no script
anterior.

A propriedade de preservação garante que uma expressão bem tipada ao
executar um passo produz outra expressão bem tipada. A demontração de
preservação é realizada por indução sobre a derivação de tipos,
conforme abaixo.

```coq
Theorem preservation : forall e t, e <<- t -> forall e', e ==> e' -> e' <<- t.
Proof.
  induction 1 ; intros ; repeat (s ; eauto) ;
    try repeat (match goal with
                | [H : _ ==> _ |- _] => inverts H ; eauto
                | [H : (Succ _) <<- _ |- _] => inverts H ; eauto
                end).
Qed.
```

Outra propriedade importante deste sistema de tipos é a unicidade de
tipos (ou determinismo), isto é, uma expressão bem tipada possui
somente um tipo válido.

```coq
Theorem has_type_det : forall e t, e <<- t -> forall t', e <<- t' -> t = t'.
Proof.
  induction 1 ; intros t' Hc ; inverts Hc ; eauto.
Qed.
```

## Definindo um typechecker

Nosso último exemplo consiste em implementar um typechecker para a
linguagem de expressões usando um tipo que garanta sua correção com
respeito ao sistema de tipos da linguagem.

Para definição do typechecker vamos precisar de uma função para testar
a igualdade de tipos, definida abaixo usando a tática `decide
equality` e algumas notações.

```
Definition eq_ty_dec : forall (t t' : type), {t = t'} + {t <> t'}.
  decide equality.
Defined.

Notation "!!" := (inright _ _).
Notation "[|| x ||]" := (inleft _ [x]).

Notation "x <-- e1 ; e2" := (match e1 with
                               | inright _ => !!
                               | inleft (exist _ x _) => e2
                             end)
                             (right associativity, at level 60).

Notation "e1 ;;; e2" := (if e1 then e2 else !!)
                          (right associativity, at level 60).
```

O type checker é apresentado abaixo e utiliza automação de prova para
descartar obrigações produzidas pelo uso da tática `refine` em sua
definição. 

```coq
Definition typecheck : forall e, {t | e <<- t} + {forall t, ~ (e <<- t)}.
  refine (fix tc (e : exp) : {t | e <<- t} + {forall t, ~ (e <<- t)} :=
            match e as e' return e = e' -> {t | e' <<- t} + {forall t, ~ (e' <<- t)} with
            | T  => fun _ => [|| TBool ||]
            | F  => fun _ => [|| TBool ||]
            | Zero  => fun _ => [|| TNat ||]
            | Succ e => fun _ =>
                          ty <-- tc e ;
                          eq_ty_dec ty TNat ;;;
                          [|| TNat ||]          
            | Pred e => fun _ => 
                          ty <-- tc e ;
                          eq_ty_dec ty TNat ;;;
                          [|| TNat ||]          
            | IsZero e => fun _ => 
                          ty <-- tc e ;
                          eq_ty_dec ty TNat ;;;
                          [|| TBool ||]          
            | If e e1 e2 => fun _ =>
                          ty <-- tc e ;
                          ty1 <-- tc e1 ;
                          ty2 <-- tc e2 ;
                          eq_ty_dec ty TBool ;;;
                          eq_ty_dec ty1 ty2  ;;;
                          [|| ty1 ||]
            end eq_refl) ; clear tc ;
           simpl in * ; subst ;
             try (intro ; intro) ;
             try (match goal with
                  | [ H : _ <<- _ |- _] => inverts H
                  end) ;
                 try (match goal with
                      | [ H : forall x, ~ (_ <<- _) |- False ] => eapply H ; eauto
                    | [H : ?e <<- ?t , H1 : ?e <<- ?t' |- _] =>
                      eapply (has_type_det H) in H1 ; subst
                      end) ; eauto.
Defined.
```
Note que o tipo do type checker é
`forall e, {t | e <<- t} + {forall t, ~ (e <<- t)}`,  que a partir de
                          uma expressão `e`, retorna como resultado um
                          tipo `t` e uma prova de que este é o tipo da
                          expressão `e` ou returna a prova de que
                          nenhum tipo pode ser atribuído a expressão `e`.
