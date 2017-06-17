Require Import Omega.

(* combinadores de táticas *)

Theorem seq_comb
  : forall (A B : Prop), (((A -> B) -> B) -> B) -> A -> B.
Proof.
  intros A B HImp Ha ; apply HImp ; intros Hab ; apply Hab ; assumption.
Qed.

Theorem chain
  : forall (A B C : Prop), (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
  intros A B C Habc Hab Ha ; apply Habc ; [ assumption | apply Hab ; assumption ].
Qed.

Theorem orElse_example
  : forall (A B C D : Prop), (A -> B) -> C -> ((A -> B) -> C -> (D -> B) -> D) -> A -> D.
Proof.
  intros A B C D Hab Hc H Ha ;
    apply H ; (assumption || intro H1) ;
      apply Hab ; assumption.
Qed.


Lemma try_test
  : forall (A B C D : Prop), (A -> B -> C -> D) -> (A -> B) -> (A -> C -> D).
Proof.
  intros A B C D H H1 HA HC.
  apply H  ; try (assumption || (apply H1 ; assumption)).
Qed.

Inductive even : nat -> Prop :=
| ev_zero : even 0
| ev_ss   : forall n, even n -> even (S (S n)).


Lemma even_100 : even 100.
Proof.
  repeat ((apply ev_ss) || (apply ev_zero)).
Qed.

(** táticas adicionais *)

Lemma one_not_zero : 0 <> 1.
Proof.
  intro ; congruence.
Qed.

Theorem orElse_example1
  : forall (A B C D : Prop), (A -> B) -> C -> ((A -> B) -> C -> (D -> B) -> D) -> A -> D.
Proof.
  intuition.
Qed.

Lemma le_S_cong_omega : forall n m, S n <= S m -> n <= m.
Proof.
  intros n m ; omega.
Qed.

(** tática auto *)

Theorem auto_example1
  : forall (A B C D : Prop), (A -> B) -> C -> ((A -> B) -> C -> (D -> B) -> D) -> A -> D.
Proof.
  auto.
Qed.

Inductive Plus : nat -> nat -> nat -> Prop :=
| PlusZero
  : forall m, Plus 0 m m
| PlusSucc
  : forall n m r,
    Plus n m r ->
    Plus (S n) m (S r).

Example plus_4_3 : Plus 4 3 7.
Proof.
  repeat constructor.
Qed.

Hint Constructors Plus.

Example plus_4_3_auto : Plus 4 3 7.
Proof.
  auto.
Qed.

Lemma plus_complete : forall n m r, Plus n m r -> n + m = r.
Proof.
  induction n ; intros m r H ; inversion H ;
    subst ; clear H ; simpl ; f_equal ; auto. 
Qed.

(** programando táticas com Ltac *)

Ltac break_if :=
  match goal with
  | [ |- if ?X then _ else _ ] => destruct X
  end.

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

Ltac break_if_inside :=
  match goal with
  | [ |- context[if ?X then _ else _] ] => destruct X
  end.

Theorem hmm2 : forall (a b : bool),
    (if a then 42 else 42) = (if b then 42 else 42).
Proof.
  intros; repeat break_if_inside; reflexivity.
Qed.

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
