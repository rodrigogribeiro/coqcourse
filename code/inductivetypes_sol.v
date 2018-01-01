(** definindo tipos indutivos *)

Inductive True1 : Prop :=
| tt1 : True1.

Inductive False1 : Prop := .

Inductive conj1 (A
                   B : Prop) : Prop :=
| and1 : A -> B -> conj1 A B.

(** exercício 13 
    Defina o conectivo de disjunção *)

Inductive disj1 : Prop :=.

(** booleanos *)

Inductive bool1 : Set :=
| true1 : bool1
| false1 : bool1.

Require Import Bool.

Definition not_bool (b : bool) : bool :=
  match b with
  | false => true
  | true  => false
  end.

Definition and_bool (b1 b2 : bool) : bool :=
  match b1 , b2 with
  | true  , b2 => b2
  | false , b2 => false
  end.

(** exercício 14: Defina funções para os conectivos de disjunção, "ou", e 
    exclusive-or, "xor" *)

Eval compute in not_bool false.

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

(** exercício 15 *)

Lemma and_true_left : forall b, and_bool true b = b.
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

(** exercício 16 *)

Lemma and_false_left : forall b, and_bool false b = false.
Proof.
  intro b.
  simpl.
  reflexivity.
Qed.

(** exercício 17 *)

Lemma and_com : forall b b', and_bool b b' = and_bool b' b.
Proof.
  intro b.
  intro b'.
  destruct b.
  +
    destruct b'.
    -
       simpl.
       reflexivity.
    -
      simpl.
      reflexivity.
  +
    destruct b'.
    -
       simpl.
       reflexivity.
    -
      simpl.
      reflexivity.
Qed.

(** exercício 18 *)

Lemma and_assocc : forall b1 b2 b3, and_bool b1 (and_bool b2 b3) = and_bool (and_bool b1 b2) b3.
Proof.
  intro b1.
  intro b2.
  intro b3.
  destruct b1.
  +
    destruct b2.
    -
      destruct b3.
      *
        simpl.
        reflexivity.
      *
        simpl.
        reflexivity.
    -
      destruct b3.
      *
        simpl.
        reflexivity.
      *
        simpl.
        reflexivity.
   +
        destruct b2.
    -
      destruct b3.
      *
        simpl.
        reflexivity.
      *
        simpl.
        reflexivity.
    -
      destruct b3.
      *
        simpl.
        reflexivity.
      *
        simpl.
        reflexivity.
Qed.

(** Números naturais *)

Lemma zero_identity_add_left : forall n, 0 + n = n.
Proof.
    intro n.
    simpl.
    reflexivity.
Qed.

Lemma zero_identity_add_right : forall n, n + 0 = n.
Proof.
   intro n.
   simpl.
   Restart.
   intro n.
   destruct n.
   +
     simpl.
     reflexivity.
   +
     simpl.
     (** reflexivity. *)
     Restart.
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

(** exercício 19 *)

Lemma add_associative : forall n m p, n + (m + p) = (n + m) + p.
Proof.
  intro n.
  induction n.
  +
    intros m p.
    simpl.
    reflexivity.
  +
    intros m p.
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

(**
Exercício 20

A seguir apresentamos uma definição da operação de multiplicação sobre números 
naturais. 


A partir desta definição, enuncie e prove os seguintes fatos sobre a multiplicação:
        
- O número 1 é identidade à esquerda da multiplicação.
- O número 1 é identidade à direita da multiplicação.
- A operação de multiplicação é associativa.
- A operação de multiplicação é comutativa.
 **)

Fixpoint times (n m : nat) : nat :=
  match n with
  | 0    => 0
  | S n' => m + (times n' m)
  end.

Lemma mult_one_id_left : forall n, 1 * n = n.
Proof.
  intro n.
  simpl.
  rewrite zero_identity_add_right.
  reflexivity.
Qed.

Lemma mult_one_id_right : forall n, n * 1 = n.
Proof.
  intro n.
  induction n.
  +
    simpl.
    reflexivity.
  +
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma zero_null_right : forall n, 0 = n * 0.
Proof.
  intro n.
  induction n.
  +
    simpl.
    reflexivity.
  +
    simpl.
    rewrite <- IHn.
    reflexivity.
Qed.    

Lemma inc_mult : forall m n, m + m * n = m * S n.
Proof.
  intros m n.
  induction m.
  +
    simpl.
    reflexivity.
  +
    simpl.
    rewrite <- IHm.
    rewrite add_associative.
    rewrite add_associative.
    assert (H : m + n = n + m).
    -
      apply add_commut.
    -
      rewrite H.
      reflexivity.
Qed.    

Lemma mult_comm : forall n m, n * m = m * n.
Proof.
  intros n m.
  induction n.
  +
    simpl.
    apply zero_null_right.
  +
    simpl.
    rewrite <- inc_mult.
    rewrite IHn.
    reflexivity.
Qed.
    
(**
Exercício 21

Defina a função `even_bool : nat -> bool` que, a partir de um número natural, retorne
verdadeiro se este é par.
 **)

Fixpoint even_bool (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n) => even_bool n
  end.

(** 
Exercício 22 
 **)

Lemma even_add_n : forall n, even_bool (n + n) = true.
Proof.
  intro n.
  induction n.
  +
    simpl.
    reflexivity.
  +
    simpl.
    rewrite <- add_inc.
    assumption.
Qed.

(** 
Exercício 23
Defina a função `odd_bool : nat -> bool` que, a partir de um número natural, 
retorne verdadeiro se este é ímpar
 **)

Fixpoint odd_bool (n : nat) : bool :=
  match n with
  | O => false
  | S O => true
  | S (S n) => odd_bool n           
  end.


(** Exercício 24 *)

Lemma odd_add_n_Sn : forall n, odd_bool (n + S n) = true.
Proof.
  intro n.
  rewrite <- add_inc.
  simpl.
  induction n.
  +
    simpl.
    reflexivity.
  +
    rewrite <- add_inc.
    simpl.
    assumption.
Qed.

(** Exercício 25 *)

Lemma even_SS : forall n, even_bool n = even_bool (S (S n)).
Proof.
  intro n.
  induction n.
  +
    simpl.
    reflexivity.
  +
    simpl.
    destruct n.
    - reflexivity.
    - reflexivity.
Qed.


(** Exercício 26 *)

Lemma odd_SS : forall n, odd_bool n = odd_bool (S (S n)).
Proof.
  intro n.
  induction n.
  +
    simpl.
    reflexivity.
  +
    simpl.
    destruct n.
    - reflexivity.
    - reflexivity.
Qed.

(** Exercício 27 *)

Lemma even_bool_S : forall n, even_bool n = not_bool (even_bool (S n)).
Proof.
  intro n.
  induction n.
  +
    simpl.
    reflexivity.
  +
    destruct n.
    -
      simpl.
      reflexivity.
    -
      simpl in *.
      rewrite IHn.
      rewrite not_bool_inv.
      reflexivity.
Qed.

(** Listas *)

Require Import List.

Notation "x :: l" := (cons x l)
                       (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition list1 : list nat := 1 :: 2 :: 3 :: nil.
Definition list2 : list nat := [1 ; 2 ; 3].

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

Fixpoint map {A B : Type}(f : A -> B)(xs : list A) : list B :=
  match xs with
  | []      => []
  | y :: ys =>  f y :: map f ys
  end.

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

Fixpoint reverse {A : Type}(xs : list A) : list A :=
  match xs with
  | [] => []
  | y :: ys => reverse ys ++ [ y ]
  end.

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

(** exercício 28 *)

Lemma repeat_length {A : Type} : forall (n : nat)(x : A), length (repeat n x) = n.
Proof.
  intros n x.
  induction n.
  +
    simpl.
    reflexivity.
  +
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

(** exercício 29 *)

Lemma app_nil_right {A : Type} : forall (xs : list A), xs ++ [] = xs.
Proof.
  induction xs.
  +
    simpl.
    reflexivity.
  +
    simpl.
    rewrite IHxs.
    reflexivity.
Qed.

(** exercício 30 *)

Lemma app_assoc {A : Type} : forall (xs ys zs : list A), xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
Proof.
  intros xs.
  induction xs.
  +
    intros ys zs.
    simpl.
    reflexivity.
  +
    intros ys zs.
    simpl.
    rewrite IHxs.
    reflexivity.
Qed.

(** exercício 31 *)

Lemma map_app {A B : Type}{f : A -> B}
  : forall xs ys, map f (xs ++ ys) = map f xs ++ map f ys.
Proof.
  intros xs ys.
  induction xs.
  +
    simpl.
    reflexivity.
  +
    simpl.
    rewrite IHxs.
    reflexivity.
Qed.

(** exercício 32 *)

Lemma reverse_app {A : Type}
  : forall (xs ys : list A), reverse (xs ++ ys) = reverse ys ++ reverse xs.
Proof.
  intros xs ys.
  induction xs.
  +
    simpl.
    rewrite app_nil_right.
    reflexivity.
  +
    simpl.
    rewrite IHxs.
    rewrite app_assoc.
    reflexivity.
Qed.

(** exercício 33 *)

Lemma reverse_inv {A : Type}
  : forall (xs : list A), reverse (reverse xs) = xs.
Proof.
  intros xs.
  induction xs.
  +
    simpl.
    reflexivity.
  +
    simpl.
    rewrite reverse_app.
    simpl.
    rewrite IHxs.
    reflexivity.
Qed.

(** Predicados indutivos *)


Inductive even : nat -> Prop :=
| ev_zero : even 0
| ev_ss   : forall n, even n -> even (S (S n)).

Example eight_is_even : even 8.
Proof.
  apply ev_ss.
  apply ev_ss.
  apply ev_ss.
  apply ev_ss.
  apply ev_zero.
Qed.

Example teste : even 1 -> 1 = 2.
Proof.
  intro H.
  inversion H.
Qed.
Definition double (n : nat) := 2 * n.

(** exercício 34 *)

Lemma double_plus : forall n, 2 * n = n + n.
Proof.
  intros n.
  induction n.
  +
    simpl.
    reflexivity.
  +
    simpl.
    rewrite zero_identity_add_right.
    reflexivity.
Qed.    

Lemma double_even : forall n, even (double n).
Proof.
  intro n.
  unfold double.
  induction n.
  +
    simpl.
    apply ev_zero.
  +
    simpl.
    rewrite zero_identity_add_right.
    rewrite <- add_inc.
    apply ev_ss.
    rewrite <- double_plus.
    assumption.
Qed.

(** Princípio de inversão *)

Lemma one_not_even : ~ even 1.
Proof.
  intros Hone.
  inversion Hone.
Qed.

Lemma even_2_inv : forall n, even (2 + n) -> even n.
Proof.
  intros n H.
  inversion H.
  assumption.
Qed.

(**
   Inductive le (n : nat) : nat -> Prop :=
   | le_n : n <= n 
   | le_S : forall m : nat, n <= m -> n <= S m
 *)

Example teste_le : 3 <= 6.
Proof.
  apply le_S.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

Example teste_le_false : 2 <= 1 -> 1 + 1 = 10.
Proof.
  intros H.
  inversion H.
  inversion H1.
Qed.

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

(** exercício 35 *)

Lemma le_refl : forall n, n <= n.
Proof.
  apply le_n.
Qed.

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

Ltac inverts H := inversion H ; subst ; clear H.

(** exercício 36 *)

Lemma le_zero : forall n, 0 <= n.
Proof.
  intros n.
  induction n.
  +
    apply le_n.
  +
    apply le_S.
    assumption.
Qed.

Lemma le_trans : forall n m p, n <= m -> m <= p -> n <= p.
Proof.
  intros n m p Hnm Hmp.
  induction Hmp.
  + assumption.
  +
    apply le_S.
    assumption.
Qed.

(** exercício 37 *)

Lemma le_antisym : forall n m, n <= m -> m <= n -> n = m.
Proof.
  induction n.
  intros.
  -
    inverts H0.
    reflexivity.
  -
    intros.
    destruct m.
    inverts H.
    f_equal.
    apply IHn.
    apply le_S_cong.
    assumption.
    apply le_S_cong.
    assumption.
Qed.

(** exercício 38 

Considere a tarefa de projetar um predicado indutivo
`Sorted : list nat -> Prop` que constitui uma prova
de que uma certa lista de números naturais está ordenada. 
Sua definição deve utilizar o predicado `<=` e conseguir
demonstrar os casos de teste abaixo.

*)

Inductive Sorted : list nat -> Prop :=
| Sorted_nil : Sorted []
| Sorted_sing : forall x, Sorted [ x ]
| Sorted_rec : forall x y xs, Sorted (y :: xs) -> x <= y -> Sorted (x :: y :: xs).

Example test_sorted1 : Sorted [].
Proof.
  apply Sorted_nil.
Qed.

Example test_sorted2 : Sorted [10].
Proof.
  apply Sorted_sing.
Qed.

Example test_sorted3 : Sorted [1 ; 3 ; 5 ].
Proof.
  apply Sorted_rec.
  apply Sorted_rec.
  apply Sorted_sing.
  repeat constructor.
  repeat constructor.
Qed.

Reserved Notation "x '<<=' y" (at level 40, no associativity).

Inductive le_alt : nat -> nat -> Prop :=
| le_alt_zero : forall n, 0 <<= n
| le_alt_succ : forall n m, n <<= m -> S n <<= S m
where "x '<<=' y" := (le_alt x y).

(** exercício 39 *)

Lemma le_alt_refl : forall n, n <<= n.
Proof.
  intros n.
  induction n.
  +
    constructor.
  +
    constructor.
    assumption.
Qed.

(** exercício 40 *)

Lemma le_alt_trans
  : forall n m p, n <<= m -> m <<= p -> n <<= p.
Proof.
  induction n.
  +
    intros  m p Hnm Hmp.
    constructor.
  +
    intros m p Hnm Hmp.
    inverts Hnm.
    inverts Hmp.
    constructor.
    apply IHn with (m := m0).
    - assumption.
    - assumption.
Qed.      

(** exercício 41 *)

Lemma le_alt_antisym : forall n m, n <<= m -> m <<= n -> n = m.
Proof.
  intros n.
  induction n.
  +
    intros m Hnm Hmn.
    inverts Hmn.
    reflexivity.
  +
    intros m Hnm Hmn.
    inverts Hmn.
    - inverts Hnm.
    -
      inverts Hnm.
      rewrite (IHn _ H2 H1).
      reflexivity.
Qed.

(** exercício 42 *)

Lemma le_alt_s : forall n m, n <<= m -> n <<= S m.
Proof.
  intro n.
  induction n.
  +
    intros m Hnm.
    apply le_alt_zero.
  +
    intros m Hnm.
    inverts Hnm.
    apply le_alt_succ.
    apply IHn.
    assumption.
Qed.

Lemma le_alt_equiv_le : forall n m, n <<= m <-> n <= m.
Proof.
  intros n m.
  split.
  +
    intros H.
    induction H.
    -
      apply le_zero.
    -
      apply le_cong_S.
      assumption.
  +
    intros H.
    induction H.
    -
      apply le_alt_refl.
    -
      apply le_alt_s.
      assumption.
Qed.
