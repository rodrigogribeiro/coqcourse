(** definindo tipos indutivos *)

Inductive True1 : Prop :=
| tt1 : True1.

Inductive False1 : Prop := .

Inductive conj1 (A B : Prop) : Prop :=
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
  | false , b2 => b2
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
Admitted.

(** exercício 16 *)

Lemma and_false_left : forall b, and_bool false b = false.
Proof.
Admitted.

(** exercício 17 *)

Lemma and_com : forall b b', and_bool b b' = and_bool b' b.
Proof.
Admitted.

(** exercício 18 *)

Lemma and_assocc : forall b1 b2 b3, and_bool b1 (and_bool b2 b3) = and_bool (and_bool b1 b2) b3.
Proof.
Admitted.

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
Admitted.

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


(**
Exercício 21

Defina a função `even_bool : nat -> bool` que, a partir de um número natural, retorne
verdadeiro se este é par.
 **)

Definition even_bool (n : nat) : bool.
Admitted.

(** 
Exercício 22 
 **)

Lemma even_add_n : forall n, even_bool (n + n) = true.
Proof.
Admitted.

(** 
Exercício 23
Defina a função `odd_bool : nat -> bool` que, a partir de um número natural, 
retorne verdadeirso se este é ímpar
 **)

Definition odd_bool (n : nat) : bool.
Admitted.


(** Exercício 24 *)

Lemma odd_add_n_Sn : forall n, odd_bool (n + S n) = true.
Proof.
Admitted.

(** Exercício 25 *)

Lemma even_SS : forall n, even_bool n = even_bool (S (S n)).
Proof.
Admitted.


(** Exercício 26 *)

Lemma odd_SS : forall n, odd_bool n = odd_bool (S (S n)).
Proof.
Admitted.

(** Exercício 27 *)

Lemma even_bool_S : forall n, even_bool n = not_bool (even_bool (S n)).
Proof.
Admitted.

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
Admitted.

(** exercício 29 *)

Lemma app_nil_right {A : Type} : forall (xs : list A), xs ++ [] = xs.
Proof.
Admitted.

(** exercício 30 *)

Lemma app_assoc {A : Type} : forall (xs ys zs : list A), xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
Proof.
Admitted.

(** exercício 31 *)

Lemma map_app {A B : Type}{f : A -> B}
  : forall xs ys, map f (xs ++ ys) = map f xs ++ map f ys.
Proof.
Admitted.

(** exercício 32 *)

Lemma reverse_app {A : Type}
  : forall (xs ys : list A), reverse (xs ++ ys) = reverse ys ++ reverse xs.
Proof.
Admitted.

(** exercício 33 *)

Lemma reverse_inv {A : Type}
  : forall (xs : list A), reverse (reverse xs) = xs.
Proof.
Admitted.

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


Definition double (n : nat) := 2 * n.

(** exercício 34 *)

Lemma double_even : forall n, even (double n).
Proof.
Admitted.

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
Admitted.

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

(** exercício 36 *)

Lemma le_trans : forall n m p, n <= m -> m <= p -> n <= p.
Proof.
Admitted.

(** exercício 37 *)

Lemma le_antisym : forall n m, n <= m -> m <= n -> n = m.
Proof.
Admitted.

(** exercício 38 

Considere a tarefa de projetar um predicado indutivo
`Sorted : list nat -> Prop` que constitui uma prova
de que uma certa lista de números naturais está ordenada. 
Sua definição deve utilizar o predicado `<=` e conseguir
demonstrar os casos de teste abaixo.

*)

Inductive Sorted : list nat -> Prop := .

Example test_sorted1 : Sorted [].
Proof.
Admitted.

Example test_sorted2 : Sorted [10].
Proof.
Admitted .

Example test_sorted3 : Sorted [1 ; 3 ; 5 ].
Proof.
Admitted.

Reserved Notation "x '<<=' y" (at level 40, no associativity).

Inductive le_alt : nat -> nat -> Prop :=
| le_alt_zero : forall n, 0 <<= n
| le_alt_succ : forall n m, n <<= m -> S n <<= S m
where "x '<<=' y" := (le_alt x y).

(** exercício 39 *)

Lemma le_alt_refl : forall n, n <<= n.
Proof.
Admitted.

(** exercício 40 *)

Lemma le_alt_trans
  : forall n m p, n <<= m -> m <<= p -> n <<= p.
Proof.
Admitted.

(** exercício 41 *)

Lemma le_alt_antisym : forall n m, n <<= m -> m <<= n -> n = m.
Proof.
Admitted.

(** exercício 42 *)

Lemma le_alt_equiv_le : forall n m, n <<= m <-> n <= m.
Proof.
Admitted.
