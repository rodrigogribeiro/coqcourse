From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.

Require Import List Arith_base PeanoNat String.
Import ListNotations.

Open Scope coq_nat.

Section ISORT.

  Fixpoint insert (x : nat)(xs : list nat) : list nat :=
    match xs with
    | [] => [ x ]
    | (y :: ys) =>
      if leb x y then x :: y :: ys else y :: (insert x ys)
    end.

  Fixpoint isort (xs : list nat) : list nat :=
    match xs with
    | [] => []
    | (x :: xs) => insert x (isort xs)          
    end.
End ISORT.

Section TEST_SPEC.

  Fixpoint is_sorted (xs : list nat) : bool :=
    match xs with
    | [] => true
    | [ x ] => true
    | (x :: x' :: xs) => leb x x' && is_sorted xs
    end.

  Fixpoint elem (x : nat)(xs : list nat) : bool :=
    match xs with
    | [] => false
    | (y :: ys) => beq_nat x y || elem x ys
    end.
  
  Definition is_permutation (xs ys : list nat) :=
    forallb (fun x => elem x ys) xs &&
            forallb (fun y => elem y xs) ys.  
  
  Definition isort_is_sorted (xs : list nat) := is_sorted (isort xs).
  
  Definition isort_permutation (xs : list nat) := is_permutation xs (isort xs).

  Definition isort_correct (xs : list nat) :=
    isort_is_sorted xs && isort_permutation xs.

End TEST_SPEC.

QuickChick isort_correct.

Section PROOF.

  Inductive sorted : list nat -> Prop :=
  | SortedNil : sorted []
  | SortedSing : forall x, sorted [ x ]
  | SortedRec : forall x y l, x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

  Hint Constructors sorted.

  Require Import Omega.

  Ltac inv H := inversion H ; clear H ; subst.

  Lemma sorted_inv : forall x l, sorted (x :: l) -> sorted l.
  Proof.
    intros x l H ; inv H ; auto.
  Qed.

  Lemma insert_sorted
    : forall l x, sorted l -> sorted (insert x l).
  Proof.
    intros l x H ; elim H ; simpl ; eauto.
    intros z ; destruct (x <=? z) eqn : Heqn; simpl ; eauto.
    +
      apply leb_iff in Heqn ; eauto.
    +
      apply leb_iff_conv in Heqn.
      assert (z <= x) by omega.
      eauto.
    +
      intros.
      destruct (x <=? y) eqn : Heqn ; destruct (x <=? x0) eqn : Heqm.
      apply leb_iff in Heqn.
      apply leb_iff in Heqm.
      eauto.
      apply leb_iff in Heqn.
      apply leb_iff_conv in Heqm.
      assert (x0 <= x) by omega.
      eauto.
      apply leb_iff_conv in Heqn.
      apply leb_iff in Heqm.
      eauto.
      apply leb_iff_conv in Heqn.
      apply leb_iff_conv in Heqm.
      eauto.
  Qed.

  Inductive permutation {A : Type}: list A -> list A -> Prop :=
    perm_nil : permutation [] []
  | perm_skip : forall (x : A) (l l' : list A),
                permutation l l' -> 
                permutation (x :: l) (x :: l')
  | perm_swap : forall (x y : A) (l : list A),
                permutation (y :: x :: l) (x :: y :: l)
  | perm_trans : forall l l' l'' : list A,
                 permutation l l' -> 
                 permutation l' l'' -> 
                 permutation l l''. 

  Hint Constructors permutation.

  Lemma permutation_refl {A : Type}: forall (l : list A), permutation l l.
  Proof.
    induction l ; eauto.
  Qed.

  Lemma permutation_sym {A : Type}
    : forall (l l' : list A), permutation l l' -> permutation l' l.
  Proof.
    induction 1 ; eauto.
  Qed.

  Lemma permutation_trans {A : Type}
    : forall (l1 l2 l3 : list A), permutation l1 l2 ->
                  permutation l2 l3 ->
                  permutation l1 l3.
  Proof.
    induction 1 ; intros ; eauto.
  Qed.

  Lemma permutation_nil {A : Type} : forall (l : list A), permutation [] l -> l = [].
  Proof.
      intros l HF.
      remember (@nil A) as m in HF.
      induction HF; discriminate || auto.
  Qed.

  Lemma insert_permutation
    : forall l x, permutation (x :: l) (insert x l).
  Proof.
    induction l ; intros ; simpl in * ; eauto.
    destruct (x <=? a) eqn : Ha ; eauto.
  Qed.

  Lemma isort_permutation_thm : forall l, permutation l (isort l).
  Proof.
    Hint Resolve insert_permutation.
    induction l ; simpl in * ; eauto.
  Qed.

  Theorem isort_correct_thm : forall l, permutation l (isort l) /\
                                   sorted (isort l).
  Proof.
    induction l ; split ; simpl ; eauto.
    +
      destruct IHl ; simpl ; eauto.
    +
      destruct IHl.
      apply insert_sorted ; auto.
  Qed.
End PROOF. 