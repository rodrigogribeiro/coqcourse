Require Import Omega.

Inductive Plus : nat -> nat -> nat -> Prop :=
| PlusZero
  : forall m, Plus 0 m m
| PlusSucc
  : forall n m r,
    Plus n m r ->
    Plus (S n) m (S r).

Hint Constructors Plus.

Definition plus_cert : forall (n m : nat), {r : nat | Plus n m r}.
  refine (fix plus_cert (n m : nat) : {r | Plus n m r} :=
            match n return {r | Plus n m r} with
            | O    => exist _ m _
            | S n1 =>
              match plus_cert n1 m with
              | exist _ r1 _ => exist _ (S r1) _
              end
            end) ; clear plus_cert ; auto.
Defined.

Definition pred_cert : forall (n : nat), n > 0 -> {r | n = 1 + r}.
  refine (fun n =>
            match n return n > 0 -> {r | n = 1 + r} with
            | O => fun _ => False_rec _ _
            | S n' => fun _ => exist _ n' _
            end) ; omega.
Defined.

Notation "!" := (False_rec _ _).
Notation "[ e ]" := (exist _ e _).

Definition pred_cert1 : forall (n : nat), n > 0 -> {r | n = 1 + r}.
  refine (fun n =>
            match n return n > 0 -> {r | n = 1 + r} with
            | O => fun _ => !
            | S n' => fun _ => [ n' ]
            end) ; omega.
Defined.

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).

Definition eq_nat_dec : forall (n m : nat), {n = m} + {n <> m}.
  refine (fix eq_nat n m : {n = m} + {n <> m} :=
            match n , m with
            | O    , O    => Yes
            | S n' , S m' => Reduce (eq_nat n' m')
            | _    , _    => No
            end) ; clear eq_nat ; congruence.
Defined.

(** exercício 44 *)

Definition eq_bool_dec : forall (a b : bool), {a = b} + {a <> b}.
  refine (fun (a b : bool) => 
                match a, b return {a = b} + {a <> b} with
                | false, false => Yes
                | true , true  => Yes
                | _    , _     => No                    
                end) ; auto ; intro ; congruence.
Defined.

(** exercício 45 *)

Definition eq_list_dec
           {A : Type}
           (eqAdec : forall (x y : A), {x = y} + {x <> y})
  : forall (xs ys : list A), {xs = ys} + {xs <> ys}.
  induction xs.
  +
    intro ys.
    destruct ys.
    -
      left ; auto.
    -
      right ; intro ; congruence.
  +
    intro ys.
    destruct ys.
    -
      right ; intro ; congruence.
    -
      destruct (eqAdec a a0).
      *
        subst.
        destruct (IHxs ys).
        ++
          subst ; left ; f_equal.
        ++
          right ; intro ; congruence.
      *
        right ; intro ; congruence.
Defined.


Notation "!!" := (inright _ _).
Notation "[|| x ||]" := (inleft _ [x]).


Definition pred_cert_full : forall n, {r | n = 1 + r} + {n = 0}.
  refine (fun n =>
            match n return {r | n = 1 + r} + {n = 0} with
            | O => !!
            | S n' => [|| n' ||] 
            end) ; auto.
Defined.

Ltac inverts H := inversion H ; subst ; clear H.

Section MAP.
  Variable Key : Type.
  Variable Value : Type.
  Variable eqKeyDec : forall (x y : Key), {x = y} + {x <> y}.

  Inductive Map : Type :=
  | nil : Map
  | cons : Key -> Value -> Map -> Map.

  Inductive MapsTo : Key -> Value -> Map -> Prop :=
  | Here  : forall k v m, MapsTo k v (cons k v m)
  | There : forall k v m k' v', k <> k' ->
            MapsTo k v m -> MapsTo k v (cons k' v' m).
  
  Hint Constructors MapsTo.
  
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

  (** exercício 46 *)

  Definition insertMap : forall (k : Key)(v : Value)(m : Map), {m' | MapsTo k v m'}.
    intros k v m.
    exists (cons k v m).
    auto.
  Defined.
  
  (** exercício 47 *)

  Definition removeMap : forall (k : Key)(m : Map), {m' | forall v, ~ MapsTo k v m'}.
    intros k m.
    induction m.
    +
      exists nil.
      intros v H.
      inverts H.
    +
      destruct IHm as [m' Hm'].
      destruct m'.
      -
        exists nil.
        auto.
      -
        destruct (eqKeyDec k k1).
        *
          subst.
          assert (H: ~ MapsTo k1 v0 (cons k1 v0 m')).
          ** auto.
          **
            exists m'.
            intros v1 H1.
            apply H.
            auto.
        *
          exists (cons k1 v0 m').
          intros v1 ; auto.
  Defined.
End MAP.  


Section VEC.

  Inductive vector (A : Set) : nat -> Type :=
  | vnil  : vector A 0
  | vcons : forall n, A -> vector A n -> vector A (S n).

  Fixpoint app {A : Set}{n1 n2}(ls1 : vector A n1)(ls2 : vector A n2) : vector A (n1 + n2) :=
    match ls1 with
    | vnil _ => ls2
    | vcons _ _ x ls1' => vcons _ _ x (app ls1' ls2)
    end.

  Definition vhead {A : Set}{n}(v : vector A (S n)) : A :=
    match v with
    | vcons _ _ x _ => x  
    end.

  (** exercício 48 *)

  Fixpoint vmap {A B : Set}{n}(f : A -> B)(v : vector A n) : vector B n :=
    match v with
    | vnil _ => vnil _
    | vcons _ _ x vs => vcons _ _ (f x) (vmap f vs)
    end.
  

  (** exercício 49 
      Enuncie um teorema sobre a associatividade da 
      concatenação de vectors e o prove. *)

  Inductive fin : nat -> Set :=
  | fzero : forall {n}, fin (S n)
  | fsucc : forall {n}, fin n -> fin (S n).                          

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
End VEC.  
