(* type class examples *)

Require Import String Arith.Arith_base.

Open Scope string_scope.

(* type class for showing values *)

Class Show (A : Type) : Type
   :={
        show : A -> string
     }.


Instance showBool : Show bool :=
  {
    show := fun b:bool => if b then "true" else "false"
  }.

Inductive color := Red | Green | Blue.

Instance showColor : Show color :=
  {
    show :=
      fun c:color =>
        match c with
        | Red => "Red"
        | Green => "Green"
        | Blue => "Blue"
        end
  }.

Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match n mod 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
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
  string_of_nat_aux n n "".

Instance showNat : Show nat :=
  {
    show := string_of_nat
  }.

Definition showOne {A : Type} `{Show A} (a : A) : string :=
  "The value is " ++ show a.

Definition showTwo {A B : Type}
           `{Show A} `{Show B} (a : A) (b : B) : string :=
  "First is " ++ show a ++ " and second is " ++ show b.

