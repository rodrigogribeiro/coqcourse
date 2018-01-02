From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import seq ssreflect ssrbool ssrnat eqtype.

Require Import List ZArith String.
Import ListNotations.

(* primeiro exemplo *)

Fixpoint remove (x : nat) (l : list nat) : list nat :=
  match l with
    | []   => []
    | h::t => if beq_nat h x then t else h :: remove x t
  end.


Definition removeP (x : nat) (l : list nat) :=
  (~~ (existsb (fun y => beq_nat y x) (remove x l))).

QuickChick removeP.

Check choose.
Sample (choose(0, 10)).

Sample (listOf (choose (0,4))).
Sample (vectorOf 2 (choose (0,4))).

Inductive Tree A :=
| Leaf : Tree A
| Node : A -> Tree A -> Tree A -> Tree A.

Arguments Leaf {A}.
Arguments Node {A} _ _ _.

Instance showTree {A} `{_ : Show A} : Show (Tree A) :=
  {| show := 
       let fix aux t :=
         match t with
           | Leaf => "Leaf"
           | Node x l r => ("Node (" ++ show x ++ ") (" ++
                                    aux l ++ ") (" ++ aux r ++ ")")%string
         end
       in aux
  |}.

Fixpoint genTreeSized {A} (sz : nat) (g : G A) : G (Tree A) :=
  match sz with
    | O => returnGen Leaf
    | S sz' => oneOf [ returnGen Leaf ;
                       liftGen3  Node g (genTreeSized sz' g) (genTreeSized sz' g)
                     ]
  end.

Sample (genTreeSized 3 (choose(0,3))).

Fixpoint genTreeSized' {A} (sz : nat) (g : G A) : G (Tree A) :=
  match sz with
    | O => returnGen Leaf 
    | S sz' => freq [ (1,  returnGen Leaf) ;
                       (sz, liftGen3  Node g (genTreeSized' sz' g)
                                      (genTreeSized' sz' g))
                    ]
  end.

Sample (genTreeSized' 3 (choose(0,3))).

Fixpoint mirror {A : Type} (t : Tree A) : Tree A :=
  match t with
    | Leaf => Leaf
    | Node x l r => Node x (mirror r) (mirror l)
  end.

Fixpoint eq_tree (t1 t2 : Tree nat) : bool :=
  match t1, t2 with
    | Leaf, Leaf => true
    | Node x1 l1 r1, Node x2 l2 r2 =>
      beq_nat x1 x2 && eq_tree l1 l2 && eq_tree r1 r2
    | _, _ => false
  end.

Definition mirrorP (t : Tree nat) := eq_tree (mirror (mirror t)) t.

QuickChick (forAll (genTreeSized' 5 (choose (0,5))) mirrorP).

Definition faultyMirrorP (t : Tree nat) := eq_tree (mirror t) t.

QuickChick (forAll (genTreeSized' 5 (choose (0,5))) faultyMirrorP).


Open Scope list.

Fixpoint shrinkTree {A} (s : A -> list A) (t : Tree A) : seq.seq (Tree A) :=
  match t with
    | Leaf => []
    | Node x l r => [l] ++ [r] ++
                    map (fun x' => Node x' l r) (s x) ++
                    map (fun l' => Node x l' r) (shrinkTree s l) ++
                    map (fun r' => Node x l r') (shrinkTree s r)
  end.

QuickChick (forAllShrink
              (genTreeSized' 5 (choose (0,5))) (shrinkTree shrink) faultyMirrorP).


Instance genTree {A} `{Gen A} : GenSized (Tree A) := 
  {| arbitrarySized n := genTreeSized n arbitrary |}.

Instance shrTree {A} `{Shrink A} : Shrink (Tree A) := 
  {| shrink x := shrinkTree shrink x |}.

QuickChick faultyMirrorP.

Derive Arbitrary for Tree.
(* genSTree is defined *)
(* shrTree0 is defined *)
Print genSTree.
Print shrTree0.

Derive Show for Tree.
(* showTree0 is defined *)
Print showTree0.
