Set Implicit Arguments.

Hint Extern 1 (_ = _) => congruence.

(* syntax *)

Inductive exp : Set :=
| Zero   : exp
| Succ   : exp -> exp
| T      : exp
| F      : exp
| Pred   : exp -> exp             
| If     : exp -> exp -> exp -> exp
| IsZero : exp -> exp.


(* values *)

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

Definition normal_form e :=
  ~ exists e', step e e'.

Definition stuck e :=
  normal_form e /\ ~ value e.

Hint Unfold normal_form stuck.

(* first lemma *)

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

Lemma value_is_nf : forall e, value e -> normal_form e.
Proof.
  unfold normal_form ; intros e H contra ; induction e ;
    try (repeat s) ; eauto.
Qed.

Hint Resolve value_is_nf.

Ltac s1 :=
  match goal with
  | [ H : (nvalue ?e) , H1 : ?e ==> _ |- _] =>
    apply Nvalue in H ; apply value_is_nf in H ;
    unfold normal_form in H ; apply ex_intro in H1 ; contradiction
  end.  

Lemma step_deterministic
  : forall e e', e ==> e' -> forall e'', e ==> e'' -> e' = e''.
Proof.
  intros e e' H ; induction H ; intros e'' H' ;
    inverts H' ; f_equal ; try repeat s ; auto ; try repeat s1.
Qed.

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

Lemma succ_multi_step : forall e e', e ==>* e' -> Succ e ==>* Succ e'.
Proof.
  induction 1 ;
     try match goal with
         | [H : ?e ==> ?e1, IH : Succ ?e1 ==>* Succ ?e' |- _] =>
           apply ST_Succ in H ; eapply mstep_step with (e1 := Succ e1) 
         end ; auto.
Qed.
  
Hint Resolve succ_multi_step.

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
    e ==>> (Succ nv) ->
    (IsZero e) ==>> F
where "e '==>>' e1" := (big_step e e1).

Hint Constructors big_step.

Ltac bs := match goal with
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
            | [ IH : forall v, ?e ==>> v -> forall v', ?e ==>> v' -> _
                , H : ?e ==>> _, H1 : ?e ==>> _ |- _] =>
              apply (IH _ H) in H1
            end ; subst ; try f_equal ; auto.
  

Lemma big_step_deterministic : forall e v, e ==>> v -> forall v', e ==>> v' -> v = v'.
Proof.
  induction e ; intros ; repeat bs.
Qed.

(* typing *)

Inductive type : Set :=
| TBool : type
| TNat  : type.

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

Hint Constructors has_type.

Lemma bool_canonical : forall e, e <<- TBool -> value e -> bvalue e.
Proof.
  intros e H Hv ; inverts Hv ; inverts H ; repeat s ; auto.
Qed.

Lemma nat_canonical : forall e, e <<- TNat -> value e -> nvalue e. 
Proof.
  intros e H Hv ; inverts H ; inverts Hv ; repeat s ; auto.
Qed.

Hint Resolve bool_canonical nat_canonical.

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

Theorem preservation : forall e t, e <<- t -> forall e', e ==> e' -> e' <<- t.
Proof.
  induction 1 ; intros ; repeat (s ; eauto) ;
    try repeat (match goal with
                | [H : _ ==> _ |- _] => inverts H ; eauto
                | [H : (Succ _) <<- _ |- _] => inverts H ; eauto  
                end).
Qed.



(* notations for subset types -- sig types *)

Notation "!" := (False_rec _ _).
Notation "[ e ]" := (exist _ e _).

(* notations for sumbool types *)

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).
Notation "x || y" := (if x then Yes else Reduce y).

(* notations for sumor *)

Notation "!!" := (inright _ _).
Notation "[|| x ||]" := (inleft _ [x]).

Notation "x <-- e1 ; e2" := (match e1 with
                               | inright _ => !!
                               | inleft (exist _ x _) => e2
                             end)
                              (right associativity, at level 60).

Notation "e1 ;;; e2" := (if e1 then e2 else !!)
                          (right associativity, at level 60).

Definition eq_ty_dec : forall (t t' : type), {t = t'} + {t <> t'}.
  decide equality.
Defined.

Theorem has_type_det : forall e t, e <<- t -> forall t', e <<- t' -> t = t'.
Proof.
  induction 1 ; intros t' Hc ; inverts Hc ; eauto.
Qed.

Hint Resolve has_type_det.

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