Section PropositionalLogic.
  Variables A B C : Prop.

  (** implicação *)

  Theorem first_theorem : (A -> B) -> A -> B.
  Proof.
    intro Hab.
    intro Ha.
    apply Hab.
    assumption.
  Qed.

  (** exercício 1 *)

  Lemma ex1 : A -> B -> A.
  Proof.
    intro HA.
    intro HB.
    assumption.
  Qed.


  (** exercício 2 *)

  Lemma ex2 : (A -> B) -> (B -> C) -> A -> C.
  Proof.
    intro HAB.
    intro HBC.
    intro HA.
    apply HBC.
    apply HAB.
    assumption.
  Qed.

  (** conjunção *)  

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
  
  (** exercício 3 *)

  Lemma ex3 : (A /\ B) /\ C -> A /\ (B /\ C).
  Proof.
    intro H.
    destruct H as [[HA HB] HC].
    split.
    +
      assumption.
    +
      split.
      - assumption.
      - assumption.
  Qed.

  (** exercício 4 *)

  Lemma ex4 : ((A /\ B) -> C) -> (A -> B -> C).
  Proof.
    intro H.
    intro HA.
    intro HB.
    apply H.
    split.
    + assumption.
    + assumption.  
  Qed.

  (** exercício 5 *)

  Lemma ex5 : (A -> B -> C) -> ((A /\ B) -> C).
  Proof.
    intro H.
    intro HAB.
    destruct HAB as [HA HB].
    apply H.
    + assumption.
    + assumption.  
  Qed.

  (** exercício 6 *)

  Lemma ex6 : ((A -> B) /\ (A -> C)) -> A -> (B /\ C).
  Proof.
    intro H.
    destruct H as [HAB HAC].
    intro HA.
    split.
    +
      apply HAB.
      assumption.
    +
      apply HAC.
      assumption.
  Qed.

  (** bicondicional *)
  
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

  (** negação *)

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
  
  Lemma contra : A -> ~ A -> B.
  Proof.
    intro Ha.
    intro Hna.
    contradiction.
  Qed.

  (** disjunção *)

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

  (** exercício 7 *)

  Lemma ex7 : ((A \/ B) /\ ~ A) -> B.
  Proof.
    intro H.
    destruct H as [[HA | HB] Hna].
    + contradiction.
    + assumption.  
  Qed.

  (** exercício 8 *)

  Lemma ex8 : (A \/ (B /\ C)) -> (A \/ B) /\ (A \/ C).
  Proof.
    intro H.
    destruct H as [HA | [HB HC]].
    +
      split.
      -
        left.
        assumption.
      -
        left.
        assumption.
    +    
      split.
      -
        right.
        assumption.
      -
        right.
        assumption.
  Qed.  
End PropositionalLogic.

Section PredicateLogic.
  Hypothesis U : Set.
  Hypothesis u : U.
  Hypothesis P : U -> Prop.
  Hypothesis Q : U -> Prop.
  Hypothesis R : U -> Prop.

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

  Lemma ex_or : (exists x : U, P x \/ Q x) ->
                (exists x : U, P x) \/ (exists y : U, Q y).
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

  (** exercício 9 *)

  Lemma ex9 : forall x : U, P x -> exists y : U, P y.
  Proof.
    intro x.
    intro Hpx.
    exists x.
    assumption.
  Qed.

  (** exercício 10 *)

  Lemma ex10 : (forall x : U, P x -> ~ Q x) -> ~ exists y : U, P y /\ Q y.
  Proof.
    intro Hpq.
    intro Hnpq.
    destruct Hnpq as [y [Py Qy]].
    apply Hpq in Py.
    contradiction.
  Qed.

  (** exercício 11 *)

  Lemma ex11 : (forall x : U, P x -> Q x) -> (forall x : U, ~ Q x) -> (forall x : U, ~ P x).
  Proof.
    intro Hpq.
    intro Hq.
    intro x.
    unfold not.
    intro Px.
    apply Hpq in Px.
    apply Hq in Px.
    contradiction.
  Qed.

End PredicateLogic.  