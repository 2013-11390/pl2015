Require Export Assignment05_08.

(* problem #09: 10 points *)



(** 2 stars (contrapositive)  *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros.
  unfold not.
  intros.
  apply H in H1.
  Lemma contradiction : forall P Q : Prop,
  (~P)/\P -> Q.
  Proof.
    intros.
    inversion H.
    unfold not in H0.
    apply H0 in H1.
    inversion H1.
  Qed.
  apply contradiction with (P:=Q).
  split.
  apply H0.
  apply H1.
Qed.