Require Export Assignment05_04.

(* problem #05: 10 points *)


(** 1 star, optional (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros.
  split.
  intros H.
  inversion H.
  split.
  left.
  apply H0.
  left.
  apply H0.
  split.
  right.
  inversion H0.
  apply H1.
  right.
  inversion H0.
  apply H2.
  intros.
  inversion H.
  inversion H0.
  left.
  apply H2.
  inversion H1.
  left.
  apply H3.
  right.
  apply conj.
  apply H2.
  apply H3.
Qed.


