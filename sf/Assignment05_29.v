Require Export Assignment05_28.

(* problem #29: 10 points *)

Check le.

Eval compute in le.

Check 3<=4.

Eval compute in 3<=4.
(** 2 stars, optional (le_exercises)  *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros.
  induction H0.
  apply H.
  apply le_S.
  apply IHle.
  apply H.
Qed.