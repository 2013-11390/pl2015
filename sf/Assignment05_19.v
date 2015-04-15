Require Export Assignment05_18.

(* problem #19: 10 points *)




(** 2 stars (gorgeous_sum)  *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros n m Gn Gm.
  induction Gn as [ | n' | n'].
  apply Gm.
  apply g_plus3 with (n:=(n'+m)).
  apply IHGn.
  apply g_plus5 with (n:=(n'+m)).
  apply IHGn.
Qed.