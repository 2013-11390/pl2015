Require Export Assignment05_32.

(* problem #33: 10 points *)

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
  intros.
  induction b.
  rewrite -> plus_0_r.
  apply le_n.
  rewrite <- plus_n_Sm.
  apply le_S.
  apply IHb.
Qed.