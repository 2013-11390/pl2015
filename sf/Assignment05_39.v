Require Export Assignment05_38.

(* problem #39: 10 points *)

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  unfold not.
  induction n.
  intros n.
  intros H.
  inversion H.
  induction m.
  simpl.
  intros.
  inversion H0.
  simpl.
  intros. 
  apply Sn_le_Sm__n_le_m in H0.
  revert H H0.
  apply IHn.
Qed.