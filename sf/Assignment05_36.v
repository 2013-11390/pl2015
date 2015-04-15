Require Export Assignment05_35.

(* problem #36: 10 points *)

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  intros n m H. generalize dependent m. induction n as [|n'].
  intros m H. apply O_le_n.
  intros m H. induction m as [|m'].
  inversion H.
  apply n_le_m__Sn_le_Sm. apply IHn'. simpl in H. apply H.
Qed.