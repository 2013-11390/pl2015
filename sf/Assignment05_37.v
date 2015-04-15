Require Export Assignment05_36.

(* problem #37: 10 points *)

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  intros n m H. generalize dependent n. induction m as [|m'].
  intros n H. inversion H. reflexivity.
  intros n H. induction n as [|n']. reflexivity.
  simpl. apply IHm'. apply Sn_le_Sm__n_le_m. apply H.
Qed.


