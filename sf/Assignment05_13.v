Require Export Assignment05_12.

(* problem #13: 10 points *)



(** 2 stars, optional (beq_nat_false)  *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.

 intros n. induction n.
    Case "n = 0". intros. unfold not. intros F. destruct m. 
      inversion H.
      inversion F.
    Case "n = Sn". intros. unfold not. intros Y. 
      destruct m. inversion Y. rewrite <- Y in H. simpl in H. apply IHn in H. inversion Y.
      unfold not in H. apply H. reflexivity.
Qed.