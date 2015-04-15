Require Export Assignment05_11.

(* problem #12: 10 points *)


Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra. inversion contra.
Qed.




(** 2 stars (false_beq_nat)  *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
  intros n. induction n.
    Case "n=0". destruct m. 
      intros H. unfold not in H. apply ex_falso_quodlibet. apply H. reflexivity.
      reflexivity.
    Case "n = S n". destruct m. 
      intros H. reflexivity. 
      intros H. simpl. apply IHn. 
      unfold not. unfold not in H.
      intros Y. apply H. rewrite Y. reflexivity.
Qed.


  