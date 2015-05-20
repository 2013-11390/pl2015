Require Export Assignment08_09.

(* problem #10: 10 points *)

(** **** Exercise: 2 stars, optional (seq_assoc)  *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
  intros.
  split.
  intros.
  inversion H; subst.
  inversion H2; subst.
  econstructor.
  eapply H3.
  eapply E_Seq.
  eapply H7.
  eapply H5.
  intros.
  inversion H; subst.
  inversion H5; subst.
  eapply E_Seq.
  eapply E_Seq.
  eapply H2.
  eapply H3.
  eapply H7.
Qed.

(*-- Check --*)
Check seq_assoc : forall c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).

