Require Export Assignment08_11.

(* problem #12: 10 points *)

(** **** Exercise: 3 stars, optional (CSeq_congruence)  *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
  intros.
  split.
  intros.
  inversion H1; subst.
  eapply E_Seq.
  eapply H.
  eapply H4.
  eapply H0.
  eapply H7.
  intros.
  inversion H1; subst.
  eapply E_Seq.
  eapply H.
  eapply H4.
  eapply H0.
  eapply H7.
Qed.

(*-- Check --*)
Check CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').


  