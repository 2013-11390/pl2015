Require Export Assignment08_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
  intros.
  split.
  intros.
  inversion H2; subst.
  eapply E_IfTrue.
  rewrite <- H.
  eapply H8.
  eapply H0.
  eapply H9.
  eapply E_IfFalse.
  rewrite <- H.
  eapply H8.
  eapply H1.
  eapply H9.
  intros.
  inversion H2; subst.
  eapply E_IfTrue.
  rewrite <- H in H8.
  eapply H8.
  eapply H0 in H9.
  eapply H9.
  eapply E_IfFalse.
  rewrite <- H in H8.
  eapply H8.
  eapply H1 in H9.
  eapply H9.
Qed.

(*-- Check --*)
Check CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).

