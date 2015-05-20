Require Export Assignment08_07.

(* problem #08: 10 points *)

(** **** Exercise: 3 stars (swap_if_branches)  *)
(** Show that we can swap the branches of an IF by negating its
    condition *)

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros.
  split.
  intros.
  inversion H.
  subst.
  eapply E_IfFalse.
  simpl.
  eapply negb_false_iff.
  eapply H5.
  eapply H6.
  eapply E_IfTrue.
  simpl.
  eapply negb_true_iff.
  eapply H5.
  eapply H6.
  intros.
  inversion H.
  subst.
  eapply E_IfFalse.
  simpl in H5.
  eapply negb_true_iff in H5.
  eapply H5.
  eapply H6.
  eapply E_IfTrue.
  simpl in H5.
  eapply negb_false_iff in H5.
  eapply H5.
  eapply H6.
Qed.

(*-- Check --*)
Check swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).

