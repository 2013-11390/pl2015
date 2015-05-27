Require Export Assignment09_11.

(* problem #12: 10 points *)

(** **** Exercise: 2 stars, advanced (hoare_asgn_weakest)  *)
(** Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
  unfold is_wp.
  unfold hoare_triple.
  unfold assn_sub.
  unfold update.
  unfold assert_implies.
  split.
    intros.
    assert (st' = update st X (aeval st a)).
    apply functional_extensionality.
    inversion H. subst.
    reflexivity.
    rewrite -> H1. 
    apply H0.
    intros.
    remember (update st X (aeval st a)) as st'.
    assert  ((X ::= a) / st || st').
    subst.
    eapply E_Ass.
    reflexivity.
    eapply H in H1.
    subst.
    eapply H1.
    eapply H0.
Qed.

(*-- Check --*)
Check hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
