Require Export Assignment10_09.

(* problem #10: 10 points *)

(** The fact that small-step reduction implies big-step is now
    straightforward to prove, once it is stated correctly. 

    The proof proceeds by induction on the multi-step reduction
    sequence that is buried in the hypothesis [normal_form_of t t']. *)
(** Make sure you understand the statement before you start to
    work on the proof.  *)

(** **** Exercise: 3 stars (multistep__eval)  *)
Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t || n.
Proof.
  unfold normal_form_of.
  intros.
  inversion H.
  clear H.
  induction H0.
  induction x.
  exists n.
  split.
  reflexivity.
  constructor.
  induction IHx1.
  induction H.
  induction IHx2.
  induction H2.
  exists (x + x0).
  split.
  eapply ex_falso_quodlibet.
  eapply H1.
  exists (C (x+x0)).
  rewrite -> H.
  rewrite -> H2.
  constructor.
  constructor.
  assumption.
  assumption.
  intros Hs.
  eapply H1.
  inversion Hs.
  exists (P x1 x0).
  constructor.
  rewrite -> H.
  constructor.
  eapply H2.
  intros Hs.
  eapply H1.
  inversion Hs.
  exists (P x x2).
  constructor.
  eapply H.
  induction IHmulti.
  exists x0.
  induction H2.
  split.
  eapply H2.
  apply step__eval with y.
  assumption.
  assumption.
  eapply H1.
Qed.

(*-- Check --*)
Check multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t || n.

