Require Export Assignment08_05.

(* problem #06: 10 points *)

(** **** Exercise: 2 stars (skip_right)  *)
(** Prove that adding a SKIP after a command results in an equivalent
    program *)

Theorem skip_right: forall c,
  cequiv 
    (c;; SKIP) 
    c.
Proof.
  unfold cequiv.
  intros.
  split.
  intros.
  inversion H.
  inversion H5.
  rewrite <- H8.
  eapply H2.
  intros.
  eapply E_Seq.
  eapply H.
  eapply E_Skip.
Qed.

(*-- Check --*)
Check skip_right: forall c,
  cequiv 
    (c;; SKIP) 
    c.

