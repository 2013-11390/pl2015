Require Export Assignment11_01.

(* problem #02: 10 points *)

(** **** Exercise: 3 stars, advanced (value_is_nf)  *)
(** Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways. *)

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  intros t H.
  induction H.
  inversion H; subst; unfold normal_form; unfold not; intros; inversion H0; inversion H1.
  induction H; unfold normal_form; unfold not; intros.
  destruct H.
  inversion H.
  destruct H0.
  inversion H0; subst.
  unfold normal_form in IHnvalue.
  unfold not in IHnvalue.
  eapply IHnvalue.
  exists t1'.
  assumption.
Qed.

(*-- Check --*)
Check value_is_nf : forall t,
  value t -> step_normal_form t.

