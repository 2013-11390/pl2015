Require Export Assignment08_03.

(* problem #04: 10 points *)

(** **** Exercise: 4 stars (no_whiles_terminating)  *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)

(* Hint *)
Check andb_true_iff.
Theorem no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.
Proof.
  intros.
  generalize dependent st.
  induction c.
  intros.
  exists st.
  apply E_Skip.
  intros.
  exists (update st i (aeval st a)).
  apply E_Ass.
  reflexivity.
  intros.
  inversion NOWHL.
  subst.
  assert (exists st', c1 / st || st') as term_fst.
  apply IHc1. 
  apply andb_true_iff in H0.
  inversion H0.
  apply H.
  inversion term_fst.
  assert (exists st'', c2 / x || st'') as term_snd.
  apply IHc2. 
  apply andb_true_iff in H0.
  inversion H0.
  apply H2.
  inversion term_snd.
  exists x0.
  apply E_Seq with x; assumption.
  intros.
  inversion NOWHL.
  subst.
  assert (exists st', c1 / st || st') as term_then.
  apply IHc1.
  apply andb_true_iff in H0.
  inversion H0.
  apply H.
  inversion term_then.
  assert (exists st', c2 / st || st') as term_else.
  apply IHc2.
  apply andb_true_iff in H0.
  inversion H0.
  apply H2.
  inversion term_else.
  remember (beval st b) as evalb.
  destruct evalb.
  exists x.
  apply E_IfTrue. symmetry. assumption. assumption.
  exists x0.
  apply E_IfFalse. symmetry. assumption. assumption.
  inversion NOWHL.
Qed.
(*-- Check --*)
Check no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.


