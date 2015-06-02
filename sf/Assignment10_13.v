Require Export Assignment10_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  induction n; intros.
  exists st.
  split.
  eapply multi_refl.
  assumption.
  assert(exists st' : state,
  par_loop / st ==>c* par_loop / st' /\ st' X = n /\ st' Y = 0).
  apply IHn.
  assumption.
  inversion H0.
  exists (update x X (S n)).
  split; inversion H1 as [H2 H3]. 
  eapply multi_trans.
  eapply H2.
  eapply par_body_n__Sn.
  assumption.
  split.
  rewrite update_eq.
  reflexivity.
  inversion H3 as [H4 H5].
  rewrite update_neq.
  assumption.
  destruct (eq_id_dec X Y) eqn:xy; inversion xy.
  assumption.
Qed.

(*-- Check --*)
Check par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.

