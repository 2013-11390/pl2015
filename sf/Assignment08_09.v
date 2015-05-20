Require Export Assignment08_08.

(* problem #09: 10 points *)

(** **** Exercise: 2 stars (WHILE_true)  *)
(** Prove the following theorem. _Hint_: You'll want to use
    [WHILE_true_nonterm] here. *)

Theorem WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv 
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).
Proof.
  intros.
  split.
  intros.
Lemma WHILE_true_nonterm : forall b c st st',
     bequiv b BTrue ->
     ~( (WHILE b DO c END) / st || st' ).
Proof.
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw.
  ceval_cases (induction H) Case;
  inversion Heqcw; subst; clear Heqcw.
  unfold bequiv in Hb.
  rewrite Hb in H. inversion H.
  apply IHceval2. reflexivity.
Qed.
  apply WHILE_true_nonterm in H0.
  apply ex_falso_quodlibet.
  assumption.
  assumption.
  intros.
  apply WHILE_true_nonterm in H0.
  apply ex_falso_quodlibet.
  assumption.
  unfold bequiv.
  simpl.
  reflexivity.
Qed.

(*-- Check --*)
Check WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv 
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).

