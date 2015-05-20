Require Export Assignment08_18.

(* problem #19: 10 points *)
Lemma constfold_0plus_sound:
  ctrans_sound constfold_0plus.
Proof.
  unfold constfold_0plus.
  simpl.
  unfold ctrans_sound.
  intros c.
  remember (fold_constants_com c).
  apply trans_cequiv with c0.
  rewrite Heqc0.
  apply fold_constants_com_sound.
  apply optimize_0plus_com_sound. 
Qed.

(*-- Check --*)
Check constfold_0plus_sound:
  ctrans_sound constfold_0plus.
