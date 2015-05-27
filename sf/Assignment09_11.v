Require Export Assignment09_10.

(* problem #11: 10 points *)

(** **** Exercise: 3 stars, advanced, optional (is_wp_formal)  *)
(** Prove formally using the definition of [hoare_triple] that [Y <= 4]
   is indeed the weakest precondition of [X ::= Y + 1] with respect to
   postcondition [X <= 5]. *)

Theorem is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).
Proof.
  unfold is_wp.
  split.
  unfold hoare_triple.
  intros.
  inversion H; subst.
  simpl.
  unfold update.
  assert (5 = (4+1)).
  reflexivity.
  rewrite H1.
  apply plus_le_compat_r.
  apply H0.
  intros P' ht st P'_holds.
  unfold hoare_triple in ht.
  remember (update st X (st Y + 1)) as st'.
  assert ((X ::= APlus (AId Y) (ANum 1)) / st || st') as E.
  subst st'.
  apply E_Ass.
  reflexivity.
  apply ht in E.
  rewrite Heqst' in E.
  unfold update in E.
  apply le_pred in E.
  rewrite plus_comm in E.
  simpl in E.
  apply E.
  assumption.
Qed.
 
(*-- Check --*)
Check is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).

