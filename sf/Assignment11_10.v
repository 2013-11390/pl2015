Require Export Assignment11_09.

(* problem #10: 30 points *)

(** Write a type checking function [tyeq: tm -> ty -> bool].
**)

Fixpoint tycheck (t: tm) (T: ty) : bool :=
  match t with
  |ttrue => 
    match T with
    | TBool => true
    | TNat => false
    end
  |tfalse => 
    match T with
    | TBool => true
    | TNat => false
    end
  |tif t1 t2 t3 => andb (andb (tycheck t1 TBool) (tycheck t2 T)) (tycheck t3 T)
  |tzero =>  
    match T with
    | TBool => false
    | TNat => true
    end
  |tsucc t => 
    match T with
    | TBool => false
    | TNat => tycheck t T
    end
  |tpred t => 
    match T with
    | TBool => false
    | TNat => tycheck t T
    end
  |tiszero t =>
    match T with
    | TBool => tycheck t TNat
    | TNat => false
    end
end.

Example tycheck_ex1:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true.
Proof. 
  auto.
Qed.

Example tycheck_ex2:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false.
Proof.
  eauto.
Qed.

(** Prove that the type checking function [tyeq: tm -> ty -> bool] is correct.

    Hint: use the lemma [andb_prop].
**)

Check andb_prop.

Theorem tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.
Proof.
  induction t; intros; destruct T; auto; try inversion TYCHK.
  inversion TYCHK.
  eapply andb_prop in H0.
  destruct H0.
  eapply andb_prop in H.
  destruct H.
  eauto.
  inversion TYCHK.
  eapply andb_prop in H0.
  destruct H0.
  eapply andb_prop in H.
  destruct H.
  eauto.
Qed.

Theorem tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
Proof.
  induction t; intros; destruct T; eauto; try inversion HASTY.
  inversion HASTY; subst.
  simpl.
  eapply andb_true_intro; split; eauto; eapply andb_true_intro; split; eauto.
  inversion HASTY; subst.
  simpl.
  eapply andb_true_intro; split; eauto; eapply andb_true_intro; split; eauto.
  simpl.
  inversion HASTY; subst.
  eauto.
  simpl.
  inversion HASTY; subst.
  eauto.
  simpl.
  inversion HASTY; subst.
  eauto.
Qed.

(*-- Check --*)

Check (conj tycheck_ex1 tycheck_ex2 :
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true)
 /\
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false)).

Check tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.

Check tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
