Require Export Assignment11_04.

(* problem #05: 10 points *)

(** The typing relation enjoys two critical properties.  The first is
    that well-typed normal forms are values (i.e., not stuck). *)

(** **** Exercise: 3 stars (finish_progress)  *)
(** Complete the formal proof of the [progress] property.  (Make sure
    you understand the informal proof fragment in the following
    exercise before starting -- this will save you a lot of time.) *)

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.
Proof with auto.
  intros t T HT.
  has_type_cases (induction HT) Case...
  (* The cases that were obviously values, like T_True and
     T_False, were eliminated immediately by auto *)
  Case "T_If".
    right. inversion IHHT1; clear IHHT1.
    SCase "t1 is a value".
    apply (bool_canonical t1 HT1) in H.
    inversion H; subst; clear H.
      exists t2...
      exists t3...
    SCase "t1 can take a step".
      inversion H as [t1' H1].
      exists (tif t1' t2 t3)...
  Case "T_Succ".
    inversion IHHT.
    inversion H; subst.
    inversion H0; subst; inversion HT; subst.
    induction H0.
    left. eauto.
    left. eauto.
    right.
    destruct H.
    exists (tsucc x). apply ST_Succ.
    assumption.
  Case "T_Pred".
     inversion IHHT.
     SCase "t1 is a value". inversion H; subst.
      SSCase "t1 is a bvalue". inversion H0; subst; inversion HT; subst.
      SSCase "t1 is a nvalue". induction H0.
        SSSCase "t1 is tzero".
          right. exists tzero. apply ST_PredZero.
        SSSCase "t1 is tssuc t".
          right. exists t. apply ST_PredSucc. assumption.
      SCase "t1 can take a step". destruct H.
        right. exists (tpred x). auto.
  Case "T_Iszero".
    inversion IHHT.
     SCase "t1 is a value". inversion H; subst. 
         SSCase "t1 is a bvalue". inversion H0; subst; inversion HT; subst.
         SSCase "t1 is a nvalue". inversion H0; subst.
           SSSCase "t1 is tzero".
             right. exists ttrue. auto.
           SSSCase "t1 is succ t' ".
             right. exists tfalse. auto.
      SCase "t1 can take a step".
        right. destruct H. exists (tiszero x). auto.
Qed.

(*-- Check --*)
Check progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.

