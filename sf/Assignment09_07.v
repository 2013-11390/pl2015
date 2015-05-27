Require Export Assignment09_06.

(* problem #07: 10 points *)

(** **** Exercise: 3 stars, optional (add_slowly_decoration)  *)
(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z.
  WHILE X <> 0 DO
     Z ::= Z + 1;;
     X ::= X - 1
  END

    Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

Theorem slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.
Proof.
  intros.
  eapply hoare_consequence_pre with (P' := fun st : state => st X + st Y = n+m).
  eapply hoare_consequence_post. 
  eapply hoare_while.
  eapply hoare_consequence_pre with (P' := fun st : state => st X-1 + st Y+1 = n+m).
  eapply hoare_seq with(Q := fun st : state => st X-1 + st Y = n+m).
  eapply hoare_consequence_pre.
  eapply hoare_asgn.
  unfold assn_sub.
  unfold update.
  unfold assert_implies.
  intros. 
  simpl.
  apply H.
  eapply hoare_consequence_pre.
  eapply hoare_asgn.
  unfold assn_sub.
  unfold update.
  unfold assert_implies.
  intros. 
  simpl.
  omega.
  unfold assert_implies.
  intros.
  induction H.
  simpl in H0.
  eapply negb_true in H0.
  eapply beq_nat_false in H0.
  omega.
  unfold assert_implies.
  intros.
  induction H.
  simpl in H0.
  eapply negb_false in H0.
  eapply beq_nat_true in H0.
  omega.
  unfold assert_implies.
  intros.
  induction H.
  simpl in H0.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.
(*-- Check --*)
Check slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.

