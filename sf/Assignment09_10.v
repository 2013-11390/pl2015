Require Export Assignment09_09.

(* problem #10: 10 points *)

(** **** Exercise: 3 stars (two_loops)  *)
(** Here is a very inefficient way of adding 3 numbers:
  X ::= 0;;
  Y ::= 0;;
  Z ::= c;;
  WHILE X <> a DO
    X ::= X + 1;;
    Z ::= Z + 1
  END;;
  WHILE Y <> b DO
    Y ::= Y + 1;;
    Z ::= Z + 1
  END

    Show that it does what it should by filling in the blanks in the
    following decorated program.

    {{ True }} ->>
    {{                                        }}
  X ::= 0;;
    {{                                        }}
  Y ::= 0;;
    {{                                        }}
  Z ::= c;;
    {{                                        }}
  WHILE X <> a DO
      {{                                        }} ->>
      {{                                        }}
    X ::= X + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END;;
    {{                                        }} ->>
    {{                                        }}
  WHILE Y <> b DO
      {{                                        }} ->>
      {{                                        }}
    Y ::= Y + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END
    {{                                        }} ->>
    {{ Z = a + b + c }}
*)

Definition add_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    Z ::= APlus (AId Z) (ANum 1);;
    X ::= AMinus (AId X) (ANum 1)
  END.

Theorem add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.
Proof.
  intros.
  eapply hoare_consequence_pre with (P' := fun st : state => c = 0+0+c).
  eapply hoare_seq with (Q := fun st : state => c = st X + 0 + c).
  eapply hoare_seq with (Q := fun st : state => c = st X + st Y + c).
  eapply hoare_seq with (Q := fun st : state => st Z = st X + st Y + c).
  eapply hoare_seq with (Q := fun st : state => st Z = a + st Y + c).
  eapply hoare_consequence_post.
  eapply hoare_while.
  eapply hoare_consequence_pre with (P' := fun st : state => st Z + 1 = a + st Y + 1 +c).
  eapply hoare_seq with (Q := fun st : state => st Z + 1 = a + st Y + c).
  eapply hoare_consequence_pre. 
  apply hoare_asgn.
  unfold assn_sub.
  unfold update.
  unfold assert_implies.
  simpl.
  intros.
  omega.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold assn_sub.
  unfold update.
  unfold assert_implies.
  simpl.
  intros.
  omega.
  unfold assert_implies.
  simpl.
  intros.
  induction H.
  eapply negb_true in H0.
  eapply beq_nat_false in H0.
  rewrite H.
  omega.
  unfold assert_implies.
  simpl.
  intros.
  induction H.
  eapply negb_false in H0.
  eapply beq_nat_true in H0.
  rewrite H.
  omega.
  eapply hoare_consequence_post.
  eapply hoare_while.
  eapply hoare_consequence_pre with (P' := fun st : state => st Z + 1 = st X + 1 + st Y + c).
  eapply hoare_seq with (Q := fun st : state => st Z + 1 = st X + st Y + c).
  eapply hoare_consequence_pre.
  eapply hoare_asgn.
  unfold assn_sub.
  unfold update.
  unfold assert_implies.
  simpl.
  intros.
  omega.
  eapply hoare_consequence_pre.
  eapply hoare_asgn.
  unfold assn_sub.
  unfold update.
  unfold assert_implies.
  simpl.
  intros.
  omega.
  unfold assn_sub.
  unfold update.
  unfold assert_implies.
  simpl.
  intros.
  omega.
  unfold assn_sub.
  unfold update.
  unfold assert_implies.
  simpl.
  intros.
  induction H.
  eapply negb_false in H0.
  eapply beq_nat_true in H0.
  omega.
  eapply hoare_consequence_pre.
  eapply hoare_asgn.
  unfold assn_sub.
  unfold update.
  unfold assert_implies.
  intros.
  simpl.
  eapply H.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold assn_sub.
  unfold update.
  unfold assert_implies.
  intros.
  simpl.
  eapply H.
  eapply hoare_consequence_pre.
  eapply hoare_asgn.
  unfold assn_sub.
  unfold update.
  unfold assert_implies.
  intros.
  simpl.
  eapply H.
  unfold assert_implies.
  intros.
  omega.
Qed.

(*-- Check --*)
Check add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.

