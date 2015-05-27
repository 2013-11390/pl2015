Require Export Assignment09_08.

(* problem #09: 10 points *)

(** **** Exercise: 4 stars (factorial)  *)
(** Recall that [n!] denotes the factorial of [n] (i.e. [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:
    {{ X = m }} 
  Y ::= 1 ;;
  WHILE X <> 0
  DO
     Y ::= Y * X ;;
     X ::= X - 1
  END
    {{ Y = m! }}

    Fill in the blanks in following decorated program:
    {{ X = m }} ->>
    {{                                      }}
  Y ::= 1;;
    {{                                      }}
  WHILE X <> 0
  DO   {{                                      }} ->>
       {{                                      }}
     Y ::= Y * X;;
       {{                                      }}
     X ::= X - 1
       {{                                      }}
  END
    {{                                      }} ->>
    {{ Y = m! }}
*)

Print fact.

Theorem factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.
Proof.
  intros.
  eapply hoare_consequence_pre with (P' := fun st : state => fact (st X) = fact m).
  eapply hoare_seq with (Q := fun st : state => (st Y) * fact (st X) = fact m).
  eapply hoare_consequence_post.
  eapply hoare_while.
  eapply hoare_consequence_pre with (P' := fun st : state => (st Y) *(st X) * fact (st X-1) = fact m).
  eapply hoare_seq with (Q := fun st : state => (st Y) * fact (st X-1) = fact m).
  eapply hoare_consequence_pre.
  eapply hoare_asgn.
  unfold assn_sub.
  unfold update.
  unfold assert_implies.
  intros.
  assumption.
  eapply hoare_consequence_pre.
  eapply hoare_asgn.
  unfold assn_sub.
  unfold update.
  unfold assert_implies.
  intros.
  assumption.
  unfold assert_implies.
  simpl.
  intros.
  induction H.
  eapply negb_true in H0.
  eapply beq_nat_false in H0.
  assert (st X * fact(st X-1) = fact (st X)).
  Lemma hi : (forall n, n<>0 -> n * fact(n-1) = fact n).
  Proof.
    intros.
    induction n.
    eapply ex_falso_quodlibet.
    apply H.
    reflexivity.
    simpl.
    Lemma hi2 : forall n, n-0=n.
    Proof.
      induction n.
      simpl.
      reflexivity.
      simpl.
      reflexivity.
    Qed.
    rewrite hi2.
    reflexivity.
  Qed.
  eapply hi.
  eapply H0.
  rewrite <- H.
  rewrite <- H1.
  Lemma hi3 : forall a b c, a*b*c = a *(b*c).
  Proof.
    intros.
    rewrite <- mult_assoc_reverse.
    reflexivity.
  Qed.
  rewrite <- hi3. 
  reflexivity.
  unfold assert_implies.
  simpl.
  intros.
  induction H.
  eapply negb_false in H0.
  eapply beq_nat_true in H0.
  rewrite H0 in H.
  simpl in H.
  omega.
  eapply hoare_consequence_pre.
  eapply hoare_asgn.
  unfold assn_sub.
  unfold update.
  unfold assert_implies.
  simpl.
  intros.
  omega.
  unfold assert_implies.
  intros.
  rewrite H.
  reflexivity.
Qed.
(*-- Check --*)
Check factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.

