Require Export Assignment08_01.

(* problem #02: 10 points *)

(** **** Exercise: 3 stars, advanced (pup_to_n)  *)
(** Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].
   Prove that this program executes as intended for X = 2
   (this latter part is trickier than you might expect). *)

Definition pup_to_n : com :=
  Y ::= (ANum 0) ;;
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    Y ::= (APlus (AId Y) (AId X));;
    X ::= (AMinus (AId X) (ANum 1))
  END.

Example pup_to_2_ceval :
  pup_to_n / (update empty_state X 2) ||
    update (update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
unfold pup_to_n.
  eapply E_Seq with (st':=(update (update empty_state X 2) Y 0)).
  eapply E_Ass.
  reflexivity.
  eapply E_WhileLoop with (st':=(update (update (update (update empty_state X 2) Y 0) Y 2) X 1)).
  reflexivity.
  eapply E_Seq with (st':=(update (update (update empty_state X 2) Y 0) Y 2)).
  eapply E_Ass.
  compute.
  reflexivity.
  eapply E_Ass.
  compute.
  reflexivity.
  eapply E_WhileLoop with (st':= update (update (update (update (update (update empty_state X 2) Y 0) Y 2) X 1)
        Y 3) X 0).
  simpl.
  reflexivity.
  eapply E_Seq with (st':= (update (update (update (update (update empty_state X 2) Y 0) Y 2) X 1) Y 3)).
  eapply E_Ass.
  simpl.
  reflexivity.
  eapply E_Ass.
  simpl.
  reflexivity.
  eapply E_WhileEnd.
  simpl.
  reflexivity.
Qed.
(*-- Check --*)
Check pup_to_2_ceval :
  pup_to_n / (update empty_state X 2) ||
    update (update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
 
