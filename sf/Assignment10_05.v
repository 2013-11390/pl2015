Require Export Assignment10_04.

(* problem #05: 10 points *)

(** **** Exercise: 2 stars (test_multistep_4)  *)
Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  ==>*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
  econstructor.
  apply ST_Plus2.
  constructor.
  apply ST_Plus2.
  constructor.
  apply ST_PlusConstConst.
  econstructor.
  apply ST_Plus2.
  constructor.
  apply ST_PlusConstConst.
  econstructor.
Qed.
(*-- Check --*)
Check test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  ==>*
      P
        (C 0)
        (C (2 + (0 + 3))).

