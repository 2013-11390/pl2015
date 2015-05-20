Require Export Assignment08_04.

(* problem #05: 20 points *)

(** Write a function which compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr :=
match e with
    | ANum n => [ SPush n ]
    | AId ident => [ SLoad ident ]
    | APlus e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [ SPlus ]
    | AMinus e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [ SMinus ]
    | AMult e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [ SMult ]
  end.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof.
  simpl.
  reflexivity.
Qed.

(** **** Exercise: 3 stars, advanced (stack_compiler_correct)  *)
(** The task of this exercise is to prove the correctness of the
    compiler implemented in the previous exercise.  Remember that
    the specification left unspecified what to do when encountering an
    [SPlus], [SMinus], or [SMult] instruction if the stack contains
    less than two elements.  (In order to make your correctness proof
    easier you may find it useful to go back and change your
    implementation!)

    Prove the following theorem, stating that the [compile] function
    behaves correctly.  You will need to start by stating a more
    general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma. *)

Theorem execute_theorem : forall (e : aexp) (st : state) (s1 : list nat) (other : list sinstr),
		s_execute st s1 (s_compile e ++ other) =
				s_execute st ((aeval st e) :: s1) other.
Proof.
induction e; try reflexivity.
simpl in |- *.
intros st s1 other.
assert
((s_compile e1 ++ s_compile e2 ++ [SPlus]) ++ other =
 s_compile e1 ++ s_compile e2 ++ [SPlus] ++ other).
rewrite -> app_ass.
rewrite -> app_ass.
reflexivity.

rewrite H in |- *.
assert
(s_execute st s1 (s_compile e1 ++ s_compile e2 ++ SPlus :: other) =
 s_execute st (aeval st e1 :: s1) (s_compile e2 ++ SPlus :: other)).
apply IHe1.

simpl in |- *.
rewrite H0 in |- *.
assert
(s_execute st (aeval st e1 :: s1) (s_compile e2 ++ SPlus :: other) =
 s_execute st (aeval st e2 :: aeval st e1 :: s1) (SPlus :: other)).
apply IHe2.

rewrite H1 in |- *.
simpl in |- *.
rewrite plus_comm in |- *.
reflexivity.

intros st s1 other.
assert
(s_execute st s1 (s_compile e1 ++ s_compile e2 ++ SMinus :: other) =
 s_execute st (aeval st e1 :: s1) (s_compile e2 ++ SMinus :: other)).
apply IHe1.

simpl in |- *.
assert
((s_compile e1 ++ s_compile e2 ++ [SMinus]) ++ other =
 s_compile e1 ++ s_compile e2 ++ [SMinus] ++ other).
rewrite -> app_ass.
rewrite -> app_ass.
reflexivity.

simpl in |- *.
rewrite H0 in |- *.
simpl in |- *.
rewrite H in |- *.
assert
(s_execute st (aeval st e1 :: s1) (s_compile e2 ++ SMinus :: other) =
 s_execute st (aeval st e2 :: aeval st e1 :: s1) (SMinus :: other)).
apply IHe2.

rewrite H1 in |- *.
simpl in |- *.
reflexivity.

intros st s1 other.
simpl in |- *.
simpl in |- *.
assert
((s_compile e1 ++ s_compile e2 ++ [SMult]) ++ other =
 s_compile e1 ++ s_compile e2 ++ [SMult] ++ other).
rewrite -> app_ass.
rewrite -> app_ass.
reflexivity.

rewrite H in |- *.
simpl in |- *.
assert
(s_execute st s1 (s_compile e1 ++ s_compile e2 ++ SMult :: other) =
 s_execute st (aeval st e1 :: s1) (s_compile e2 ++ SMult :: other)).
apply IHe1.

rewrite H0 in |- *.
assert
(s_execute st (aeval st e1 :: s1) (s_compile e2 ++ SMult :: other) =
 s_execute st (aeval st e2 :: aeval st e1 :: s1) (SMult :: other)).
apply IHe2.

rewrite H1 in |- *.
simpl in |- *.
rewrite mult_comm in |- *.
reflexivity.
Qed.


Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
intros st e.
assert ([aeval st e] = s_execute st [aeval st e] []).
simpl in |- *.
reflexivity.

rewrite H in |- *.
assert (s_compile e ++ [] = s_compile e).
simpl in |- *.
rewrite -> app_nil_end.
reflexivity.

rewrite <- H0 in |- *.
apply execute_theorem.
Qed.

(*-- Check --*)
Check s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].

Check s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].

