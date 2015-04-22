Require Export Assignment06_04.

(* problem #05: 20 points *)

(** **** Exercise: 3 stars (all_forallb)  *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Check all.

Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
  | all_nil : all P nil
  | all_cons : forall x l, P x -> all P l -> all P (x :: l).
(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

Theorem forallb_correct: forall X (P: X -> bool) l,
  forallb P l = true <-> all (fun x => P x = true) l.
Proof.
  split.
  intros.
  induction l.
  apply all_nil.
  apply all_cons.
  simpl in H.
  apply andb_prop in H.
  inversion H.
  apply H0.
  apply IHl.
  inversion H.
  apply andb_prop in H1.
  inversion H1.
  rewrite -> H2.
  rewrite -> H0.
  simpl.
  reflexivity.
  intros.
  induction l.
  simpl.
  reflexivity.
  inversion H.
  simpl.
  rewrite -> H2.
  simpl.
  apply IHl.
  apply H3.
Qed.