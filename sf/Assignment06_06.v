Require Export Assignment06_05.

(* problem #06: 20 points *)

(** **** Exercise: 4 stars, advanced (no_repeats)  *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros X a b x H.
  induction a.
  right.
  simpl in H.
  apply H.
  inversion H.
  left.
  apply ai_here.
  apply IHa in H1.
  inversion H1.
  left.
  apply ai_later.
  apply H3.
  right.
  apply H3.
Qed.

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros.
  destruct H.
  induction xs.
  inversion H.
  inversion H.
  constructor.
  simpl.
  constructor 2.
  auto.
  induction xs.
  simpl.
  apply H.
  simpl.
  constructor 2.
  apply IHxs.
Qed.