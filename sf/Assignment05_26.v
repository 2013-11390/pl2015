Require Export Assignment05_25.

(* problem #26: 10 points *)



Theorem even_ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  (* Hint: Use induction on [n]. *)
   induction n as [| n'].
      split.  
        intros eq. apply ev_0.
        intros eq. inversion eq.
      inversion IHn' as [H1 H2].
      split. 
        apply H2. 
        intros eq. apply ev_SS. apply H1. 
        inversion eq as [H3].
        apply H3.
Qed.









(** 3 star (even__ev)  
    Note that proving [even__ev] directly is hard.
    You might find it easier to prove [even__ev_strong] first
    and then prove [even__ev] using it.
*)

Lemma even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).
Proof.
  induction n.
  split.
  simpl.
  intros.
  apply ev_0.
  intros.
  apply ev_0.
  split.
  inversion IHn.
  intros.
  simpl.
  apply H0.
  inversion H1.
  unfold even.
  apply H3.
  intros.
  destruct n.
  inversion H.
  apply ev_SS.
  simpl in IHn.
  destruct IHn.
  apply H0.
  apply H.
Qed.