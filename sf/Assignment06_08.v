Require Export Assignment06_07.

(* problem #08: 40 points *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  intros.
  induction l1.
  reflexivity.
  simpl.
  rewrite -> IHl1.
  reflexivity.
Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros.
  induction H.
  exists nil.
  exists l.
  simpl.
  reflexivity.
  destruct IHappears_in.
  exists (b::witness).
  destruct proof.
  exists witness0.
  simpl.
  rewrite <- proof.
  reflexivity.
Qed.
(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  rp_ext : forall x:X, forall l: list X, 
             repeats l -> repeats (x::l) |
  rp_intr : forall x:X, forall l: list X,
             appears_in x l -> repeats (x :: l).
(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)

Theorem pigeonhole_principle: forall {X:Type} (l1 l2:list X),
  excluded_middle -> 
  (forall x, appears_in x l1 -> appears_in x l2) -> 
  length l2 < length l1 -> 
  repeats l1.
Proof.  
  intros X l1.
  induction l1.
  intros l2 em h lt.
  inversion lt.
  intros l2 em h lt.
  remember (em (appears_in x l1)) as em_ai.
  destruct em_ai as [appears | appears_not].
  apply rp_intr.
  apply appears.  
  apply rp_ext.
  destruct (appears_in_app_split X x l2 (h x (ai_here x l1))) as [w1 [w2]].
  apply IHl1 with (l2 := w1 ++ w2).
  apply em.
  intros y ai.
  assert (ai' := ai).
  apply ai_later with (b := x) in ai.
  apply h in ai.
  rewrite -> proof in ai.
  apply appears_in_app in ai.
  destruct ai as [inw1 | inxw2].
  apply app_appears_in. 
  left.
  apply inw1.
  apply app_appears_in.
  right.
  inversion inxw2.
  rewrite -> H0 in ai'.
  apply contradiction_implies_anything with (P := appears_in x l1).
  split.
  apply ai'.
  apply appears_not.
  apply H0.
  rewrite -> proof in lt.
  rewrite -> app_length in lt.
  simpl in lt.
  rewrite <- plus_n_Sm in lt.
  apply Sn_le_Sm__n_le_m in lt.
  rewrite <- app_length in lt.
  apply lt.
Qed.