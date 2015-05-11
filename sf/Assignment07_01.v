Require Export Assignment07_00.

(* problem #01: 20 points *)


(** **** Exercise: 3 stars (optimize_0plus_b)  *)
(** Since the [optimize_0plus] tranformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function which performs that transformation on [bexp]s, and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as elegant as possible. *)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
    | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
    | BNot b1 => BNot (optimize_0plus_b b1)
    | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.

Theorem optimize_0plus_sound: forall e,
  aeval (optimize_0plus e) = aeval e.
Proof.
  intros e. induction e.
  Case "ANum". reflexivity.
  Case "APlus". destruct e1.
    SCase "e1 = ANum n". destruct n.
      SSCase "n = 0".  simpl. apply IHe2. 
      SSCase "n <> 0". simpl. rewrite IHe2. reflexivity.
    SCase "e1 = APlus e1_1 e1_2". 
      simpl. simpl in IHe1. rewrite IHe1. 
      rewrite IHe2. reflexivity.
    SCase "e1 = AMinus e1_1 e1_2". 
      simpl. simpl in IHe1. rewrite IHe1. 
      rewrite IHe2. reflexivity.
    SCase "e1 = AMult e1_1 e1_2". 
      simpl. simpl in IHe1. rewrite IHe1. 
      rewrite IHe2. reflexivity.
  Case "AMinus".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  Case "AMult".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.  Qed.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros.
  induction b.
  try reflexivity.
  try reflexivity.
  unfold optimize_0plus_b.
  simpl.
  assert (aeval (optimize_0plus a) = aeval a).
  apply optimize_0plus_sound.
  rewrite H.
  assert (aeval (optimize_0plus a0)=aeval a0).
  apply optimize_0plus_sound with (e:=a0).
  rewrite H0.
  reflexivity.
  unfold optimize_0plus_b.
  simpl.
  assert (aeval (optimize_0plus a) =aeval a).
  apply optimize_0plus_sound.
  assert (aeval (optimize_0plus a0)=aeval a0).
  apply optimize_0plus_sound with (e:=a0).
  rewrite H. rewrite H0. reflexivity.
  simpl.
  rewrite IHb.
  reflexivity.
  simpl.
  rewrite IHb1.
  rewrite IHb2.
  reflexivity.
Qed.