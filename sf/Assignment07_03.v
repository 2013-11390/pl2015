Require Export Assignment07_02.

(* problem #03: 20 points *)

(** **** Exercise: 3 stars  (bevalR)  *)
(** Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)


Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue  : bevalR BTrue true
  | E_BFalse : bevalR BFalse false
  | E_BEq    : forall e1 e2 n m, aevalR e1 n -> aevalR e2 m -> bevalR (BEq e1 e2) (beq_nat n m)
  | E_BLe    : forall e1 e2 n m, aevalR e1 n -> aevalR e2 m -> bevalR (BLe e1 e2) (ble_nat n m)
  | E_BNot   : forall e b, bevalR e b -> bevalR (BNot e) (negb b)
  | E_BAnd   : forall e1 e2 b1 b2, bevalR e1 b1 -> bevalR e2 b2 -> bevalR (BAnd e1 e2) (andb b1 b2).

Theorem beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  split.
  intros.
  induction H.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  apply aeval_iff_aevalR in H.
  apply aeval_iff_aevalR in H0.
  rewrite H.
  rewrite H0.
  reflexivity.
  simpl.
  apply aeval_iff_aevalR in H.
  apply aeval_iff_aevalR in H0.
  rewrite H.
  rewrite H0.
  reflexivity.
  simpl.
  rewrite IHbevalR.
  reflexivity.
  simpl.
  rewrite IHbevalR1.
  rewrite IHbevalR2.
  reflexivity.
  generalize dependent bv.
  induction b.
  intros.
  simpl in H.
  rewrite <- H.
  constructor.
  intros.
  simpl in H.
  rewrite <- H.
  constructor.
  intros.
  simpl in H.
  rewrite <- H.
  constructor.
  apply aeval_iff_aevalR.
  reflexivity.
  apply aeval_iff_aevalR.
  reflexivity.
  intros.
  simpl in H.
  rewrite <- H.
  constructor.
  apply aeval_iff_aevalR.
  reflexivity.
  apply aeval_iff_aevalR.
  reflexivity.
  intros.
  simpl in H.
  simpl in H.
  rewrite <- H.
  constructor.
  apply IHb.
  reflexivity.
  intros.
  simpl in H.
  rewrite <- H.
  constructor.
  apply IHb1.
  reflexivity.
  apply IHb2.
  reflexivity.
Qed.