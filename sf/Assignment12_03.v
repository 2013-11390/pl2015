Require Export Assignment12_02.

(* problem #03: 10 points *)

(** **** Exercise: 3 stars (types_unique)  *)
(** Another pleasant property of the STLC is that types are
    unique: a given term (in a given context) has at most one
    type. *)

Lemma type_is_unique: forall t G T T'
    (TYPED: G |- t \in T)
    (TYPED': G |- t \in T'),
  T = T'.
Proof.
 induction t; intros; inversion TYPED; inversion TYPED'; subst; auto.
  rewrite H1 in H5.
  inversion H5.
  reflexivity.
  assert (TArrow T1 T = TArrow T0 T').
    eapply IHt1.
    apply H2.
    assumption.
  inversion H.
  eauto.
  f_equal.
  eapply IHt.
  eapply H4.
  eauto.
  eapply IHt2.
  eapply H5.
  eauto.
  f_equal.
  eapply IHt1.
  eapply H2.
  eauto.
  eapply IHt2.
  apply H4.
  eauto.
  assert (TProd T T2 = TProd T' T3).
    eapply IHt.
    eapply H1.
    eauto.
  inversion H.
  eauto.
  assert (TProd T1 T = TProd T0 T').
    eapply IHt.
    eapply H1.
    eauto.
  inversion H.
  eauto.
  assert (T1 = T0).
    eapply IHt1.
    eapply H4.
    auto.
  rewrite H in H5.
  eapply IHt2.
  apply H5.
  auto.
  f_equal.
  eapply IHt.
  apply H3.
  auto.
  f_equal.
  eapply IHt.
  apply H3. 
  eauto.
  assert (TSum T1 T2 = TSum T3 T4).
    eapply IHt1.
    eapply H6.
    eauto.
  inversion H; subst.
  eapply IHt2.
  eapply H7.
  eauto.
  eapply IHt2.
  eapply H4.
  eauto.
  eapply IHt2.
  eapply H7.
  eauto.
  assert (TArrow (TArrow T1 T2) (TArrow T1 T2) = TArrow (TArrow T0 T3) (TArrow T0 T3)).
    eapply IHt.
    eapply H1.
    eauto.
  inversion H; subst.
  eauto.
Qed.

(*-- Check --*)
Check type_is_unique: forall t G T T'
    (HTyped: G |- t \in T)
    (HTyped': G |- t \in T'),
  T = T'.

