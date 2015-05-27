Require Export Assignment09_04.

(* problem #05: 10 points *)

(** **** Exercise: 2 stars (if_minus_plus)  *)
(** Prove the following hoare triple using [hoare_if]: *)

Definition basn b : Assertion :=
  fun st => (beval st b = true).


Lemma bexp_eval_true : forall b st,
  beval st b = true -> (basn b) st.
Proof.
  intros b st Hbe.
  unfold basn.
  assumption.
Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((basn b) st).
Proof.
  intros b st Hbe contra.
  unfold basn in contra.
  rewrite -> contra in Hbe.
  inversion Hbe.
Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ basn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(basn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  apply (HTrue st st'). 
  assumption. 
  split.
  assumption. 
  apply bexp_eval_true.
  assumption.
  apply (HFalse st st'). 
  assumption. 
  split.
  assumption.
  apply bexp_eval_false.
  assumption.
Qed.

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 
Proof.
  apply hoare_if.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold basn, assert_implies, assn_sub, update.
  simpl.
  intros st [_ H].
  apply le_plus_minus.
  apply ble_nat_true in H.
  assumption.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold basn, assert_implies, assn_sub, update.
  simpl.
  intros st [_ H].
  reflexivity.
Qed.

(*-- Check --*)
Check if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 

