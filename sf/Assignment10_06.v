Require Export Assignment10_05.

(* problem #06: 10 points *)

Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  unfold deterministic. unfold normal_form_of.  intros x y1 y2 P1 P2.
  inversion P1 as [P11 P12]; clear P1. inversion P2 as [P21 P22]; clear P2. 
  generalize dependent y2. 
  (* We recommend using this initial setup as-is! *)
  induction P11.
  intros y2 P21 P22.
  inversion P21.
  reflexivity.
  exfalso.
  apply P12.
  exists y.
  assumption.
  intros y2 P21 P22.
  inversion P21.
  subst.
  eapply ex_falso_quodlibet.
  eapply P22.
  eexists y.
  assumption.
  subst.
  eapply IHP11.
  assumption.
  assert (y0 = y) as Eq.
  eapply step_deterministic_alt.
  eapply H0.
  eapply H.
  rewrite Eq in *; clear Eq.
  inversion P21.
  subst.
  eapply ex_falso_quodlibet.
  eapply P22.
  eexists y.
  eapply H.
  subst.
  assert (y = y1) as Eq.
  eapply step_deterministic_alt.
  eapply H0.
  eapply H2.
  rewrite Eq in *; clear Eq.
  eapply H3.
  eapply P22.
Qed.


(*-- Check --*)
Check normal_forms_unique:
  deterministic normal_form_of.

