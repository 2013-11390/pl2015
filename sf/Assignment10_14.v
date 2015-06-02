Require Export Assignment10_13.

(* problem #14: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 4 lines thanks to: 
     Hint Constructors aval
     Hint Constructors astep.
  
   You can use the following intro pattern:
     destruct ... as [[? ?] | [? ?]].
*)

Theorem aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.
Proof.
  intros.
  induction a.
  eauto.
  eauto.
  destruct IHa1 as [[n1 H1] | [a' H2]];
  destruct IHa2 as [[n2 H3] | [a'' H4]]; right; eexists.
  rewrite H1.
  rewrite H3.
  eauto.
  rewrite H1.
  inversion H4.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  destruct IHa1 as [[n1 H1] | [a' H2]];
  destruct IHa2 as [[n2 H3] | [a'' H4]]; right; eexists.
  rewrite H3.
  rewrite H1.
  eauto.
  rewrite H1.
  inversion H4.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.  
  destruct IHa1 as [[n1 H1] | [a' H2]];
  destruct IHa2 as [[n2 H3] | [a'' H4]]; right; eexists.
  rewrite H3.
  rewrite H1.
  eauto.
  rewrite H1.
  inversion H4.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
Qed.

(*-- Check --*)
Check aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.

