Require Export Assignment05_24.

(* problem #25: 10 points *)









(** 3 stars, optional (ev_plus_plus)  *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious. 
    Hint: You can use [plus_comm], [plus_assoc], [double_plus], [double_even], [ev_sum], [ev_ev__ev].
*)
Check plus_comm.
Check plus_assoc.
Check double_plus.
Check double_even.
Check ev_sum.
Check ev_ev__ev.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Enm Enp.
  apply ev_sum with (n:=n+m) (m:=n+p) in Enm.
  (* (n + m) + (n + p) *)
  replace ((n+m) + (n+p)) with ((n + n) + (m + p)) in Enm.
  replace (n+n) with (double n) in Enm.
  apply ev_ev__ev with (m:=m+p) in Enm.
  apply Enm.
  replace (double n + (m + p) + (m + p)) with (double n + ((m + p) + (m + p))).
  replace  (m + p + (m + p)) with (double (m + p)).
  apply ev_sum.
  apply double_even.
  apply double_even.
  apply double_plus with (n:=m+p).
  apply plus_assoc with (n:=double n).
  apply double_plus.
  rewrite <- plus_assoc.
  replace (n+(m+p)) with (m+(n+ p)).
  rewrite plus_assoc.
  reflexivity.
  apply plus_swap'.
  apply Enp.
Qed.



