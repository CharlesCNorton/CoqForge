(** * Addition Inequality Monotonicity
    
    This module provides the two-sided monotonicity lemma for addition
    with respect to the less-than-or-equal relation on natural numbers.
    
    Author: Charles C Norton
    Date: June 8th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Arith.Arith.

(** ** Overview
    
    While Coq's standard library provides one-sided monotonicity lemmas
    like [plus_le_compat_l] and [plus_le_compat_r], it lacks the full
    two-sided version that allows adding inequalities.
    
    This property states: if n ≤ m and p ≤ q, then n + p ≤ m + q.
    
    This lemma is essential for:
    - Simplifying arithmetic proofs involving multiple inequalities
    - Reasoning about bounds in algorithms
    - Proving properties of summations
    - Avoiding repeated applications of one-sided lemmas
*)

(** ** Main Theorem *)

(** If n ≤ m and p ≤ q, then n + p ≤ m + q *)
Lemma plus_le_compat_both (n m p q : nat) :
  n <= m -> p <= q -> n + p <= m + q.
Proof.
  intros Hnm Hpq.
  (* First apply left compatibility with n <= m *)
  apply (Nat.le_trans _ (m + p)).
  - apply Nat.add_le_mono_r. exact Hnm.
  (* Then apply right compatibility with p <= q *)
  - apply Nat.add_le_mono_l. exact Hpq.
Qed.

(** ** Alternative Proof *)

(** Here's a more direct proof using the existing lemmas *)
Lemma plus_le_compat_both' (n m p q : nat) :
  n <= m -> p <= q -> n + p <= m + q.
Proof.
  intros Hnm Hpq.
  (* We can also use the transitive property differently *)
  rewrite (Nat.add_comm n p).
  rewrite (Nat.add_comm m q).
  (* Now we have p + n <= q + m *)
  apply Nat.le_trans with (p + m).
  - apply Nat.add_le_mono_l. exact Hnm.
  - apply Nat.add_le_mono_r. exact Hpq.
Qed.

(** ** Corollaries *)

(** Special case: adding the same value preserves inequality *)
Lemma plus_le_compat_both_same (n m k : nat) :
  n <= m -> n + k <= m + k.
Proof.
  intro H.
  apply plus_le_compat_both.
  - exact H.
  - apply le_n.
Qed.

(** Adding positive values to both sides of an inequality *)
Lemma plus_lt_compat_both (n m p q : nat) :
  n < m -> p < q -> n + p < m + q.
Proof.
  intros Hnm Hpq.
  unfold lt in *.
  (* n < m means S n <= m, and p < q means S p <= q *)
  (* So we need to show S (n + p) <= m + q *)
  rewrite <- Nat.add_succ_l.
  (* Now we need to show S n + p <= m + q *)
  apply plus_le_compat_both.
  - exact Hnm.  (* S n <= m *)
  - (* Need to show p <= q, but we have S p <= q *)
    (* From S p <= q, we can derive p < q, and then p <= q *)
    apply Nat.lt_le_incl.
    unfold lt. exact Hpq.
Qed.

(** ** Examples *)

Example plus_le_ex1 : 3 + 5 <= 7 + 8.
Proof.
  apply plus_le_compat_both.
  - (* 3 <= 7 *)
    repeat constructor.
  - (* 5 <= 8 *)
    repeat constructor.
Qed.

Example plus_le_ex2 : forall n, n <= 10 -> n + n <= 10 + 15.
Proof.
  intros n Hn.
  apply plus_le_compat_both.
  - exact Hn.
  - (* Need to prove n <= 15 *)
    apply Nat.le_trans with 10.
    + exact Hn.
    + (* Prove 10 <= 15 *)
      repeat constructor.
Qed.

Example complex_inequality_fixed : forall a b c d,
  a <= 5 -> b <= 3 -> c <= 7 -> d <= 2 ->
  a + b + c + d <= 17.
Proof.
  intros a b c d Ha Hb Hc Hd.
  assert (H17: 5 + 3 + 7 + 2 = 17) by reflexivity.
  rewrite <- H17.
  (* The goal is ((a + b) + c) + d <= ((5 + 3) + 7) + 2 *)
  
  (* Apply to the outermost '+' *)
  apply plus_le_compat_both.
  - (* New Goal: (a + b) + c <= (5 + 3) + 7 *)
    apply plus_le_compat_both.
    + (* New Goal: a + b <= 5 + 3 *)
      apply plus_le_compat_both.
      * exact Ha.
      * exact Hb.
    + (* New Goal: c <= 7 *)
      exact Hc.
  - (* New Goal: d <= 2 *)
    exact Hd.
Qed.

(** ** Related Lemmas in Standard Library
    
    For reference, here are the one-sided lemmas that ARE in the
    standard library (in the Nat module):
    
    - [Nat.add_le_mono_l]: ∀ n m p, n ≤ m → p + n ≤ p + m
    - [Nat.add_le_mono_r]: ∀ n m p, n ≤ m → n + p ≤ m + p
    - [Nat.le_add_r]: ∀ n m, n ≤ n + m
    - [Nat.le_add_l]: ∀ n m, n ≤ m + n
    
    Our lemma combines the first two for a more powerful result.
*)
