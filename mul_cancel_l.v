(** * Multiplication Cancellation Left
    
    This module provides the fundamental multiplication cancellation
    property for natural numbers that is missing from Coq's standard
    library.
    
    Author: Charles C Norton
    Date: June 8th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Arith.Arith.

(** ** Overview
    
    Multiplication cancellation states that if p ≠ 0 and p × n = p × m,
    then n = m. This is a fundamental property of multiplication that
    is available for integers (Z) but surprisingly missing for natural
    numbers (nat).
    
    This property is useful for:
    - Simplifying equations involving multiplication
    - Proving uniqueness of solutions
    - Reasoning about divisibility and factors
    - Establishing properties of proportions
    - Algebraic manipulations in arithmetic proofs
*)

(** ** Main Theorem *)

(** Left multiplication cancellation for natural numbers *)
Lemma mul_cancel_l (n m p : nat) : 
  p <> 0 -> p * n = p * m -> n = m.
Proof.
  intros Hp Heq.
  (* We'll use the fact that multiplication preserves order *)
  destruct (Nat.lt_trichotomy n m) as [Hlt | [Heq' | Hgt]].
  - (* n < m *)
    assert (p * n < p * m).
    { apply Nat.mul_lt_mono_pos_l. 
      - apply Nat.neq_0_lt_0. exact Hp.
      - exact Hlt. }
    rewrite Heq in H.
    apply Nat.lt_irrefl in H.
    contradiction.
  - (* n = m *)
    exact Heq'.
  - (* m < n *)
    assert (p * m < p * n).
    { apply Nat.mul_lt_mono_pos_l.
      - apply Nat.neq_0_lt_0. exact Hp.
      - exact Hgt. }
    rewrite <- Heq in H.
    apply Nat.lt_irrefl in H.
    contradiction.
Qed.

(** ** Examples *)

(** Example 1: Solving a simple equation *)
Example mul_cancel_l_ex1 : forall x : nat,
  3 * x = 3 * 5 -> x = 5.
Proof.
  intro x.
  apply mul_cancel_l.
  discriminate.
Qed.

(** Example 2: Practical example with unknowns *)
Example mul_cancel_l_ex2 : forall x : nat,
  5 * x = 5 * 12 -> x = 12.
Proof.
  intro x.
  apply (mul_cancel_l x 12 5).
  discriminate.
Qed.

(** Example 3: Using cancellation to prove uniqueness of solutions *)
Example mul_cancel_l_ex3 : forall x y : nat,
  7 * x = 42 -> 7 * y = 42 -> x = y.
Proof.
  intros x y Hx Hy.
  apply (mul_cancel_l x y 7).
  - discriminate.
  - rewrite Hx, Hy. reflexivity.
Qed.

(** ** Corollaries *)

(** Right multiplication cancellation (follows from commutativity) *)
Lemma mul_cancel_r (n m p : nat) :
  p <> 0 -> n * p = m * p -> n = m.
Proof.
  intros Hp Heq.
  apply (mul_cancel_l n m p).
  - exact Hp.
  - (* Goal: p * n = p * m *)
    rewrite <- (Nat.mul_comm n p).
    rewrite <- (Nat.mul_comm m p).
    exact Heq.
Qed.

(** ** Notes
    
    This lemma is one of the most frequently requested additions to
    the standard library. While Coq provides this for integers (Z),
    the natural number version requires manual proof each time.
    
    The proof uses trichotomy on n and m: we show that if n ≠ m,
    then multiplication by positive p would preserve the strict
    inequality, contradicting our hypothesis that p * n = p * m.
    
    The standard library provides some related lemmas but oddly
    omits this fundamental cancellation property for left
    multiplication.
*)
