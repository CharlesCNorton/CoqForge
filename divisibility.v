(** * Basic Divisibility Properties
    
    This module provides fundamental lemmas about divisibility that are
    missing from Coq's standard library.
    
    Author: Charles C Norton
    Date: June 8th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Arith.Arith.

(** ** Overview
    
    Divisibility is a fundamental concept in number theory and arithmetic
    reasoning, yet Coq's standard library lacks some basic properties.
    
    The divides relation (x | y) means "x divides y", i.e., there exists
    some k such that y = k * x.
    
    These lemmas are essential for:
    - Number theory proofs
    - Reasoning about GCD and LCM
    - Proving properties of modular arithmetic
    - Algorithm correctness (e.g., primality testing)
*)

(** ** Divisibility definition *)

(** We use the standard definition of divisibility *)
Definition divides (x y : nat) : Prop := exists k, y = k * x.
Notation "( x | y )" := (divides x y) (at level 0) : nat_scope.

(** ** Main Theorems *)

(** If x divides y and y is non-zero, then x is non-zero *)
Lemma divide_ne_0 (x y : nat) : (x | y) -> y <> 0 -> x <> 0.
Proof.
  intros [k Hk] Hy Hx.
  (* If x = 0, then y = k * 0 = 0, contradicting Hy *)
  subst x.
  rewrite Nat.mul_0_r in Hk.
  apply Hy.
  exact Hk.
Qed.

(** ** Basic Properties *)

(** Zero divides only zero *)
Lemma zero_divide (n : nat) : (0 | n) -> n = 0.
Proof.
  intros [k Hk].
  rewrite Nat.mul_0_r in Hk.
  exact Hk.
Qed.

(** Everything divides zero *)
Lemma divide_zero (n : nat) : (n | 0).
Proof.
  unfold divides.
  exists 0.
  rewrite <- (Nat.mul_0_l n).
  reflexivity.
Qed.

(** One divides everything *)
Lemma one_divide (n : nat) : (1 | n).
Proof.
  unfold divides.
  exists n.
  rewrite Nat.mul_1_r.
  reflexivity.
Qed.

(** Every number divides itself (reflexivity) *)
Lemma divide_refl (n : nat) : (n | n).
Proof.
  unfold divides.
  exists 1.
  rewrite Nat.mul_1_l.
  reflexivity.
Qed.

(** Divisibility is transitive *)
Lemma divide_trans (x y z : nat) : (x | y) -> (y | z) -> (x | z).
Proof.
  intros [k1 Hk1] [k2 Hk2].
  exists (k2 * k1).
  subst y z.
  apply Nat.mul_assoc.
Qed.

(** If x divides y, then x ≤ y (when y ≠ 0) *)
Lemma divide_le (x y : nat) : (x | y) -> y <> 0 -> x <= y.
Proof.
  intros [k Hk] Hy.
  subst y.
  destruct k.
  - (* k = 0, so k * x = 0, contradicting y ≠ 0 *)
    exfalso. apply Hy. reflexivity.
  - (* k = S k', so y = S k' * x *)
    simpl.
    apply Nat.le_add_r.
Qed.

(** Divisibility and multiplication *)
Lemma divide_mul_r (x y z : nat) : (x | y) -> (x | y * z).
Proof.
  intros [k Hk].
  unfold divides.
  exists (k * z).
  rewrite Hk.
  (* Goal: (k * x) * z = (k * z) * x *)
  (* Let's check what we actually have *)
  simpl.
  rewrite <- Nat.mul_assoc.
  rewrite <- Nat.mul_assoc.
  (* Now we should have: k * x * z = k * z * x *)
  f_equal.
  apply Nat.mul_comm.
Qed.

Lemma divide_mul_l (x y z : nat) : (x | y) -> (x | z * y).
Proof.
  intros H.
  rewrite Nat.mul_comm.
  apply divide_mul_r.
  exact H.
Qed.

(** ** Examples *)

Example divide_ex1 : (3 | 12).
Proof.
  exists 4.
  reflexivity.
Qed.

Example divide_ex2 : (5 | 25) /\ 25 <> 0 -> 5 <> 0.
Proof.
  intros [H1 H2].
  apply (divide_ne_0 5 25); assumption.
Qed.

Example divide_chain : (2 | 6) -> (6 | 30) -> (2 | 30).
Proof.
  apply divide_trans.
Qed.

(** ** Extended Properties *)

(** Sum of multiples *)
Lemma divide_add (x y z : nat) : (x | y) -> (x | z) -> (x | y + z).
Proof.
  intros [k1 Hk1] [k2 Hk2].
  exists (k1 + k2).
  subst y z.
  symmetry.
  apply Nat.mul_add_distr_r.
Qed.

(** Difference of multiples (when y ≥ z) *)
Lemma divide_sub (x y z : nat) : (x | y) -> (x | z) -> z <= y -> (x | y - z).
Proof.
  intros [k1 Hk1] [k2 Hk2] Hle.
  exists (k1 - k2).
  subst y z.
  rewrite <- Nat.mul_sub_distr_r.
  reflexivity.
Qed.

(** ** Notes
    
    These basic divisibility properties are fundamental for number theory
    but missing from Coq's standard library. They're needed whenever
    reasoning about:
    
    - GCD and LCM algorithms
    - Prime factorization
    - Modular arithmetic
    - Integer division properties
    
    The standard library provides Zdivide for integers (Z) but lacks
    these basic properties for natural numbers (nat).
*)
Qed.  