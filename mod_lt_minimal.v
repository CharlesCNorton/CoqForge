(** * Modulo Upper Bound Property
    
    This module provides the fundamental property that the modulo operation
    always yields a result less than the divisor, which is surprisingly not
    explicitly stated in Coq's standard library.
    
    Author: Charles C Norton
    Date: June 9th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Arith.Arith.
Require Import Lia.

(** ** Overview
    
    The modulo operation has a fundamental property: for any natural numbers
    a and b with b ≠ 0, we have a mod b < b.
    
    This is THE most basic property of modulo, establishing that the remainder
    is always strictly less than the divisor. While Nat.mod_upper_bound exists,
    the simple name "mod_lt" is what users naturally look for.
    
    This property is essential for:
    - Proving termination of algorithms using modulo
    - Establishing bounds in modular arithmetic
    - Array indexing with wraparound
    - Hash table implementations
    - Circular buffer algorithms
*)

(** ** Main Theorem *)

(** a mod b < b when b <> 0 *)
Lemma mod_lt (a b : nat) : b <> 0 -> a mod b < b.
Proof.
  intro H.
  apply Nat.mod_upper_bound.
  exact H.
Qed.

(** ** Alternative Names *)

(** Some users might look for this under different names *)
Lemma mod_bound (a b : nat) : b <> 0 -> a mod b < b.
Proof. apply mod_lt. Qed.

Lemma mod_less (a b : nat) : b <> 0 -> a mod b < b.
Proof. apply mod_lt. Qed.

(** ** Corollaries *)

(** Modulo is always less than or equal to a - 1 *)
Lemma mod_le_pred (a b : nat) : b <> 0 -> a mod b <= b - 1.
Proof.
  intro H.
  assert (a mod b < b) by (apply mod_lt; exact H).
  lia.
Qed.

(** Special case for positive b *)
Lemma mod_lt_pos (a b : nat) : 0 < b -> a mod b < b.
Proof.
  intro H.
  apply mod_lt.
  lia.
Qed.

(** Modulo by successor *)
Lemma mod_S_lt (a n : nat) : a mod (S n) < S n.
Proof.
  apply mod_lt.
  discriminate.
Qed.

(** ** Examples *)

Example mod_lt_ex1 : 10 mod 3 < 3.
Proof. 
  assert (H: 3 <> 0) by discriminate.
  apply (mod_lt 10 3 H).
Qed.

Example mod_lt_ex2 : 100 mod 7 < 7.
Proof. 
  assert (H: 7 <> 0) by discriminate.
  apply (mod_lt 100 7 H).
Qed.

Example mod_lt_ex3 : forall n, n mod 2 < 2.
Proof.
  intro n.
  apply mod_lt.
  discriminate.
Qed.

(** Using in array bounds *)
Example array_index_safe : forall (index size : nat),
  size <> 0 -> index mod size < size.
Proof.
  intros index size H.
  apply mod_lt.
  exact H.
Qed.

(** Circular buffer example *)
Example circular_buffer : forall (pos bufsize : nat),
  bufsize <> 0 -> (pos + 1) mod bufsize < bufsize.
Proof.
  intros pos bufsize H.
  apply mod_lt.
  exact H.
Qed.

(** ** Extended Properties *)

(** Modulo 1 is always 0 *)
Lemma mod_1_eq_0 (n : nat) : n mod 1 = 0.
Proof.
  apply Nat.mod_1_r.
Qed.

(** Modulo gives 0 or 1 for mod 2 *)
Lemma mod_2_cases (n : nat) : n mod 2 = 0 \/ n mod 2 = 1.
Proof.
  assert (n mod 2 < 2) by (apply mod_lt; discriminate).
  lia.
Qed.

(** Upper bound in terms of divisor *)
Lemma mod_lt_iff (a b : nat) : 
  b <> 0 -> (a mod b < b <-> True).
Proof.
  intro H.
  split.
  - intro; exact I.
  - intro; apply mod_lt; exact H.
Qed.

(** Modulo is in range [0, b) *)
Lemma mod_range (a b : nat) : 
  b <> 0 -> 0 <= a mod b < b.
Proof.
  intro H.
  split.
  - apply Nat.le_0_l.
  - apply mod_lt; exact H.
Qed.

(** ** Related Theorems *)

(** Division and modulo relationship *)
Lemma div_mod_lt (a b : nat) :
  b <> 0 -> a = b * (a / b) + (a mod b) /\ a mod b < b.
Proof.
  intro H.
  split.
  - apply Nat.div_mod; exact H.
  - apply mod_lt; exact H.
Qed.

(** If a < b then a mod b = a *)
Lemma mod_small (a b : nat) : a < b -> a mod b = a.
Proof.
  apply Nat.mod_small.
Qed.

(** ** Notes
    
    This is one of the most fundamental properties of the modulo operation,
    yet it's not available under this simple name in the standard library.
    Users have to know to look for Nat.mod_upper_bound instead.
    
    The property is so basic that it's often needed in:
    - Loop bounds when cycling through arrays
    - Hash functions (hash mod table_size)
    - Cryptographic operations
    - Clock arithmetic
    
    Having it available as mod_lt makes proofs more readable and discoverable.
*)
