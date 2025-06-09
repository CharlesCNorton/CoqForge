(** * Power Function Properties
    
    This module provides fundamental properties of the power function (exponentiation)
    that are missing from Coq's standard library.
    
    Author: Charles C Norton
    Date: June 9th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Arith.Arith.
Require Import Lia.

(** ** Overview
    
    The power function (^ in Coq) has several fundamental properties that
    are not explicitly provided in Coq's standard library:
    
    - 0^n = 0 for all n > 0
    - 1^n = 1 for all n
    
    These are basic algebraic properties that users must prove repeatedly.
    
    These properties are useful for:
    - Simplifying arithmetic expressions
    - Proving properties of exponential algorithms
    - Reasoning about geometric series
    - Teaching basic exponentiation rules
    - Optimizing power computations
*)

(** ** Main Theorems *)

(** 0 to any positive power is 0 *)
Lemma pow_0_l (n : nat) : n <> 0 -> 0 ^ n = 0.
Proof.
  intro H.
  destruct n.
  - contradiction.
  - reflexivity.
Qed.

(** 1 to any power is 1 *)
Lemma pow_1_l (n : nat) : 1 ^ n = 1.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(** ** Corollaries *)

(** Zero to successor *)
Lemma pow_0_succ (n : nat) : 0 ^ (S n) = 0.
Proof.
  reflexivity.
Qed.

(** Special case for squared *)
Lemma zero_squared : 0 ^ 2 = 0.
Proof.
  reflexivity.
Qed.

Lemma one_squared : 1 ^ 2 = 1.
Proof.
  reflexivity.
Qed.

(** Power preserves identity *)
Lemma pow_1_r (n : nat) : n ^ 1 = n.
Proof.
  simpl. apply Nat.mul_1_r.
Qed.

(** ** Examples *)

Example pow_0_l_ex1 : 0 ^ 5 = 0.
Proof. reflexivity. Qed.

Example pow_0_l_ex2 : 0 ^ 100 = 0.
Proof. reflexivity. Qed.

Example pow_1_l_ex1 : 1 ^ 7 = 1.
Proof. reflexivity. Qed.

Example pow_1_l_ex2 : 1 ^ 1000 = 1.
Proof. reflexivity. Qed.

(** Using the lemmas *)
Example simplify_expr : forall n : nat,
  n <> 0 -> 0 ^ n + 1 ^ n = 1.
Proof.
  intros n H.
  rewrite pow_0_l by assumption.
  rewrite pow_1_l.
  reflexivity.
Qed.

(** Product of powers *)
Example pow_product : forall n : nat,
  1 ^ n * 1 ^ n = 1.
Proof.
  intro n.
  rewrite !pow_1_l.
  reflexivity.
Qed.

(** ** Extended Properties *)

(** Powers of 2 *)
Lemma pow_2_pos (n : nat) : 0 < 2 ^ n.
Proof.
  induction n.
  - simpl. auto.
  - simpl. lia.
Qed.

(** Monotonicity for base 0 *)
Lemma pow_0_le (n m : nat) : n <= m -> 0 ^ m <= 0 ^ n.
Proof.
  intros H.
  destruct n, m; simpl; auto.
  - inversion H.
  - lia.
Qed.

(** Powers of successor of 1 *)
Lemma pow_2_double (n : nat) : 2 ^ (S n) = 2 * 2 ^ n.
Proof.
  reflexivity.
Qed.

(** Interaction with addition *)
Lemma pow_1_add (n m : nat) : 1 ^ (n + m) = 1 ^ n * 1 ^ m.
Proof.
  rewrite !pow_1_l.
  reflexivity.
Qed.

(** Non-zero base gives non-zero result *)
Lemma pow_nonzero (a n : nat) : a <> 0 -> a ^ n <> 0.
Proof.
  intros Ha.
  induction n.
  - simpl. auto.
  - simpl. 
    intro H.
    apply Nat.eq_mul_0 in H.
    destruct H; contradiction.
Qed.

(** ** Special Cases and Edge Cases *)

(** The special case 0^0 = 1 by definition in Coq *)
Example pow_0_0 : 0 ^ 0 = 1.
Proof. reflexivity. Qed.

(** Empty product convention *)
Lemma pow_n_0 (n : nat) : n ^ 0 = 1.
Proof. reflexivity. Qed.

(** ** Notes
    
    These properties are fundamental to working with exponentiation but
    are missing from Coq's standard library. The proofs are straightforward:
    
    - For 0^n with n > 0: The recursive definition immediately gives 0
    - For 1^n: By induction, using the fact that 1 * 1 = 1
    
    The standard library does provide many other power properties
    (like a^(n+m) = a^n * a^m), but these basic special cases for
    0 and 1 are curiously absent.
    
    Note that Coq follows the standard convention that 0^0 = 1, which
    is the empty product interpretation and the most useful choice for
    computer science applications.
*)
