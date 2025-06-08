(** * Square of Sum Identity
    
    This module provides the fundamental algebraic identity for the square
    of a sum, which is missing from Coq's standard library.
    
    Author: Charles C Norton
    Date: June 8th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Arith.Arith.

(** ** Overview
    
    The square of a sum identity states that (n + m)² = n² + 2nm + m².
    This is one of the most basic algebraic identities, yet it's not
    explicitly provided in Coq's standard library.
    
    This identity is useful for:
    - Simplifying arithmetic expressions
    - Proving properties about quadratic forms
    - Reasoning about distance metrics
    - Optimizing arithmetic computations
    - Teaching fundamental algebra concepts
*)

(** ** Main Theorem *)

(** The square of a sum equals the sum of squares plus twice the product *)
Lemma square_of_sum (n m : nat) :
  (n + m) * (n + m) = n * n + 2 * n * m + m * m.
Proof.
  ring.
Qed.

(** ** Corollaries *)

(** Square of successor *)
Lemma square_of_successor (n : nat) :
  S n * S n = n * n + 2 * n + 1.
Proof.
  rewrite <- Nat.add_1_r.
  rewrite square_of_sum.
  rewrite Nat.mul_1_r, Nat.mul_1_l.
  reflexivity.
Qed.

(** Square of double *)
Lemma square_of_double (n : nat) :
  (2 * n) * (2 * n) = 4 * n * n.
Proof.
  ring.
Qed.

(** Square of sum with zero *)
Lemma square_of_sum_0_r (n : nat) :
  (n + 0) * (n + 0) = n * n.
Proof.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

(** ** Examples *)

(** Basic computational example *)
Example square_of_sum_ex1 : (3 + 4) * (3 + 4) = 49.
Proof.
  rewrite square_of_sum.
  (* 3 * 3 + 2 * 3 * 4 + 4 * 4 = 9 + 24 + 16 = 49 *)
  reflexivity.
Qed.

(** Using the lemma in a proof *)
Example square_of_sum_ex2 : forall n : nat,
  (n + 1) * (n + 1) = n * n + 2 * n + 1.
Proof.
  intro n.
  rewrite square_of_sum.
  (* n * n + 2 * n * 1 + 1 * 1 = n * n + 2 * n + 1 *)
  rewrite Nat.mul_1_r.
  rewrite Nat.mul_1_l.
  reflexivity.
Qed.

(** Showing (a+b)² ≠ a² + b² in general *)
Example square_sum_not_additive : 
  exists a b : nat, (a + b) * (a + b) <> a * a + b * b.
Proof.
  exists 1, 1.
  intro H.
  (* (1 + 1)² = 4, but 1² + 1² = 2 *)
  assert (4 = 2).
  - simpl in H. exact H.
  - discriminate.
Qed.

(** Computing squares efficiently *)
Example compute_square_25 : 25 * 25 = 625.
Proof.
  (* 25 = 20 + 5 *)
  change 25 with (20 + 5).
  rewrite square_of_sum.
  (* 20² + 2×20×5 + 5² = 400 + 200 + 25 = 625 *)
  reflexivity.
Qed.

(** Mental math trick *)
Example mental_math_square : forall n : nat,
  (10 * n + 5) * (10 * n + 5) = 100 * n * n + 100 * n + 25.
Proof.
  intro n.
  rewrite square_of_sum.
  (* Simplify 10n × 10n + 2×10n×5 + 5×5 *)
  ring.
Qed.

(** ** Properties *)

(** Commutativity of the expansion *)
Lemma square_of_sum_comm (n m : nat) :
  (n + m) * (n + m) = (m + n) * (m + n).
Proof.
  rewrite Nat.add_comm.
  reflexivity.
Qed.

(** Expansion is symmetric in n and m *)
Lemma square_of_sum_symm (n m : nat) :
  n * n + 2 * n * m + m * m = m * m + 2 * m * n + n * n.
Proof.
  ring.
Qed.

(** Triple sum (first step of expansion) *)
Lemma square_of_triple_sum_partial (a b c : nat) :
  (a + b + c) * (a + b + c) = 
  (a + b) * (a + b) + 2 * (a + b) * c + c * c.
Proof.
  ring.
Qed.

(** ** Notes
    
    This proof uses the ring tactic, which can automatically prove
    polynomial identities over semirings (like nat). While the proof
    is trivial with ring, having this as an explicit lemma allows
    for direct rewriting in larger proofs.
    
    The identity generalizes to any commutative semiring, but we
    state it for nat as that's the most common use case.
    
    Note that natural number subtraction makes some related identities
    (like square of difference) more complex to state and prove. For
    full algebraic manipulation, integers (Z) are often more convenient.
*)
