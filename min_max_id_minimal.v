(** * Min/Max Idempotent Properties
    
    This module provides the fundamental idempotent properties of min and max
    that are missing from Coq's standard library.
    
    Author: Charles C Norton
    Date: June 9th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Arith.Arith.

(** ** Overview
    
    The idempotent property states that applying an operation to the same
    value twice yields that value. For min and max:
    - min n n = n
    - max n n = n
    
    These are fundamental properties that hold for any idempotent operation,
    yet they are not explicitly provided in Coq's standard library.
    
    These properties are useful for:
    - Simplifying expressions involving min/max
    - Proving properties about bounds and limits
    - Reasoning about lattice operations
    - Optimizing computations
*)

(** ** Main Theorems *)

(** min is idempotent *)
Lemma min_id (n : nat) : min n n = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(** max is idempotent *)
Lemma max_id (n : nat) : max n n = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

(** ** Corollaries *)

(** min/max with equal values *)
Lemma min_eq (n m : nat) : n = m -> min n m = n.
Proof.
  intro H.
  rewrite H.
  apply min_id.
Qed.

Lemma max_eq (n m : nat) : n = m -> max n m = n.
Proof.
  intro H.
  rewrite H.
  apply max_id.
Qed.

(** ** Examples *)

Example min_id_ex1 : min 5 5 = 5.
Proof. apply min_id. Qed.

Example max_id_ex1 : max 10 10 = 10.
Proof. apply max_id. Qed.

Example min_id_compute : min 42 42 = 42.
Proof. reflexivity. Qed.

Example max_id_compute : max 42 42 = 42.
Proof. reflexivity. Qed.

(** ** Notes
    
    These lemmas are so basic that they're often proved inline when needed,
    leading to proof clutter. Having them as standard lemmas would improve
    proof readability.
    
    The proofs are by simple induction on the natural number. Since min
    and max are defined recursively on the structure of their arguments,
    the inductive proof naturally follows this structure.
*)
