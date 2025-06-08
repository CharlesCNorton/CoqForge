(** * Boolean Decidability
    
    This module provides the decidability lemma for boolean equality
    that is missing from Coq's standard library.
    
    Author: Charles C Norton
    Date: June 8th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Bool.Bool.

(** ** Overview
    
    This lemma states that for any boolean value, we can computationally
    decide whether it equals true or false. While trivial, this is
    surprisingly not provided in the standard library.
    
    This lemma is useful for:
    - Converting between boolean computations and propositions
    - Case analysis in boolean functions
    - Building decision procedures
    - Avoiding awkward destruct patterns in proofs
*)

(** ** Main Theorem *)

(** For any boolean b, either b = true or b = false (computationally) *)
Lemma bool_dec : forall b : bool, {b = true} + {b = false}.
Proof.
  intro b.
  destruct b.
  - left. reflexivity.
  - right. reflexivity.
Qed.

(** ** Examples *)

Example bool_dec_ex1 : {true = true} + {true = false}.
Proof.
  apply bool_dec.
Qed.

Example bool_dec_usage : forall (f : nat -> bool) (n : nat),
  {f n = true} + {f n = false}.
Proof.
  intros f n.
  apply bool_dec.
Qed.

(** ** Notes
    
    This is a sumbool ({A} + {B}) rather than a regular disjunction
    (A \/ B), which means it provides computational content - we can
    actually use this in programs to make decisions, not just in proofs.
    
    Compare with the non-computational version that requires only:
    Lemma bool_classic : forall b : bool, b = true \/ b = false.
    
    The decidable version is strictly more useful.
*)