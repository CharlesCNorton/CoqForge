(** * Iterator Right Successor Property
    
    This module provides a fundamental lemma about iteration that is
    missing from Coq's standard library: iterating S n times equals
    iterating n times on the result of one application.
    
    Author: Charles C Norton
    Date: June 8th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Arith.Arith.

(** ** Overview
    
    The Nat.iter function iterates a function f a given number of times.
    This lemma states that iterating (S n) times starting from x is the
    same as iterating n times starting from (f x).
    
    In other words: f^(n+1)(x) = f^n(f(x))
    
    This property is useful for:
    - Reasoning about iterative algorithms
    - Proving properties of recursive functions
    - Optimizing iterations by pulling out initial applications
    - Converting between different iteration patterns
    - Establishing loop invariants
*)

(** ** Main Theorem *)
(** Iterating S n times equals iterating n times after one application *)
Lemma iter_succ_r {A : Type} (n : nat) (f : A -> A) (x : A) : 
  Nat.iter (S n) f x = Nat.iter n f (f x).
Proof.
  induction n as [|n' IH] in x |- *.
  - reflexivity.
  - simpl. f_equal. apply IH.
Qed.

(** ** Notes
    
    This lemma is dual to the left version (pulling out the last
    application rather than the first). The standard library doesn't
    provide either version explicitly, forcing users to unfold the
    definition of Nat.iter and reason directly.
    
    The proof is straightforward by induction on n, using the fact
    that Nat.iter is defined recursively:
    - Nat.iter 0 f x = x
    - Nat.iter (S n) f x = f (Nat.iter n f x)
*)
