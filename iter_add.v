(** * Iterator Addition Property
    
    This module provides a fundamental lemma about iteration composition
    that is missing from Coq's standard library: iterating (n1 + n2) times
    equals iterating n2 times, then n1 times.
    
    Author: Charles C Norton
    Date: June 8th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Arith.Arith.

(** ** Overview
    
    The Nat.iter function iterates a function f a given number of times.
    This lemma states that iterating (n1 + n2) times is the same as
    first iterating n2 times, then iterating n1 times on the result.
    
    In mathematical notation: f^(n1+n2)(x) = f^n1(f^n2(x))
    
    This property is useful for:
    - Decomposing complex iterations into simpler parts
    - Reasoning about loop fusion and splitting
    - Proving properties of iterative algorithms
    - Optimizing nested loops
    - Establishing equivalences between different iteration strategies
*)

(** ** Main Theorem *)

(** Iterating (n1 + n2) times equals composing n1 and n2 iterations *)
Lemma iter_add {A : Type} (n1 n2 : nat) (f : A -> A) (x : A) : 
  Nat.iter (n1 + n2) f x = Nat.iter n1 f (Nat.iter n2 f x).
Proof.
  induction n1 as [|n1' IH] in x |- *.
  - (* Base case: n1 = 0 *)
    (* Nat.iter (0 + n2) f x = Nat.iter n2 f x *)
    (* Nat.iter 0 f (Nat.iter n2 f x) = Nat.iter n2 f x *)
    simpl.
    reflexivity.
  - (* Inductive case: n1 = S n1' *)
    (* Nat.iter (S n1' + n2) f x = Nat.iter (S n1') f (Nat.iter n2 f x) *)
    simpl.
    (* f (Nat.iter (n1' + n2) f x) = f (Nat.iter n1' f (Nat.iter n2 f x)) *)
    f_equal.
    apply IH.
Qed.

(** ** Notes
    
    This lemma shows that iteration distributes over addition in the
    expected way. Together with iter_succ_r, it provides a complete
    toolkit for reasoning about iteration counts.
    
    The proof is by induction on n1, which makes the structure cleaner
    than inducting on n2. The key insight is that:
    - Nat.iter 0 f y = y (identity)
    - Nat.iter (S n) f y = f (Nat.iter n f y) (recursive step)
    
    This fundamental property should be in the standard library but isn't,
    forcing users to reprove it whenever they need to reason about
    composed iterations.
*)
