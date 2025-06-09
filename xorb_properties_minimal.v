(** * Boolean XOR Properties
    
    This module provides fundamental properties of the boolean XOR operation
    that are missing from Coq's standard library.
    
    Author: Charles C Norton
    Date: June 9th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope list_scope.

(** ** Overview
    
    The boolean XOR (exclusive or) operation has several fundamental properties
    that are not explicitly provided in Coq's standard library:
    
    - Nilpotency: xorb b b = false (XORing a value with itself gives false)
    - Left identity: xorb false b = b (false is the identity element)
    
    While xorb is defined in the standard library, these basic properties
    require manual proof each time they're needed.
    
    These properties are useful for:
    - Simplifying boolean expressions
    - Proving properties of cryptographic algorithms
    - Reasoning about parity and checksums
    - Optimizing boolean circuits
    - Teaching fundamental properties of XOR
*)

(** ** Main Theorems *)

(** XOR is nilpotent *)
Lemma xorb_nilpotent (b : bool) : xorb b b = false.
Proof.
  destruct b; reflexivity.
Qed.

(** XOR with false is identity *)
Lemma xorb_false_l (b : bool) : xorb false b = b.
Proof.
  reflexivity.
Qed.

(** ** Corollaries *)

(** Right identity *)
Lemma xorb_false_r (b : bool) : xorb b false = b.
Proof.
  destruct b; reflexivity.
Qed.

(** XOR with true is negation *)
Lemma xorb_true_l (b : bool) : xorb true b = negb b.
Proof.
  destruct b; reflexivity.
Qed.

Lemma xorb_true_r (b : bool) : xorb b true = negb b.
Proof.
  destruct b; reflexivity.
Qed.

(** Double XOR *)
Lemma xorb_cancel_l (a b : bool) : xorb a (xorb a b) = b.
Proof.
  destruct a, b; reflexivity.
Qed.

Lemma xorb_cancel_r (a b : bool) : xorb (xorb a b) b = a.
Proof.
  destruct a, b; reflexivity.
Qed.

(** ** Examples *)

Example xorb_nilpotent_ex1 : xorb true true = false.
Proof. reflexivity. Qed.

Example xorb_nilpotent_ex2 : xorb false false = false.
Proof. reflexivity. Qed.

Example xorb_false_l_ex : xorb false true = true.
Proof. reflexivity. Qed.

(** Using nilpotency for simplification *)
Example simplify_xor : forall b c : bool,
  xorb b (xorb b c) = c.
Proof.
  intros b c.
  apply xorb_cancel_l.
Qed.

(** Swap encryption example *)
Example xor_swap : forall a b : bool,
  let a' := xorb a b in
  let b' := xorb a' b in
  let a'' := xorb a' b' in
  a'' = b /\ b' = a.
Proof.
  intros a b.
  simpl.
  split.
  - rewrite xorb_cancel_l. reflexivity.
  - rewrite xorb_cancel_r. reflexivity.
Qed.

(** ** Extended Properties *)

(** Commutativity (already in standard library, shown for completeness) *)
Lemma xorb_comm (a b : bool) : xorb a b = xorb b a.
Proof.
  destruct a, b; reflexivity.
Qed.

(** Associativity (already in standard library, shown for completeness) *)
Lemma xorb_assoc (a b c : bool) : xorb a (xorb b c) = xorb (xorb a b) c.
Proof.
  destruct a, b, c; reflexivity.
Qed.

(** XOR forms an abelian group *)
Lemma xorb_group_inverse (b : bool) : xorb b b = false.
Proof.
  apply xorb_nilpotent.
Qed.

Lemma xorb_group_identity (b : bool) : xorb false b = b.
Proof.
  apply xorb_false_l.
Qed.

(** Interaction with other boolean operations *)
Lemma xorb_andb_distrib_r (a b c : bool) :
  xorb (andb a c) (andb b c) = andb (xorb a b) c.
Proof.
  destruct a, b, c; reflexivity.
Qed.

Lemma xorb_negb (a : bool) : xorb a (negb a) = true.
Proof.
  destruct a; reflexivity.
Qed.

Lemma negb_xorb (a b : bool) : negb (xorb a b) = xorb (negb a) b.
Proof.
  destruct a, b; reflexivity.
Qed.

(** ** Applications *)

(** Parity function *)
Definition parity (l : list bool) : bool :=
  fold_left xorb l false.

(** Auxiliary lemma for parity *)
Lemma fold_left_xorb_init (l : list bool) (init : bool) :
  fold_left xorb l init = xorb init (fold_left xorb l false).
Proof.
  revert init.
  induction l as [|h t IH]; intro init; simpl.
  - rewrite xorb_false_r. reflexivity.
  - rewrite IH. rewrite (IH h). 
    rewrite xorb_assoc, (xorb_comm init h), <- xorb_assoc.
    reflexivity.
Qed.

Lemma parity_app (l1 l2 : list bool) :
  parity (l1 ++ l2) = xorb (parity l1) (parity l2).
Proof.
  unfold parity.
  rewrite fold_left_app.
  apply fold_left_xorb_init.
Qed.

(** ** Notes
    
    XOR is a fundamental boolean operation with many important properties.
    The nilpotent property (b ⊕ b = false) and identity property (false ⊕ b = b)
    are particularly basic, yet they're missing from the standard library.
    
    These properties show that booleans with XOR form an abelian group,
    with false as the identity and each element as its own inverse.
    This algebraic structure is the foundation for many applications
    in computer science, from error correction to cryptography.
    
    The proofs are all by simple case analysis on booleans, reflecting
    the computational nature of these properties.
*)
