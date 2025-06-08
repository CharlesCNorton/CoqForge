(** * Basic Contrapositive
    
    This module provides the contrapositive lemma for propositional logic
    that is not available in Coq's standard library without importing
    classical logic.
    
    Author: Charles C Norton
    Date: June 8th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Lists.List.

(** ** Overview
    
    The contrapositive states that (P → Q) → (¬Q → ¬P).
    
    This is a fundamental principle of logic, but in Coq's intuitionistic
    logic, it requires a proof. While the converse (¬Q → ¬P) → (P → Q)
    requires classical logic, this direction is constructively valid.
    
    This lemma is useful for:
    - Proof by contradiction arguments
    - Reasoning backwards from negative information
    - Converting between different forms of implications
    - Simplifying proofs involving negations
*)

(** ** Main Theorem *)

(** The contrapositive: if P implies Q, then not Q implies not P *)
Lemma contrapositive (P Q : Prop) : (P -> Q) -> (~Q -> ~P).
Proof.
  intros HPQ HnQ HP.
  (* We have HP : P and HnQ : ~Q (i.e., Q -> False) *)
  (* We need to derive False *)
  apply HnQ.
  apply HPQ.
  exact HP.
Qed.

(** ** Alternative Formulations *)

(** Contrapositive with explicit False *)
Lemma contrapositive_false (P Q : Prop) : 
  (P -> Q) -> ((Q -> False) -> (P -> False)).
Proof.
  exact (contrapositive P Q).
Qed.

(** Contrapositive for decidable propositions *)
Lemma contrapositive_bool (p q : bool) :
  (p = true -> q = true) -> (q = false -> p = false).
Proof.
  intros Hpq Hqf.
  destruct p eqn:Hp.
  - (* p = true *)
    assert (q = true) by (apply Hpq; reflexivity).
    rewrite H in Hqf. discriminate.
  - (* p = false *)
    reflexivity.
Qed.

(** ** Corollaries *)

(** Modus tollens: from P → Q and ¬Q, derive ¬P *)
Lemma modus_tollens (P Q : Prop) : (P -> Q) -> ~Q -> ~P.
Proof.
  apply contrapositive.
Qed.

(** Chain contrapositive *)
Lemma contrapositive_trans (P Q R : Prop) :
  (P -> Q) -> (Q -> R) -> (~R -> ~P).
Proof.
  intros HPQ HQR HnR.
  apply (contrapositive P R).
  - intro HP. apply HQR. apply HPQ. exact HP.
  - exact HnR.
Qed.

(** ** Examples *)

Example contrapositive_ex1 : forall n : nat,
  (n = 0 -> n + 1 = 1) -> (n + 1 <> 1 -> n <> 0).
Proof.
  intros n.
  apply (contrapositive (n = 0) (n + 1 = 1)).
Qed.

Example contrapositive_ex2 : forall (A B : Type) (l : list A) (f : A -> B),
  (l = nil -> map f l = nil) -> (map f l <> nil -> l <> nil).
Proof.
  intros A B l f.
  apply (contrapositive (l = nil) (map f l = nil)).
Qed.

(** Example with natural number ordering *)
Example contrapositive_ordering : forall n m : nat,
  (n < m -> n <> m) -> (n = m -> ~(n < m)).
Proof.
  intros n m H Heq Hlt.
  apply (contrapositive (n < m) (n <> m)).
  - exact H.
  - intro Hneq. apply Hneq. exact Heq.
  - exact Hlt.
Qed.

(** ** Notes on Classical Logic
    
    The converse of the contrapositive, namely:
    (¬Q → ¬P) → (P → Q)
    
    is NOT provable in Coq's intuitionistic logic. It requires the
    law of excluded middle or other classical axioms.
    
    However, the direction we prove here is constructively valid
    and very useful in practice.
    
    If you need the full equivalence, you must:
    Require Import Coq.Logic.Classical.
    
    But this comes with the cost of losing computational content
    in your proofs.
*)

(** ** Relation to Standard Library
    
    Interestingly, while Coq doesn't provide this basic lemma in the
    standard intuitionistic library, it does provide many specialized
    versions for specific contexts (like for boolean functions).
    
    Our general version works for any propositions and can be
    instantiated as needed.
*)