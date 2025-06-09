(** * Fold Left Empty List
    
    This module provides the fundamental lemma about fold_left on empty lists
    that is missing from Coq's standard library.
    
    Author: Charles C Norton
    Date: June 9th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(** ** Overview
    
    The fold_left function processes a list with an accumulator, but the
    base case (empty list) doesn't have an explicit lemma in the standard
    library. This lemma states:
    
    fold_left f [] a0 = a0
    
    While trivial (it follows directly from the definition), having this
    as an explicit lemma improves proof readability and automation.
    
    This property is useful for:
    - Base cases in inductive proofs about fold_left
    - Simplifying expressions involving fold_left
    - Teaching the behavior of fold operations
    - Automated simplification tactics
    - Reasoning about accumulator-based algorithms
*)

(** ** Main Theorem *)

(** fold_left on empty list returns initial value *)
Lemma fold_left_nil {A B : Type} (f : A -> B -> A) (a0 : A) :
  fold_left f [] a0 = a0.
Proof.
  reflexivity.
Qed.

(** ** Alternative Names *)

(** Some users might look for this under different names *)
Lemma fold_left_empty {A B : Type} (f : A -> B -> A) (a0 : A) :
  fold_left f [] a0 = a0.
Proof.
  apply fold_left_nil.
Qed.

Lemma fold_left_base {A B : Type} (f : A -> B -> A) (a0 : A) :
  fold_left f [] a0 = a0.
Proof.
  apply fold_left_nil.
Qed.

(** ** Corollaries *)

(** Specialized for common operations *)
Lemma fold_left_nil_plus (n : nat) :
  fold_left plus [] n = n.
Proof.
  apply fold_left_nil.
Qed.

Lemma fold_left_nil_app {A : Type} (l : list A) :
  fold_left (@app A) [] l = l.
Proof.
  apply fold_left_nil.
Qed.

(** Composition with other operations *)
Lemma fold_left_nil_map {A B C : Type} (f : B -> C -> B) (g : A -> C) (b : B) :
  fold_left f (map g []) b = b.
Proof.
  simpl. reflexivity.
Qed.

(** ** Examples *)

Example fold_left_nil_ex1 : fold_left plus [] 10 = 10.
Proof. reflexivity. Qed.

Example fold_left_nil_ex2 : fold_left mult [] 1 = 1.
Proof. reflexivity. Qed.

Example fold_left_nil_ex3 : 
  fold_left (fun acc x => x :: acc) [] (@nil nat) = [].
Proof. reflexivity. Qed.

(** Using the lemma in a larger proof *)
Example fold_left_singleton : forall {A B : Type} (f : A -> B -> A) (a : A) (b : B),
  fold_left f [b] a = f a b.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

(** Simplifying complex expressions *)
Example simplify_fold : forall {A B : Type} (f : A -> B -> A) (a : A) (l : list B),
  l = [] -> fold_left f l a = a.
Proof.
  intros A B f a l H.
  rewrite H.
  apply fold_left_nil.
Qed.

(** ** Related Properties *)

(** fold_right on empty list *)
Lemma fold_right_nil {A B : Type} (f : A -> B -> B) (b : B) :
  fold_right f b [] = b.
Proof.
  reflexivity.
Qed.

(** Relationship between fold_left and fold_right on empty list *)
Lemma fold_left_right_nil {A : Type} (f : A -> A -> A) (a : A) :
  fold_left f [] a = fold_right f a [].
Proof.
  reflexivity.
Qed.

(** ** Notes
    
    This is perhaps the most trivial lemma missing from the standard library.
    The proof is just reflexivity since fold_left is defined as:
    
    Fixpoint fold_left (f : B -> A -> B) (l : list A) (b : B) : B :=
      match l with
      | [] => b
      | x :: xs => fold_left f xs (f b x)
      end.
    
    So fold_left f [] b immediately reduces to b.
    
    Despite its triviality, having this lemma explicit makes many proofs
    cleaner, especially when teaching or when building automation tactics
    that need to recognize this pattern.
*)
