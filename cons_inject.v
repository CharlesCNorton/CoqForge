(** * List Constructor Injectivity
    
    This module provides a fundamental lemma about the injectivity of the
    list constructor [::] (cons) that is surprisingly absent from Coq's
    standard library.
    
    Author: Charles C Norton
    Date: June 7th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.10+
*)

Require Import Coq.Lists.List.
Import ListNotations.

(** ** Overview
    
    The [cons] constructor for lists is injective in both of its arguments.
    This means that if two list constructions [x :: l] and [x' :: l'] are
    equal, then we can deduce that [x = x'] and [l = l'].
    
    While Coq's [injection] tactic can derive this fact when needed during
    proofs, there is no explicit lemma in the standard library that states
    this property. This can be inconvenient when:
    
    - You need to apply the injectivity property as part of a larger
      rewriting step
    - You want to use it with tactics like [apply] or [rewrite]
    - You need to reason about list equality in a forward-reasoning style
    - You want to use it as a parameter to higher-order functions or tactics
    
    This module provides [cons_eq], which extracts the tail equality from
    an equality between two lists with the same head.
*)

(** ** Main Theorem *)

(** The [cons_eq] lemma states that if two lists constructed with the same
    head element are equal, then their tails must also be equal.
    
    More formally: For any type [A], element [x : A], and lists [l, l' : list A],
    if [x :: l = x :: l'], then [l = l'].
    
    This is a direct consequence of the injectivity of the [cons] constructor,
    but having it as an explicit lemma can simplify many proofs.
    
    Note that this lemma only extracts the tail equality. The head elements
    are already known to be equal by assumption (they are both [x]).
    
    For the more general case where the heads might be different, see the
    [injection] tactic or define a variant like [cons_eq_full].
*)
Lemma cons_eq {A : Type} (x : A) (l l' : list A) : 
  x :: l = x :: l' -> l = l'.
Proof.
  intro H.
  injection H.
  auto.
Qed.

(** ** Alternative Formulations *)

(** Sometimes you may want to extract both equalities from a cons equality.
    Here's a more general version that handles potentially different heads: *)
Lemma cons_eq_full {A : Type} (x x' : A) (l l' : list A) :
  x :: l = x' :: l' -> x = x' /\ l = l'.
Proof.
  intro H.
  injection H.
  auto.
Qed.

(** For the special case of extracting just the head equality: *)
Lemma cons_eq_head {A : Type} (x x' : A) (l l' : list A) :
  x :: l = x' :: l' -> x = x'.
Proof.
  intro H.
  injection H as H1 H2.
  exact H1.
Qed.

(** ** Examples and Applications *)

(** *** Example 1: Simple tail extraction
    
    This example demonstrates the most basic use case: extracting the
    equality of tails when we know two lists with the same head are equal.
*)
Example test_cons_eq : forall (n : nat), 
  1 :: 2 :: 3 :: nil = 1 :: 2 :: 3 :: nil -> 
  2 :: 3 :: nil = 2 :: 3 :: nil.
Proof.
  intros n H.
  apply (cons_eq 1).
  exact H.
Qed.

(** *** Example 2: Nested list equality
    
    This example shows how [cons_eq] can be applied repeatedly to peel
    off multiple elements from the front of equal lists.
*)
Lemma tail_eq_example : forall (A : Type) (x y : A) (l1 l2 : list A),
  x :: y :: l1 = x :: y :: l2 -> l1 = l2.
Proof.
  intros A x y l1 l2 H.
  (* First application: remove x from both sides *)
  apply cons_eq in H.
  (* Second application: remove y from both sides *)
  apply cons_eq in H.
  exact H.
Qed.

(** *** Example 3: Using in a larger proof
    
    This example demonstrates how [cons_eq] can be used as part of a
    larger proof about list properties.
*)
Lemma cons_eq_length : forall (A : Type) (x : A) (l1 l2 : list A),
  x :: l1 = x :: l2 -> length l1 = length l2.
Proof.
  intros A x l1 l2 H.
  (* Use cons_eq to get l1 = l2 *)
  apply cons_eq in H.
  (* Now we can rewrite with this equality *)
  rewrite H.
  reflexivity.
Qed.

(** *** Example 4: Contrapositive usage
    
    Sometimes it's useful to use the contrapositive: if the tails are
    different, then the constructed lists are different.
*)
Lemma cons_neq : forall (A : Type) (x : A) (l1 l2 : list A),
  l1 <> l2 -> x :: l1 <> x :: l2.
Proof.
  intros A x l1 l2 H_neq H_eq.
  (* If x :: l1 = x :: l2, then by cons_eq, l1 = l2 *)
  apply cons_eq in H_eq.
  (* But this contradicts H_neq *)
  contradiction.
Qed.

(** ** Related Concepts and Tactics
    
    - [injection]: A tactic that can derive injectivity facts for any
      constructor. Use this when you don't need a lemma form.
      
    - [discriminate]: A tactic that can prove inequalities between terms
      built with different constructors (e.g., [nil <> x :: l]).
      
    - [inversion]: A more powerful tactic that combines [injection] and
      [discriminate] and can also handle inductive predicates.
      
    - [f_equal]: Can be used to prove the reverse direction - if the
      arguments are equal, then the constructed terms are equal.
      
    See also:
    - The [List] module in Coq's standard library
    - Software Foundations, chapter on Lists
    - Coq'Art, section on inductive types
*)

(** ** Technical Notes
    
    1. The lemma is universe polymorphic (works for any [Type], not just [Set])
    
    2. The proof is trivial using [injection], but having it as a lemma
       allows for more flexible usage patterns
       
    3. This pattern extends to other inductive types - any constructor is
       injective in all its arguments
       
    4. In dependent type theory, injectivity of constructors is a fundamental
       property that follows from the way inductive types are defined
*)
