(** * Option Map Composition
    
    This module provides the fundamental lemma about composing functions
    within option map operations, which is missing from Coq's standard library.
    
    Author: Charles C Norton
    Date: June 9th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Init.Datatypes.

(** ** Overview
    
    The option_map composition law states that mapping a composition
    of functions is the same as composing the maps:
    
    option_map (f ∘ g) = option_map f ∘ option_map g
    
    In Coq syntax: option_map (fun x => f (g x)) o = option_map f (option_map g o)
    
    This is a fundamental property of functors in category theory and
    the option type's version of the map_compose lemma for lists.
    
    This lemma is essential for:
    - Optimizing option processing by fusing traversals
    - Reasoning about function composition in error-handling code
    - Establishing functor laws for option types
    - Simplifying nested option_map calls
*)

(** ** Main Theorem *)

(** option_map composition: same as map_compose but for options *)
Lemma option_map_compose {A B C : Type} (f : B -> C) (g : A -> B) (o : option A) :
  option_map (fun x => f (g x)) o = option_map f (option_map g o).
Proof.
  destruct o; reflexivity.
Qed.

(** ** Corollaries *)

(** Identity function property *)
Lemma option_map_id {A : Type} (o : option A) :
  option_map (fun x => x) o = o.
Proof.
  destruct o; reflexivity.
Qed.

(** Triple composition *)
Lemma option_map_compose3 {A B C D : Type} (f : C -> D) (g : B -> C) (h : A -> B) (o : option A) :
  option_map f (option_map g (option_map h o)) = option_map (fun x => f (g (h x))) o.
Proof.
  rewrite <- option_map_compose.
  rewrite <- option_map_compose.
  reflexivity.
Qed.

(** ** Examples *)

(** Quick test *)
Example test : option_map S (option_map S (Some 0)) = Some 2.
Proof. reflexivity. Qed.

(** Example with None *)
Example test_none : option_map S (option_map S None) = (@None nat).
Proof. reflexivity. Qed.

(** Example using the lemma *)
Example test_compose : forall n : option nat,
  option_map (fun x => x + 1) (option_map (fun x => x * 2) n) = 
  option_map (fun x => x * 2 + 1) n.
Proof.
  intro n.
  rewrite <- option_map_compose.
  reflexivity.
Qed.

(** ** Notes
    
    This lemma is the option type's instance of the functor composition law.
    The proof is simpler than the list version (map_compose) because options
    have only two cases (Some/None) rather than requiring induction.
    
    The standard library provides option_map but lacks this fundamental
    composition property, forcing users to prove it repeatedly.
*)
