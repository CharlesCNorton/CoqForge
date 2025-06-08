(** * Map Function Composition
    
    This module provides the fundamental lemma about composing functions
    within list map operations, which is missing from Coq's standard library.
    
    Author: Charles C Norton
    Date: June 8th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(** ** Overview
    
    The map function composition law states that mapping a composition
    of functions is the same as composing the maps:
    
    map (f ∘ g) = map f ∘ map g
    
    In Coq syntax: map (fun x => f (g x)) l = map f (map g l)
    
    This is a fundamental property of functors in category theory and
    a basic optimization rule in functional programming.
    
    This lemma is essential for:
    - Optimizing list processing by fusing traversals
    - Reasoning about function composition in data structures
    - Proving properties of functional programs
    - Establishing functor laws for lists
    
    Without this lemma, users must prove it repeatedly using induction,
    cluttering proofs with routine details.
*)

(** ** Main Theorem *)

(** Mapping a function composition equals composing the maps *)
Lemma map_compose {A B C : Type} (f : B -> C) (g : A -> B) (l : list A) :
  map (fun x => f (g x)) l = map f (map g l).
Proof.
  induction l as [|h t IH].
  - (* Base case: empty list *)
    reflexivity.
  - (* Inductive case: h :: t *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(** ** Alternative Formulations *)

(** Version with explicit function composition *)
Lemma map_compose_explicit {A B C : Type} (f : B -> C) (g : A -> B) :
  forall l : list A,
  map (fun x => f (g x)) l = map f (map g l).
Proof.
  apply map_compose.
Qed.

(** ** Corollaries *)

(** Helper: map with extensionally equal functions *)
Lemma map_ext {A B : Type} (f g : A -> B) (l : list A) :
  (forall x, f x = g x) -> map f l = map g l.
Proof.
  intro H.
  induction l as [|h t IH].
  - reflexivity.
  - simpl. rewrite H. rewrite IH. reflexivity.
Qed.

(** Triple composition *)
Lemma map_compose3 {A B C D : Type} (f : C -> D) (g : B -> C) (h : A -> B) (l : list A) :
  map (fun x => f (g (h x))) l = map f (map g (map h l)).
Proof.
  rewrite <- map_compose.
  rewrite <- map_compose.
  reflexivity.
Qed.

(** Identity function property *)
Lemma map_id {A : Type} (l : list A) :
  map (fun x => x) l = l.
Proof.
  induction l as [|h t IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** Composition with identity *)
Lemma map_compose_id_l {A B : Type} (f : A -> B) (l : list A) :
  map (fun x => (fun y => y) (f x)) l = map f l.
Proof.
  (* The function simplifies directly: (fun y => y) (f x) = f x *)
  induction l as [|h t IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** ** Examples *)

(** Basic computational example *)
Example map_compose_compute : 
  map (fun n => n + 1) (map (fun n => n * 2) [1; 2; 3]) = [3; 5; 7].
Proof.
  reflexivity.
Qed.

(** Simplest use of map_compose *)
Example map_compose_simple : forall (A B C : Type) (f : B -> C) (g : A -> B) (l : list A),
  map (fun x => f (g x)) l = map f (map g l).
Proof.
  intros.
  apply map_compose.
Qed.

(** Concrete example with nat *)
Example map_compose_nat : forall (l : list nat),
  map (fun n => S (n * 2)) l = map S (map (fun n => n * 2) l).
Proof.
  intro l.
  apply map_compose.
Qed.

(** Optimization example - showing map fusion *)
Example map_compose_optimize : 
  map S (map S (map S [0; 1; 2])) = [3; 4; 5].
Proof.
  reflexivity.
Qed.

(** General fusion principle *)
Example map_fusion : forall (l : list nat),
  map S (map S l) = map (fun n => S (S n)) l.
Proof.
  intro l.
  (* map_compose gives us: map (fun x => f (g x)) l = map f (map g l) *)
  (* We want the reverse direction *)
  symmetry.
  apply map_compose.
Qed.

(** ** Functor Laws *)

(** Identity function *)
Definition id {A : Type} : A -> A := fun x => x.

(** Lists form a functor, and map_compose is one of the functor laws *)

(** Functor law 1: map preserves identity *)
Lemma map_functor_id {A : Type} : forall (l : list A),
  map id l = l.
Proof.
  apply map_id.
Qed.

(** Functor law 2: map preserves composition *)
Lemma map_functor_compose {A B C : Type} : forall (f : B -> C) (g : A -> B) (l : list A),
  map (fun x => f (g x)) l = map f (map g l).
Proof.
  intros.
  apply map_compose.
Qed.

(** ** Performance Note
    
    In functional programming, map fusion (using map_compose in reverse)
    is an important optimization. Instead of traversing a list multiple
    times:
    
    map f (map g l)  -- traverses l twice
    
    We can fuse the maps:
    
    map (fun x => f (g x)) l  -- traverses l once
    
    This lemma proves that this optimization is correct.
*)

(** ** Relation to Standard Library
    
    The standard library provides many lemmas about map:
    - map_app : map f (l ++ l') = map f l ++ map f l'
    - map_rev : map f (rev l) = rev (map f l)
    - map_length : length (map f l) = length l
    
    But somehow misses this fundamental composition property!
    
    Some libraries (like MathComp) do include this, but it should
    be in the core library given how fundamental it is.
*)
