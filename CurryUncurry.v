(** * Curry-Uncurry Logical Equivalence
    
    This module provides the fundamental curry/uncurry equivalence for
    implications that is missing from Coq's standard library.
    
    Author: Charles C Norton
    Date: June 8th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

(** ** Overview
    
    The curry/uncurry equivalence states that an implication from a
    conjunction is equivalent to a nested implication:
    ((P ∧ Q) → R) ↔ (P → Q → R)
    
    This fundamental logical principle connects two ways of expressing
    multi-argument implications.
    
    This lemma is useful for:
    - Converting between different proof styles
    - Simplifying hypothesis management in proofs  
    - Transforming lemma statements to more convenient forms
    - Functional programming analogies in type theory
*)

(** ** Main Theorem *)

(** Curry-uncurry equivalence for implications *)
Lemma curry_uncurry : forall P Q R : Prop,
  ((P /\ Q) -> R) <-> (P -> Q -> R).
Proof.
  intros P Q R.
  split.
  - (* curry direction: ((P ∧ Q) → R) → (P → Q → R) *)
    intros H HP HQ.
    apply H.
    split; assumption.
  - (* uncurry direction: (P → Q → R) → ((P ∧ Q) → R) *)
    intros H [HP HQ].
    apply H; assumption.
Qed.

(** ** Named Directional Lemmas *)

(** Curry: convert conjunction to nested implications *)
Lemma curry : forall P Q R : Prop,
  ((P /\ Q) -> R) -> (P -> Q -> R).
Proof.
  intros P Q R H HP HQ.
  apply H.
  split; assumption.
Qed.

(** Uncurry: convert nested implications to conjunction *)
Lemma uncurry : forall P Q R : Prop,
  (P -> Q -> R) -> ((P /\ Q) -> R).
Proof.
  intros P Q R H [HP HQ].
  apply H; assumption.
Qed.

(** ** Generalized Versions *)

(** Triple curry *)
Lemma curry3 : forall P Q R S : Prop,
  ((P /\ Q /\ R) -> S) -> (P -> Q -> R -> S).
Proof.
  intros P Q R S H HP HQ HR.
  apply H.
  split; [|split]; assumption.
Qed.

(** Triple uncurry *)
Lemma uncurry3 : forall P Q R S : Prop,
  (P -> Q -> R -> S) -> ((P /\ Q /\ R) -> S).
Proof.
  intros P Q R S H [HP [HQ HR]].
  apply H; assumption.
Qed.

(** ** Examples *)

Example curry_ex1 : forall n m : nat,
  ((n = 0 /\ m = 0) -> n + m = 0) -> (n = 0 -> m = 0 -> n + m = 0).
Proof.
  intros n m.
  apply curry.
Qed.

Example uncurry_ex1 : forall (A : Type) (P Q : A -> Prop) (x : A),
  (P x -> Q x -> P x /\ Q x) -> ((P x /\ Q x) -> P x /\ Q x).
Proof.
  intros A P Q x.
  apply uncurry.
Qed.

(** Using curry to simplify a proof *)
Example curry_usage : 
  ((forall n m : nat, (n = 0 /\ m = 0) -> n + m = 0) ->
   (forall n m : nat, n = 0 -> m = 0 -> n + m = 0)).
Proof.
  intro H.
  intros n m.
  apply curry.
  apply H.
Qed.

(** Transforming a lemma statement *)
Example transform_statement : 
  (forall x y : nat, x = 0 /\ y = 0 -> x + y = 0) <->
  (forall x y : nat, x = 0 -> y = 0 -> x + y = 0).
Proof.
  split.
  - intros H x y. apply curry. apply H.
  - intros H x y. apply uncurry. apply H.
Qed.

(** ** Variations *)

(** Curry with exists *)
Lemma curry_exists : forall (A : Type) (P : A -> Prop) (Q : Prop),
  ((exists x, P x) -> Q) -> (forall x, P x -> Q).
Proof.
  intros A P Q H x HPx.
  apply H.
  exists x; assumption.
Qed.

(** ** Notes
    
    This lemma is named after Haskell Curry, who studied the
    correspondence between multi-argument and single-argument functions.
    
    In programming languages, currying converts a function that takes
    multiple arguments into a sequence of functions that each take a
    single argument. This logical version shows the same principle
    applies to implications.
    
    The absence of this basic equivalence from the standard library
    means users often write awkward proofs that could be simplified
    by applying curry or uncurry.
*)