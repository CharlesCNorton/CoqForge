(** * Some Constructor Injectivity
    
    This module provides the fundamental lemma about the injectivity of the
    option constructor [Some] that is surprisingly absent from Coq's standard
    library.
    
    Author: Charles C Norton
    Date: June 9th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Init.Datatypes.

(** ** Overview
    
    The [Some] constructor for options is injective: if two option values
    constructed with [Some] are equal, then their arguments must be equal.
    
    More formally: For any type [A] and values [x, y : A],
    if [Some x = Some y], then [x = y].
    
    While Coq's [injection] tactic can derive this fact when needed during
    proofs, there is no explicit lemma in the standard library that states
    this property. This can be inconvenient when:
    
    - You need to apply the injectivity property as part of a larger
      rewriting step
    - You want to use it with tactics like [apply] or [rewrite]
    - You need to reason about option equality in a forward-reasoning style
    - You want to use it as a parameter to higher-order functions or tactics
    
    This property is useful for:
    - Simplifying option equality proofs
    - Extracting values from option equalities
    - Proving properties about functions that return options
    - Establishing injectivity of functions that use Some
*)

(** ** Main Theorem *)

(** The [Some] constructor is injective *)
Lemma Some_inj {A : Type} (x y : A) : Some x = Some y -> x = y.
Proof.
  intro H.
  injection H.
  auto.
Qed.

(** ** Alternative Formulations *)

(** Contrapositive: if values are different, the options are different *)
Lemma Some_neq {A : Type} (x y : A) : x <> y -> Some x <> Some y.
Proof.
  intros Hneq Heq.
  apply Hneq.
  apply Some_inj.
  exact Heq.
Qed.

(** Iff version *)
Lemma Some_eq_iff {A : Type} (x y : A) : Some x = Some y <-> x = y.
Proof.
  split.
  - apply Some_inj.
  - intro H. rewrite H. reflexivity.
Qed.

(** ** Corollaries *)

(** Option equality decider given value equality decider *)
Lemma Some_eq_dec {A : Type} (x y : A) :
  {x = y} + {x <> y} -> {Some x = Some y} + {Some x <> Some y}.
Proof.
  intro H.
  destruct H as [Heq | Hneq].
  - left. rewrite Heq. reflexivity.
  - right. apply Some_neq. exact Hneq.
Qed.

(** ** Examples *)

(** Basic usage *)
Example Some_inj_ex1 : Some 42 = Some 42 -> 42 = 42.
Proof.
  apply Some_inj.
Qed.

(** Extracting values *)
Example Some_inj_ex2 : forall n m : nat,
  Some (n + m) = Some 10 -> n + m = 10.
Proof.
  intros n m H.
  apply Some_inj in H.
  exact H.
Qed.

(** Using in a larger proof *)
Example Some_inj_ex3 : forall (A : Type) (f : nat -> A) (x : A),
  Some (f 5) = Some x -> f 5 = x.
Proof.
  intros A f x H.
  apply Some_inj.
  exact H.
Qed.

(** Chaining injections *)
Example Some_inj_chain : forall n m : nat,
  Some (Some n) = Some (Some m) -> n = m.
Proof.
  intros n m H.
  apply Some_inj in H.
  apply Some_inj in H.
  exact H.
Qed.

(** Using the contrapositive *)
Example Some_neq_ex : 3 <> 5 -> Some 3 <> Some 5.
Proof.
  apply Some_neq.
Qed.

(** ** Extended Properties *)

(** Interaction with option_map *)
Lemma option_map_Some_inj {A B : Type} (f : A -> B) (x y : A) :
  option_map f (Some x) = option_map f (Some y) -> f x = f y.
Proof.
  simpl.
  apply Some_inj.
Qed.

(** None is different from Some *)
Lemma None_not_Some {A : Type} (x : A) : None <> Some x.
Proof.
  discriminate.
Qed.

Lemma Some_not_None {A : Type} (x : A) : Some x <> None.
Proof.
  discriminate.
Qed.

(** ** Relation to Inductive Types
    
    The injectivity of [Some] follows from the general principle that
    all constructors of inductive types are injective. This property
    is built into Coq's type theory.
    
    Similar lemmas for other constructors:
    - cons_eq: proved for lists in your collection
    - pair_eq_iff: provable for products
    - inl_inj, inr_inj: provable for sums
    
    Despite being derivable via the [injection] tactic, having these
    as explicit lemmas improves proof readability and enables better
    automation.
*)

(** ** Notes
    
    This is perhaps the simplest missing lemma in Coq's standard library.
    The proof is trivial (just apply injection), yet having it as an
    explicit lemma makes many proofs cleaner.
    
    The fact that such a basic property is missing demonstrates the
    minimalist philosophy of Coq's standard library - even the most
    fundamental properties are omitted if they can be derived using
    tactics.
    
    In practice, users often need this lemma when:
    - Pattern matching would be overkill
    - Working with option equality in hypothesis
    - Building larger automation tactics
    - Teaching Coq to beginners (explicit is clearer than tactics)
*)
