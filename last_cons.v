(** * Last Element Properties
    
    This module provides fundamental properties of the last function
    on lists, which are missing from Coq's standard library.
    
    Author: Charles C Norton
    Date: June 9th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(** ** Overview
    
    The last function returns the last element of a list, or a default
    value if the list is empty. While the function is defined in the
    standard library, basic properties about its behavior are missing.
    
    The main property is that consing an element to a non-empty list
    doesn't change its last element: last (a :: l) d = last l d when l ≠ [].
    
    This seemingly trivial property is needed whenever reasoning about
    list operations that preserve the last element.
    
    This property is useful for:
    - Reasoning about list construction and deconstruction
    - Proving properties of algorithms that process list ends
    - Establishing invariants for accumulator-based functions
    - Verifying queue implementations using lists
    - Reasoning about path operations in graph algorithms
*)

(** ** Main Theorem *)

(** The last element of a cons is the last of the tail when non-empty *)
Lemma last_cons {A : Type} (a d : A) (l : list A) :
  l <> [] -> last (a :: l) d = last l d.
Proof.
  intro H.
  destruct l as [|h t].
  - contradiction.
  - reflexivity.
Qed.

(** ** Alternative Formulations *)

(** Version with explicit length condition *)
Lemma last_cons_length {A : Type} (a d : A) (l : list A) :
  length l > 0 -> last (a :: l) d = last l d.
Proof.
  intro H.
  apply last_cons.
  destruct l.
  - simpl in H. inversion H.
  - discriminate.
Qed.

(** Version for specific list shapes *)
Lemma last_cons_cons {A : Type} (a b d : A) (l : list A) :
  last (a :: b :: l) d = last (b :: l) d.
Proof.
  reflexivity.
Qed.

(** ** Corollaries *)

(** Last of singleton *)
Lemma last_singleton {A : Type} (a d : A) :
  last [a] d = a.
Proof.
  reflexivity.
Qed.

(** Last is independent of first elements *)
Lemma last_cons_irrelevance {A : Type} (a b d : A) (l : list A) :
  l <> [] -> last (a :: l) d = last (b :: l) d.
Proof.
  intro H.
  rewrite !last_cons; auto.
Qed.

(** Multiple cons *)
Lemma last_cons_many {A : Type} (a : A) (l1 l2 : list A) (d : A) :
  l2 <> [] -> last (l1 ++ a :: l2) d = last l2 d.
Proof.
  intro H.
  induction l1 as [|h t IH].
  - simpl. apply last_cons. exact H.
  - simpl. destruct t.
    + simpl. destruct l2.
      * contradiction.
      * reflexivity.
    + simpl in IH. exact IH.
Qed.

(** ** Examples *)

Example last_cons_ex1 : 
  last (1 :: [2; 3; 4]) 0 = 4.
Proof.
  reflexivity.
Qed.

Example last_cons_ex2 : forall (d : nat),
  last (5 :: [6; 7]) d = last [6; 7] d.
Proof.
  intro d.
  apply last_cons.
  discriminate.
Qed.

(** The default value is irrelevant for non-empty tails *)
Example last_cons_default_irrelevant :
  last (10 :: [20; 30]) 99 = last (10 :: [20; 30]) 0.
Proof.
  reflexivity.
Qed.

(** Building lists while preserving last *)
Example last_preserved : forall n : nat,
  last [1; 2; 3] n = last (0 :: [1; 2; 3]) n.
Proof.
  intro n.
  symmetry.
  apply last_cons.
  discriminate.
Qed.

(** Practical example: maintaining final result *)
Example accumulator_last : forall (A : Type) (f : A -> A -> A) (init x y z : A) (d : A),
  last [f init x; f (f init x) y; f (f (f init x) y) z] d = f (f (f init x) y) z.
Proof.
  intros.
  reflexivity.
Qed.

(** ** Extended Properties *)

(** Relationship with removelast *)
Lemma last_removelast {A : Type} (l : list A) (d : A) :
  l <> [] -> 
  exists l', l = l' ++ [last l d] /\ removelast l = l'.
Proof.
  intro H.
  exists (removelast l).
  split.
  - apply app_removelast_last. exact H.
  - reflexivity.
Qed.

(** Induction principle using last *)
Lemma list_ind_last {A : Type} (P : list A -> Prop) :
  P [] ->
  (forall a, P [a]) ->
  (forall a l, l <> [] -> P l -> P (a :: l)) ->
  forall l, P l.
Proof.
  intros Hnil Hsing Hcons.
  intro l. induction l as [|h t IH].
  - exact Hnil.
  - destruct t.
    + apply Hsing.
    + apply Hcons.
      * discriminate.
      * exact IH.
Qed.

(** ** Edge Cases *)

(** Empty list *)
Example last_nil {A : Type} (d : A) :
  last [] d = d.
Proof.
  reflexivity.
Qed.

(** Very long list *)
Example last_long_list :
  last [1;2;3;4;5;6;7;8;9;10] 0 = 10.
Proof.
  reflexivity.
Qed.

(** ** Notes
    
    The last_cons property is surprisingly absent from the standard library,
    despite being fundamental for reasoning about list operations. The proof
    is trivial, but users shouldn't have to reprove it.
    
    The standard library provides:
    - Definition of last
    - app_removelast_last (decomposition lemma)
    - exists_last (existence of decomposition)
    
    But lacks basic properties like:
    - How last behaves with cons (our main theorem)
    - Independence from default value for non-empty lists
    - Relationship with other list operations
    
    These omissions force users to prove these properties repeatedly,
    cluttering proofs with trivial details about list structure.
    
    The default value parameter in last is a common source of confusion.
    Our lemmas clarify that it's only used for empty lists, making it
    easier to reason about last in typical use cases.
    
    Note that for some applications, using option types might be cleaner
    than a default value, but that would require a different last function
    than what the standard library provides.
*)
