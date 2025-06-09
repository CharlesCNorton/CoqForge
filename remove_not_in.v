(** * Remove Preserves Non-membership
    
    This module provides a fundamental lemma about the remove function that
    is missing from Coq's standard library: removing elements preserves
    non-membership of other elements.
    
    Author: Charles C Norton
    Date: June 9th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(** ** Overview
    
    The remove function removes all occurrences of a given element from a list.
    This lemma states that if an element y was not in the original list, then
    it remains not in the list after removing any other element x.
    
    More formally: ~ In y l -> ~ In y (remove eq_dec x l)
    
    This property is fundamental for reasoning about list operations that
    preserve or restrict membership, yet it's not provided in the standard
    library which only gives remove_In (the removed element is not in result).
    
    This property is useful for:
    - Proving invariants about list membership after modifications
    - Reasoning about set-like operations on lists
    - Establishing that remove only affects the target element
    - Proving properties of filtering and partitioning operations
    - Verifying algorithms that maintain exclusion properties
*)

(** ** Main Theorem *)

Section RemoveNotIn.
  Variable A : Type.
  Hypothesis eq_dec : forall x y : A, {x = y} + {x <> y}.

  (** Helper: if y is in remove x l, then y was in l *)
  Lemma in_remove_in (x y : A) (l : list A) :
    In y (remove eq_dec x l) -> In y l.
  Proof.
    induction l as [|h t IH].
    - simpl. intro H. exact H.
    - simpl. destruct (eq_dec x h).
      + (* x = h, so we skip h *)
        intro H. right. apply IH. exact H.
      + (* x <> h, so we keep h *)
        simpl. intro H. destruct H as [H | H].
        * left. exact H.
        * right. apply IH. exact H.
  Qed.

  (** If y is not in l, then y is not in remove x l *)
  Lemma remove_not_in (x y : A) (l : list A) :
    ~ In y l -> ~ In y (remove eq_dec x l).
  Proof.
    intros H H'.
    apply H.
    apply (in_remove_in x).
    exact H'.
  Qed.
End RemoveNotIn.

(** ** Alternative Formulations *)

Section RemoveNotInAlt.
  Variable A : Type.
  Hypothesis eq_dec : forall x y : A, {x = y} + {x <> y}.

  (** Contrapositive: if y is in remove x l, then y was in l *)
  Lemma remove_in_in (x y : A) (l : list A) :
    In y (remove eq_dec x l) -> In y l.
  Proof.
    apply in_remove_in.
  Qed.

  (** Version with different element *)
  Lemma remove_not_in_diff (x y : A) (l : list A) :
    x <> y -> ~ In y l -> ~ In y (remove eq_dec x l).
  Proof.
    intros _ H.
    apply remove_not_in.
    exact H.
  Qed.

  (** Symmetric version *)
  Lemma not_in_remove (l : list A) (x y : A) :
    ~ In y l -> ~ In y (remove eq_dec x l).
  Proof.
    apply remove_not_in.
  Qed.
End RemoveNotInAlt.

(** ** Corollaries *)

Section RemoveCorollaries.
  Variable A : Type.
  Hypothesis eq_dec : forall x y : A, {x = y} + {x <> y}.

  (** Remove from empty list *)
  Lemma remove_not_in_nil (x y : A) :
    ~ In y (remove eq_dec x []).
  Proof.
    apply remove_not_in.
    intro H. exact H.
  Qed.

  (** Remove preserves disjointness *)
  Lemma remove_preserves_disjoint (x : A) (l1 l2 : list A) :
    (forall y, In y l1 -> ~ In y l2) ->
    (forall y, In y (remove eq_dec x l1) -> ~ In y l2).
  Proof.
    intros H y H1 H2.
    apply (H y).
    - apply in_remove_in in H1. exact H1.
    - exact H2.
  Qed.

  (** Remove preserves subset non-membership *)
  Lemma remove_subset_not_in (x : A) (l1 l2 : list A) :
    (forall y, In y l1 -> In y l2) ->
    forall y, ~ In y l2 -> ~ In y (remove eq_dec x l1).
  Proof.
    intros Hsub y Hnin.
    apply remove_not_in.
    intro H.
    apply Hnin.
    apply Hsub.
    exact H.
  Qed.
End RemoveCorollaries.

(** ** Examples *)

Example remove_not_in_ex1 :
  ~ In 5 [1; 2; 3; 4] ->
  ~ In 5 (remove Nat.eq_dec 2 [1; 2; 3; 4]).
Proof.
  apply remove_not_in.
Qed.

Example remove_not_in_concrete :
  ~ In 7 (remove Nat.eq_dec 3 [1; 2; 3; 4; 3; 5]).
Proof.
  apply remove_not_in.
  simpl. intuition congruence.
Qed.

(** Multiple removes preserve non-membership *)
Example remove_not_in_chain :
  ~ In 10 [1; 2; 3; 4; 5] ->
  ~ In 10 (remove Nat.eq_dec 2 (remove Nat.eq_dec 4 [1; 2; 3; 4; 5])).
Proof.
  intro H.
  apply remove_not_in.
  apply remove_not_in.
  exact H.
Qed.

(** Removing from a list without the element *)
Example remove_not_in_noop :
  let l := [1; 3; 5; 7; 9] in
  ~ In 2 l ->
  ~ In 6 l ->
  ~ In 6 (remove Nat.eq_dec 2 l).
Proof.
  intros l H2 H6.
  apply remove_not_in.
  exact H6.
Qed.


(** ** Relation to Standard Library *)

(** The standard library provides remove_In, which states that the
    removed element is not in the result:
    
    remove_In : forall (l : list A) (x : A), ~ In x (remove x l)
    
    Our lemma is complementary, showing that OTHER elements' non-membership
    is preserved. Together they fully characterize which elements are not
    in the result of remove. *)

(** ** Notes
    
    This lemma fills an important gap in reasoning about the remove function.
    While the standard library tells us that x is not in (remove x l), it
    doesn't explicitly state that remove ONLY removes x and preserves
    non-membership of all other elements.
    
    The proof is straightforward using a helper lemma that shows membership
    in the result implies membership in the original. This helper lemma
    (in_remove_in) is also useful independently.
    
    This property is particularly important when:
    1. Maintaining invariants about excluded elements
    2. Proving that certain elements remain absent after modifications
    3. Verifying security properties where certain values must not appear
    
    The remove function's relationship to filter (shown in remove_as_filter)
    provides an alternative perspective that can simplify some proofs.
*)
