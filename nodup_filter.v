(** * NoDup Filter Preservation
    
    This module provides a fundamental lemma about list filtering that
    preserves the no-duplicates property, which is missing from Coq's
    standard library.
    
    Author: Charles C Norton
    Date: June 8th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Lists.List.
Import ListNotations.

(** ** Overview
    
    When filtering a list that has no duplicate elements, the resulting
    filtered list also has no duplicate elements. This is an obvious
    but important invariant property.
    
    The NoDup predicate states that all elements in a list are distinct.
    This lemma shows that the filter operation preserves this property.
    
    This property is useful for:
    - Proving correctness of algorithms that filter unique collections
    - Maintaining invariants in data structures
    - Reasoning about set-like operations on lists
    - Establishing properties of database-like queries
    - Optimizing algorithms that rely on uniqueness
*)

(** ** Main Theorem *)

(** Filtering preserves the no-duplicates property *)
Lemma NoDup_filter {A : Type} (P : A -> bool) (l : list A) :
  NoDup l -> NoDup (filter P l).
Proof.
  induction 1 as [|x l' Hnotinl' Hnodupl' IH].
  - (* Base case: empty list *)
    simpl.
    constructor.
  - (* Inductive case: x :: l' *)
    simpl.
    destruct (P x) eqn:HPx.
    + (* P x = true, so x is kept *)
      constructor.
      * (* Show: ~ In x (filter P l') *)
        intro Hin.
        (* x is in the filtered list, so it must be in l' *)
        apply filter_In in Hin.
        destruct Hin as [Hinl' _].
        (* But we know x is not in l' *)
        contradiction.
      * (* Show: NoDup (filter P l') *)
        apply IH.
    + (* P x = false, so x is discarded *)
      apply IH.
Qed.

(** ** Helper Lemmas *)

(** Filtering with always-false gives empty list *)
Lemma filter_false_nil {A : Type} (l : list A) :
  filter (fun _ => false) l = [].
Proof.
  induction l; simpl; auto.
Qed.

(** Filtering with always-true gives identity *)
Lemma filter_true_id {A : Type} (l : list A) :
  filter (fun _ => true) l = l.
Proof.
  induction l as [|h t IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** ** Corollaries *)

(** Filtering with always-false preserves NoDup trivially *)
Lemma NoDup_filter_false {A : Type} (l : list A) :
  NoDup l -> NoDup (filter (fun _ => false) l).
Proof.
  intro H.
  rewrite filter_false_nil.
  constructor.
Qed.

(** Filtering with always-true preserves the original NoDup *)
Lemma NoDup_filter_true {A : Type} (l : list A) :
  NoDup l -> NoDup (filter (fun _ => true) l).
Proof.
  intro H.
  rewrite filter_true_id.
  exact H.
Qed.

(** Composition of filters preserves NoDup *)
Lemma NoDup_filter_filter {A : Type} (P Q : A -> bool) (l : list A) :
  NoDup l -> NoDup (filter P (filter Q l)).
Proof.
  intro H.
  apply NoDup_filter.
  apply NoDup_filter.
  exact H.
Qed.

(** ** Examples *)

Example NoDup_filter_ex1 :
  NoDup [1; 2; 3; 4; 5] ->
  NoDup (filter (fun n => Nat.ltb n 4) [1; 2; 3; 4; 5]).
Proof.
  apply NoDup_filter.
Qed.

Example NoDup_filter_ex2 :
  NoDup [1; 3; 5; 7; 9] ->
  NoDup (filter (fun n => Nat.eqb (Nat.modulo n 2) 1) [1; 3; 5; 7; 9]).
Proof.
  apply NoDup_filter.
Qed.

(** Example showing the filtered list is a subset *)
Example NoDup_filter_subset : forall (A : Type) (P : A -> bool) (l : list A) (x : A),
  NoDup l ->
  In x (filter P l) ->
  In x l /\ P x = true.
Proof.
  intros A P l x Hnodup Hin.
  apply filter_In.
  exact Hin.
Qed.

(** Example with concrete computation *)
Example NoDup_filter_compute :
  NoDup (filter (fun n => Nat.ltb (n * n) 20) [1; 2; 3; 4; 5; 6; 7]).
Proof.
  simpl.
  (* Computes to [1; 2; 3; 4] *)
  repeat constructor.
  - (* 1 not in [2; 3; 4] *)
    simpl. intuition congruence.
  - (* 2 not in [3; 4] *) 
    simpl. intuition congruence.
  - (* 3 not in [4] *)
    simpl. intuition congruence.
  - (* 4 not in [] *)
    simpl. auto.
Qed.

(** ** Extended Properties *)

(** Partition preserves NoDup on both parts *)
Lemma NoDup_partition {A : Type} (P : A -> bool) (l : list A) :
  NoDup l ->
  let (l1, l2) := partition P l in
  NoDup l1 /\ NoDup l2.
Proof.
  intro H.
  destruct (partition P l) as [l1 l2] eqn:Hpart.
  split.
  - (* NoDup l1 *)
    assert (l1 = fst (partition P l)) by (rewrite Hpart; reflexivity).
    rewrite H0.
    rewrite partition_as_filter.
    apply NoDup_filter.
    exact H.
  - (* NoDup l2 *)
    assert (l2 = snd (partition P l)) by (rewrite Hpart; reflexivity).
    rewrite H0.
    rewrite partition_as_filter.
    apply NoDup_filter.
    exact H.
Qed.

(** Filtering with contradictory predicates gives disjoint lists *)
Lemma NoDup_filter_disjoint {A : Type} (P : A -> bool) (l : list A) :
  NoDup l ->
  forall x, ~ (In x (filter P l) /\ In x (filter (fun y => negb (P y)) l)).
Proof.
  intros H x [H1 H2].
  apply filter_In in H1.
  apply filter_In in H2.
  destruct H1 as [_ HP].
  destruct H2 as [_ HnP].
  rewrite HP in HnP.
  discriminate.
Qed.

(** ** Edge Cases and Observations *)

(** Empty list trivially maintains NoDup *)
Example NoDup_filter_nil {A : Type} (P : A -> bool) :
  NoDup (filter P []).
Proof.
  simpl.
  constructor.
Qed.

(** Singleton lists maintain NoDup regardless of predicate *)
Example NoDup_filter_singleton {A : Type} (P : A -> bool) (x : A) :
  NoDup [x] -> NoDup (filter P [x]).
Proof.
  intro H.
  simpl.
  destruct (P x).
  - constructor; [intro H'; destruct H' | constructor].
  - constructor.
Qed.


(** ** Notes
    
    This lemma is a fundamental property of filtering that should be
    in the standard library. Without it, users must reprove this
    invariant every time they work with filtered unique lists.
    
    The proof is by induction on the NoDup hypothesis, which gives us
    both the fact that x is not in l' and that l' has no duplicates.
    The key insight is that if x passes the filter, it still won't be
    in the filtered tail because it wasn't in the original tail.
    
    Related missing lemmas that would be useful:
    - NoDup_map with injective functions
    - NoDup_flat_map with appropriate conditions  
    - NoDup_remove for removing single elements
*)
