(** * Filter Length Inequality
    
    This module provides a fundamental lemma about the length of filtered lists
    that is surprisingly absent from Coq's standard library.
    
    Author: Charles C Norton
    Date: June 8th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.10+
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(** ** Overview
    
    When filtering a list with a predicate, the resulting list can never be
    longer than the original list. This is an obvious property, but Coq's
    standard library doesn't provide it explicitly.
    
    This property is useful when:
    - Proving termination of algorithms that recursively filter sublists
    - Establishing bounds in complexity analysis
    - Reasoning about memory usage of filtering operations
    - Proving properties about partition operations
*)

(** ** Main Theorem *)

(** The length of a filtered list is always less than or equal to the length
    of the original list.
    
    This holds for any type [A], any decidable predicate [P : A -> bool],
    and any list [l : list A].
*)
Lemma filter_length {A : Type} (P : A -> bool) (l : list A) :
  length (filter P l) <= length l.
Proof.
  induction l as [|h t IH].
  - (* Base case: empty list *)
    simpl. reflexivity.
  - (* Inductive case: h :: t *)
    simpl. destruct (P h).
    + (* P h = true, so h is kept *)
      simpl. apply le_n_S. exact IH.
    + (* P h = false, so h is discarded *)
      apply le_S. exact IH.
Qed.

(** ** Corollaries and Related Properties *)

(** If we filter with the always-false predicate, we get the empty list *)
Lemma filter_false_nil {A : Type} (l : list A) :
  filter (fun _ => false) l = [].
Proof.
  induction l; simpl; auto.
Qed.

(** If we filter with the always-true predicate, we get the original list *)
Lemma filter_true_id {A : Type} (l : list A) :
  filter (fun _ => true) l = l.
Proof.
  induction l as [|h t IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** The length can only equal the original if all elements satisfy the predicate *)
Lemma filter_length_eq {A : Type} (P : A -> bool) (l : list A) :
  length (filter P l) = length l -> filter P l = l.
Proof.
  induction l as [|h t IH].
  - simpl. auto.
  - simpl. destruct (P h) eqn:Hph.
    + simpl. intro H. 
      f_equal. apply IH.
      injection H. auto.
    + simpl. intro H.
      (* If P h = false, then we have length (filter P t) = S (length t) *)
      (* This contradicts filter_length *)
      absurd (length (filter P t) <= length t).
      * (* Show ~(length (filter P t) <= length t) *)
        rewrite H. auto with arith.
      * (* Show length (filter P t) <= length t *)
        apply filter_length.
Qed.

(** ** Examples *)

Example filter_length_ex1 :
  length (filter (fun n => n <? 5) [1; 7; 3; 9; 2; 8]) <= 6.
Proof.
  apply filter_length.
Qed.

Example filter_length_ex2 :
  forall l : list nat,
  length (filter (fun n => n =? 0) l) <= length l.
Proof.
  intro l. apply filter_length.
Qed.

(** Filtering with opposite predicates partitions the list *)
Example filter_partition {A : Type} (P : A -> bool) (l : list A) :
  length (filter P l) + length (filter (fun x => negb (P x)) l) = length l.
Proof.
  induction l as [|h t IH].
  - reflexivity.
  - simpl. destruct (P h) eqn:Hp; simpl.
    + rewrite <- IH. reflexivity.
    + rewrite <- IH. rewrite plus_n_Sm. reflexivity.
Qed.

(** ** Notes
    
    This lemma is so basic that many Coq users have likely proven it
    independently multiple times. Its absence from the standard library
    forces redundant work and clutters proof scripts.
    
    The proof is by straightforward induction on the list structure,
    with a case analysis on whether each element satisfies the predicate.
    
    Related functions that could benefit from similar lemmas:
    - partition (which is essentially two filters)
    - remove_if / remove_all
    - take_while / drop_while
*)