(** * Nth Error None Characterization
    
    This module provides the fundamental characterization of when nth_error
    returns None, which is surprisingly absent from Coq's standard library.
    
    Author: Charles C Norton
    Date: June 9th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(** ** Overview
    
    The nth_error function provides safe list indexing by returning an option:
    Some element if the index is valid, None if it's out of bounds. This
    lemma characterizes exactly when None is returned.
    
    The theorem states: nth_error l n = None if and only if length l ≤ n.
    
    This bidirectional characterization connects list indexing with list length,
    providing a complete description of when lookups fail.
    
    This property is useful for:
    - Proving that indices are out of bounds
    - Establishing preconditions for safe list access
    - Reasoning about list operations that may fail
    - Optimizing bounds checking in algorithms
    - Converting between different error handling styles
*)

(** ** Main Theorem *)

(** nth_error returns None if and only if the index is out of bounds *)
Lemma nth_error_None {A : Type} (l : list A) (n : nat) :
  nth_error l n = None <-> length l <= n.
Proof.
  revert n.
  induction l as [|h t IH]; intro n.
  - (* Base case: empty list *)
    simpl. split.
    + intro H. apply Nat.le_0_l.
    + intro H. destruct n; reflexivity.
  - (* Inductive case: h :: t *)
    destruct n as [|n'].
    + (* n = 0 *)
      simpl. split.
      * intro H. discriminate.
      * intro H. inversion H.
    + (* n = S n' *)
      simpl. rewrite IH. split.
      * intro H. apply le_n_S. exact H.
      * intro H. apply Nat.succ_le_mono in H. exact H.
Qed.

(** ** Alternative Formulations *)

(** Forward direction only *)
Lemma nth_error_None_iff_length_le {A : Type} (l : list A) (n : nat) :
  nth_error l n = None -> length l <= n.
Proof.
  apply nth_error_None.
Qed.

(** Backward direction only *)
Lemma length_le_iff_nth_error_None {A : Type} (l : list A) (n : nat) :
  length l <= n -> nth_error l n = None.
Proof.
  apply nth_error_None.
Qed.

(** Contrapositive: if nth_error succeeds, index is in bounds *)
Lemma nth_error_Some_lt {A : Type} (l : list A) (n : nat) :
  (exists x, nth_error l n = Some x) -> n < length l.
Proof.
  intros [x Hx].
  destruct (Nat.lt_ge_cases n (length l)) as [H | H]; [exact H |].
  (* If length l <= n, then nth_error l n = None *)
  assert (nth_error l n = None) by (apply nth_error_None; exact H).
  rewrite H0 in Hx. discriminate.
Qed.

(** ** Corollaries *)

(** nth_error always fails on indices >= length *)
Lemma nth_error_None_ge {A : Type} (l : list A) (n : nat) :
  length l <= n -> nth_error l n = None.
Proof.
  apply nth_error_None.
Qed.

(** Special case for exact length *)
Lemma nth_error_length {A : Type} (l : list A) :
  nth_error l (length l) = None.
Proof.
  apply nth_error_None.
  apply Nat.le_refl.
Qed.

(** Out of bounds by strict inequality *)
Lemma nth_error_None_lt {A : Type} (l : list A) (n : nat) :
  length l < S n -> nth_error l n = None.
Proof.
  intro H.
  apply nth_error_None.
  apply Nat.lt_succ_r.
  exact H.
Qed.

(** Empty list always returns None *)
Lemma nth_error_nil {A : Type} (n : nat) :
  nth_error (@nil A) n = None.
Proof.
  apply nth_error_None.
  simpl. apply Nat.le_0_l.
Qed.

(** If index is within bounds, nth_error doesn't return None *)
Lemma nth_error_Some_not_None {A : Type} (l : list A) (n : nat) :
  n < length l -> nth_error l n <> None.
Proof.
  intro H.
  intro H'.
  apply nth_error_None in H'.
  apply (Nat.lt_irrefl n).
  apply (Nat.lt_le_trans _ _ _ H H').
Qed.

(** ** Examples *)

Example nth_error_None_ex1 :
  nth_error [1; 2; 3] 3 = None.
Proof.
  reflexivity.
Qed.

Example nth_error_None_ex2 :
  nth_error [1; 2; 3] 5 = None.
Proof.
  reflexivity.
Qed.

Example nth_error_None_ex3 : forall l : list nat,
  length l = 10 -> nth_error l 10 = None.
Proof.
  intros l H.
  apply nth_error_None.
  rewrite H.
  apply Nat.le_refl.
Qed.

(** Using the characterization *)
Example nth_error_bounds_check : forall (A : Type) (l : list A) (n : nat),
  nth_error l n = None \/ exists x, nth_error l n = Some x.
Proof.
  intros A l n.
  destruct (nth_error l n) eqn:H.
  - right. exists a. reflexivity.
  - left. reflexivity.
Qed.

(** Relationship with length *)
Example nth_error_length_relationship : forall l : list nat,
  length l = 5 ->
  nth_error l 4 <> None /\
  nth_error l 5 = None.
Proof.
  intros l H.
  split.
  - apply nth_error_Some_not_None.
    rewrite H. auto.
  - apply nth_error_None.
    rewrite H.
    apply Nat.le_refl.
Qed.

(** ** Extended Properties *)

(** Decidability of bounds checking *)
Lemma nth_error_in_bounds_dec {A : Type} (l : list A) (n : nat) :
  {n < length l} + {length l <= n}.
Proof.
  destruct (lt_dec n (length l)).
  - left. exact l0.
  - right. apply Nat.nlt_ge. exact n0.
Qed.

(** Connection with nth_error being total *)
Lemma nth_error_total_characterization {A : Type} (l : list A) (n : nat) :
  (nth_error l n = None /\ length l <= n) \/
  (exists x, nth_error l n = Some x /\ n < length l).
Proof.
  destruct (nth_error l n) eqn:H.
  - right. exists a. split.
    + reflexivity.
    + apply nth_error_Some_lt. exists a. exact H.
  - left. split.
    + reflexivity.
    + apply nth_error_None. exact H.
Qed.

(** Interaction with list operations *)
Lemma nth_error_app_None {A : Type} (l1 l2 : list A) (n : nat) :
  nth_error (l1 ++ l2) n = None <-> length (l1 ++ l2) <= n.
Proof.
  apply nth_error_None.
Qed.

Lemma nth_error_map_None {A B : Type} (f : A -> B) (l : list A) (n : nat) :
  nth_error (map f l) n = None <-> nth_error l n = None.
Proof.
  rewrite !nth_error_None.
  rewrite map_length.
  reflexivity.
Qed.

(** Safe head via nth_error *)
Lemma hd_error_as_nth_error {A : Type} (l : list A) :
  hd_error l = nth_error l 0.
Proof.
  destruct l; reflexivity.
Qed.


(** ** Related Lemmas (already proven) *)

(** These complement nth_error_None: *)
(** - nth_error_In: if nth_error returns Some, element is in list *)
(** - In_nth_error: if element is in list, there exists valid index *)
(** - nth_error_Some_lt: if nth_error returns Some, index < length *)

(** ** Notes
    
    This characterization is fundamental for reasoning about list bounds,
    yet it's missing from Coq's standard library. Without it, users must
    repeatedly prove that failed lookups correspond to out-of-bounds indices.
    
    The proof proceeds by induction on the list structure, with case
    analysis on the index. The key insight is that nth_error recursively
    decrements the index while traversing the list, so the index is out
    of bounds precisely when we run out of list elements before the index
    reaches 0.
    
    This lemma is particularly useful in conjunction with:
    - nth_error_In (proving elements are in the list)
    - decidable equality (for searching lists)
    - list manipulation functions (map, filter, etc.)
    
    The bidirectional nature (iff) makes this lemma especially powerful
    for rewriting in both directions during proofs.
*)
