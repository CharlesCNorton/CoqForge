(** * Nth Error Membership
    
    This module provides the connection between nth_error and list membership
    that is missing from Coq's standard library.
    
    Author: Charles C Norton
    Date: June 8th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Lists.List.
Import ListNotations.

(** ** Overview
    
    This lemma connects nth_error with the In predicate: if nth_error
    returns Some element, then that element is in the list.
    
    This property is useful for:
    - Converting between index-based and membership-based reasoning
    - Proving correctness of algorithms that access lists by index
    - Establishing bounds and membership properties
    - Working with proofs involving list lookups
*)

(** ** Main Theorem *)

(** If nth_error succeeds, the element is in the list *)
(** If nth_error succeeds, the element is in the list *)
Lemma nth_error_In : forall {A : Type} (l : list A) (n : nat) (x : A),
  nth_error l n = Some x -> In x l.
Proof.
  intros A l n x H.
  generalize dependent n.
  induction l as [|h t IH].
  - (* Base case: empty list *)
    intros n H.
    (* nth_error [] n = Some x is impossible *)
    destruct n; discriminate H.
  - (* Inductive case: h :: t *)
    intros n H.
    destruct n as [|n'].
    + (* n = 0 *)
      simpl in H.
      injection H as H.
      subst x.
      left. reflexivity.
    + (* n = S n' *)
      simpl in H.
      right.
      apply IH with n'.
      exact H.
Qed.

(** ** Corollaries *)
(** If an index is valid, there exists an element at that position *)
Lemma nth_error_Some_length : forall {A : Type} (l : list A) (n : nat),
  n < length l -> exists x, nth_error l n = Some x.
Proof.
  intros A l.
  induction l as [|h t IH].
  - (* Base case: empty list *)
    intros n H.
    simpl in H.
    inversion H.
  - (* Inductive case: h :: t *)
    intros n H.
    destruct n as [|n'].
    + (* n = 0 *)
      exists h. reflexivity.
    + (* n = S n' *)
      simpl in H.
      (* H : S n' < S (length t), need to show exists x, nth_error t n' = Some x *)
      apply IH.
      (* Need: n' < length t *)
      unfold lt in *.
      (* H : S (S n') <= S (length t) *)
      apply le_S_n.
      exact H.
Qed.


(** Combining with membership gives us a witness *)
Lemma In_nth_error : forall {A : Type} (l : list A) (x : A),
  In x l -> exists n, nth_error l n = Some x.
Proof.
  intros A l x H.
  induction l as [|h t IH].
  - contradiction.
  - destruct H as [H | H].
    + (* x = h *)
      exists 0.
      simpl.
      rewrite H.
      reflexivity.
    + (* In x t *)
      destruct (IH H) as [n Hn].
      exists (S n).
      simpl.
      exact Hn.
Qed.

(** ** Examples *)

Example nth_error_In_ex1 : 
  nth_error [1; 2; 3] 1 = Some 2 -> In 2 [1; 2; 3].
Proof.
  apply nth_error_In.
Qed.

Example nth_error_In_ex2 : forall (A : Type) (x y z : A),
  nth_error [x; y; z] 2 = Some z -> In z [x; y; z].
Proof.
  intros A x y z.
  apply nth_error_In.
Qed.

(** ** Notes
    
    The standard library provides nth_error for safe list indexing
    and In for list membership, but surprisingly doesn't connect them.
    
    This forces users to reprove this connection repeatedly in their
    own projects, especially when working with algorithms that mix
    index-based and membership-based reasoning.
    
    The reverse direction (In_nth_error) shows that membership implies
    the existence of a valid index, completing the correspondence.
*)
