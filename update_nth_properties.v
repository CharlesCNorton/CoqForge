(** * Functional List Update – Missing Basics

    Elementary lemmas about in‑place replacement of the *n*-th element
    of a list, frequently re‑proved yet absent from Coq’s standard
    library.

    Author: Charles C Norton  
    Date:   June 13th 2025  
    License: GNU Lesser General Public License Version 2.1

    Compatibility: Coq 8.20.1+
*)

From Coq Require Import Lists.List Arith.PeanoNat.
From Coq Require Import Lia. 
Import ListNotations.

(* -------------------------------------------------------------------- *)
(** ** Definition *)

Fixpoint update_nth {A} (n : nat) (a : A) (l : list A) : list A :=
  match n, l with
  | 0   , []       => []              (* out‑of‑bounds – keep list *)
  | 0   , _ :: xs  => a :: xs
  | S n', []       => []              (* out‑of‑bounds – keep list *)
  | S n', y :: ys  => y :: update_nth n' a ys
  end.

(* -------------------------------------------------------------------- *)
(** ** Main lemmas *)

(** Length is preserved. *)
Lemma length_update :
  forall (A : Type) (n : nat) (a : A) (l : list A),
    length (update_nth n a l) = length l.
Proof.
  intros A n a l; revert n.
  induction l as [|x xs IH]; intros k; simpl.
  - (* empty list – analyse k to make [update_nth] compute *)
    destruct k; reflexivity.
  - (* non‑empty list *)
    destruct k; simpl; [reflexivity |].
    rewrite IH; reflexivity.
Qed.


(** Updated position yields the new element (if it is in range). *)
Lemma nth_error_update_eq :
  forall (A : Type) (n : nat) (a : A) (l : list A),
    n < length l ->
    nth_error (update_nth n a l) n = Some a.
Proof.
  intros A n a l Hlt; revert n Hlt.
  induction l as [|x xs IH]; intros k Hlt; simpl in *; [lia|].
  destruct k as [|k']; simpl.
  - reflexivity.
  - apply IH. lia.
Qed.

(** Other positions are unaffected. *)
Lemma nth_error_update_neq :
  forall (A : Type) (n m : nat) (a : A) (l : list A),
    m < length l ->
    m <> n ->
    nth_error (update_nth n a l) m = nth_error l m.
Proof.
  intros A n m a l Hlen Hneq; revert n m Hlen Hneq.
  induction l as [|x xs IH]; intros k j Hlen' Hneq'; simpl in *; [lia|].
  destruct k as [|k'] , j as [|j']; simpl in *.
  - contradiction.
  - reflexivity.
  - reflexivity.
  - apply IH; [lia| congruence].
Qed.

(** Every element of the updated list is either the new value
    or came from the original list. *)
Lemma incl_update :
  forall (A : Type) (n : nat) (a : A) (l : list A),
    incl (update_nth n a l) (a :: l).
Proof.
  intros A n a l.
  revert n.
  induction l as [|h t IH]; intros k y Hin; simpl in *.
  - (* l = [] : force [update_nth] to reduce, then contradiction *)
    destruct k; simpl in Hin; inversion Hin.
  - destruct k as [|k'].
    + (* update at the head *)
      simpl in Hin. destruct Hin as [Hy | Hy].
      * subst y. left. reflexivity.                     (* y = a          *)
      * right. apply in_cons. exact Hy.                 (* y from tail t  *)
    + (* update deeper in the tail *)
      simpl in Hin. destruct Hin as [Hy | Hy].
      * subst y. right. left. reflexivity.              (* y = h          *)
      * (* y originates from [update_nth k' a t]        *)
        specialize (IH k' y Hy) as Hin_a_t.
        destruct Hin_a_t as [Hya | Hyt].
        -- left. exact Hya.                             (* y = a          *)
        -- right. apply in_cons. exact Hyt.             (* y in tail t    *)
Qed.

(* -------------------------------------------------------------------- *)
(** ** Example *)

Example update_nth_example :
  update_nth 1 42 [10; 11; 12] = [10; 42; 12].
Proof. reflexivity. Qed.

Example nth_error_update_eq_example :
  nth_error (update_nth 2 99 [2;4;6;8]) 2 = Some 99.
Proof.
  (* index 2 is within bounds (length = 4) *)
  apply nth_error_update_eq.
  simpl; lia.
Qed.

Example nth_error_update_neq_example :
  nth_error (update_nth 1 42 [7;8;9]) 0 = Some 7.
Proof.
  (* index 0 is different from updated index 1 *)
  apply nth_error_update_neq; simpl; lia.
Qed.

(* -------------------------------------------------------------------- *)
(** ** Notes

    *Out‑of‑bounds policy.*  
    When the index *n* exceeds the list length,
    [`update_nth n a l = l`].  The lemmas above target the usual
    in‑range scenarios (`n < length l`) or properties independent of
    bounds (`length_update`, `incl_update`).

    *Relationship to stdlib.*  
    Coq 8.20 introduces a similar function `upd_nth` plus lemmas, but
    earlier releases differ.  Including this 40‑line file keeps
    **Coq Missing Basics** self‑contained and version‑agnostic.
*)
