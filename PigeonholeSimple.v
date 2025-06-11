(** * Simple Pigeonhole Principle

    A finitary pigeon‑hole principle for lists of natural numbers that
    relies only on Coq’s standard library.

    Author: Charles C Norton  
    Date:   June 11th 2025  
    License: GNU Lesser General Public License Version 2.1

    Compatibility: Coq 8.20.1+
*)

From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lists.List.
From Coq Require Import Lists.ListDec.
From Coq Require Import Lia.
Import ListNotations.

(* -------------------------------------------------------------------- *)
(** ** Auxiliary lemmas *)

(* If an element occurs in a list, [count_occ] is at least 1. *)
Lemma count_occ_In_ge1_nat :
  forall (l : list nat) (x : nat),
    In x l -> 1 <= count_occ Nat.eq_dec l x.
Proof.
  intros l x Hin.
  induction l as [|y ys IH]; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + (* Head is the element *)
      subst y.
      destruct (Nat.eq_dec x x); [lia|contradiction].
    + (* Element is in the tail *)
      destruct (Nat.eq_dec y x).
      * subst y. lia.
      * apply IH, Hin.
Qed.

(* Any list that is *not* [NoDup] contains an element occurring ≥ 2 times. *)
Lemma duplicate_element :
  forall l : list nat,
    ~ NoDup l ->
    exists x, In x l /\ 2 <= count_occ Nat.eq_dec l x.
Proof.
  intros l Hnotdup.
  induction l as [|x xs IH].
  - (* Empty list contradicts the premise *)
    exfalso. apply Hnotdup. constructor.
  - destruct (in_dec Nat.eq_dec x xs) as [Hin | Hnotin].
    + (* Head value already occurs in the tail *)
      exists x. split.
      * simpl; auto.
      * simpl. destruct (Nat.eq_dec x x); [|contradiction].
        assert (1 <= count_occ Nat.eq_dec xs x)
          by (apply count_occ_In_ge1_nat; exact Hin).
        lia.
    + (* Duplicate must be in the tail *)
      assert (~ NoDup xs) as Hdup_tail.
      { intro Hnd; apply Hnotdup; now constructor. }
      specialize (IH Hdup_tail) as [y [Hy Hcnt]].
      exists y. split.
      * simpl; right; exact Hy.
      * simpl. destruct (Nat.eq_dec x y).
        -- subst y. contradiction.
        -- exact Hcnt.
Qed.

(* Length of [seq start len] is exactly [len]. *)
Lemma length_seq :
  forall start len, length (seq start len) = len.
Proof.
  intros start len; revert start.
  induction len as [|len IH]; intros start; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* If [l₁] is [NoDup] and included in [l₂], its length is ≤ length [l₂]. *)
Lemma NoDup_incl_length :
  forall (A : Type) (l1 l2 : list A),
    NoDup l1 ->
    incl l1 l2 ->
    length l1 <= length l2.
Proof.
  intros A l1 l2 Hnd.
  revert l2.
  induction Hnd as [|x l1' Hnotin Hnd' IH]; intros l2 Hincl.
  - (* l1 = [] *) simpl; lia.
  - (* l1 = x :: l1' *)
    simpl.
    (* x must occur in l2, split l2 around x *)
    assert (In x l2) as Hx by (apply Hincl; simpl; auto).
    apply in_split in Hx as [l2a [l2b Hl2]].
    subst l2.
    (* Everything in l1' appears in l2a ++ l2b *)
    assert (incl l1' (l2a ++ l2b)) as Hincl'.
    { intros y Hy.
      specialize (Hincl y (or_intror Hy)) as HyIn.
      rewrite in_app_iff in HyIn; simpl in HyIn.
      destruct HyIn as [Hleft | [Heq | Hright]].
      - apply in_or_app; left; exact Hleft.
      - subst y; contradiction.
      - apply in_or_app; right; exact Hright. }
    (* Apply induction hypothesis to the tail *)
    specialize (IH (l2a ++ l2b) Hincl').
    (* Compare lengths *)
    rewrite !app_length in *; simpl in *.
    lia.
Qed.

(* A duplicate‑free list of naturals bounded by [n] has length ≤ [n]. *)
Lemma nodup_upper_bound_length :
  forall (l : list nat) (n : nat),
    NoDup l ->
    (forall x, In x l -> x < n) ->
    length l <= n.
Proof.
  intros l n Hnd Hbound.
  (* Every element of [l] lies in [seq 0 n] *)
  assert (incl l (seq 0 n)) as Hincl.
  { intros x HIn.
    apply in_seq.
    split.
    - lia.                             (* 0 ≤ x *)
    - apply Hbound; exact HIn.         (* x < n *)
  }
  (* Now compare lengths using the previous lemma *)
  eapply NoDup_incl_length in Hnd; [|exact Hincl].
  rewrite length_seq in Hnd.           (* |seq 0 n| = n *)
  exact Hnd.
Qed.

(* -------------------------------------------------------------------- *)
(** ** Main theorem *)

Lemma pigeonhole_simple :
  forall (l : list nat) (n : nat),
    (forall x, In x l -> x < n) ->          (* every value < n *)
    n < length l ->                         (* more pigeons than holes *)
    exists x,                               (* some value …              *)
      In x l /\                             (* … occurs in the list …    *)
      2 <= count_occ Nat.eq_dec l x.        (* … at least twice          *)
Proof.
  intros l n Hbound Hlong.
  destruct (NoDup_dec Nat.eq_dec l) as [Hnd | Hnd].
  - (* If [l] were duplicate‑free, its length cannot exceed [n] *)
    pose proof (nodup_upper_bound_length l n Hnd Hbound) as Hle.
    lia.                                     (* contradicts [n < |l|] *)
  - (* Otherwise a duplicate element exists – obtain it *) 
    apply duplicate_element in Hnd; exact Hnd.
Qed.

(** ** Corollary *)

(* A list of naturals longer than [n] and bounded by [n] **cannot** be [NoDup]. *)
Corollary pigeonhole_simple_not_NoDup :
  forall (l : list nat) (n : nat),
    (forall x, In x l -> x < n) ->
    n < length l ->
    ~ NoDup l.
Proof.
  intros l n Hbound Hlong Hnodup.
  pose proof (nodup_upper_bound_length l n Hnodup Hbound) as Hle.
  lia.
Qed.

(** ** Example *)

Example pigeonhole_example :
  exists x, In x [0; 0] /\ 2 <= count_occ Nat.eq_dec [0; 0] x.
Proof.
  (* 1.  Every element of [0;0] is < 1. *)
  assert (Hbound : forall y, In y [0; 0] -> y < 1).
  { intros y Hy; destruct Hy as [->|[->|[]]]; lia. }
  (* 2.  Apply the main theorem with n := 1 (|[0;0]| = 2 > 1). *)
  apply (pigeonhole_simple [0; 0] 1); simpl; try lia; exact Hbound.
Qed.

(** ** Dual form *)

(* A duplicate‑free list of naturals whose elements are all < n
   can never be longer than n. *)
Corollary pigeonhole_simple_NoDup_length :
  forall (l : list nat) (n : nat),
    NoDup l ->
    (forall x, In x l -> x < n) ->
    length l <= n.
Proof.
  intros l n Hnd Hbound.
  apply nodup_upper_bound_length; assumption.
Qed.

(* -------------------------------------------------------------------- *)
(** ** Notes

    - **Purpose and scope.**  This file delivers a *self‑contained*
      finite pigeon‑hole principle for lists of natural numbers,
      requiring *only* Coq’s standard library.  It avoids heavier
      alternatives such as MathComp’s `FinFun`/`FinSet` or stdpp’s
      finite‑set infrastructure.

    - **Proof structure recap.**
      1.  `NoDup_incl_length` shows that a duplicate‑free list
          included in another list cannot be longer than the latter.
      2.  Instantiating the “other list” with `seq 0 n` yields
         `nodup_upper_bound_length`.
      3.  If a list is longer than `n`, duplicate‑freedom contradicts
         step 2, so `pigeonhole_simple` must exhibit a duplicate,
         which `duplicate_element` constructs explicitly.

    - **Constructivity.**  All proofs are constructive; the witness
      produced by `pigeonhole_simple` can be *computed* and reused in
      further developments.

    - **Why this is not in stdlib.**  The standard library contains
      many lemmas about `NoDup`, `count_occ`, and `seq` individually,
      but it never puts them together into this classical principle.
      External libraries do, but at the cost of extra dependencies.

    - **Typical usage pattern.**

      ```coq
      (* l : list nat,  n : nat,  Hlen : n < length l *)
      assert (Hbound : forall x, In x l -> x < n) by <prove>;
      destruct (pigeonhole_simple l n Hbound Hlen)
        as [x [Hin Hdup]].
      ```

      You now have a concrete `x` with `2 ≤ count_occ _ l x`.

    - **Compatibility.**  Verified with Coq 8.20.1; should work
      unchanged with any 8.16 or newer release that exports
      `count_occ` for lists.

*)
