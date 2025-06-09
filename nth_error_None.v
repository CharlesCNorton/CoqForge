Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(** Basic version: nth_error returns None iff index >= length *)
Lemma nth_error_None {A : Type} (l : list A) (n : nat) :
  nth_error l n = None <-> length l <= n.
Proof.
  split.
  - (* -> direction *)
    generalize dependent n.
    induction l as [|h t IH]; intro n.
    + (* l = [] *)
      simpl. destruct n; intro H; auto with arith.
    + (* l = h :: t *)
      destruct n; simpl; intro H.
      * discriminate.
      * apply le_n_S. apply IH. exact H.
  - (* <- direction *)
    generalize dependent n.
    induction l as [|h t IH]; intro n.
    + (* l = [] *)
      simpl. destruct n; reflexivity.
    + (* l = h :: t *)
      destruct n; simpl; intro H.
      * inversion H.
      * apply IH. apply le_S_n. exact H.
Qed.

(** ** Examples *)

Example nth_error_None_ex1 : 
  nth_error [1; 2; 3] 5 = None.
Proof.
  reflexivity.
Qed.

Example nth_error_None_ex2 : 
  nth_error [1; 2; 3] 3 = None <-> length [1; 2; 3] <= 3.
Proof.
  apply nth_error_None.
Qed.

Example nth_error_None_ex3 : forall (A : Type) (l : list A),
  nth_error l (length l) = None.
Proof.
  intros A l.
  rewrite nth_error_None.
  reflexivity.
Qed.

(** ** Corollaries *)

(** nth_error succeeds iff index < length *)
Lemma nth_error_Some_iff {A : Type} (l : list A) (n : nat) :
  (exists x, nth_error l n = Some x) <-> n < length l.
Proof.
  split.
  - intros [x Hx].
    destruct (le_lt_dec (length l) n) as [Hle | Hlt].
    + (* length l <= n *)
      assert (nth_error l n = None).
      { apply nth_error_None. exact Hle. }
      rewrite H in Hx. discriminate.
    + exact Hlt.
  - intro H.
    destruct (nth_error l n) eqn:Hn.
    + exists a. reflexivity.
    + (* nth_error l n = None *)
      rewrite nth_error_None in Hn.
      apply Nat.lt_nge in H.
      contradiction.
Qed.

(** Out of bounds access always returns None *)
Lemma nth_error_out_of_bounds {A : Type} (l : list A) (n : nat) :
  length l < n -> nth_error l n = None.
Proof.
  intro H.
  rewrite nth_error_None.
  apply Nat.lt_le_incl.
  exact H.
Qed.

(** nth_error on nil always returns None *)
Lemma nth_error_nil {A : Type} (n : nat) :
  nth_error (@nil A) n = None.
Proof.
  rewrite nth_error_None.
  simpl.
  apply Nat.le_0_l.
Qed.

(** Accessing beyond first list in append *)
Lemma nth_error_app_r {A : Type} (l1 l2 : list A) (n : nat) :
  length l1 <= n -> 
  nth_error (l1 ++ l2) n = nth_error l2 (n - length l1).
Proof.
  generalize dependent n.
  induction l1 as [|h1 t1 IH]; intros n Hle.
  - simpl in *. rewrite Nat.sub_0_r. reflexivity.
  - destruct n.
    + simpl in Hle. inversion Hle.
    + simpl in *. apply IH. apply le_S_n. exact Hle.
Qed.

(** ** Notes
    
    This lemma provides the missing half of the characterization of nth_error.
    While the standard library tells us when nth_error succeeds (through
    nth_error_In and related lemmas), it doesn't explicitly state when it fails.
    
    The standard library provides:
    - nth_error_In: if nth_error returns Some, the element is in the list
    - Various lemmas about valid indices
    
    But lacks this basic characterization of when nth_error returns None.
    This forces users to reason by cases or use the definition directly.
    
    This lemma is fundamental for:
    - Proving completeness of bounds checking
    - Establishing that algorithms handle all cases
    - Reasoning about out-of-bounds access
    - Converting between different representations of invalid indices
    
    The proof is straightforward by induction on the list structure,
    mirroring the definition of nth_error. The key insight is that
    nth_error returns None precisely when we've exhausted the list
    before exhausting the index.
    
    Together with nth_error_Some_iff, this gives a complete characterization
    of nth_error's behavior, making it easier to reason about list access
    in a compositional way.
*)
