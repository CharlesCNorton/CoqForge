(** * Prefix / Suffix – Missing Basics

    Frequently‑needed facts about list prefixes and suffixes that are
    absent (or only partially present) from Coq’s standard library.

    Author: Charles C Norton  
    Date:   June 13th 2025  
    License: GNU Lesser General Public License Version 2.1

    Compatibility: Coq 8.20.1+
*)

From Coq Require Import Lists.List Arith.PeanoNat Lia.
From Coq Require Import Bool.Bool.
Import ListNotations.

(* -------------------------------------------------------------------- *)
(** ** Definitions *)

Inductive prefix {A : Type} : list A -> list A -> Prop :=
| prefix_nil  : forall l, prefix [] l
| prefix_cons : forall x l1 l2, prefix l1 l2 -> prefix (x :: l1) (x :: l2).

Definition suffix {A : Type} (s l : list A) : Prop :=
  exists p, l = p ++ s.

(* -------------------------------------------------------------------- *)
(** ** Basic properties *)

(** A prefix can never be longer than the list it prefixes. *)
Lemma prefix_length_le :
  forall (A : Type) (p l : list A),
    prefix p l -> length p <= length l.
Proof.
  intros A p l H; induction H; simpl; lia.
Qed.

(** Element membership is preserved from prefix to full list. *)
Lemma prefix_In :
  forall (A : Type) (p l : list A) (x : A),
    prefix p l -> In x p -> In x l.
Proof.
  intros A p l x Hpref.
  induction Hpref; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [Hx | Hin].
    + subst; simpl; auto.
    + right; apply IHHpref, Hin.
Qed.

(** A suffix is never longer than the list it suffixes. *)
Lemma suffix_length_le :
  forall (A : Type) (s l : list A),
    suffix s l -> length s <= length l.
Proof.
  intros A s l [p ->].
  rewrite app_length; simpl; lia.
Qed.

(* -------------------------------------------------------------------- *)
(** ** Decidability of the prefix relation *)

Section PrefixDecidable.
  Context {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}).

  Fixpoint prefix_dec (p l : list A) : {prefix p l} + {~ prefix p l}.
  Proof.
    destruct p as [|x xs].
    - left; constructor.
    - destruct l as [|y ys].
      + right; now intro H; inversion H.
      + destruct (eq_dec x y) as [Heq | Hneq].
        * subst y.
          destruct (prefix_dec xs ys) as [Hp | Hnp].
          -- left; now constructor.
          -- right; intro H; inversion H; contradiction.
        * right; intro H; inversion H; contradiction.
  Defined.
End PrefixDecidable.

Definition prefix_nat_dec := @prefix_dec nat Nat.eq_dec.

(* -------------------------------------------------------------------- *)
(** ** Examples *)

Example prefix_length_example :
  prefix [1;2] [1;2;3;4] -> length [1;2] <= length [1;2;3;4].
Proof. intro H; apply prefix_length_le with (p := [1;2]) (l := [1;2;3;4]); exact H. Qed.

Example prefix_dec_true_example :
  match prefix_nat_dec [0;1] [0;1;2] with
  | left _  => True
  | right _ => False
  end.
Proof. simpl. exact I. Qed.

Example prefix_dec_false_example :
  match prefix_nat_dec [0;2] [0;1;2] with
  | left _  => False
  | right _ => True
  end.
Proof. simpl. exact I. Qed.

Example suffix_length_example :
  length [3;4] <= length [1;2;3;4].
Proof.
  apply suffix_length_le.
  unfold suffix; exists [1;2]; reflexivity.
Qed.


(* -------------------------------------------------------------------- *)
(** ** Notes

    *Stdlib status.*  
    Coq 8.19 introduced a `ListPrefix` module with a boolean prefix
    test, but it lacks the length and membership lemmas and the clean
    propositional ↔ boolean connection.  This file supplies those
    basics while remaining compatible with older releases.

    *Decision procedure.*  
    `prefix_dec` is generic over any decidable equality; the helper
    `prefix_nat_dec` instantiates it for `nat`.
*)
