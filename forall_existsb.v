(** * Boolean List Quantifiers – Missing Basics

    Bidirectional characterisations of `forallb` and `existsb` that the
    standard library provides only in one direction.

    Author: Charles C Norton
    Date:   June 12ᵗʰ 2025
    License: GNU Lesser General Public License Version 2.1

    Compatibility: Coq 8.20.1+
*)

From Coq Require Import Lists.List Bool.Bool.
Import ListNotations.

(* -------------------------------------------------------------------- *)
(** ** Overview

    Stdlib offers

    - `forallb_forall`   :  `forallb f l = true → ∀ x, In x l → f x = true`
    - `existsb_exists`   :  `existsb f l = true → ∃ x, In x l ∧ f x = true`

    but *not* the converse directions.  The ⇐ directions are needed
    whenever one wants to *compute* the boolean once a logical proof is
    at hand.  This file supplies the missing halves and packages the
    results as proper equivalences.
*)

(* -------------------------------------------------------------------- *)
(** ** Main lemmas *)

(** `forallb` viewed as a logical universal quantifier over a list. *)
Lemma forallb_forall_iff :
  forall (A : Type) (f : A -> bool) (l : list A),
    forallb f l = true <-> (forall x, In x l -> f x = true).
Proof.
  intros A f l; split.
  - (* → direction: stdlib *) apply forallb_forall.
  - (* ← direction: induction on the list *)
    intros H.
    induction l as [|a l' IH]; simpl.
    + reflexivity.
    + rewrite (H a (or_introl eq_refl)).
      apply IH. intros x HIn.
      apply H; right; exact HIn.
Qed.

(* -------------------------------------------------------------------- *)
(** ** Helpers for the ⇐ direction *)

(* Produce [existsb f l = true] from a concrete witness in the list. *)
Lemma existsb_true_of_exists
      (A : Type) (f : A -> bool) (l : list A) (x : A) :
  In x l -> f x = true -> existsb f l = true.
Proof.
  induction l as [|y ys IH]; intros Hin Hfx; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + rewrite Hfx; reflexivity.
    + apply orb_true_intro; right.
      apply IH; assumption.
Qed.

(* -------------------------------------------------------------------- *)
(** ** `existsb` equivalence (both directions) *)

Lemma existsb_exists_iff :
  forall (A : Type) (f : A -> bool) (l : list A),
    existsb f l = true <-> (exists x, In x l /\ f x = true).
Proof.
  intros A f l; split.
  - (* → direction: stdlib already provides this *)
    apply existsb_exists.
  - (* ← direction: build the boolean result from a witness *)
    intros [x [Hin Hfx]].
    exact (existsb_true_of_exists _ _ _ _ Hin Hfx).
Qed.

(* -------------------------------------------------------------------- *)
(** ** Examples *)

From Coq Require Import Arith.PeanoNat.   (* for [Nat.even] and [<?] *)

Example forallb_example :
  forallb (fun n => n <? 3) [0; 1; 2] = true.
Proof. reflexivity. Qed.

Example forallb_to_logic_example :
  forall x, In x [0; 1; 2] -> (x <? 3) = true.
Proof.
  apply (proj1 (forallb_forall_iff _ _ _)).
  reflexivity.
Qed.

Example existsb_example :
  existsb Nat.even [3; 4; 5] = true.
Proof. reflexivity. Qed.

Example existsb_from_logic_example :
  exists n, In n [3; 4; 5] /\ Nat.even n = true.
Proof.
  apply (proj1 (existsb_exists_iff _ _ _)).
  simpl. reflexivity.
Qed.

(* -------------------------------------------------------------------- *)
(** ** Notes

    *Why are these handy?*  
    When you run `cbv` or `vm_compute` you often obtain a concrete
    boolean such as `forallb f l`, then want to turn it into usable
    hypotheses about every element of `l`.  Conversely, once you have
    proved a logical property about all (or some) elements, you may
    wish to *re‑evaluate* the boolean to `true` so that rewrite and
    decision procedures can act on it.  The `↔` lemmas added here
    remove that impedance mismatch without requiring any external
    library.
*)

