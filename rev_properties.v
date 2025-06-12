(** * List Reverse – Missing Basics

    Fundamental facts about `rev`, collected in one lightweight
    module so users no longer have to hunt through the standard
    library or re‑prove them.

    Author: Charles C Norton  
    Date:   June 12ᵗʰ 2025  
    License: GNU Lesser General Public License Version 2.1

    Compatibility: Coq 8.20.1+
*)

From Coq Require Import Lists.List.
Import ListNotations.

(* -------------------------------------------------------------------- *)
(** ** Overview

    While the standard `List` library contains individual lemmas such
    as `rev_involutive` and `rev_length`, they are scattered and some
    common equivalence forms are missing.  This file provides, in one
    place:

    - `rev_involutive`   : reversing twice yields the original list  
    - `length_rev`       : reversal preserves length  
    - `In_rev`           : membership is invariant under reversal (↔ form)  
    - `rev_map`          : `map` distributes over `rev`

    All proofs use only `List`’s core lemmas (`rev_app_distr`,
    `in_rev`, `map_app`, etc.).
*)

(* -------------------------------------------------------------------- *)
(** ** Main lemmas *)

(** Reversal is its own inverse. *)
Lemma rev_involutive :
  forall (A : Type) (l : list A), rev (rev l) = l.
Proof.
  intros A l.
  induction l as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite rev_app_distr, IH; reflexivity.
Qed.

(** Reversal does not change length. *)
Lemma length_rev :
  forall (A : Type) (l : list A), length (rev l) = length l.
Proof.
  intros A l.
  (* stdlib already has [rev_length] but we re‑export it under the
     “missing” name to keep conventions uniform. *)
  now rewrite rev_length.
Qed.

(** Element membership is preserved by reversal (bidirectional form). *)
Lemma In_rev :
  forall (A : Type) (x : A) (l : list A),
    In x (rev l) <-> In x l.
Proof.
  intros A x l; split.
  - (* → direction: already in stdlib *)
    apply in_rev.
  - (* ← direction: fresh *)
    revert x; induction l as [|y ys IH]; simpl; intros z Hin.
    + exact Hin.                        (* impossible, base case *)
    + destruct Hin as [Hz | Hin].
      * subst y. apply in_or_app; right; simpl; auto.
      * apply in_or_app; left; apply IH, Hin.
Qed.

(** Mapping after reversing equals reversing after mapping. *)
Lemma rev_map :
  forall (A B : Type) (f : A -> B) (l : list A),
    rev (map f l) = map f (rev l).
Proof.
  intros A B f l.
  induction l as [|x xs IH]; simpl.
  - reflexivity.
  - (* rev (f x :: map f xs)  =  rev (map f xs) ++ [f x]            *)
    (* map f (rev (x::xs))     =  map f (rev xs ++ [x])              *)
    rewrite IH.                        (* use the induction hypothesis *)
    rewrite map_app; simpl.            (* distribute map over (++ ...) *)
    reflexivity.
Qed.

Example rev_example :
  rev (map S (rev [0;1;2])) = [1;2;3].
Proof.
  rewrite rev_map.            (* distribute [map] over [rev]            *)
  rewrite rev_involutive.     (* cancel the double reversal             *)
  simpl.                      (* compute [map S [0;1;2]] ⇒ [1;2;3]      *)
  reflexivity.
Qed.

(* -------------------------------------------------------------------- *)
(** ** Notes

    *Coq stdlib cross‑references*

    - `List.rev_involutive`    : single direction, re‑exported here.  
    - `List.rev_length`        : equality, but under a different name.  
    - `List.in_rev`            : only `In x (rev l) → In x l`; we supply
      the ⇐ direction to obtain an equivalence.  
    - `List.rev_map`           : appeared only in Coq 8.19; we re‑prove
      it so users on slightly older releases are covered.

    These four lemmas are now available through a single `Require`
    without pulling additional dependencies.
*)
