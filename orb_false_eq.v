(** * Boolean OR False Equality
    
    This module provides the bidirectional characterization of when
    a boolean OR equals false, which is missing from Coq's standard library.
    
    Author: Charles C Norton
    Date: June 8th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Bool.Bool.
Require Import Coq.Setoids.Setoid.

(** ** Overview
    
    This lemma characterizes when orb (||) equals false: it happens
    if and only if both arguments are false. This is the dual of
    andb_true_eq.
    
    This lemma is useful for:
    - Simplifying boolean expressions in proofs
    - Converting between boolean disjunctions and logical ones
    - Rewriting goals involving || = false
    - Reasoning about negative conditions
*)

(** ** Main Theorem *)

(** a || b = false if and only if a = false and b = false *)
Lemma orb_false_eq : forall a b : bool,
  a || b = false <-> a = false /\ b = false.
Proof.
  intros a b.
  split.
  - (* Forward direction *)
    destruct a, b; simpl; intro H.
    + discriminate.
    + discriminate.
    + discriminate.
    + split; reflexivity.
  - (* Backward direction *)
    intros [Ha Hb].
    rewrite Ha, Hb.
    reflexivity.
Qed.

(** ** Corollaries *)

(** If a || b = false, then a = false *)
Lemma orb_false_l : forall a b : bool,
  a || b = false -> a = false.
Proof.
  intros a b H.
  apply orb_false_eq in H.
  destruct H as [Ha _].
  exact Ha.
Qed.

(** If a || b = false, then b = false *)
Lemma orb_false_r : forall a b : bool,
  a || b = false -> b = false.
Proof.
  intros a b H.
  apply orb_false_eq in H.
  destruct H as [_ Hb].
  exact Hb.
Qed.

(** ** Examples *)

Example orb_false_eq_ex1 : false || false = false <-> false = false /\ false = false.
Proof.
  apply orb_false_eq.
Qed.

Example orb_false_eq_ex2 : forall (f g : nat -> bool) (n : nat),
  f n || g n = false -> g n = false.
Proof.
  intros f g n H.
  apply orb_false_eq in H.
  destruct H as [_ Hg].
  exact Hg.
Qed.

(** Using it for rewriting *)
Example orb_rewrite : forall a b c : bool,
  a || b || c = false -> b = false.
Proof.
  intros a b c H.
  rewrite orb_false_eq in H.
  destruct H as [Hab Hc].
  rewrite orb_false_eq in Hab.
  destruct Hab as [Ha Hb].
  exact Hb.
Qed.

(** De Morgan's law for booleans *)
Example demorgan_bool : forall a b : bool,
  negb (a || b) = negb a && negb b.
Proof.
  intros a b.
  destruct a, b; reflexivity.
Qed.

(** ** Notes
    
    This is the dual of andb_true_eq. Together they provide complete
    characterizations of when boolean operations yield their "absorbing"
    elements (true for &&, false for ||).
    
    The standard library lacks this basic characterization, forcing users
    to repeatedly prove it inline or use awkward workarounds.
*)