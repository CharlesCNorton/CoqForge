(** * Boolean AND True Equality
    
    This module provides the bidirectional characterization of when
    a boolean AND equals true, which is missing from Coq's standard library.
    
    Author: Charles C Norton
    Date: June 8th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Bool.Bool.
Require Import Coq.Setoids.Setoid.

(** ** Overview
    
    This lemma characterizes when andb (&&) equals true: it happens
    if and only if both arguments are true. While obvious, this 
    bidirectional version is not in the standard library.
    
    The standard library provides only the forward direction as
    [andb_true_iff], but not as an equality.
    
    This lemma is useful for:
    - Simplifying boolean expressions in proofs
    - Converting between boolean conjunctions and logical ones
    - Rewriting goals involving && = true
    - Automation tactics that work with boolean equality
*)

(** ** Main Theorem *)

(** a && b = true if and only if a = true and b = true *)
Lemma andb_true_eq : forall a b : bool,
  a && b = true <-> a = true /\ b = true.
Proof.
  intros a b.
  split.
  - (* Forward direction *)
    destruct a, b; simpl; intro H.
    + split; reflexivity.
    + discriminate.
    + discriminate.
    + discriminate.
  - (* Backward direction *)
    intros [Ha Hb].
    rewrite Ha, Hb.
    reflexivity.
Qed.

(** ** Corollaries *)

(** If a && b = true, then a = true *)
Lemma andb_true_l : forall a b : bool,
  a && b = true -> a = true.
Proof.
  intros a b H.
  apply andb_true_eq in H.
  destruct H as [Ha _].
  exact Ha.
Qed.

(** If a && b = true, then b = true *)
Lemma andb_true_r : forall a b : bool,
  a && b = true -> b = true.
Proof.
  intros a b H.
  apply andb_true_eq in H.
  destruct H as [_ Hb].
  exact Hb.
Qed.

(** ** Examples *)

Example andb_true_eq_ex1 : true && true = true <-> true = true /\ true = true.
Proof.
  apply andb_true_eq.
Qed.

Example andb_true_eq_ex2 : forall (f g : nat -> bool) (n : nat),
  f n && g n = true -> f n = true.
Proof.
  intros f g n H.
  apply andb_true_eq in H.
  destruct H as [Hf _].
  exact Hf.
Qed.

(** Using it for rewriting *)
Example andb_rewrite : forall a b c : bool,
  a && b && c = true -> b = true.
Proof.
  intros a b c H.
  rewrite andb_true_eq in H.
  destruct H as [Hab Hc].
  rewrite andb_true_eq in Hab.
  destruct Hab as [Ha Hb].
  exact Hb.
Qed.

(** ** Notes
    
    The standard library provides some related lemmas:
    - [andb_true_iff] : a && b = true <-> a = true /\ b = true
      (but only in recent versions)
    - [andb_prop] : a && b = true -> a = true /\ b = true
      (only forward direction)
    
    Our version provides the full bidirectional equality, making it
    more convenient for rewriting in both directions.
*)