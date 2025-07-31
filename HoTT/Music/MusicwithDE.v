(** ================================================================= *)
(** A Full Formalization of Musical Set Theory in Homotopy Type Theory
    
    This library provides a foundation for formalizing mathematical
    music theory using Homotopy Type Theory (HoTT) with decideable equality.
    
    Author: Charles Norton
    Date: July 31st 2025
    ================================================================= *)

(** ================================================================= *)
(** Dependencies                                                      *)
(** ================================================================= *)

(** Core HoTT foundations *)
From HoTT Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids.
From HoTT Require Import Basics.Decidable Basics.Equivalences.

(** Types and type formers *)
From HoTT Require Import Types.Forall Types.Sigma Types.Paths Types.Unit Types.Prod.
From HoTT Require Import Types.Sum Types.Bool Types.Arrow Types.Universe.

(** Truncation machinery *)
From HoTT Require Import Truncations.Core.

(** Colimits for quotients *)
From HoTT Require Import Colimits.Quotient.

(** Numeric types *)
From HoTT Require Import Spaces.BinInt.Core Spaces.BinInt.Spec.
From HoTT Require Import Spaces.Nat.Core Spaces.Nat.Arithmetic.
From HoTT Require Import Spaces.Finite.Fin.

(** Algebraic structures *)
From HoTT Require Import Algebra.Groups Algebra.AbGroups.
From HoTT Require Import Classes.interfaces.canonical_names.

(** Open standard scopes *)
Local Open Scope path_scope.
Local Open Scope type_scope.

(** ================================================================= *)
(** Section 1: Octave Equivalence Relation                           *)
(** ================================================================= *)

(** The fundamental equivalence relation for pitch classes.
    Two integers m and n are octave-equivalent if they differ by
    a multiple of 12 semitones. This captures the musical notion
    that pitches separated by octaves are functionally equivalent
    in many musical contexts.
    
    Formally: m ~ n ⟺ ∃k ∈ Z. n = m + 12k *)

Definition octave_equiv : BinInt -> BinInt -> Type :=
  fun m n => { k : BinInt | n = m + 12 * k }%binint.
  
(** We must prove that octave_equiv is an equivalence relation.
    This requires showing reflexivity, symmetry, and transitivity. *)

(** Reflexivity: Every integer is octave-equivalent to itself *)
Lemma octave_equiv_refl : forall n : BinInt, octave_equiv n n.
Proof.
  intro n.
  (* We need to show ∃k. n = n + 12k *)
  (* Taking k = 0 gives n = n + 12·0 = n + 0 = n *)
  exists 0%binint.
  (* Now we must prove: n = (n + 12 * 0)%binint *)
  assert (H1 : (12 * 0 = 0)%binint).
  { apply binint_mul_0_r. }
  rewrite H1.
  (* Now we need: n = (n + 0)%binint *)
  symmetry.
  apply binint_add_0_r.
Defined.

(** Symmetry: If m ~ n then n ~ m *)
Lemma octave_equiv_sym : forall m n : BinInt, 
  octave_equiv m n -> octave_equiv n m.
Proof.
  intros m n H.
  (* H tells us ∃k. n = m + 12k *)
  destruct H as [k Hk].
  (* Hk : n = (m + 12 * k)%binint *)
  (* We need to show ∃k'. m = n + 12k' *)
  (* From n = m + 12k, we get m = n - 12k = n + 12(-k) *)
  exists (binint_negation k).
  (* Goal: m = (n + 12 * binint_negation k)%binint *)
  (* Rewrite using Hk *)
  rewrite Hk.
  (* Goal: m = ((m + 12 * k) + 12 * binint_negation k)%binint *)
  rewrite <- binint_add_assoc.
  (* Goal: m = (m + (12 * k + 12 * binint_negation k))%binint *)
  assert (H1 : (12 * k + 12 * binint_negation k = 0)%binint).
  { 
    rewrite <- binint_mul_add_distr_l.
    rewrite binint_add_negation_r.
    apply binint_mul_0_r.
  }
  rewrite H1.
  symmetry.
  apply binint_add_0_r.
Defined.

(** Transitivity: If m ~ n and n ~ p then m ~ p *)
Lemma octave_equiv_trans : forall m n p : BinInt,
  octave_equiv m n -> octave_equiv n p -> octave_equiv m p.
Proof.
  intros m n p H1 H2.
  (* H1: ∃k1. n = m + 12k1 *)
  (* H2: ∃k2. p = n + 12k2 *)
  destruct H1 as [k1 Hk1].
  destruct H2 as [k2 Hk2].
  (* Hk1: n = (m + 12 * k1)%binint *)
  (* Hk2: p = (n + 12 * k2)%binint *)
  (* We need: ∃k. p = m + 12k *)
  (* Substituting: p = (m + 12k1) + 12k2 = m + 12(k1 + k2) *)
  exists (k1 + k2)%binint.
  (* Goal: p = (m + 12 * (k1 + k2))%binint *)
  rewrite Hk2.
  rewrite Hk1.
  (* Goal: (m + 12 * k1 + 12 * k2)%binint = (m + 12 * (k1 + k2))%binint *)
  rewrite binint_mul_add_distr_l.
  (* Goal: (m + 12 * k1 + 12 * k2)%binint = (m + (12 * k1 + 12 * k2))%binint *)
  symmetry.
  apply binint_add_assoc.
Defined.

(** ================================================================= *)
(** Section 2: Decidable Octave Equivalence                          *)
(** ================================================================= *)

(** Two integers are octave equivalent iff their difference is a multiple of 12.
    We need to decide if n - m = 12k for some k. *)

(** First, let's check if a given k witnesses octave equivalence *)
Definition is_octave_witness (m n k : BinInt) : Bool :=
  match dec (n = (m + 12 * k)%binint) with
  | inl _ => true
  | inr _ => false
  end.
  
(** Convert nat to Core.Pos *)
Fixpoint pos_of_nat (n : nat) : Core.Pos :=
  match n with
  | O => Core.xH
  | S n' => Core.pos_succ (pos_of_nat n')
  end.
 
 (** Check if k is in the range -bound to bound *)
Fixpoint check_witness_in_range (m n : BinInt) (bound : nat) : Bool :=
  match bound with
  | O => is_octave_witness m n 0%binint
  | S bound' => 
      orb (is_octave_witness m n (pos (pos_of_nat (S bound'))))
      (orb (is_octave_witness m n (neg (pos_of_nat (S bound'))))
           (check_witness_in_range m n bound'))
  end.
 
(** Search for a witness k such that n = m + 12k *)
Fixpoint find_octave_witness (m n : BinInt) (bound : nat) : option BinInt :=
  match bound with
  | O => 
      if is_octave_witness m n 0%binint then Some 0%binint else None
  | S bound' =>
      let k_pos := pos (pos_of_nat (S bound')) in
      let k_neg := neg (pos_of_nat (S bound')) in
      if is_octave_witness m n k_pos then Some k_pos
      else if is_octave_witness m n k_neg then Some k_neg
      else find_octave_witness m n bound'
  end.
 
 (** When is_octave_witness returns true, we have a valid witness *)
Lemma is_octave_witness_true (m n k : BinInt) :
  is_octave_witness m n k = true -> n = (m + 12 * k)%binint.
Proof.
  unfold is_octave_witness.
  intro H.
  destruct (dec (n = (m + 12 * k)%binint)) as [H_eq | H_neq].
  - exact H_eq.
  - discriminate H.
Defined.
 
(** If we find a witness at 0, it's valid *)
Lemma find_witness_zero (m n : BinInt) :
  is_octave_witness m n 0%binint = true -> n = (m + 12 * 0)%binint.
Proof.
  intro H.
  apply is_octave_witness_true.
  exact H.
Defined.

(** If we find a positive witness, it's valid *)
Lemma find_witness_pos (m n : BinInt) (p : Core.Pos) :
  is_octave_witness m n (pos p) = true -> n = (m + 12 * pos p)%binint.
Proof.
  intro H.
  apply is_octave_witness_true.
  exact H.
Defined.

(** If we find a negative witness, it's valid *)
Lemma find_witness_neg (m n : BinInt) (p : Core.Pos) :
  is_octave_witness m n (neg p) = true -> n = (m + 12 * neg p)%binint.
Proof.
  intro H.
  apply is_octave_witness_true.
  exact H.
Defined.

(** Helper to handle the pattern matching in find_octave_witness *)
Lemma find_octave_witness_base (m n : BinInt) :
  forall k, find_octave_witness m n 0 = Some k -> n = (m + 12 * k)%binint.
Proof.
  intros k H.
  simpl in H.
  remember (is_octave_witness m n 0%binint) as wit eqn:Heqwit.
  destruct wit.
  - injection H. intro H_eq.
    rewrite <- H_eq.
    apply find_witness_zero.
    exact Heqwit.
  - discriminate H.
Defined.

(** Helper: When positive witness is found at S bound' *)
Lemma find_witness_succ_pos (m n : BinInt) (bound' : nat) :
  is_octave_witness m n (pos (pos_of_nat (S bound'))) = true ->
  find_octave_witness m n (S bound') = Some (pos (pos_of_nat (S bound'))).
Proof.
  intro H.
  simpl.
  rewrite H.
  reflexivity.
Defined.

(** Helper: When negative witness is found at S bound' and positive is not *)
Lemma find_witness_succ_neg (m n : BinInt) (bound' : nat) :
  is_octave_witness m n (pos (pos_of_nat (S bound'))) = false ->
  is_octave_witness m n (neg (pos_of_nat (S bound'))) = true ->
  find_octave_witness m n (S bound') = Some (neg (pos_of_nat (S bound'))).
Proof.
  intros H1 H2.
  simpl.
  rewrite H1.
  rewrite H2.
  reflexivity.
Defined.

(** Helper: When no witness is found at S bound' *)
Lemma find_witness_succ_none (m n : BinInt) (bound' : nat) :
  is_octave_witness m n (pos (pos_of_nat (S bound'))) = false ->
  is_octave_witness m n (neg (pos_of_nat (S bound'))) = false ->
  find_octave_witness m n (S bound') = find_octave_witness m n bound'.
Proof.
  intros H1 H2.
  simpl.
  rewrite H1.
  rewrite H2.
  reflexivity.
Defined.  

(** Helper: If find_octave_witness at S bound' returns Some k and positive witness is true, then k is that positive witness *)
Lemma find_witness_succ_extract_pos (m n : BinInt) (bound' : nat) (k : BinInt) :
  is_octave_witness m n (pos (pos_of_nat (S bound'))) = true ->
  find_octave_witness m n (S bound') = Some k ->
  k = pos (pos_of_nat (S bound')).
Proof.
  intros H1 H2.
  rewrite (find_witness_succ_pos m n bound' H1) in H2.
  injection H2.
  intro H_eq.
  symmetry.
  exact H_eq.
Defined.

(** Helper: If find_octave_witness at S bound' returns Some k and negative witness is true but positive is false, then k is that negative witness *)
Lemma find_witness_succ_extract_neg (m n : BinInt) (bound' : nat) (k : BinInt) :
  is_octave_witness m n (pos (pos_of_nat (S bound'))) = false ->
  is_octave_witness m n (neg (pos_of_nat (S bound'))) = true ->
  find_octave_witness m n (S bound') = Some k ->
  k = neg (pos_of_nat (S bound')).
Proof.
  intros H1 H2 H3.
  rewrite (find_witness_succ_neg m n bound' H1 H2) in H3.
  injection H3.
  intro H_eq.
  symmetry.
  exact H_eq.
Defined.

(** When find_octave_witness returns Some k, it's a valid witness *)
Lemma find_octave_witness_some (m n : BinInt) (bound : nat) (k : BinInt) :
  find_octave_witness m n bound = Some k -> n = (m + 12 * k)%binint.
Proof.
  generalize dependent k.
  induction bound as [|bound' IH].
  - (* Base case *)
    apply find_octave_witness_base.
  - (* Inductive case *)
    intros k H.
    remember (is_octave_witness m n (pos (pos_of_nat (S bound')))) as b1 eqn:Hb1.
    remember (is_octave_witness m n (neg (pos_of_nat (S bound')))) as b2 eqn:Hb2.
    destruct b1; destruct b2.
    + (* both true - take positive *)
      assert (Hk: k = pos (pos_of_nat (S bound'))).
      { apply (find_witness_succ_extract_pos m n bound' k Hb1 H). }
      rewrite Hk.
      apply find_witness_pos.
      exact Hb1.
    + (* b1 true, b2 false *)
      assert (Hk: k = pos (pos_of_nat (S bound'))).
      { apply (find_witness_succ_extract_pos m n bound' k Hb1 H). }
      rewrite Hk.
      apply find_witness_pos.
      exact Hb1.
    + (* b1 false, b2 true *)
      assert (Hk: k = neg (pos_of_nat (S bound'))).
      { apply (find_witness_succ_extract_neg m n bound' k Hb1 Hb2 H). }
      rewrite Hk.
      apply find_witness_neg.
      exact Hb2.
    + (* both false *)
      rewrite (find_witness_succ_none m n bound' Hb1 Hb2) in H.
      apply IH.
      exact H.
Defined.

(** If is_octave_witness returns false, then k is not a witness *)
Lemma is_octave_witness_false (m n k : BinInt) :
  is_octave_witness m n k = false -> n <> (m + 12 * k)%binint.
Proof.
  unfold is_octave_witness.
  intro H.
  destruct (dec (n = (m + 12 * k)%binint)) as [H_eq | H_neq].
  - discriminate H.
  - exact H_neq.
Defined.

(** Absolute value of a binary integer *)
Definition binint_abs (n : BinInt) : BinInt :=
  match n with
  | neg p => pos p
  | n => n
  end.
