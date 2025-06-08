(** * Successor Flips Evenness
    
    This module provides a fundamental lemma about parity that is
    missing from Coq's standard library: taking the successor of a
    natural number flips its evenness.
    
    Author: Charles C Norton
    Date: June 8th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

(** ** Overview
    
    This lemma captures the intuitive fact that adding 1 to a number
    changes it from even to odd or vice versa. While obvious, this
    property is not explicitly provided in Coq's standard library.
    
    The parity of natural numbers alternates: 0 is even, 1 is odd,
    2 is even, 3 is odd, and so on. This lemma formalizes this
    alternation pattern.
    
    This property is useful for:
    - Reasoning about parity in arithmetic proofs
    - Proving properties of alternating sequences
    - Establishing invariants in algorithms that process even/odd numbers
    - Simplifying case analysis on natural numbers
    - Proving properties of division by 2
*)

(** ** Main Theorem *)

(** The evenness of n is the negation of the evenness of S n *)
Lemma successor_flips_evenness (n : nat) : 
  Nat.even n = negb (Nat.even (S n)).
Proof.
  induction n as [|n' IH].
  - (* Base case: n = 0 *)
    (* Nat.even 0 = true, Nat.even 1 = false, negb false = true *)
    reflexivity.
  - (* Inductive case: n = S n' *)
    (* Need to show: Nat.even (S n') = negb (Nat.even (S (S n'))) *)
    simpl.
    (* By simpl: Nat.even (S n') = negb (Nat.even n') and
                 Nat.even (S (S n')) = Nat.even n' *)
    (* So we need: negb (Nat.even n') = negb (negb (Nat.even n')) *)
    rewrite IH.
    (* Now we have: negb (Nat.even n') = negb (negb (negb (Nat.even (S n')))) *)
    rewrite Bool.negb_involutive.
    (* negb (negb x) = x, so we're done *)
    reflexivity.
Qed.

(** ** Corollaries *)

(** The reverse: evenness of S n is the negation of evenness of n *)
Lemma successor_flips_evenness_rev (n : nat) :
  Nat.even (S n) = negb (Nat.even n).
Proof.
  (* From successor_flips_evenness: Nat.even n = negb (Nat.even (S n)) *)
  (* Apply negb to both sides *)
  rewrite <- (Bool.negb_involutive (Nat.even (S n))).
  (* Now we have: Nat.even (S n) = negb (negb (Nat.even (S n))) *)
  rewrite <- successor_flips_evenness.
  (* Now we have: Nat.even (S n) = negb (Nat.even n) *)
  reflexivity.
Qed.

(** Odd version: oddness also flips with successor *)
Lemma successor_flips_oddness (n : nat) :
  Nat.odd n = negb (Nat.odd (S n)).
Proof.
  unfold Nat.odd.
  rewrite successor_flips_evenness_rev.
  rewrite Bool.negb_involutive.
  reflexivity.
Qed.

(** Two successors preserve evenness *)
Lemma two_successors_preserve_evenness (n : nat) :
  Nat.even n = Nat.even (S (S n)).
Proof.
  rewrite successor_flips_evenness.
  rewrite successor_flips_evenness_rev.
  rewrite Bool.negb_involutive.
  reflexivity.
Qed.

(** ** Examples *)

Example even_odd_pattern : 
  Nat.even 0 = true /\
  Nat.even 1 = false /\
  Nat.even 2 = true /\
  Nat.even 3 = false /\
  Nat.even 4 = true.
Proof.
  repeat split; reflexivity.
Qed.

Example successor_flips_ex1 : Nat.even 10 = negb (Nat.even 11).
Proof.
  apply successor_flips_evenness.
Qed.

Example successor_flips_ex2 : forall n,
  Nat.even n = true -> Nat.even (S n) = false.
Proof.
  intros n H.
  rewrite successor_flips_evenness_rev.
  rewrite H.
  reflexivity.
Qed.

Example alternating_sum : forall n,
  Nat.even n = true ->
  Nat.even n = true /\
  Nat.even (S n) = false /\
  Nat.even (S (S n)) = true.
Proof.
  intros n H.
  split. exact H.
  split.
  - rewrite successor_flips_evenness_rev. rewrite H. reflexivity.
  - rewrite two_successors_preserve_evenness. exact H.
Qed.

(** ** Notes
    
    This lemma is fundamental for any reasoning about parity, yet it's
    missing from the standard library. Users are forced to either:
    1. Prove it inline whenever needed
    2. Reason by cases on n being even or odd
    3. Use the definition of Nat.even directly
    
    Having this as an explicit lemma simplifies many proofs and makes
    the alternating nature of parity explicit.
    
    The proof is by induction, using the fact that Nat.even is defined
    recursively:
    - Nat.even 0 = true
    - Nat.even (S n) = negb (Nat.even n)
    
    This definition already encodes the flipping behavior, but our
    lemma makes it explicit in a more usable form.
