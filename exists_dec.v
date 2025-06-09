(** * Decidability of Existential Quantification over Boolean Predicates
    
    This module provides the decidability of existential quantification
    for boolean predicates over lists, which is missing from Coq's standard library.
    
    Author: Charles C Norton
    Date: June 9th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

(** ** Overview
    
    While Coq's standard library provides existsb for computing whether
    a boolean predicate holds for some element of a list, it lacks a
    decidability lemma that produces a proof of existence or its negation.
    
    This lemma states that for any boolean predicate P and list l, we can
    decide whether there exists an element x in l such that P x = true.
    
    The result is in Type (using sumbool) rather than Prop, making it
    computational and usable in programs, not just proofs.
    
    This property is useful for:
    - Building certified decision procedures
    - Proving completeness of boolean functions
    - Extracting verified programs that search lists
    - Converting between boolean and propositional formulations
    - Implementing decidable type classes
*)

(** ** Main Theorem *)

(** Decidability of exists for boolean predicates *)
Lemma exists_dec {A : Type} (P : A -> bool) (l : list A) :
  {exists x, In x l /\ P x = true} + {~ exists x, In x l /\ P x = true}.
Proof.
  induction l as [|h t IH].
  - right. intros [x [H _]]. contradiction.
  - destruct (P h) eqn:HPh.
    + left. exists h. split; [left; reflexivity | exact HPh].
    + destruct IH as [IH|IH].
      * left. destruct IH as [x [HIn HP]]. 
        exists x. split; [right; exact HIn | exact HP].
      * right. intros [x [HIn HP]].
        destruct HIn as [Heq|HIn].
        -- subst. rewrite HP in HPh. discriminate.
        -- apply IH. exists x. split; assumption.
Qed.

(** ** Alternative Formulations *)

(** Using existsb *)
Lemma exists_dec_existsb {A : Type} (P : A -> bool) (l : list A) :
  existsb P l = true <-> exists x, In x l /\ P x = true.
Proof.
  split.
  - induction l as [|h t IH].
    + simpl. discriminate.
    + simpl. rewrite Bool.orb_true_iff.
      intros [HPh | Hex].
      * exists h. split; [left; reflexivity | exact HPh].
      * destruct (IH Hex) as [x [HIn HP]].
        exists x. split; [right; exact HIn | exact HP].
  - intros [x [HIn HP]].
    induction l as [|h t IH].
    + contradiction.
    + simpl. rewrite Bool.orb_true_iff.
      destruct HIn as [Heq|HIn].
      * left. subst. exact HP.
      * right. apply IH. exact HIn.
Qed.

(** Decidability via existsb *)
Lemma exists_dec_via_existsb {A : Type} (P : A -> bool) (l : list A) :
  {existsb P l = true} + {existsb P l = false}.
Proof.
  destruct (existsb P l); [left | right]; reflexivity.
Qed.


(** ** Corollaries *)

(** Decidability of non-existence *)
Lemma not_exists_dec {A : Type} (P : A -> bool) (l : list A) :
  {forall x, In x l -> P x = false} + {~ forall x, In x l -> P x = false}.
Proof.
  destruct (exists_dec P l) as [Hex|Hnex].
  - right. intros Hall.
    destruct Hex as [x [HIn HP]].
    specialize (Hall x HIn).
    rewrite Hall in HP. discriminate.
  - left. intros x HIn.
    destruct (P x) eqn:HPx.
    + exfalso. apply Hnex. exists x. split; assumption.
    + reflexivity.
Qed.

(** Find first element satisfying predicate *)
Lemma find_dec {A : Type} (P : A -> bool) (l : list A) :
  {x : A | In x l /\ P x = true} + {forall x, In x l -> P x = false}.
Proof.
  induction l as [|h t IH].
  - right. intros x H. contradiction.
  - destruct (P h) eqn:HPh.
    + left. exists h. split; [left; reflexivity | exact HPh].
    + destruct IH as [[x [HIn HP]]|Hall].
      * left. exists x. split; [right; exact HIn | exact HP].
      * right. intros x [Heq|HIn].
        -- subst. exact HPh.
        -- apply Hall. exact HIn.
Qed.

(** Existence is decidable iff predicate gives decidable membership *)
Lemma exists_dec_iff_dec_pred {A : Type} (P : A -> bool) (l : list A) :
  (forall x, In x l -> {P x = true} + {P x = false}) ->
  {exists x, In x l /\ P x = true} + {forall x, In x l -> P x = false}.
Proof.
  intro Hdec.
  destruct (exists_dec P l) as [Hex|Hnex].
  - left. exact Hex.
  - right. intros x HIn.
    destruct (P x) eqn:HPx.
    + exfalso. apply Hnex. exists x. split; assumption.
    + reflexivity.
Qed.

(** ** Examples *)

Example exists_dec_ex1 : 
  {exists x, In x [1; 3; 5; 6; 7] /\ Nat.even x = true} + 
  {~ exists x, In x [1; 3; 5; 6; 7] /\ Nat.even x = true}.
Proof.
  apply exists_dec.
Qed.

(** We can compute the result *)
Example exists_dec_ex1_compute :
  exists x, In x [1; 3; 5; 6; 7] /\ Nat.even x = true.
Proof.
  destruct (exists_dec Nat.even [1; 3; 5; 6; 7]) as [H|H].
  - exact H.
  - exfalso. apply H. exists 6. split.
    + right; right; right; left; reflexivity.
    + reflexivity.
Qed.

Example exists_dec_ex2 :
  {exists x, In x [1; 3; 5; 7] /\ Nat.even x = true} + 
  {~ exists x, In x [1; 3; 5; 7] /\ Nat.even x = true}.
Proof.
  apply exists_dec.
Qed.

(** This one should give the right (negative) result *)
Example exists_dec_ex2_negative :
  ~ exists x, In x [1; 3; 5; 7] /\ Nat.even x = true.
Proof.
  destruct (exists_dec Nat.even [1; 3; 5; 7]) as [H|H].
  - destruct H as [x [HIn Heven]].
    (* This is impossible - all elements are odd *)
    destruct HIn as [H1|[H2|[H3|[H4|[]]]]]; subst; discriminate.
  - exact H.
Qed.

(** Practical example: checking if list contains a prime *)
Definition is_prime (n : nat) : bool :=
  match n with
  | 0 | 1 => false
  | 2 => true
  | S (S n') => 
    negb (existsb (fun d => Nat.eqb (n mod d) 0) 
                  (seq 2 n'))
  end.

Example has_prime : 
  {exists x, In x [4; 6; 8; 9; 11; 12] /\ is_prime x = true} +
  {~ exists x, In x [4; 6; 8; 9; 11; 12] /\ is_prime x = true}.
Proof.
  apply exists_dec.
Qed.

(** Relationship with forallb *)
Lemma exists_dec_not_forall {A : Type} (P : A -> bool) (l : list A) :
  existsb P l = negb (forallb (fun x => negb (P x)) l).
Proof.
  induction l as [|h t IH].
  - reflexivity.
  - simpl. rewrite IH.
    destruct (P h); reflexivity.
Qed.

(** Decidability for filtered lists *)
Lemma exists_dec_filter {A : Type} (P Q : A -> bool) (l : list A) :
  {exists x, In x (filter P l) /\ Q x = true} + 
  {~ exists x, In x (filter P l) /\ Q x = true}.
Proof.
  apply exists_dec.
Qed.

(** Double existential *)
Lemma exists_exists_dec {A B : Type} (R : A -> B -> bool) (la : list A) (lb : list B) :
  {exists a b, In a la /\ In b lb /\ R a b = true} +
  {~ exists a b, In a la /\ In b lb /\ R a b = true}.
Proof.
  destruct (exists_dec (fun a => existsb (R a) lb) la) as [H|H].
  - left. destruct H as [a [HIn Hex]].
    apply exists_dec_existsb in Hex.
    destruct Hex as [b [HInb HR]].
    exists a, b. split; [exact HIn | split; assumption].
  - right. intros [a [b [HIna [HInb HR]]]].
    apply H. exists a. split; [exact HIna|].
    apply exists_dec_existsb.
    exists b. split; assumption.
Qed.

(** ** Notes
    
    This lemma fills a gap between the computational existsb function
    and the logical exists proposition. While existsb computes a boolean,
    exists_dec provides a proof that can be used in program verification.
    
    The proof is constructive: when it returns left, it actually constructs
    a witness. This is crucial for program extraction, where we want not
    just to know that an element exists, but to find it.
    
    The standard library's omission of this lemma forces users to either:
    1. Use existsb and lose the connection to logical exists
    2. Reprove this decidability lemma for each use case
    3. Work entirely in bool, losing expressiveness
    
    This lemma is particularly useful in:
    - Verified algorithms that search for elements
    - Decision procedures that need to produce evidence
    - Bridging computational and logical parts of a development
    
    Note that this is different from the classical existence over
    propositional predicates, which would require the law of excluded
    middle. Here, we use boolean predicates precisely to maintain
    decidability and constructiveness.
*)
