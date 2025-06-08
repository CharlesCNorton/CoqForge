(** * Double Implication Decomposition
    
    This module provides the fundamental lemma for decomposing a
    bidirectional implication (iff) into a conjunction of implications,
    which is surprisingly absent from Coq's standard library.
    
    Author: Charles C Norton
    Date: June 8th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

(** ** Overview
    
    The iff connective (↔) represents logical equivalence between two
    propositions. While Coq provides [iff_conj] for the reverse direction
    (building an iff from a conjunction), it lacks the decomposition in
    this direction.
    
    This lemma states: if P ↔ Q, then we have both P → Q and Q → P.
    
    This lemma is essential for:
    - Extracting individual implications from equivalences
    - Converting between proof styles (iff vs separate implications)
    - Applying tactics that work only on implications
    - Decomposing complex equivalences in proofs
    
    Without this lemma, users must repeatedly unfold the definition
    of iff and project out the components manually.
*)

(** ** Main Theorem *)

(** If P is equivalent to Q, then P implies Q and Q implies P *)
Lemma iff_and (P Q : Prop) : (P <-> Q) -> ((P -> Q) /\ (Q -> P)).
Proof.
  intro H.
  exact H.  (* iff is literally defined as this conjunction! *)
Qed.

(** ** Alternative Names and Formulations *)

(** Some users might expect this under different names *)
Lemma iff_to_and (P Q : Prop) : (P <-> Q) -> ((P -> Q) /\ (Q -> P)).
Proof.
  exact (iff_and P Q).
Qed.

Lemma iff_elim (P Q : Prop) : (P <-> Q) -> ((P -> Q) /\ (Q -> P)).
Proof.
  exact (iff_and P Q).
Qed.

(** ** Directional Projections *)

(** Extract just the forward implication *)
Lemma iff_fwd (P Q : Prop) : (P <-> Q) -> (P -> Q).
Proof.
  intro H.
  apply (proj1 (iff_and P Q H)).
Qed.

(** Extract just the backward implication *)
Lemma iff_bwd (P Q : Prop) : (P <-> Q) -> (Q -> P).
Proof.
  intro H.
  apply (proj2 (iff_and P Q H)).
Qed.

(** ** Examples *)

(** Basic usage *)
Example iff_and_ex1 : forall P Q : Prop,
  P <-> Q -> (P -> Q) /\ (Q -> P).
Proof.
  intros P Q.
  apply iff_and.
Qed.

(** Using it to extract one direction *)
Example iff_and_ex2 : forall n m : nat,
  (n = 0 <-> m = 0) -> (n = 0 -> m = 0).
Proof.
  intros n m H.
  apply iff_and in H.
  destruct H as [Hfwd Hbwd].
  exact Hfwd.
Qed.

(** Combining with other logical lemmas *)
Example iff_and_contrapositive : forall P Q : Prop,
  (P <-> Q) -> (~Q -> ~P).
Proof.
  intros P Q H.
  apply iff_and in H.
  destruct H as [HPQ HQP].
  (* Now we can use contrapositive *)
  intros HnQ HP.
  apply HnQ.
  apply HPQ.
  exact HP.
Qed.

(** Working with multiple equivalences *)
Example iff_and_chain : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> ((P -> R) /\ (R -> P)).
Proof.
  intros P Q R HPQ HQR.
  apply iff_and in HPQ.
  apply iff_and in HQR.
  destruct HPQ as [HPQ HQP].
  destruct HQR as [HQR HRQ].
  split.
  - (* P -> R *)
    intro HP.
    apply HQR.
    apply HPQ.
    exact HP.
  - (* R -> P *)
    intro HR.
    apply HQP.
    apply HRQ.
    exact HR.
Qed.

(** ** Relation to Standard Library
    
    The standard library provides the reverse direction:
    - [iff_conj] : (P -> Q) -> (Q -> P) -> (P <-> Q)
    
    But surprisingly lacks this decomposition direction, even though
    iff is literally defined as the conjunction (P -> Q) /\ (Q -> P).
    
    Users are forced to either:
    1. Unfold the definition of iff
    2. Use destruct on the hypothesis
    3. Apply proj1/proj2 manually
    
    Our lemma provides a cleaner, more explicit approach.
*)

(** ** Notes
    
    This might be the simplest missing lemma in Coq's standard library.
    The proof is trivial because iff is definitionally equal to the
    conjunction, yet having it as an explicit lemma improves readability
    and usability of proofs.
    
    In classical logic, iff is often treated as a primitive connective,
    but in Coq's constructive logic, it's defined as a conjunction of
    implications, making this decomposition particularly natural.
*)
