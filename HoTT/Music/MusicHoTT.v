(** ================================================================= *)
(** A Full Formalization of Musical Set Theory in Homotopy Type Theory
    
    This library provides a foundation for formalizing mathematical
    music theory using Homotopy Type Theory (HoTT). By leveraging
    HoTT's native support for quotient types, higher inductive types,
    and homotopical reasoning, we develop a framework for exploring
    both classical and novel mathematical structures in music.

    Author: Charles Norton
    Date: July 2nd 2025
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
    in many musical contexts. *)

Definition octave_equiv : BinInt -> BinInt -> Type :=
  fun m n => { k : BinInt | n = m + 12 * k }%binint.

(** We prove that octave equivalence is indeed an equivalence relation,
    satisfying reflexivity, symmetry, and transitivity. *)

(** Every pitch is octave-equivalent to itself (k = 0) *)
Lemma octave_equiv_refl : forall n, octave_equiv n n.
Proof.
  intro n.
  exists 0%binint.
  rewrite binint_mul_0_r.
  rewrite binint_add_0_r.
  reflexivity.
Defined.

(** If m ~ n with witness k, then n ~ m with witness -k *)
Lemma octave_equiv_sym : forall m n, 
  octave_equiv m n -> octave_equiv n m.
Proof.
  intros m n [k Hk].
  exists (binint_negation k).
  rewrite Hk.
  rewrite <- binint_add_assoc.
  assert (H: (12 * k + 12 * binint_negation k = 0)%binint).
  { rewrite <- binint_mul_add_distr_l.
    rewrite binint_add_negation_r.
    apply binint_mul_0_r. }
  rewrite H.
  symmetry.
  apply binint_add_0_r.
Defined.

(** If m ~ n with witness k1 and n ~ p with witness k2,
    then m ~ p with witness k1 + k2 *)
Lemma octave_equiv_trans : forall m n p,
  octave_equiv m n -> octave_equiv n p -> octave_equiv m p.
Proof.
  intros m n p [k1 Hk1] [k2 Hk2].
  exists (k1 + k2)%binint.
  rewrite Hk2.
  rewrite Hk1.
  rewrite binint_mul_add_distr_l.
  symmetry.
  apply binint_add_assoc.
Defined.


(** ================================================================= *)
(** Section 2: Pitch Classes as a Quotient Type                      *)
(** ================================================================= *)

(** The type of pitch classes is the quotient of integers by octave
    equivalence. This gives us the mathematical structure Z/12Z. *)

Definition PitchClass : Type := 
  Quotient octave_equiv.

(** The canonical quotient map from integers to pitch classes *)
Definition pitch_class_of : BinInt -> PitchClass :=
  class_of octave_equiv.

(** Notation for the quotient map - we write [n] for the pitch class
    containing the integer n *)
Notation "[ n ]" := (pitch_class_of n) (at level 0).

(** The twelve pitch class names, following standard musical notation.
    C = 0, C# = 1, D = 2, etc. These form the standard representatives
    of the equivalence classes. *)

Definition C  : PitchClass := [ 0%binint ].
Definition Cs : PitchClass := [ 1%binint ].  (* C♯/D♭ *)
Definition D  : PitchClass := [ 2%binint ].
Definition Ds : PitchClass := [ 3%binint ].  (* D♯/E♭ *)
Definition E  : PitchClass := [ 4%binint ].
Definition F  : PitchClass := [ 5%binint ].
Definition Fs : PitchClass := [ 6%binint ].  (* F♯/G♭ *)
Definition G  : PitchClass := [ 7%binint ].
Definition Gs : PitchClass := [ 8%binint ].  (* G♯/A♭ *)
Definition A  : PitchClass := [ 9%binint ].
Definition As : PitchClass := [ 10%binint ]. (* A♯/B♭ *)
Definition B  : PitchClass := [ 11%binint ].


(** ================================================================= *)
(** Section 3: Pitch Class Addition                                  *)
(** ================================================================= *)

(** To define addition on pitch classes, we must first prove that
    addition respects the octave equivalence relation. *)

Lemma add_respects_octave_equiv : forall m1 n1 m2 n2,
  octave_equiv m1 n1 -> octave_equiv m2 n2 -> 
  octave_equiv (m1 + m2)%binint (n1 + n2)%binint.
Proof.
  intros m1 n1 m2 n2 [k1 Hk1] [k2 Hk2].
  exists (k1 + k2)%binint.
  rewrite Hk1, Hk2.
  rewrite binint_mul_add_distr_l.
  transitivity ((m1 + m2) + (12 * k1 + 12 * k2))%binint.
  2: reflexivity.
  rewrite <- binint_add_assoc, <- binint_add_assoc.
  f_ap.
  rewrite binint_add_assoc, binint_add_assoc.
  rewrite (binint_add_comm (12 * k1)%binint m2).
  reflexivity.
Defined.

(** Addition on pitch classes is defined by lifting integer addition
    to the quotient. This is well-defined by the previous lemma. *)

Definition pitch_class_add : PitchClass -> PitchClass -> PitchClass.
Proof.
  intro p.
  srapply Quotient_rec.
  - intro m.
    revert p.
    srapply Quotient_rec.
    + intro n.
      exact (pitch_class_of (n + m)%binint).
    + intros n1 n2 Hn.
      apply qglue.
      apply add_respects_octave_equiv.
      * exact Hn.
      * apply octave_equiv_refl.
  - intros m1 m2 Hm.
    revert p.
    srapply Quotient_ind.
    + intro n.
      simpl.
      apply qglue.
      apply add_respects_octave_equiv.
      * apply octave_equiv_refl.
      * exact Hm.
    + intros; apply path_ishprop.
Defined.

(** Infix notation for pitch class addition *)
Notation "p +pc q" := (pitch_class_add p q) (at level 50, left associativity).


(** ================================================================= *)
(** Section 4: Properties of Pitch Class Addition                    *)
(** ================================================================= *)

(** Pitch class addition is associative *)
Lemma pitch_class_add_assoc : forall p q r : PitchClass,
  (p +pc q) +pc r = p +pc (q +pc r).
Proof.
  intros p q r.
  revert r.
  srapply Quotient_ind.
  - intro k.
    revert q.
    srapply Quotient_ind.
    + intro n.
      revert p.
      srapply Quotient_ind.
      * intro m.
        simpl.
        apply ap.
        symmetry.
        apply binint_add_assoc.
      * intros; apply path_ishprop.
    + intros; apply path_ishprop.
  - intros; apply path_ishprop.
Defined.

(** Pitch class addition is commutative *)
Lemma pitch_class_add_comm : forall p q : PitchClass,
  p +pc q = q +pc p.
Proof.
  intros p q.
  revert q.
  srapply Quotient_ind.
  - intro n.
    revert p.
    srapply Quotient_ind.
    + intro m.
      simpl.
      apply ap.
      apply binint_add_comm.
    + intros; apply path_ishprop.
  - intros; apply path_ishprop.
Defined.

(** C (pitch class 0) is the additive identity *)
Lemma pitch_class_add_zero_l : forall p : PitchClass,
  C +pc p = p.
Proof.
  srapply Quotient_ind.
  - intro n.
    unfold C.
    simpl.
    reflexivity.
  - intros; apply path_ishprop.
Defined.

Lemma pitch_class_add_zero_r : forall p : PitchClass,
  p +pc C = p.
Proof.
  srapply Quotient_ind.
  - intro n.
    unfold C.
    simpl.
    apply ap.
    apply binint_add_0_r.
  - intros; apply path_ishprop.
Defined.


(** ================================================================= *)
(** Section 5: Auxiliary Lemmas for Integer Arithmetic               *)
(** ================================================================= *)

(** These lemmas about integer arithmetic are needed for our
    development but are not part of the main musical theory. *)

(** Multiples of 12 are octave-equivalent to 0 *)
Lemma twelve_mult_octave_equiv : forall n : BinInt,
  octave_equiv (12 * n)%binint 0%binint.
Proof.
  intro n.
  exists (binint_negation n).
  rewrite <- binint_mul_add_distr_l.
  rewrite binint_add_negation_r.
  rewrite binint_mul_0_r.
  reflexivity.
Defined.

(** Rearrangement lemmas for products involving 12 *)
Lemma twelve_mult_comm_assoc : forall a b : BinInt,
  (a * 12 * b)%binint = (12 * a * b)%binint.
Proof.
  intros a b.
  f_ap.
  apply binint_mul_comm.
Defined.

Lemma expand_octave_mult : forall a b c : BinInt,
  ((a + 12 * b) * c)%binint = (a * c + 12 * b * c)%binint.
Proof.
  intros a b c.
  rewrite binint_mul_add_distr_r.
  reflexivity.
Defined.

Lemma twelve_factor_rearrange : forall a b c : BinInt,
  (a * 12 * b + 12 * c)%binint = (12 * (a * b + c))%binint.
Proof.
  intros a b c.
  rewrite (binint_mul_comm a 12%binint).
  rewrite <- binint_mul_assoc.
  rewrite <- binint_mul_add_distr_l.
  reflexivity.
Defined.

Lemma twelve_mul_rearrange : forall a b : BinInt,
  (12 * a * 12 * b)%binint = (12 * 12 * a * b)%binint.
Proof.
  intros a b.
  rewrite (binint_mul_comm (12 * a)%binint 12%binint).
  rewrite <- binint_mul_assoc.
  rewrite binint_mul_assoc.
  rewrite binint_mul_assoc.
  reflexivity.
Defined.

(** Addition shuffle - useful for proving group properties *)
Lemma binint_add_shuffle : forall a b c d : BinInt,
  ((a + b) + (c + d))%binint = ((a + c) + (b + d))%binint.
Proof.
  intros a b c d.
  rewrite <- binint_add_assoc.
  rewrite <- binint_add_assoc.
  rewrite (binint_add_assoc b).
  rewrite (binint_add_comm b c).
  rewrite <- (binint_add_assoc c).
  rewrite binint_add_assoc.
  rewrite binint_add_assoc.
  reflexivity.
Defined.

(** Helper for cancellation laws *)
Lemma binint_add_neg_add_l : forall a b : BinInt,
  ((- a) + a + b)%binint = (0 + b)%binint.
Proof.
  intros a b.
  rewrite binint_add_negation_l.
  reflexivity.
Defined.

(** Left cancellation for integer addition *)
Lemma binint_add_cancel_l : forall a b c : BinInt,
  (a + b)%binint = (a + c)%binint -> b = c.
Proof.
  intros a b c H.
  assert (H2: ((- a) + (a + b))%binint = ((- a) + (a + c))%binint).
  { rewrite H. reflexivity. }
  rewrite binint_add_assoc in H2.
  rewrite binint_add_assoc in H2.
  rewrite binint_add_neg_add_l in H2.
  rewrite binint_add_neg_add_l in H2.
  rewrite binint_add_0_l in H2.
  rewrite binint_add_0_l in H2.
  exact H2.
Defined.

(** Negation distributes over addition *)
Lemma binint_negation_add : forall a b : BinInt,
  binint_negation (a + b)%binint = (binint_negation a + binint_negation b)%binint.
Proof.
  intros a b.
  assert (H: ((a + b) + (- (a + b)))%binint = ((a + b) + (- a + - b))%binint).
  - rewrite binint_add_negation_r.
    rewrite binint_add_shuffle.
    rewrite binint_add_negation_r.
    rewrite binint_add_negation_r.
    rewrite binint_add_0_r.
    reflexivity.
  - exact (binint_add_cancel_l (a + b)%binint _ _ H).
Defined.

(** Negation distributes over multiplication (right) *)
Lemma binint_negation_mult_r : forall a b : BinInt,
  binint_negation (a * b)%binint = (a * binint_negation b)%binint.
Proof.
  intros a b.
  assert (H: ((a * b) + (a * - b))%binint = 0%binint).
  - rewrite <- binint_mul_add_distr_l.
    rewrite binint_add_negation_r.
    apply binint_mul_0_r.
  - apply (binint_add_cancel_l (a * b)%binint).
    rewrite binint_add_negation_r.
    rewrite H.
    reflexivity.
Defined.


(** ================================================================= *)
(** Section 6: Pitch Class Negation                                  *)
(** ================================================================= *)

(** Negation on pitch classes gives the additive inverse.
    Musically, this corresponds to inversion about C (pitch class 0). *)

Definition pitch_class_neg : PitchClass -> PitchClass.
Proof.
  srapply Quotient_rec.
  - intro n.
    exact (pitch_class_of (binint_negation n)).
  - intros n1 n2 [k Hk].
    apply qglue.
    exists (binint_negation k).
    rewrite Hk.
    rewrite binint_negation_add.
    f_ap.
    apply binint_negation_mult_r.
Defined.

(** Notation for pitch class negation *)
Notation "-pc p" := (pitch_class_neg p) (at level 35, right associativity).

(** Negation gives left inverses *)
Lemma pitch_class_add_neg_l : forall p : PitchClass,
  (-pc p) +pc p = C.
Proof.
  srapply Quotient_ind.
  - intro n.
    unfold C.
    simpl.
    apply qglue.
    exists 0%binint.
    rewrite binint_mul_0_r.
    rewrite binint_add_0_r.
    symmetry.
    apply binint_add_negation_l.
  - intros; apply path_ishprop.
Defined.

(** Negation gives right inverses *)
Lemma pitch_class_add_neg_r : forall p : PitchClass,
  p +pc (-pc p) = C.
Proof.
  intro p.
  rewrite pitch_class_add_comm.
  apply pitch_class_add_neg_l.
Defined.

(** ================================================================= *)
(** Section 7: Collected Properties (so far)                                          *)
(** ================================================================= *)

(** The main algebraic structures proved so far: pitch classes form an
    abelian group under addition. *)

Theorem pitch_class_group_properties :
  (forall p q r : PitchClass, (p +pc q) +pc r = p +pc (q +pc r)) /\  (* associativity *)
  (forall p : PitchClass, C +pc p = p) /\                             (* left identity *)
  (forall p : PitchClass, p +pc C = p) /\                             (* right identity *)
  (forall p q : PitchClass, p +pc q = q +pc p) /\                     (* commutativity *)
  (forall p : PitchClass, (-pc p) +pc p = C).                         (* left inverse *)
Proof.
  split.
  - exact pitch_class_add_assoc.
  - split.
    + exact pitch_class_add_zero_l.
    + split.
      * exact pitch_class_add_zero_r.
      * split.
        -- exact pitch_class_add_comm.
        -- exact pitch_class_add_neg_l.
Defined.


(** ================================================================= *)
(** Section 8: Musical Examples                                      *)
(** ================================================================= *)

(** These examples demonstrate the musical relevance of our
    formalization and serve as sanity checks for the theory. *)

(** Octave equivalence: adding 12 semitones returns to the same
    pitch class *)
Example octave_equivalence : [ 12%binint ] = C.
Proof.
  apply qglue.
  exists (binint_negation 1%binint).
  unfold C.
  rewrite <- binint_negation_mult_r.
  rewrite binint_mul_1_r.
  symmetry.
  apply binint_add_negation_r.
Defined.

(** Negative octaves also return to C *)
Example negative_octave : [ (-12)%binint ] = C.
Proof.
  apply qglue.
  exists 1%binint.
  unfold C.
  simpl.
  reflexivity.
Defined.

(** Musical intervals behave as expected *)
Example perfect_fifth : C +pc G = G.
Proof.
  simpl.
  apply ap.
  apply binint_add_0_l.
Defined.

Example major_third : C +pc E = E.
Proof.
  simpl.
  apply ap.
  apply binint_add_0_l.
Defined.

(** Transposition of a C major triad *)
Example transpose_C_major_chord : 
  (C +pc C, E +pc C, G +pc C) = (C, E, G).
Proof.
  rewrite pitch_class_add_zero_r.
  rewrite pitch_class_add_comm, pitch_class_add_zero_l.
  rewrite pitch_class_add_comm, pitch_class_add_zero_l.
  reflexivity.
Defined.

(** Intervals larger than an octave reduce correctly *)
Example octave_reduction_13 : [ 13%binint ] = Cs.
Proof.
  apply qglue.
  exists (binint_negation 1%binint).
  unfold Cs.
  rewrite <- binint_negation_mult_r.
  rewrite binint_mul_1_r.
  simpl.
  reflexivity.
Defined.

(** Enharmonic equivalence is built into our representation *)
Example enharmonic : Fs = [ 6%binint ].
Proof.
  reflexivity.
Defined.

(** ================================================================= *)
(** General work, to be organized                                   *)
(** ================================================================= *)

(** Scalar multiplication represents transposition by a fixed interval.
    For example, 3 *pc p transposes pitch class p up by 3 semitones. *)
Definition pitch_class_scalar_mult (n : BinInt) (p : PitchClass) : PitchClass.
Proof.
  revert p.
  srapply Quotient_rec.
  - intro m.
    exact (pitch_class_of (n * m)%binint).
  - intros m1 m2 [k Hk].
    apply qglue.
    exists (n * k)%binint.
    rewrite Hk.
    rewrite binint_mul_add_distr_l.
    rewrite binint_mul_assoc.
    rewrite (binint_mul_comm n 12%binint).
    rewrite binint_mul_assoc.
    reflexivity.
Defined.

Notation "n *pc p" := (pitch_class_scalar_mult n p) (at level 40).

(** Scalar multiplication by 1 is the identity *)
Lemma pitch_class_scalar_mult_1 : forall p : PitchClass,
  1%binint *pc p = p.
Proof.
  srapply Quotient_ind.
  - intro n.
    simpl.
    apply ap.
    apply binint_mul_1_l.
  - intros; apply path_ishprop.
Defined.

Lemma pitch_class_scalar_mult_0 : forall p : PitchClass,
  0%binint *pc p = C.
Proof.
  srapply Quotient_ind.
  - intro n.
    unfold C.
    simpl.
    reflexivity.
  - intros; apply path_ishprop.
Defined.

(** Scalar multiplication distributes over pitch class addition *)
Lemma pitch_class_scalar_mult_add : forall n : BinInt, forall p q : PitchClass,
  n *pc (p +pc q) = (n *pc p) +pc (n *pc q).
Proof.
  intro n.
  intros p q.
  revert q.
  srapply Quotient_ind.
  - intro m2.
    revert p.
    srapply Quotient_ind.
    + intro m1.
      simpl.
      apply ap.
      apply binint_mul_add_distr_l.
    + intros; apply path_ishprop.
  - intros; apply path_ishprop.
Defined.

Lemma pitch_class_scalar_mult_comp : forall n m : BinInt, forall p : PitchClass,
  n *pc (m *pc p) = (n * m)%binint *pc p.
Proof.
  intros n m p.
  revert p.
  srapply Quotient_ind.
  - intro k.
    simpl.
    apply ap.
    apply binint_mul_assoc.
  - intros; apply path_ishprop.
Defined.

Example transpose_by_3 : 
  (C +pc Ds, E +pc Ds, G +pc Ds) = (Ds, G, As).
Proof.
  unfold C, E, G, Ds, As.
  simpl.
  repeat split; reflexivity.
Defined.

(** Scalar multiplication by 5 maps pitch classes by perfect fourths *)
Example scalar_mult_5 : 5%binint *pc Cs = F.
Proof.
  unfold Cs, F.
  simpl.
  reflexivity.
Defined.

(** Scalar multiplication by 7 maps pitch classes by perfect fifths *)
Example scalar_mult_7 : 7%binint *pc Cs = G.
Proof.
 unfold Cs, G.
 simpl.
 reflexivity.
Defined.

(** The inversion operation I_n inverts pitch classes around n/2.
    It maps pitch class p to n - p. *)
Definition pitch_class_inversion (n : BinInt) (p : PitchClass) : PitchClass :=
  [n] +pc (-pc p).

Notation "'I' n" := (pitch_class_inversion n) (at level 30).

(** I_0 is pitch class negation *)
Lemma inversion_0_is_negation : forall p : PitchClass,
  pitch_class_inversion 0%binint p = -pc p.
Proof.
  intro p.
  unfold pitch_class_inversion.
  unfold C.
  apply pitch_class_add_zero_l.
Defined.

(** Negation distributes over pitch class addition *)
Lemma pitch_class_neg_add : forall p q : PitchClass,
 -pc (p +pc q) = (-pc p) +pc (-pc q).
Proof.
 intros p q.
 revert q.
 srapply Quotient_ind.
 - intro n.
   revert p.
   srapply Quotient_ind.
   + intro m.
     simpl.
     apply ap.
     apply binint_negation_add.
   + intros; apply path_ishprop.
 - intros; apply path_ishprop.
Defined.

(** Negation of zero is zero *)
Lemma binint_negation_0 : binint_negation 0%binint = 0%binint.
Proof.
  assert (H: (0 + binint_negation 0)%binint = 0%binint).
  { rewrite binint_add_0_l. reflexivity. }
  rewrite <- H.
  rewrite binint_add_negation_r.
  reflexivity.
Defined.

(** Double negation is the identity *)
Lemma binint_negation_negation : forall n : BinInt,
  binint_negation (binint_negation n) = n.
Proof.
  intro n.
  apply (binint_add_cancel_l (binint_negation n)).
  rewrite binint_add_negation_r.
  symmetry.
  apply binint_add_negation_l.
Defined.

(** Double negation is the identity *)
Lemma pitch_class_neg_neg : forall p : PitchClass,
  -pc -pc p = p.
Proof.
  srapply Quotient_ind.
  - intro n.
    simpl.
    apply ap.
    apply binint_negation_negation.
  - intros; apply path_ishprop.
Defined.

(** Helper: adding inverse on right gives zero *)
Lemma add_neg_r_helper : forall n : BinInt,
  n *pc C +pc -pc (n *pc C) = C.
Proof.
  intro n.
  apply pitch_class_add_neg_r.
Defined.

(** Helper for inversion involution *)
Lemma inversion_involution_helper2 : forall n : BinInt, forall p : PitchClass,
 (n *pc C +pc -pc (n *pc C)) +pc p = C +pc p.
Proof.
 intros n p.
 rewrite add_neg_r_helper.
 reflexivity.
Defined.

(** Inversion is an involution (applying it twice gives the identity) *)
Lemma inversion_involution : forall n : BinInt, forall p : PitchClass,
  pitch_class_inversion n (pitch_class_inversion n p) = p.
Proof.
  intros n p.
  unfold pitch_class_inversion.
  rewrite pitch_class_neg_add.
  rewrite pitch_class_neg_neg.
  rewrite <- pitch_class_add_assoc.
  rewrite pitch_class_add_neg_r.
  apply pitch_class_add_zero_l.
Defined.

(** Example: I_0 inverts pitch classes to their negatives *)
Example inversion_0_example : 
  pitch_class_inversion 0%binint E = Gs.
Proof.
  rewrite inversion_0_is_negation.
  unfold E, Gs.
  simpl.
  apply qglue.
  exists 1%binint.
  simpl.
  reflexivity.
Defined.

(** Example: I_7 (inversion around F#/Gb) maps C to G *)
Example inversion_7_C : 
  pitch_class_inversion 7%binint C = G.
Proof.
  unfold pitch_class_inversion, C, G.
  simpl.
  reflexivity.
Defined.
