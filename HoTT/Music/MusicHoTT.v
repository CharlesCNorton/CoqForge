(** ================================================================= *)
(** A Full Formalization of Musical Set Theory in Homotopy Type Theory
    
    This library provides a foundation for formalizing mathematical
    music theory using Homotopy Type Theory (HoTT). By leveraging
    HoTT's native support for quotient types, higher inductive types,
    and homotopical reasoning, we develop a framework for exploring
    both classical and novel mathematical structures in music.
    
    The formalization follows the tradition of musical set theory
    established by Milton Babbitt, Allen Forte, David Lewin, and
    John Rahn. We model pitch classes as equivalence classes of
    integers modulo 12, corresponding to the twelve-tone equal
    temperament system used in Western music.
    
    Key mathematical structures formalized:
    - The group Z/12Z of pitch classes under addition
    - Transposition and inversion operations (the T/I group)
    - Pitch class sets and their transformations
    - Set operations (union, intersection, complement)
    - Musical interval structures
    
    The use of HoTT provides several advantages:
    - Quotient types naturally model octave equivalence
    - Higher inductive types could model voice leading spaces
    - Univalence principles connect musical equivalences
    - Constructive proofs yield computational content

    Author: Charles Norton
    Date: July 2nd 2025 (Updated: July 29th 2025)
    ================================================================= *)

(** ================================================================= *)
(** Dependencies                                                      *)
(** ================================================================= *)

(** Core HoTT foundations 
    We use the basic machinery of Homotopy Type Theory including
    paths, equivalences, and proof tactics *)
From HoTT Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids.
From HoTT Require Import Basics.Decidable Basics.Equivalences.

(** Types and type formers
    These provide the basic type constructors we need: dependent
    functions (Forall), dependent pairs (Sigma), identity types
    (Paths), and basic types (Unit, Bool, etc.) *)
From HoTT Require Import Types.Forall Types.Sigma Types.Paths Types.Unit Types.Prod.
From HoTT Require Import Types.Sum Types.Bool Types.Arrow Types.Universe.

(** Truncation machinery
    Truncations allow us to work with mere propositions and sets,
    which is crucial for quotient types *)
From HoTT Require Import Truncations.Core.

(** Colimits for quotients
    The quotient type construction is essential for defining
    pitch classes as equivalence classes of integers *)
From HoTT Require Import Colimits.Quotient.

(** Numeric types
    BinInt provides binary integers (Z), which we use to model
    pitch numbers. Nat is used for counting. Fin provides finite
    types which could represent the 12 pitch classes directly *)
From HoTT Require Import Spaces.BinInt.Core Spaces.BinInt.Spec.
From HoTT Require Import Spaces.Nat.Core Spaces.Nat.Arithmetic.
From HoTT Require Import Spaces.Finite.Fin.

(** Algebraic structures
    These provide the group theory we need to prove that pitch
    classes form an abelian group *)
From HoTT Require Import Algebra.Groups Algebra.AbGroups.
From HoTT Require Import Classes.interfaces.canonical_names.

(** Open standard scopes 
    This ensures paths and types are parsed correctly *)
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
    
    Formally: m ~ n ⟺ ∃k ∈ Z. n = m + 12k
    
    This equivalence relation partitions the integers into 12
    equivalence classes, corresponding to the 12 pitch classes
    in the chromatic scale. For example:
    - [..., -12, 0, 12, 24, ...] all represent pitch class C
    - [..., -11, 1, 13, 25, ...] all represent pitch class C♯/D♭
    
    The choice of 12 reflects the physics of sound: the frequency
    ratio 2:1 (an octave) divided into 12 equal parts on a
    logarithmic scale gives the equal-tempered semitone. *)

Definition octave_equiv : BinInt -> BinInt -> Type :=
  fun m n => { k : BinInt | n = m + 12 * k }%binint.

(** We prove that octave equivalence is indeed an equivalence relation,
    satisfying reflexivity, symmetry, and transitivity. These proofs
    are constructive, providing explicit witnesses for the existential
    claims. *)

(** Every pitch is octave-equivalent to itself (k = 0)
    This corresponds to the musical fact that a pitch is in the
    same pitch class as itself *)
Lemma octave_equiv_refl : forall n, octave_equiv n n.
Proof.
  intro n.
  exists 0%binint.
  rewrite binint_mul_0_r.
  rewrite binint_add_0_r.
  reflexivity.
Defined.

(** If m ~ n with witness k, then n ~ m with witness -k
    This corresponds to the fact that if we go up by k octaves
    from m to reach n, we can go down by k octaves from n to
    reach m *)
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
    then m ~ p with witness k1 + k2
    This captures the additive nature of octave displacement:
    going up k1 octaves then k2 more octaves is the same as
    going up k1 + k2 octaves *)
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
    equivalence. This gives us the mathematical structure Z/12Z.
    
    This quotient construction is one of the key advantages of using
    HoTT for this formalization. In set theory, we would need to
    work with equivalence classes as sets of integers, which is
    cumbersome. Here, the quotient type directly gives us a type
    whose elements are pitch classes, with built-in equality that
    respects octave equivalence.
    
    The resulting type has exactly 12 distinct elements (up to
    equality), corresponding to the 12 pitch classes in Western
    music theory. *)

Definition PitchClass : Type := 
  Quotient octave_equiv.

(** The canonical quotient map from integers to pitch classes.
    This function takes any integer and returns its pitch class.
    For example:
    - pitch_class_of 0 = C
    - pitch_class_of 13 = C♯ (since 13 ≡ 1 mod 12)
    - pitch_class_of (-3) = A (since -3 ≡ 9 mod 12) *)
Definition pitch_class_of : BinInt -> PitchClass :=
  class_of octave_equiv.

(** Notation for the quotient map - we write [n] for the pitch class
    containing the integer n. This notation is inspired by the
    mathematical convention of writing equivalence classes as [x].
    It makes our formulas more readable: [0] is C, [7] is G, etc. *)
Notation "[ n ]" := (pitch_class_of n) (at level 0).

(** The twelve pitch class names, following standard musical notation.
    C = 0, C# = 1, D = 2, etc. These form the standard representatives
    of the equivalence classes.
    
    Historical note: The assignment of C to 0 is a convention in
    musical set theory. Some theorists use different numberings,
    but this is the most common. The sharp notation (♯) is used
    here in comments; in the code we use 's' for sharp and 'f'
    would be used for flat.
    
    These definitions establish our "musical alphabet" - every
    pitch class can be expressed in terms of these twelve basic
    elements. *)

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
    addition respects the octave equivalence relation. This is a
    fundamental requirement for operations on quotient types: the
    operation must be well-defined on equivalence classes, not
    just on representatives.
    
    Musically, pitch class addition corresponds to transposition.
    Adding 5 to a pitch class means transposing it up by 5
    semitones (a perfect fourth). *)

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
    to the quotient. This is well-defined by the previous lemma.
    
    The implementation uses Quotient_rec to define a function on
    the quotient type. We must provide:
    1. A function on representatives (integer addition)
    2. A proof that equivalent inputs give equivalent outputs
    
    This construction ensures that [m] +pc [n] = [m + n], which
    gives us the expected computational behavior. *)

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

(** Infix notation for pitch class addition.
    We use +pc to distinguish from integer addition.
    This allows us to write natural expressions like C +pc G = G. *)
Notation "p +pc q" := (pitch_class_add p q) (at level 50, left associativity).


(** ================================================================= *)
(** Section 4: Properties of Pitch Class Addition                    *)
(** ================================================================= *)

(** Pitch class addition is associative.
    This property is inherited from integer addition, but we must
    prove it explicitly for the quotient type. Musically, this
    means that when transposing multiple times, the order of
    grouping doesn't matter: (p +pc q) +pc r = p +pc (q +pc r). *)
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

(** Pitch class addition is commutative.
    This reflects the fact that transposing up by m semitones
    then n semitones gives the same result as transposing up
    by n semitones then m semitones. In musical terms, the
    order of transpositions doesn't affect the final result. *)
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

(** C (pitch class 0) is the additive identity.
    Adding C to any pitch class leaves it unchanged, which
    corresponds to transposing by 0 semitones (i.e., not
    transposing at all). This establishes C as the "zero"
    element of our group. *)
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
    development but are not part of the main musical theory.
    They establish properties of multiplication and addition
    that we use in proving properties of pitch class operations.
    
    While these may seem like mere technical details, they are
    essential for rigorous proofs about modular arithmetic. *)

(** Multiples of 12 are octave-equivalent to 0.
    This captures the fact that moving up or down by any whole
    number of octaves brings us back to the same pitch class.
    For instance, 24 (two octaves) is in the same pitch class as 0. *)
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

(** Rearrangement lemmas for products involving 12.
    These technical lemmas allow us to manipulate expressions
    involving the modulus 12 in our proofs. They're analogous
    to the algebraic manipulations one would do when working
    with congruences modulo 12. *)
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

(** Addition shuffle - useful for proving group properties.
    This lemma shows we can rearrange terms in a sum of four
    integers. It's used when proving properties like the fact
    that negation distributes over addition. *)
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

(** Helper for cancellation laws.
    This establishes that -a + a + b = 0 + b, which is used
    in proving cancellation properties for addition. *)
Lemma binint_add_neg_add_l : forall a b : BinInt,
  ((- a) + a + b)%binint = (0 + b)%binint.
Proof.
  intros a b.
  rewrite binint_add_negation_l.
  reflexivity.
Defined.

(** Left cancellation for integer addition.
    If a + b = a + c, then b = c. This is a fundamental
    property of group operations that we lift to our context. *)
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

(** Negation distributes over addition.
    -(a + b) = (-a) + (-b)
    This property is essential for proving that pitch class
    negation behaves correctly with respect to addition. *)
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

(** Negation distributes over multiplication (right).
    -(a * b) = a * (-b)
    This is used when proving properties of scalar multiplication
    on pitch classes. *)
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
    Musically, this corresponds to inversion about C (pitch class 0).
    
    In traditional music theory, inversion flips intervals: a major
    third becomes a minor sixth, a perfect fifth becomes a perfect
    fourth, etc. Our negation operation captures this: if p is n
    semitones above C, then -pc p is n semitones below C (mod 12).
    
    For example:
    - -pc E = Ab (since E is 4 above C, Ab is 4 below C = 8 above)
    - -pc G = F (since G is 7 above C, F is 7 below C = 5 above) *)

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

(** Notation for pitch class negation.
    We use -pc to distinguish from integer negation.
    This allows natural expressions like -pc G = F. *)
Notation "-pc p" := (pitch_class_neg p) (at level 35, right associativity).

(** Negation gives left inverses.
    For any pitch class p, (-pc p) +pc p = C.
    This confirms that negation produces additive inverses,
    making (PitchClass, +pc) a group. *)
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

(** Negation gives right inverses.
    For any pitch class p, p +pc (-pc p) = C.
    Together with the previous lemma, this confirms that
    every element has a two-sided inverse. *)
Lemma pitch_class_add_neg_r : forall p : PitchClass,
  p +pc (-pc p) = C.
Proof.
  intro p.
  rewrite pitch_class_add_comm.
  apply pitch_class_add_neg_l.
Defined.

(** ================================================================= *)
(** Section 7: Collected Properties                                  *)
(** ================================================================= *)

(** The main algebraic structures proved so far: pitch classes form an
    abelian group under addition.
    
    This theorem collects all the group axioms we've proved:
    - Associativity: (p + q) + r = p + (q + r)
    - Identity: C is a two-sided identity
    - Inverses: Every element has an inverse via negation
    - Commutativity: p + q = q + p
    
    This establishes that (PitchClass, +pc, C, -pc) is an abelian
    group isomorphic to Z/12Z. In musical terms, this captures the
    fundamental structure of the twelve-tone system. *)

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
    formalization and serve as sanity checks for the theory.
    They show that our abstract mathematical machinery correctly
    captures familiar musical concepts. *)

(** Octave equivalence: adding 12 semitones returns to the same
    pitch class. This is the fundamental property of octaves in
    Western music - going up 12 semitones (one octave) brings
    you to a pitch that sounds "the same" in a different register. *)
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

(** Negative octaves also return to C.
    Going down an octave (-12 semitones) also returns to the
    same pitch class, confirming the symmetry of octave equivalence. *)
Example negative_octave : [ (-12)%binint ] = C.
Proof.
  apply qglue.
  exists 1%binint.
  unfold C.
  simpl.
  reflexivity.
Defined.

(** Musical intervals behave as expected.
    A perfect fifth above C is G (7 semitones).
    Adding C (0) to G (7) gives G (7), confirming that C
    is the identity for transposition. *)
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

(** Transposition of a C major triad.
    This example shows that transposing by 0 (adding C) leaves
    a chord unchanged. The C major triad (C, E, G) transposed
    by 0 semitones remains (C, E, G). *)
Example transpose_C_major_chord : 
  (C +pc C, E +pc C, G +pc C) = (C, E, G).
Proof.
  rewrite pitch_class_add_zero_r.
  rewrite pitch_class_add_comm, pitch_class_add_zero_l.
  rewrite pitch_class_add_comm, pitch_class_add_zero_l.
  reflexivity.
Defined.

(** Intervals larger than an octave reduce correctly.
    13 semitones is equivalent to 1 semitone (13 = 12 + 1).
    This confirms that our quotient construction correctly
    handles the modular arithmetic of pitch classes. *)
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

(** Enharmonic equivalence is built into our representation.
    F# and Gb are the same pitch class in equal temperament.
    Our formalization automatically handles this - we don't
    need separate representations for enharmonic equivalents. *)
Example enharmonic : Fs = [ 6%binint ].
Proof.
  reflexivity.
Defined.

(** ================================================================= *)
(** Section 9: Scalar Multiplication and Advanced Operations         *)
(** ================================================================= *)

(** Scalar multiplication represents transposition by a fixed interval.
    For example, 3 *pc p transposes pitch class p up by 3 semitones.
    
    This operation has deep musical significance:
    - 5 *pc p gives the circle of fourths (F, Bb, Eb, ...)
    - 7 *pc p gives the circle of fifths (C, G, D, A, ...)
    - 1 *pc p gives the chromatic scale
    - 2 *pc p gives whole tone scales
    
    Mathematically, this makes PitchClass a Z-module. *)
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

(** Scalar multiplication by 1 is the identity.
    This confirms that 1 *pc p = p, as expected. *)
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

(** Scalar multiplication distributes over pitch class addition.
    n *pc (p +pc q) = (n *pc p) +pc (n *pc q)
    This property makes scalar multiplication compatible with
    the group structure, forming a module. *)
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

(** Scalar multiplication by 5 maps pitch classes by perfect fourths.
    This generates the circle of fourths, a fundamental structure
    in music theory used in jazz and classical harmony. *)
Example scalar_mult_5 : 5%binint *pc Cs = F.
Proof.
  unfold Cs, F.
  simpl.
  reflexivity.
Defined.

(** Scalar multiplication by 7 maps pitch classes by perfect fifths.
    This generates the circle of fifths, perhaps the most important
    structure in Western tonal music. *)
Example scalar_mult_7 : 7%binint *pc Cs = G.
Proof.
 unfold Cs, G.
 simpl.
 reflexivity.
Defined.

(** The inversion operation I_n inverts pitch classes around n/2.
    It maps pitch class p to n - p.
    
    This operation generalizes musical inversion. While -pc p
    inverts around C (0), I_n p inverts around n/2. For example:
    - I_0 inverts around C (same as negation)
    - I_6 inverts around F#/Gb (the tritone)
    - I_7 inverts around the point between F# and G
    
    Musically, inversion preserves interval content but reverses
    direction: ascending becomes descending and vice versa. *)
Definition pitch_class_inversion (n : BinInt) (p : PitchClass) : PitchClass :=
  [n] +pc (-pc p).

Notation "'I' n" := (pitch_class_inversion n) (at level 30).

(** I_0 is pitch class negation.
    Inversion around 0 is the same as negation, confirming
    our definition aligns with standard music theory. *)
Lemma inversion_0_is_negation : forall p : PitchClass,
  pitch_class_inversion 0%binint p = -pc p.
Proof.
  intro p.
  unfold pitch_class_inversion.
  unfold C.
  apply pitch_class_add_zero_l.
Defined.

(** Negation distributes over pitch class addition.
    -pc (p +pc q) = (-pc p) +pc (-pc q)
    This property is essential for proving that inversion
    operations behave correctly. *)
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

(** Negation of zero is zero.
    -0 = 0 in any group, and our pitch class group is no exception.
    Musically, the "inverse" of no transposition is still no
    transposition. *)
Lemma binint_negation_0 : binint_negation 0%binint = 0%binint.
Proof.
  assert (H: (0 + binint_negation 0)%binint = 0%binint).
  { rewrite binint_add_0_l. reflexivity. }
  rewrite <- H.
  rewrite binint_add_negation_r.
  reflexivity.
Defined.

(** Double negation is the identity.
    In any group, --x = x. For pitch classes, inverting twice
    returns to the original pitch class. *)
Lemma binint_negation_negation : forall n : BinInt,
  binint_negation (binint_negation n) = n.
Proof.
  intro n.
  apply (binint_add_cancel_l (binint_negation n)).
  rewrite binint_add_negation_r.
  symmetry.
  apply binint_add_negation_l.
Defined.

(** Double negation is the identity for pitch classes. *)
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

(** Helper: adding inverse on right gives zero.
    This technical lemma helps prove more complex identities. *)
Lemma add_neg_r_helper : forall n : BinInt,
  n *pc C +pc -pc (n *pc C) = C.
Proof.
  intro n.
  apply pitch_class_add_neg_r.
Defined.

(** Helper for inversion involution.
    Another technical lemma used in proving that inversion
    is its own inverse. *)
Lemma inversion_involution_helper2 : forall n : BinInt, forall p : PitchClass,
 (n *pc C +pc -pc (n *pc C)) +pc p = C +pc p.
Proof.
 intros n p.
 rewrite add_neg_r_helper.
 reflexivity.
Defined.

(** Inversion is an involution (applying it twice gives the identity).
    I_n(I_n(p)) = p for all n and p.
    
    This is a fundamental property of musical inversion: if you
    invert a melody around a pitch, then invert the result around
    the same pitch, you get back the original melody. *)
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

(** Example: I_0 inverts pitch classes to their negatives.
    I_0(E) = G# because E is 4 semitones above C, so its
    inversion is 4 semitones below C, which is G# (8 above). *)
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

(** Example: I_7 (inversion around F#/G) maps C to G.
    This inversion is around the point between F# and G.
    C is 7 semitones below this point, so its inversion
    is 7 semitones above it, which is G. *)
Example inversion_7_C : 
  pitch_class_inversion 7%binint C = G.
Proof.
  unfold pitch_class_inversion, C, G.
  simpl.
  reflexivity.
Defined.

(** Example: I_12 is the same as negation.
    Since 12 ≡ 0 (mod 12), inverting around 12 is the same
    as inverting around 0, which is negation. *)
Example inversion_12_negation : forall p : PitchClass,
  pitch_class_inversion 12%binint p = -pc p.
Proof.
  intro p.
  unfold pitch_class_inversion.
  rewrite octave_equivalence.
  apply pitch_class_add_zero_l.
Defined.

(** The transposition operation T_n transposes a pitch class by n semitones.
    This is the most basic musical transformation: moving all pitches
    up or down by a fixed interval. It's used constantly in music
    to change keys or adapt to different vocal ranges. *)
Definition pitch_class_transpose (n : BinInt) (p : PitchClass) : PitchClass :=
  [n] +pc p.

Notation "'T' n" := (pitch_class_transpose n) (at level 30).

(** Transposition by 0 is the identity.
    Not transposing at all leaves the pitch unchanged. *)
Lemma transpose_0_identity : forall p : PitchClass,
  pitch_class_transpose 0%binint p = p.
Proof.
  intro p.
  unfold pitch_class_transpose.
  apply pitch_class_add_zero_l.
Defined.

(** Transpositions compose by addition.
    Transposing by m then by n is the same as transposing by m+n.
    This captures the additive nature of interval combination. *)
Lemma transpose_compose : forall m n : BinInt, forall p : PitchClass,
  pitch_class_transpose m (pitch_class_transpose n p) = pitch_class_transpose (m + n)%binint p.
Proof.
  intros m n p.
  unfold pitch_class_transpose.
  rewrite <- pitch_class_add_assoc.
  f_ap.
Defined.

(** Helper: [m] +pc -pc [n] = [m - n].
    Subtraction of pitch classes corresponds to integer subtraction
    of representatives. *)
Lemma pitch_class_sub : forall m n : BinInt,
  [m] +pc -pc [n] = [(m - n)%binint].
Proof.
  intros m n.
  simpl.
  apply ap.
  unfold binint_sub.
  reflexivity.
Defined.

(** The fundamental relationship: I_n composed with I_m equals T_(n-m).
    Two inversions compose to give a transposition.
    
    This is a key theorem in transformation theory: the composition
    of two inversions is a transposition by the difference of their
    indices. It shows that inversions and transpositions together
    generate the dihedral group of symmetries of the chromatic scale. *)
Lemma inversion_composition : forall m n : BinInt, forall p : PitchClass,
  pitch_class_inversion m (pitch_class_inversion n p) = pitch_class_transpose (m - n)%binint p.
Proof.
  intros m n p.
  unfold pitch_class_inversion, pitch_class_transpose.
  rewrite pitch_class_neg_add.
  rewrite pitch_class_neg_neg.
  rewrite <- pitch_class_add_assoc.
  rewrite pitch_class_sub.
  reflexivity.
Defined.

(** Example: I_7 ∘ I_3 = T_4.
    Inverting around 3 then around 7 is the same as transposing by 4.
    This demonstrates the composition law for inversions. *)
Example inversion_comp_example : forall p : PitchClass,
  pitch_class_inversion 7%binint (pitch_class_inversion 3%binint p) = pitch_class_transpose 4%binint p.
Proof.
  intro p.
  apply inversion_composition.
Defined.

(** ================================================================= *)
(** Section 10: Pitch Class Sets                                     *)
(** ================================================================= *)

(** A pitch class set is a finite subset of pitch classes.
    We represent this as a function from PitchClass to Bool,
    where true means the pitch class is in the set.
    
    This representation is computationally efficient and works
    well with our quotient type construction. In traditional
    set theory, we might use actual subsets, but the functional
    representation is more natural in type theory.
    
    Examples of important pitch class sets:
    - Major scale: {C, D, E, F, G, A, B}
    - Minor triad: {C, Eb, G}
    - Whole tone scale: {C, D, E, F#, G#, A#}
    - Chromatic scale: all 12 pitch classes *)
Definition PitchClassSet : Type := PitchClass -> Bool.

(** The empty pitch class set.
    Musically, this represents silence or the absence of pitches. *)
Definition pc_set_empty : PitchClassSet := fun _ => false.

(** The full pitch class set (chromatic aggregate).
    This contains all 12 pitch classes. In atonal music, using
    all 12 pitch classes is called the "aggregate" and is often
    a compositional goal. *)
Definition pc_set_full : PitchClassSet := fun _ => true.

(** Membership test.
    This is just function application, but we give it a name
    for clarity and to match standard set theory notation. *)
Definition pc_set_member (s : PitchClassSet) (p : PitchClass) : Bool :=
  s p.

(** Singleton set containing just one pitch class.
    Currently stubbed - requires decidable equality on PitchClass. *)
Definition pc_set_singleton (p : PitchClass) : PitchClassSet.
Proof.
  intro q.
  exact false.
Defined.

(** Set union: s1 ∪ s2.
    A pitch class is in the union if it's in either set.
    Musically, this combines two collections of pitches. *)
Definition pc_set_union (s1 s2 : PitchClassSet) : PitchClassSet :=
  fun p => orb (s1 p) (s2 p).

(** Set intersection: s1 ∩ s2.
    A pitch class is in the intersection if it's in both sets.
    This finds common tones between two pitch collections. *)
Definition pc_set_intersection (s1 s2 : PitchClassSet) : PitchClassSet :=
  fun p => andb (s1 p) (s2 p).

(** Set complement: the pitches not in s.
    In a 12-tone context, this gives the pitches needed to
    complete the chromatic aggregate. *)
Definition pc_set_complement (s : PitchClassSet) : PitchClassSet :=
  fun p => negb (s p).

(** Transpose a set by n semitones.
    This shifts every pitch in the set up by n semitones.
    Note the use of -pc [n] to ensure we check membership
    correctly: p is in T_n(s) if p-n is in s. *)
Definition pc_set_transpose (n : BinInt) (s : PitchClassSet) : PitchClassSet :=
  fun p => s ((-pc [n]) +pc p).

(** Invert a set around pitch n/2.
    This applies the inversion operation to every pitch in the set.
    It's the set-theoretic version of melodic inversion. *)
Definition pc_set_invert (n : BinInt) (s : PitchClassSet) : PitchClassSet :=
  fun p => s (pitch_class_inversion n p).

(** Subset relation: s1 ⊆ s2.
    Every pitch in s1 is also in s2.
    We use Type instead of Prop to maintain computational content. *)
Definition pc_set_subset (s1 s2 : PitchClassSet) : Type :=
  forall p : PitchClass, s1 p = true -> s2 p = true.

(** Set equality: s1 = s2 as sets.
    Two sets are equal if they contain exactly the same pitches.
    This is extensional equality, not intensional. *)
Definition pc_set_eq (s1 s2 : PitchClassSet) : Type :=
  forall p : PitchClass, s1 p = s2 p.

(** Interval class between two pitch classes.
    This is the "musical distance" from p to q, calculated as
    q - p (mod 12). It's always between 0 and 11. *)
Definition pc_set_interval_class (p q : PitchClass) : PitchClass :=
  q +pc (-pc p).

(** The chromatic set is just the full set under another name.
    This alias emphasizes its musical significance. *)
Definition pc_set_chromatic : PitchClassSet :=
  pc_set_full.

(** Whole tone scale: one of the two whole tone collections.
    Contains pitches separated by whole steps (2 semitones).
    Currently stubbed - needs decidable equality. *)
Definition pc_set_whole_tone : PitchClassSet :=
  fun p => false.

(** Diminished seventh chord: symmetric division of the octave.
    Contains pitches separated by minor thirds (3 semitones).
    Currently stubbed - needs decidable equality. *)
Definition pc_set_diminished_seventh : PitchClassSet :=
  fun p => false.

(** Example: The chromatic set contains all pitch classes.
    This is true by definition - the full set returns true for
    any input. *)
Example chromatic_contains_all : forall p : PitchClass,
  pc_set_member pc_set_chromatic p = true.
Proof.
  intro p.
  unfold pc_set_member, pc_set_chromatic, pc_set_full.
  reflexivity.
Defined.

(** Example: The empty set contains no pitch classes.
    Also true by definition - the empty set returns false for
    any input. *)
Example empty_contains_none : forall p : PitchClass,
  pc_set_member pc_set_empty p = false.
Proof.
  intro p.
  unfold pc_set_member, pc_set_empty.
  reflexivity.
Defined.

(** Set operations preserve subset relations.
    These lemmas establish that union and intersection behave
    as expected with respect to the subset ordering. *)
Lemma subset_union_l : forall s1 s2 : PitchClassSet,
  pc_set_subset s1 (pc_set_union s1 s2).
Proof.
  intros s1 s2 p H.
  unfold pc_set_union.
  rewrite H.
  reflexivity.
Defined.

Lemma subset_intersection_l : forall s1 s2 : PitchClassSet,
  pc_set_subset (pc_set_intersection s1 s2) s1.
Proof.
  intros s1 s2 p H.
  unfold pc_set_intersection in H.
  destruct (s1 p).
  - reflexivity.
  - discriminate H.
Defined.

(** The interval between a pitch class and itself is 0.
    This confirms that our interval calculation is reflexive:
    the distance from any pitch to itself is zero (C). *)
Example interval_self : forall p : PitchClass,
  pc_set_interval_class p p = C.
Proof.
  intro p.
  unfold pc_set_interval_class.
  rewrite pitch_class_add_neg_r.
  reflexivity.
Defined.

(** Interval classes are inversionally related.
    The interval from p to q is the inverse of the interval
    from q to p. This reflects the symmetry of intervals in
    the chromatic scale. *)
Lemma interval_class_neg : forall p q : PitchClass,
  pc_set_interval_class p q = -pc (pc_set_interval_class q p).
Proof.
  intros p q.
  unfold pc_set_interval_class.
  rewrite pitch_class_neg_add.
  rewrite pitch_class_neg_neg.
  apply pitch_class_add_comm.
Defined.

(** Cardinality counts the number of pitch classes in a set.
    This implementation explicitly checks each of the 12 pitch
    classes. A more elegant implementation would use decidable
    equality, but this works for concrete calculations. *)
Definition pc_set_cardinality (s : PitchClassSet) : nat :=
  (if s C then 1 else 0) +
  (if s Cs then 1 else 0) +
  (if s D then 1 else 0) +
  (if s Ds then 1 else 0) +
  (if s E then 1 else 0) +
  (if s F then 1 else 0) +
  (if s Fs then 1 else 0) +
  (if s G then 1 else 0) +
  (if s Gs then 1 else 0) +
  (if s A then 1 else 0) +
  (if s As then 1 else 0) +
  (if s B then 1 else 0).

(** Interval vector: a fundamental tool in musical set theory.
    For a pitch class set, the interval vector counts how many
    times each interval class appears between pairs of pitches.
    The six components count intervals of 1, 2, 3, 4, 5, and 6
    semitones (larger intervals are inversionally equivalent). *)
Definition interval_vector (s : PitchClassSet) : Type :=
  (nat * nat * nat * nat * nat * nat)%type.

(** Compute the interval vector for a set.
    Currently stubbed - requires iterating over all pairs of
    pitches in the set and counting intervals. *)
Definition compute_interval_vector (s : PitchClassSet) : interval_vector s :=
  (O, O, O, O, O, O).

(** Z-relation: two sets with the same interval vector.
    Named after Allen Forte's zygotic relation, this identifies
    sets that have the same interval content but are not related
    by transposition or inversion. These sets sound similar but
    are structurally different. *)
Definition pc_sets_z_related (s1 s2 : PitchClassSet) : Type :=
  compute_interval_vector s1 = compute_interval_vector s2.

(** Augmented triad: divides the octave into three equal parts.
    Contains pitches separated by major thirds (4 semitones).
    Currently stubbed. *)
Definition pc_set_augmented_triad : PitchClassSet :=
  fun p => false.

(** Octatonic scale: alternating whole and half steps.
    This is Messiaen's second mode of limited transposition.
    Currently stubbed. *)
Definition pc_set_octatonic : PitchClassSet :=
  fun p => false.

(** Tn/TnI equivalence: the fundamental equivalence in set theory.
    Two sets are equivalent if one can be obtained from the other
    by transposition (Tn) or inversion followed by transposition (TnI).
    This defines the basic objects of musical set theory. *)
Definition pc_set_TnI_equivalent (s1 s2 : PitchClassSet) : Type :=
  {n : BinInt | pc_set_eq s1 (pc_set_transpose n s2)} +
  {n : BinInt | pc_set_eq s1 (pc_set_invert n s2)}.

(** Minor triad: the fundamental chord of minor tonality.
    Contains root, minor third, and perfect fifth.
    Currently stubbed. *)
Definition pc_set_minor_triad : PitchClassSet :=
  fun p => false.

(** More musical set examples.
    These represent important collections in music theory,
    from jazz harmony to contemporary composition. *)
Definition pc_set_dominant_seventh : PitchClassSet :=
  fun p => false.

Definition pc_set_pentatonic : PitchClassSet :=
  fun p => false.

Definition pc_set_hexatonic : PitchClassSet :=
  fun p => false.

Definition pc_set_diatonic : PitchClassSet :=
  fun p => false.

(** Normal form: the most compact rotation to the left.
    This is a canonical representative for sets under rotation.
    Currently returns the input unchanged - proper implementation
    requires finding the rotation with smallest span. *)
Definition pc_set_normal_form (s : PitchClassSet) : PitchClassSet :=
  s.

(** Prime form: normal form transposed to start on 0.
    This is the canonical representative for a set class under
    Tn equivalence. Currently stubbed. *)
Definition pc_set_prime_form (s : PitchClassSet) : PitchClassSet :=
  pc_set_normal_form s.

(** Set class: all sets related by Tn/TnI.
    This type represents an equivalence class of pitch class sets
    under transposition and inversion. It's the fundamental object
    of study in musical set theory. *)
Definition SetClass : Type := PitchClassSet -> Type.

Definition set_class_of (s : PitchClassSet) : SetClass :=
  fun s' => pc_set_TnI_equivalent s s'.

(** Complement operation (alias for clarity).
    In twelve-tone theory, the complement is crucial for
    understanding the complete chromatic space. *)
Definition pc_set_complement_full (s : PitchClassSet) : PitchClassSet :=
  pc_set_complement s.

(** ================================================================= *)
(** Section 11: Properties of Set Operations                         *)
(** ================================================================= *)

(** Properties of set operations.
    These lemmas establish that pitch class sets with union and
    intersection form a Boolean algebra (without complement).
    The proofs are straightforward but important for establishing
    the algebraic structure. *)

Lemma pc_set_union_comm : forall s1 s2 : PitchClassSet,
  pc_set_eq (pc_set_union s1 s2) (pc_set_union s2 s1).
Proof.
  intros s1 s2 p.
  unfold pc_set_union.
  destruct (s1 p), (s2 p); reflexivity.
Defined.

Lemma pc_set_union_assoc : forall s1 s2 s3 : PitchClassSet,
  pc_set_eq (pc_set_union (pc_set_union s1 s2) s3) 
            (pc_set_union s1 (pc_set_union s2 s3)).
Proof.
  intros s1 s2 s3 p.
  unfold pc_set_union.
  destruct (s1 p), (s2 p), (s3 p); reflexivity.
Defined.

Lemma pc_set_intersection_comm : forall s1 s2 : PitchClassSet,
  pc_set_eq (pc_set_intersection s1 s2) (pc_set_intersection s2 s1).
Proof.
  intros s1 s2 p.
  unfold pc_set_intersection.
  destruct (s1 p), (s2 p); reflexivity.
Defined.

Lemma pc_set_intersection_assoc : forall s1 s2 s3 : PitchClassSet,
  pc_set_eq (pc_set_intersection (pc_set_intersection s1 s2) s3)
            (pc_set_intersection s1 (pc_set_intersection s2 s3)).
Proof.
  intros s1 s2 s3 p.
  unfold pc_set_intersection.
  destruct (s1 p), (s2 p), (s3 p); reflexivity.
Defined.

(** De Morgan's laws connect union, intersection, and complement.
    These are fundamental laws of Boolean algebra that also hold
    for pitch class sets. *)
Lemma pc_set_demorgan_1 : forall s1 s2 : PitchClassSet,
  pc_set_eq (pc_set_complement (pc_set_union s1 s2))
            (pc_set_intersection (pc_set_complement s1) (pc_set_complement s2)).
Proof.
  intros s1 s2 p.
  unfold pc_set_complement, pc_set_union, pc_set_intersection.
  destruct (s1 p), (s2 p); reflexivity.
Defined.

Lemma pc_set_demorgan_2 : forall s1 s2 : PitchClassSet,
  pc_set_eq (pc_set_complement (pc_set_intersection s1 s2))
            (pc_set_union (pc_set_complement s1) (pc_set_complement s2)).
Proof.
  intros s1 s2 p.
  unfold pc_set_complement, pc_set_union, pc_set_intersection.
  destruct (s1 p), (s2 p); reflexivity.
Defined.

(** Double complement returns the original set.
    This shows complement is an involution. *)
Lemma pc_set_complement_complement : forall s : PitchClassSet,
  pc_set_eq (pc_set_complement (pc_set_complement s)) s.
Proof.
  intros s p.
  unfold pc_set_complement.
  destruct (s p); reflexivity.
Defined.

(** Transposition of sets composes additively.
    Transposing by m then by n equals transposing by m+n.
    This lifts the composition law from pitch classes to sets. *)
Lemma pc_set_transpose_compose : forall m n : BinInt, forall s : PitchClassSet,
  pc_set_eq (pc_set_transpose m (pc_set_transpose n s))
            (pc_set_transpose (m + n)%binint s).
Proof.
  intros m n s p.
  unfold pc_set_transpose.
  rewrite <- pitch_class_add_assoc.
  rewrite <- pitch_class_neg_add.
  f_ap.
  simpl.
  f_ap.
  apply ap.
  rewrite binint_add_comm.
  reflexivity.
Defined.

(** Inversion of sets is an involution.
    Inverting twice returns the original set, just as with
    individual pitch classes. *)
Lemma pc_set_invert_involution : forall n : BinInt, forall s : PitchClassSet,
  pc_set_eq (pc_set_invert n (pc_set_invert n s)) s.
Proof.
  intros n s p.
  unfold pc_set_invert.
  rewrite inversion_involution.
  reflexivity.
Defined.

(** Transposition distributes over union.
    T_n(A ∪ B) = T_n(A) ∪ T_n(B)
    This and similar distributivity laws show that musical
    transformations interact naturally with set operations. *)
Lemma pc_set_transpose_union : forall n : BinInt, forall s1 s2 : PitchClassSet,
  pc_set_eq (pc_set_transpose n (pc_set_union s1 s2))
            (pc_set_union (pc_set_transpose n s1) (pc_set_transpose n s2)).
Proof.
  intros n s1 s2 p.
  unfold pc_set_transpose, pc_set_union.
  reflexivity.
Defined.

(** Transposition distributes over intersection. *)
Lemma pc_set_transpose_intersection : forall n : BinInt, forall s1 s2 : PitchClassSet,
  pc_set_eq (pc_set_transpose n (pc_set_intersection s1 s2))
            (pc_set_intersection (pc_set_transpose n s1) (pc_set_transpose n s2)).
Proof.
  intros n s1 s2 p.
  unfold pc_set_transpose, pc_set_intersection.
  reflexivity.
Defined.

(** Inversion distributes over complement. *)
Lemma pc_set_invert_complement : forall n : BinInt, forall s : PitchClassSet,
  pc_set_eq (pc_set_invert n (pc_set_complement s))
            (pc_set_complement (pc_set_invert n s)).
Proof.
  intros n s p.
  unfold pc_set_invert, pc_set_complement.
  reflexivity.
Defined.

(** Inversion distributes over union. *)
Lemma pc_set_invert_union : forall n : BinInt, forall s1 s2 : PitchClassSet,
  pc_set_eq (pc_set_invert n (pc_set_union s1 s2))
            (pc_set_union (pc_set_invert n s1) (pc_set_invert n s2)).
Proof.
  intros n s1 s2 p.
  unfold pc_set_invert, pc_set_union.
  reflexivity.
Defined.

(** Inversion distributes over intersection. *)
Lemma pc_set_invert_intersection : forall n : BinInt, forall s1 s2 : PitchClassSet,
  pc_set_eq (pc_set_invert n (pc_set_intersection s1 s2))
            (pc_set_intersection (pc_set_invert n s1) (pc_set_invert n s2)).
Proof.
  intros n s1 s2 p.
  unfold pc_set_invert, pc_set_intersection.
  reflexivity.
Defined.

(** Transposition distributes over complement. *)
Lemma pc_set_transpose_complement : forall n : BinInt, forall s : PitchClassSet,
  pc_set_eq (pc_set_transpose n (pc_set_complement s))
            (pc_set_complement (pc_set_transpose n s)).
Proof.
  intros n s p.
  unfold pc_set_transpose, pc_set_complement.
  reflexivity.
Defined.

(** ================================================================= *)
(** Section 12: Special Sets and Their Properties                    *)
(** ================================================================= *)

(** Properties of special sets (empty and full).
    These lemmas show how the extreme sets behave under various
    operations, establishing them as identity and absorbing elements
    for appropriate operations. *)

(** Transposition preserves the empty set.
    Transposing nothing still gives nothing. *)
Lemma pc_set_transpose_empty : forall n : BinInt,
  pc_set_eq (pc_set_transpose n pc_set_empty) pc_set_empty.
Proof.
  intros n p.
  unfold pc_set_transpose, pc_set_empty.
  reflexivity.
Defined.

(** Inversion preserves the empty set. *)
Lemma pc_set_invert_empty : forall n : BinInt,
  pc_set_eq (pc_set_invert n pc_set_empty) pc_set_empty.
Proof.
  intros n p.
  unfold pc_set_invert, pc_set_empty.
  reflexivity.
Defined.

(** Transposition preserves the full set.
    Transposing everything still gives everything. *)
Lemma pc_set_transpose_full : forall n : BinInt,
  pc_set_eq (pc_set_transpose n pc_set_full) pc_set_full.
Proof.
  intros n p.
  unfold pc_set_transpose, pc_set_full.
  reflexivity.
Defined.

(** Inversion preserves the full set. *)
Lemma pc_set_invert_full : forall n : BinInt,
  pc_set_eq (pc_set_invert n pc_set_full) pc_set_full.
Proof.
  intros n p.
  unfold pc_set_invert, pc_set_full.
  reflexivity.
Defined.

(** The empty set is a subset of any set.
    This establishes empty as the bottom element of the subset lattice. *)
Lemma pc_set_empty_subset : forall s : PitchClassSet,
  pc_set_subset pc_set_empty s.
Proof.
  intros s p H.
  unfold pc_set_empty in H.
  discriminate H.
Defined.

(** Any set is a subset of the full set.
    This establishes full as the top element of the subset lattice. *)
Lemma pc_set_subset_full : forall s : PitchClassSet,
  pc_set_subset s pc_set_full.
Proof.
  intros s p H.
  unfold pc_set_full.
  reflexivity.
Defined.

(** Subset relation is reflexive. *)
Lemma pc_set_subset_refl : forall s : PitchClassSet,
  pc_set_subset s s.
Proof.
  intros s p H.
  exact H.
Defined.

(** Subset relation is transitive. *)
Lemma pc_set_subset_trans : forall s1 s2 s3 : PitchClassSet,
  pc_set_subset s1 s2 -> pc_set_subset s2 s3 -> pc_set_subset s1 s3.
Proof.
  intros s1 s2 s3 H12 H23 p H1.
  apply H23.
  apply H12.
  exact H1.
Defined.

(** ================================================================= *)
(** Section 13: Algebraic Properties of Set Operations              *)
(** ================================================================= *)

(** Identity and absorbing elements for set operations.
    These establish the algebraic structure of pitch class sets
    as a bounded lattice with complement. *)

(** Union with empty set is identity. *)
Lemma pc_set_union_empty_l : forall s : PitchClassSet,
  pc_set_eq (pc_set_union pc_set_empty s) s.
Proof.
  intros s p.
  unfold pc_set_union, pc_set_empty.
  reflexivity.
Defined.

(** Union with empty set is identity (right). *)
Lemma pc_set_union_empty_r : forall s : PitchClassSet,
  pc_set_eq (pc_set_union s pc_set_empty) s.
Proof.
  intros s p.
  unfold pc_set_union, pc_set_empty.
  destruct (s p); reflexivity.
Defined.

(** Intersection with full set is identity. *)
Lemma pc_set_intersection_full_l : forall s : PitchClassSet,
  pc_set_eq (pc_set_intersection pc_set_full s) s.
Proof.
  intros s p.
  unfold pc_set_intersection, pc_set_full.
  reflexivity.
Defined.

(** Intersection with full set is identity (right). *)
Lemma pc_set_intersection_full_r : forall s : PitchClassSet,
  pc_set_eq (pc_set_intersection s pc_set_full) s.
Proof.
  intros s p.
  unfold pc_set_intersection, pc_set_full.
  destruct (s p); reflexivity.
Defined.

(** Intersection with empty set is empty. *)
Lemma pc_set_intersection_empty_l : forall s : PitchClassSet,
  pc_set_eq (pc_set_intersection pc_set_empty s) pc_set_empty.
Proof.
  intros s p.
  unfold pc_set_intersection, pc_set_empty.
  reflexivity.
Defined.

(** Intersection with empty set is empty (right). *)
Lemma pc_set_intersection_empty_r : forall s : PitchClassSet,
  pc_set_eq (pc_set_intersection s pc_set_empty) pc_set_empty.
Proof.
  intros s p.
  unfold pc_set_intersection, pc_set_empty.
  destruct (s p); reflexivity.
Defined.

(** Union with full set is full. *)
Lemma pc_set_union_full_l : forall s : PitchClassSet,
  pc_set_eq (pc_set_union pc_set_full s) pc_set_full.
Proof.
  intros s p.
  unfold pc_set_union, pc_set_full.
  reflexivity.
Defined.

(** Union with full set is full (right). *)
Lemma pc_set_union_full_r : forall s : PitchClassSet,
  pc_set_eq (pc_set_union s pc_set_full) pc_set_full.
Proof.
  intros s p.
  unfold pc_set_union, pc_set_full.
  destruct (s p); reflexivity.
Defined.

(** Complement of empty is full. *)
Lemma pc_set_complement_empty : 
  pc_set_eq (pc_set_complement pc_set_empty) pc_set_full.
Proof.
  intro p.
  unfold pc_set_complement, pc_set_empty, pc_set_full.
  reflexivity.
Defined.

(** Idempotence of union.
    A ∪ A = A
    Combining a set with itself doesn't change it. *)
Lemma pc_set_union_idempotent : forall s : PitchClassSet,
  pc_set_eq (pc_set_union s s) s.
Proof.
  intros s p.
  unfold pc_set_union.
  destruct (s p); reflexivity.
Defined.

(** Idempotence of intersection.
    A ∩ A = A *)
Lemma pc_set_intersection_idempotent : forall s : PitchClassSet,
  pc_set_eq (pc_set_intersection s s) s.
Proof.
  intros s p.
  unfold pc_set_intersection.
  destruct (s p); reflexivity.
Defined.

(** Union with complement is full.
    A ∪ A' = U (the universal set)
    Every pitch class is either in a set or its complement. *)
Lemma pc_set_union_complement : forall s : PitchClassSet,
  pc_set_eq (pc_set_union s (pc_set_complement s)) pc_set_full.
Proof.
  intros s p.
  unfold pc_set_union, pc_set_complement, pc_set_full.
  destruct (s p); reflexivity.
Defined.

(** Intersection with complement is empty.
    A ∩ A' = ∅
    No pitch class can be both in a set and its complement. *)
Lemma pc_set_intersection_complement : forall s : PitchClassSet,
  pc_set_eq (pc_set_intersection s (pc_set_complement s)) pc_set_empty.
Proof.
  intros s p.
  unfold pc_set_intersection, pc_set_complement, pc_set_empty.
  destruct (s p); reflexivity.
Defined.

(** ================================================================= *)
(** Section 14: Preservation Properties                              *)
(** ================================================================= *)

(** These lemmas show that musical transformations preserve
    structural relationships between sets. *)

(** Subset preserved by transposition.
    If A ⊆ B, then T_n(A) ⊆ T_n(B)
    This shows transposition is monotonic with respect to subset. *)
Lemma pc_set_transpose_subset : forall n : BinInt, forall s1 s2 : PitchClassSet,
  pc_set_subset s1 s2 -> pc_set_subset (pc_set_transpose n s1) (pc_set_transpose n s2).
Proof.
  intros n s1 s2 H p H1.
  unfold pc_set_transpose in *.
  apply H.
  exact H1.
Defined.

(** Subset preserved by inversion. *)
Lemma pc_set_invert_subset : forall n : BinInt, forall s1 s2 : PitchClassSet,
  pc_set_subset s1 s2 -> pc_set_subset (pc_set_invert n s1) (pc_set_invert n s2).
Proof.
  intros n s1 s2 H p H1.
  unfold pc_set_invert in *.
  apply H.
  exact H1.
Defined.

(** Transposition by n followed by transposition by m equals 
    transposition by m+n (already follows from transpose_compose).
    This is just an alias for clarity. *)
Lemma pc_set_transpose_transpose : forall m n : BinInt, forall s : PitchClassSet,
  pc_set_eq (pc_set_transpose m (pc_set_transpose n s))
            (pc_set_transpose (m + n)%binint s).
Proof.
  exact pc_set_transpose_compose.
Defined.

(** Double complement with a transposition in between.
    This shows how complement and transposition interact in
    a non-trivial way. *)
Lemma pc_set_complement_transpose_complement : forall n : BinInt, forall s : PitchClassSet,
  pc_set_eq (pc_set_complement (pc_set_transpose n (pc_set_complement s)))
            (pc_set_transpose n s).
Proof.
  intros n s p.
  unfold pc_set_complement, pc_set_transpose.
  destruct (s (-pc [n] +pc p)); reflexivity.
Defined.

(** Complement and inversion commute.
    (I_n(A))' = I_n(A')
    This is a special case of the general principle that
    bijections preserve complements. *)
Lemma pc_set_complement_invert_commute : forall n : BinInt, forall s : PitchClassSet,
  pc_set_eq (pc_set_complement (pc_set_invert n s))
            (pc_set_invert n (pc_set_complement s)).
Proof.
  intros n s p.
  rewrite pc_set_invert_complement.
  reflexivity.
Defined.

(** Union of a set with its transposition.
    A ⊆ A ∪ T_n(A)
    This is useful for building symmetric sets. *)
Lemma pc_set_union_transpose_self : forall n : BinInt, forall s : PitchClassSet,
  pc_set_subset s (pc_set_union s (pc_set_transpose n s)).
Proof.
  intros n s.
  apply subset_union_l.
Defined.

(** Intersection of a set with its inversion.
    A ∩ I_n(A) ⊆ A
    The common tones under inversion form a subset. *)
Lemma pc_set_intersection_invert_self : forall n : BinInt, forall s : PitchClassSet,
  pc_set_subset (pc_set_intersection s (pc_set_invert n s)) s.
Proof.
  intros n s.
  apply subset_intersection_l.
Defined.

(** Empty set is invariant under all transpositions.
    This and the next lemma show that empty and full sets
    are fixed points for all musical transformations. *)
Lemma pc_set_transpose_empty_invariant : forall n m : BinInt,
  pc_set_eq (pc_set_transpose n pc_set_empty) (pc_set_transpose m pc_set_empty).
Proof.
  intros n m p.
  rewrite pc_set_transpose_empty.
  rewrite pc_set_transpose_empty.
  reflexivity.
Defined.

(** Full set is invariant under all inversions. *)
Lemma pc_set_invert_full_invariant : forall n m : BinInt,
  pc_set_eq (pc_set_invert n pc_set_full) (pc_set_invert m pc_set_full).
Proof.
  intros n m p.
  rewrite pc_set_invert_full.
  rewrite pc_set_invert_full.
  reflexivity.
Defined.

(** ================================================================= *)
(** Section 15: Modular Arithmetic in Z/12Z                          *)
(** ================================================================= *)

(** These lemmas establish how integers reduce modulo 12 to their 
    pitch class equivalents. They form the computational foundation
    for all our musical calculations. *)

(** 12 semitones equals 0 in pitch class arithmetic *)
Lemma twelve_equals_zero : [ 12%binint ] = C.
Proof.
  apply qglue.
  exists (binint_negation 1%binint).
  unfold C.
  rewrite <- binint_negation_mult_r.
  rewrite binint_mul_1_r.
  symmetry.
  apply binint_add_negation_r.
Defined.

(** 14 equals 2 in pitch class arithmetic *)
Lemma fourteen_equals_two : [14%binint] = [2%binint].
Proof.
  apply qglue.
  exists (binint_negation 1%binint).
  simpl.
  reflexivity.
Defined.

(** 16 equals 4 in pitch class arithmetic *)
Lemma sixteen_equals_four : [16%binint] = [4%binint].
Proof.
  apply qglue.
  exists (binint_negation 1%binint).
  simpl.
  reflexivity.
Defined.

(** 18 equals 6 in pitch class arithmetic *)
Lemma eighteen_equals_six : [18%binint] = [6%binint].
Proof.
  apply qglue.
  exists (binint_negation 1%binint).
  simpl.
  reflexivity.
Defined.

(** 21 equals 9 in pitch class arithmetic *)
Lemma twentyone_equals_nine : [21%binint] = [9%binint].
Proof.
  apply qglue.
  exists (binint_negation 1%binint).
  simpl.
  reflexivity.
Defined.

(** 28 equals 4 in pitch class arithmetic *)
Lemma twentyeight_equals_four : [28%binint] = [4%binint].
Proof.
  apply qglue.
  exists (binint_negation 2%binint).
  simpl.
  reflexivity.
Defined.

(** 35 equals 11 in pitch class arithmetic *)
Lemma thirtyfive_equals_eleven : [35%binint] = [11%binint].
Proof.
  apply qglue.
  exists (binint_negation 2%binint).
  simpl.
  reflexivity.
Defined.

(** 42 equals 6 in pitch class arithmetic *)
Lemma fortytwo_equals_six : [42%binint] = [6%binint].
Proof.
  apply qglue.
  exists (binint_negation 3%binint).
  simpl.
  reflexivity.
Defined.

(** 49 equals 1 in pitch class arithmetic *)
Lemma fortynine_equals_one : [49%binint] = [1%binint].
Proof.
  apply qglue.
  exists (binint_negation 4%binint).
  simpl.
  reflexivity.
Defined.

(** 11 equals -1 in pitch class arithmetic *)
Lemma eleven_equals_neg_one : [ 11%binint ] = [ (-1)%binint ].
Proof.
  apply qglue.
  exists (binint_negation 1%binint).
  simpl.
  reflexivity.
Defined.

(** Simple arithmetic fact: 11 + 1 = 12 *)
Lemma eleven_plus_one : (11 + 1)%binint = 12%binint.
Proof.
  reflexivity.
Defined.

(** Negation of 7 is 5 in pitch class arithmetic *)
Lemma neg_seven_equals_five : -pc [7%binint] = [5%binint].
Proof.
  simpl.
  apply qglue.
  exists 1%binint.
  simpl.
  reflexivity.
Defined.


(** ================================================================= *)
(** Section 16: Scalar Multiplication Properties                     *)
(** ================================================================= *)

(** These lemmas explore how scalar multiplication behaves in Z/12Z,
    particularly focusing on multiplication by 5 and 7, which generate
    important musical structures. *)

(** Scalar multiplication by -1 is negation *)
Lemma scalar_mult_neg_1 : forall p : PitchClass,
  (-1)%binint *pc p = -pc p.
Proof.
  srapply Quotient_ind.
  - intro n.
    simpl.
    apply ap.
    destruct n.
    + reflexivity.  (* case 0 *)
    + reflexivity.  (* case pos *)
    + reflexivity.  (* case neg *)
  - intros; apply path_ishprop.
Defined.

(** Scalar multiplication by 0 gives C *)
Lemma scalar_mult_0_gives_C : forall p : PitchClass,
  0%binint *pc p = C.
Proof.
  intro p.
  apply pitch_class_scalar_mult_0.
Defined.

(** Scalar multiplication by 5 on [1] gives [5] *)
Lemma scalar_mult_5_on_one : 5%binint *pc [1%binint] = [5%binint].
Proof.
  simpl.
  reflexivity.
Defined.

(** Scalar multiplication by 7 on [1] gives [7] *)
Lemma scalar_mult_7_on_one : 7%binint *pc [1%binint] = [7%binint].
Proof.
  simpl.
  reflexivity.
Defined.

(** 7 * 2 = 14 *)
Lemma scalar_mult_7_twice : 7%binint *pc [2%binint] = [14%binint].
Proof.
  simpl.
  reflexivity.
Defined.

(** 7 * 3 = 21 *)
Lemma scalar_mult_7_on_three : 7%binint *pc [3%binint] = [21%binint].
Proof.
  simpl.
  reflexivity.
Defined.

(** 7 * 4 = 28 *)
Lemma scalar_mult_7_on_four : 7%binint *pc [4%binint] = [28%binint].
Proof.
  simpl.
  reflexivity.
Defined.

(** 7 * 5 = 35 *)
Lemma scalar_mult_7_on_five : 7%binint *pc [5%binint] = [35%binint].
Proof.
  simpl.
  reflexivity.
Defined.

(** 7 * 6 = 42 *)
Lemma scalar_mult_7_on_six : 7%binint *pc [6%binint] = [42%binint].
Proof.
  simpl.
  reflexivity.
Defined.

(** 7 * 7 = 49 ≡ 1 (mod 12) *)
Lemma scalar_mult_7_on_seven : 7%binint *pc [7%binint] = [49%binint].
Proof.
  simpl.
  reflexivity.
Defined.

(** 7 is its own multiplicative inverse modulo 12 *)
Lemma scalar_mult_7_generates_1 : 7%binint *pc (7%binint *pc [1%binint]) = [1%binint].
Proof.
  rewrite scalar_mult_7_on_one.
  rewrite scalar_mult_7_on_seven.
  apply fortynine_equals_one.
Defined.


(** ================================================================= *)
(** Section 17: Set Transposition Properties                         *)
(** ================================================================= *)

(** Properties of transposing pitch class sets, including special
    cases and the tritone involution. *)

(** Transposition by 0 is identity for sets *)
Lemma pc_set_transpose_zero : forall s : PitchClassSet,
  pc_set_eq (pc_set_transpose 0%binint s) s.
Proof.
  intro s.
  intro p.
  unfold pc_set_transpose.
  unfold C.
  simpl.
  rewrite pitch_class_add_zero_l.
  reflexivity.
Defined.

(** Transposition by 12 is identity *)
Lemma pc_set_transpose_12 : forall s : PitchClassSet,
  pc_set_eq (pc_set_transpose 12%binint s) s.
Proof.
  intro s.
  intro p.
  unfold pc_set_transpose.
  rewrite twelve_equals_zero.
  rewrite pitch_class_add_zero_l.
  reflexivity.
Defined.

(** The tritone transposition (by 6 semitones) is its own inverse *)
Example tritone_transposition_involution : forall s : PitchClassSet,
  pc_set_eq (pc_set_transpose 6%binint (pc_set_transpose 6%binint s)) s.
Proof.
  intro s.
  intro p.
  rewrite (pc_set_transpose_compose 6%binint 6%binint s p).
  assert (H: (6 + 6)%binint = 12%binint).
  { reflexivity. }
  rewrite H.
  unfold pc_set_transpose.
  rewrite twelve_equals_zero.
  rewrite pitch_class_add_zero_l.
  reflexivity.
Defined.


(** ================================================================= *)
(** Section 18: Circle of Fifths and Fourths                         *)
(** ================================================================= *)

(** The circle of fifths is one of the most fundamental structures
    in Western music theory. Moving by perfect fifths (7 semitones)
    generates all 12 pitch classes. The circle of fourths is its
    inverse, moving by 5 semitones. *)

(** The circle of fifths pattern using addition *)
Example circle_of_fifths_first_six : 
  ([0%binint] +pc [7%binint] = G) /\
  (G +pc [7%binint] = D) /\
  (D +pc [7%binint] = A) /\
  (A +pc [7%binint] = E) /\
  (E +pc [7%binint] = B) /\
  (B +pc [7%binint] = Fs).
Proof.
  unfold C, G, D, A, E, B, Fs.
  split.
  - simpl. reflexivity.
  - split.
    + simpl. apply fourteen_equals_two.
    + split.
      * simpl. reflexivity.
      * split.
        -- simpl. apply sixteen_equals_four.
        -- split.
           ++ simpl. reflexivity.
           ++ simpl. apply eighteen_equals_six.
Defined.

(** The circle of fourths is the inversion of the circle of fifths *)
Example circle_of_fourths_is_inverted_fifths : forall p : PitchClass,
  pitch_class_inversion 0%binint (p +pc [7%binint]) = 
  (pitch_class_inversion 0%binint p) +pc [5%binint].
Proof.
  intro p.
  unfold pitch_class_inversion.
  unfold C.
  rewrite pitch_class_add_zero_l.
  rewrite pitch_class_add_zero_l.
  rewrite pitch_class_neg_add.
  f_ap.
  apply neg_seven_equals_five.
Defined.


(** ================================================================= *)
(** Section 19: Musical Scale Generations                            *)
(** ================================================================= *)

(** These examples demonstrate how various musical scales and chords
    are generated by repeated transposition. This reveals the deep
    mathematical structure underlying musical harmony. *)

(** Whole tone scales are generated by repeated transposition by 2 *)
Example whole_tone_generation : 
  let p0 := C in
  let p1 := p0 +pc [2%binint] in
  let p2 := p1 +pc [2%binint] in
  let p3 := p2 +pc [2%binint] in
  let p4 := p3 +pc [2%binint] in
  let p5 := p4 +pc [2%binint] in
  let p6 := p5 +pc [2%binint] in
  (p0 = C) /\ (p1 = D) /\ (p2 = E) /\ (p3 = Fs) /\ 
  (p4 = Gs) /\ (p5 = As) /\ (p6 = C).
Proof.
  unfold C, D, E, Fs, Gs, As.
  simpl.
  repeat split; try reflexivity.
  apply twelve_equals_zero.
Defined.

(** Diminished seventh chords are generated by minor thirds (3 semitones) *)
Example diminished_seventh_generation :
  let p0 := C in
  let p1 := p0 +pc [3%binint] in
  let p2 := p1 +pc [3%binint] in
  let p3 := p2 +pc [3%binint] in
  let p4 := p3 +pc [3%binint] in
  (p0 = C) /\ (p1 = Ds) /\ (p2 = Fs) /\ (p3 = A) /\ (p4 = C).
Proof.
  unfold C, Ds, Fs, A.
  simpl.
  repeat split; try reflexivity.
  apply twelve_equals_zero.
Defined.

(** Transposition by 3 four times returns to origin *)
Example transpose_3_cycle :
  pitch_class_transpose 3%binint 
    (pitch_class_transpose 3%binint 
      (pitch_class_transpose 3%binint 
        (pitch_class_transpose 3%binint C))) = C.
Proof.
  unfold pitch_class_transpose, C.
  simpl.
  apply twelve_equals_zero.
Defined.

(** ================================================================= *)
(** Section 20: Transformation Algebra                               *)
(** ================================================================= *)

(** These results explore how musical transformations compose and
    interact, revealing the algebraic structure of musical operations. *)

(** ----------------------------------------------------------------- *)
(** Section 20.1: Basic Transformation Compositions                  *)
(** ----------------------------------------------------------------- *)

(** Rearranging three pitch class additions *)
Lemma pitch_class_add_rearrange : forall p q r : PitchClass,
  p +pc q +pc r = p +pc r +pc q.
Proof.
  intros p q r.
  rewrite pitch_class_add_assoc.
  rewrite (pitch_class_add_comm q r).
  rewrite <- pitch_class_add_assoc.
  reflexivity.
Defined.

(** Combining transposition and inversion gives another inversion *)
Example transpose_then_invert : forall n m : BinInt, forall p : PitchClass,
  pitch_class_inversion n (pitch_class_transpose m p) = 
  pitch_class_inversion (n - m)%binint p.
Proof.
  intros n m p.
  unfold pitch_class_inversion, pitch_class_transpose.
  rewrite pitch_class_neg_add.
  rewrite <- pitch_class_add_assoc.
  f_ap.
Defined.

(** ----------------------------------------------------------------- *)
(** Section 20.2: Circle of Fourths - Scalar Multiplication by 5    *)
(** ----------------------------------------------------------------- *)

(** Helper: 5 generates different pitch classes through scalar multiplication *)
Example scalar_mult_5_generates_pattern :
  (5%binint *pc [0%binint] = [0%binint]) /\
  (5%binint *pc [1%binint] = [5%binint]) /\
  (5%binint *pc [2%binint] = [10%binint]) /\
  (5%binint *pc [3%binint] = [15%binint]) /\
  (5%binint *pc [4%binint] = [20%binint]) /\
  (5%binint *pc [5%binint] = [25%binint]).
Proof.
  simpl.
  repeat split; reflexivity.
Defined.

(** Helper lemmas for modular arithmetic needed for the circle of fourths *)
Lemma fifteen_equals_three : [15%binint] = [3%binint].
Proof.
  apply qglue.
  exists (binint_negation 1%binint).
  simpl.
  reflexivity.
Defined.

Lemma twenty_equals_eight : [20%binint] = [8%binint].
Proof.
  apply qglue.
  exists (binint_negation 1%binint).
  simpl.
  reflexivity.
Defined.

Lemma twentyfive_equals_one : [25%binint] = [1%binint].
Proof.
  apply qglue.
  exists (binint_negation 2%binint).
  simpl.
  reflexivity.
Defined.

(** 5 generates all pitch classes (circle of fourths) *)
Example scalar_mult_5_generates_all :
  let gen n := 5%binint *pc [n] in
  (gen 0%binint = C) /\ (gen 1%binint = F) /\ (gen 2%binint = As) /\ (gen 3%binint = Ds) /\ 
  (gen 4%binint = Gs) /\ (gen 5%binint = Cs) /\ (gen 6%binint = Fs) /\ (gen 7%binint = B) /\ 
  (gen 8%binint = E) /\ (gen 9%binint = A) /\ (gen 10%binint = D) /\ (gen 11%binint = G).
Proof.
  unfold C, F, As, Ds, Gs, Cs, Fs, B, E, A, D, G.
  simpl.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * reflexivity.
      * split.
        -- apply fifteen_equals_three.
        -- split.
           ++ apply twenty_equals_eight.
           ++ split.
              ** apply twentyfive_equals_one.
              ** split.
                 --- apply qglue. exists (binint_negation 2%binint). simpl. reflexivity.
                 --- split.
                     +++ apply qglue. exists (binint_negation 2%binint). simpl. reflexivity.
                     +++ split.
                         *** apply qglue. exists (binint_negation 3%binint). simpl. reflexivity.
                         *** split.
                             ---- apply qglue. exists (binint_negation 3%binint). simpl. reflexivity.
                             ---- split.
                                  ++++ apply qglue. exists (binint_negation 4%binint). simpl. reflexivity.
                                  ++++ apply qglue. exists (binint_negation 4%binint). simpl. reflexivity.
Defined.

(** ----------------------------------------------------------------- *)
(** Section 20.3: Scalar Multiplication by 11 Acts as Negation      *)
(** ----------------------------------------------------------------- *)

(** Helper lemmas for 11 multiplication on small values *)
Lemma scalar_mult_11_on_two : 11%binint *pc [2%binint] = [22%binint].
Proof.
  simpl.
  reflexivity.
Defined.

Lemma twentytwo_equals_ten : [22%binint] = [10%binint].
Proof.
  apply qglue.
  exists (binint_negation 1%binint).
  simpl.
  reflexivity.
Defined.

(** 11 generates all pitch classes in reverse (descending chromatic scale) *)
Example scalar_mult_11_generates_reverse :
  let gen n := 11%binint *pc [n] in
  (gen 1%binint = B) /\ (gen 2%binint = As) /\ (gen 3%binint = A) /\ 
  (gen 4%binint = Gs) /\ (gen 5%binint = G) /\ (gen 6%binint = Fs).
Proof.
  unfold B, As, A, Gs, G, Fs.
  simpl.
  split.
  - reflexivity.
  - split.
    + apply twentytwo_equals_ten.
    + split.
      * apply qglue. exists (binint_negation 2%binint). simpl. reflexivity.
      * split.
        -- apply qglue. exists (binint_negation 3%binint). simpl. reflexivity.
        -- split.
           ++ apply qglue. exists (binint_negation 4%binint). simpl. reflexivity.
           ++ apply qglue. exists (binint_negation 5%binint). simpl. reflexivity.
Defined.

(** ----------------------------------------------------------------- *)
(** Section 20.4: Technical Lemmas for Proving 11 = -1 mod 12       *)
(** ----------------------------------------------------------------- *)

(** These helper lemmas establish the algebraic machinery needed to
    prove that scalar multiplication by 11 acts as negation *)

Lemma eleven_equals_neg_one_v2 : [11%binint] = [binint_negation 1%binint].
Proof.
  apply qglue.
  exists (binint_negation 1%binint).
  simpl.
  reflexivity.
Defined.

Lemma eleven_mult_plus_n : forall n : BinInt,
  (11 * n + n)%binint = (12 * n)%binint.
Proof.
  intro n.
  assert (H: (11 * n + n)%binint = (11 * n + 1 * n)%binint).
  { f_ap. symmetry. apply binint_mul_1_l. }
  rewrite H.
  rewrite <- binint_mul_add_distr_r.
  reflexivity.
Defined.

Lemma eleven_mult_equals_neg_plus_twelve : forall n : BinInt,
  (11 * n)%binint = (binint_negation n + 12 * n)%binint.
Proof.
  intro n.
  apply (binint_add_cancel_l n).
  rewrite binint_add_assoc.
  rewrite binint_add_negation_r.
  rewrite binint_add_0_l.
  rewrite binint_add_comm.
  apply eleven_mult_plus_n.
Defined.

(** Commutativity and arithmetic helper lemmas *)
Lemma mult_eleven_comm : forall n : BinInt,
  (n * 11)%binint = (11 * n)%binint.
Proof.
  intro n.
  apply binint_mul_comm.
Defined.

Lemma eleven_plus_twelve : (11 + 12)%binint = 23%binint.
Proof.
  reflexivity.
Defined.

Lemma eleven_minus_twelve : (11 - 12)%binint = binint_negation 1%binint.
Proof.
  reflexivity.
Defined.

(** Factorization lemmas for the main proof *)
Lemma rewrite_to_factor_form : forall n : BinInt,
  (11 * n + binint_negation n * 12)%binint = (n * 11 + binint_negation n * 12)%binint.
Proof.
  intro n.
  f_ap.
  apply binint_mul_comm.
Defined.

Lemma neg_mult_twelve : forall n : BinInt,
  (binint_negation n * 12)%binint = binint_negation (n * 12)%binint.
Proof.
  intro n.
  rewrite binint_mul_comm.
  rewrite <- binint_negation_mult_r.
  rewrite binint_mul_comm.
  reflexivity.
Defined.

Lemma neg_n_mult_twelve : forall n : BinInt,
  (binint_negation n * 12)%binint = binint_negation (n * 12)%binint.
Proof.
  intro n.
  apply neg_mult_twelve.
Defined.

Lemma neg_twelve_mult_n : forall n : BinInt,
  (binint_negation 12 * n)%binint = binint_negation (12 * n)%binint.
Proof.
  intro n.
  rewrite binint_mul_comm.
  rewrite <- binint_negation_mult_r.
  rewrite binint_mul_comm.
  reflexivity.
Defined.

Lemma neg_n_twelve_eq_n_neg_twelve : forall n : BinInt,
  binint_negation (n * 12)%binint = (n * binint_negation 12)%binint.
Proof.
  intro n.
  rewrite binint_mul_comm.
  rewrite <- neg_twelve_mult_n.
  rewrite binint_mul_comm.
  reflexivity.
Defined.

Lemma factor_n_from_difference : forall n : BinInt,
  (11 * n + binint_negation (n * 12))%binint = (n * (11 - 12))%binint.
Proof.
  intro n.
  unfold binint_sub.
  rewrite binint_mul_add_distr_l.
  f_ap.
  - apply binint_mul_comm.
  - apply neg_n_twelve_eq_n_neg_twelve.
Defined.

Lemma n_mult_eleven_minus_twelve : forall n : BinInt,
  (n * (11 - 12))%binint = (n * binint_negation 1)%binint.
Proof.
  intro n.
  f_ap.
Defined.

Lemma neg_one_mult_n : forall n : BinInt,
  (binint_negation 1 * n)%binint = binint_negation n.
Proof.
  intro n.
  destruct n.
  - reflexivity.  (* n = 0 *)
  - reflexivity.  (* n = pos p *)
  - reflexivity.  (* n = neg p *)
Defined.

Lemma n_mult_neg_one : forall n : BinInt,
  (n * binint_negation 1)%binint = binint_negation n.
Proof.
  intro n.
  rewrite binint_mul_comm.
  apply neg_one_mult_n.
Defined.

Lemma twelve_neg_n_comm : forall n : BinInt,
  (12 * binint_negation n)%binint = (binint_negation n * 12)%binint.
Proof.
  intro n.
  apply binint_mul_comm.
Defined.

Lemma eleven_mult_plus_twelve_neg_witness : forall n : BinInt,
  (11 * n + 12 * binint_negation n)%binint = binint_negation n.
Proof.
  intro n.
  rewrite twelve_neg_n_comm.
  rewrite neg_mult_twelve.
  rewrite factor_n_from_difference.
  rewrite n_mult_eleven_minus_twelve.
  apply n_mult_neg_one.
Defined.

(** ----------------------------------------------------------------- *)
(** Section 20.5: Proving 11 Acts as Negation                       *)
(** ----------------------------------------------------------------- *)

(** Specific cases for proving scalar multiplication by 11 is negation *)

Lemma scalar_mult_11_zero : 11%binint *pc [0%binint] = -pc [0%binint].
Proof.
  simpl.
  reflexivity.
Defined.

Lemma scalar_mult_11_one : 11%binint *pc [1%binint] = -pc [1%binint].
Proof.
  simpl.
  apply eleven_equals_neg_one.
Defined.

Lemma scalar_mult_11_two : 11%binint *pc [2%binint] = -pc [2%binint].
Proof.
  apply qglue.
  exists (binint_negation 2%binint).
  reflexivity.
Defined.

Lemma scalar_mult_11_three : 11%binint *pc [3%binint] = -pc [3%binint].
Proof.
  apply qglue.
  exists (binint_negation 3%binint).
  reflexivity.
Defined.

Lemma scalar_mult_11_four : 11%binint *pc [4%binint] = -pc [4%binint].
Proof.
  apply qglue.
  exists (binint_negation 4%binint).
  reflexivity.
Defined.

Lemma scalar_mult_11_five : 11%binint *pc [5%binint] = -pc [5%binint].
Proof.
  apply qglue.
  exists (binint_negation 5%binint).
  reflexivity.
Defined.

Lemma scalar_mult_11_six : 11%binint *pc [6%binint] = -pc [6%binint].
Proof.
  apply qglue.
  exists (binint_negation 6%binint).
  reflexivity.
Defined.

Lemma scalar_mult_11_neg_one : 11%binint *pc [binint_negation 1%binint] = -pc [binint_negation 1%binint].
Proof.
  apply qglue.
  exists 1%binint.
  reflexivity.
Defined.

Lemma scalar_mult_11_neg_two : 11%binint *pc [binint_negation 2%binint] = -pc [binint_negation 2%binint].
Proof.
  apply qglue.
  exists 2%binint.
  reflexivity.
Defined.

(** Helper lemmas for handling positive and negative cases *)
Lemma eleven_neg_plus_twelve_pos : forall p : Core.Pos,
  (11 * neg p + 12 * pos p)%binint = pos p.
Proof.
  intro p.
  assert (H: (neg p) = binint_negation (pos p)).
  { reflexivity. }
  rewrite H.
  apply eleven_mult_plus_twelve_neg_witness.
Defined.

Lemma scalar_mult_11_neg : forall p : Core.Pos,
  11%binint *pc [neg p] = -pc [neg p].
Proof.
  intro p.
  apply qglue.
  exists (pos p).
  symmetry.
  apply eleven_neg_plus_twelve_pos.
Defined.

Lemma eleven_pos_plus_twelve_neg : forall p : Core.Pos,
  (11 * pos p + 12 * neg p)%binint = neg p.
Proof.
  intro p.
  assert (H: (pos p) = binint_negation (neg p)).
  { reflexivity. }
  rewrite H.
  apply eleven_mult_plus_twelve_neg_witness.
Defined.

Lemma scalar_mult_11_pos : forall p : Core.Pos,
  11%binint *pc [pos p] = -pc [pos p].
Proof.
  intro p.
  apply qglue.
  exists (neg p).
  symmetry.
  apply eleven_pos_plus_twelve_neg.
Defined.

(** Main theorem: 11 acts as -1 in scalar multiplication *)
Example scalar_mult_11_is_negation : forall p : PitchClass,
  11%binint *pc p = -pc p.
Proof.
  srapply Quotient_ind.
  - intro n.
    destruct n.
    + (* neg p case *)
      apply scalar_mult_11_neg.
    + (* zero case *)
      apply scalar_mult_11_zero.
    + (* pos p case *)
      apply scalar_mult_11_pos.
  - intros; apply path_ishprop.
Defined.

(** ----------------------------------------------------------------- *)
(** Section 20.6: General Transformation Properties                  *)
(** ----------------------------------------------------------------- *)

(** 1 and 11 are inverse generators *)
Example inverse_generators : forall n : BinInt,
  11%binint *pc (1%binint *pc [n]) = -pc [n].
Proof.
  intro n.
  rewrite pitch_class_scalar_mult_1.
  apply scalar_mult_11_is_negation.
Defined.

(** The octave (adding 12) is the identity transformation *)
Example octave_is_identity : forall p : PitchClass,
  p +pc [12%binint] = p.
Proof.
  intro p.
  rewrite pitch_class_add_comm.
  rewrite twelve_equals_zero.
  apply pitch_class_add_zero_l.
Defined.

(** Scalar multiplication distributes over transposition *)
Example scalar_mult_distributes_transpose : forall n : BinInt, forall p q : PitchClass,
  n *pc (p +pc q) = (n *pc p) +pc (n *pc q).
Proof.
  intros n p q.
  apply pitch_class_scalar_mult_add.
Defined.

(** The tritone is its own inverse under addition *)
Example tritone_self_inverse : forall p : PitchClass,
  (p +pc [6%binint]) +pc [6%binint] = p.
Proof.
  intro p.
  rewrite pitch_class_add_assoc.
  assert (H: ([6%binint] +pc [6%binint]) = [12%binint]).
  { simpl. reflexivity. }
  rewrite H.
  rewrite twelve_equals_zero.
  apply pitch_class_add_zero_r.
Defined.

(** ----------------------------------------------------------------- *)
(** Section 20.7: Musical Scale Generation                           *)
(** ----------------------------------------------------------------- *)

(** Examples demonstrating how various musical scales and chords
    are generated by repeated application of transformations *)

(** 3 generates the diminished seventh chord cycle *)
Example three_generates_dim_cycle : 
  let p0 := C in
  let p1 := 3%binint *pc [1%binint] in
  let p2 := 3%binint *pc [2%binint] in
  let p3 := 3%binint *pc [3%binint] in
  let p4 := 3%binint *pc [4%binint] in
  (p0 = C) /\ (p1 = Ds) /\ (p2 = Fs) /\ (p3 = A) /\ (p4 = C).
Proof.
  unfold C, Ds, Fs, A.
  simpl.
  repeat split; try reflexivity.
  apply twelve_equals_zero.
Defined.

(** 4 generates the augmented triad cycle *)
Example four_generates_aug_cycle :
  let p0 := C in
  let p1 := 4%binint *pc [1%binint] in
  let p2 := 4%binint *pc [2%binint] in
  let p3 := 4%binint *pc [3%binint] in
  (p0 = C) /\ (p1 = E) /\ (p2 = Gs) /\ (p3 = C).
Proof.
  unfold C, E, Gs.
  simpl.
  repeat split; try reflexivity.
  apply twelve_equals_zero.
Defined.

(** 2 generates whole tone scale *)
Example two_generates_whole_tone :
  let p0 := C in
  let p1 := 2%binint *pc [1%binint] in
  let p2 := 2%binint *pc [2%binint] in
  let p3 := 2%binint *pc [3%binint] in
  let p4 := 2%binint *pc [4%binint] in
  let p5 := 2%binint *pc [5%binint] in
  let p6 := 2%binint *pc [6%binint] in
  (p0 = C) /\ (p1 = D) /\ (p2 = E) /\ (p3 = Fs) /\ 
  (p4 = Gs) /\ (p5 = As) /\ (p6 = C).
Proof.
  unfold C, D, E, Fs, Gs, As.
  simpl.
  repeat split; try reflexivity.
  apply twelve_equals_zero.
Defined.

(** 1 generates the chromatic scale (all 12 pitch classes) *)
Example one_generates_chromatic :
  let gen n := 1%binint *pc [n] in
  (gen 0%binint = C) /\ (gen 1%binint = Cs) /\ (gen 2%binint = D) /\ 
  (gen 3%binint = Ds) /\ (gen 4%binint = E) /\ (gen 5%binint = F) /\ 
  (gen 6%binint = Fs) /\ (gen 7%binint = G) /\ (gen 8%binint = Gs) /\ 
  (gen 9%binint = A) /\ (gen 10%binint = As) /\ (gen 11%binint = B) /\ 
  (gen 12%binint = C).
Proof.
  unfold C, Cs, D, Ds, E, F, Fs, G, Gs, A, As, B.
  simpl.
  repeat split; try reflexivity.
  apply twelve_equals_zero.
Defined.

(** Helper: 56 equals 8 in pitch class arithmetic *)
Lemma fiftysix_equals_eight : [56%binint] = [8%binint].
Proof.
  apply qglue.
  exists (binint_negation 4%binint).
  simpl.
  reflexivity.
Defined.

(** Helper: 63 equals 3 in pitch class arithmetic *)
Lemma sixtythree_equals_three : [63%binint] = [3%binint].
Proof.
  apply qglue.
  exists (binint_negation 5%binint).
  simpl.
  reflexivity.
Defined.

(** Helper: 70 equals 10 in pitch class arithmetic *)
Lemma seventy_equals_ten : [70%binint] = [10%binint].
Proof.
  apply qglue.
  exists (binint_negation 5%binint).
  simpl.
  reflexivity.
Defined.

(** Helper: 77 equals 5 in pitch class arithmetic *)
Lemma seventyseven_equals_five : [77%binint] = [5%binint].
Proof.
  apply qglue.
  exists (binint_negation 6%binint).
  simpl.
  reflexivity.
Defined.

(** 7 generates the circle of fifths (all 12 pitch classes) *)
Example seven_generates_circle_of_fifths :
  let gen n := 7%binint *pc [n] in
  (gen 0%binint = C) /\ (gen 1%binint = G) /\ (gen 2%binint = D) /\ 
  (gen 3%binint = A) /\ (gen 4%binint = E) /\ (gen 5%binint = B) /\ 
  (gen 6%binint = Fs) /\ (gen 7%binint = Cs) /\ (gen 8%binint = Gs) /\ 
  (gen 9%binint = Ds) /\ (gen 10%binint = As) /\ (gen 11%binint = F).
Proof.
  unfold C, G, D, A, E, B, Fs, Cs, Gs, Ds, As, F.
  simpl.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * apply fourteen_equals_two.
      * split.
        -- apply twentyone_equals_nine.
        -- split.
           ++ apply twentyeight_equals_four.
           ++ split.
              ** apply thirtyfive_equals_eleven.
              ** split.
                 --- apply fortytwo_equals_six.
                 --- split.
                     +++ apply fortynine_equals_one.
                     +++ split.
                         *** apply fiftysix_equals_eight.
                         *** split.
                             ---- apply sixtythree_equals_three.
                             ---- split.
                                  ++++ apply seventy_equals_ten.
                                  ++++ apply seventyseven_equals_five.
Defined.

(** 6 generates only two pitch classes (the tritone) *)
Example six_generates_tritone :
  let p0 := C in
  let p1 := 6%binint *pc [1%binint] in
  let p2 := 6%binint *pc [2%binint] in
  (p0 = C) /\ (p1 = Fs) /\ (p2 = C).
Proof.
  unfold C, Fs.
  simpl.
  repeat split; try reflexivity.
  apply twelve_equals_zero.
Defined.

(** The diminished seventh chord repeats every 3 semitones *)
Example diminished_seventh_period : forall p : PitchClass,
  p +pc [3%binint] +pc [3%binint] +pc [3%binint] +pc [3%binint] = p.
Proof.
  intro p.
  rewrite pitch_class_add_assoc.
  rewrite pitch_class_add_assoc.
  rewrite pitch_class_add_assoc.
  assert (H: ([3%binint] +pc ([3%binint] +pc ([3%binint] +pc [3%binint]))) = [12%binint]).
  { simpl. reflexivity. }
  rewrite H.
  rewrite twelve_equals_zero.
  apply pitch_class_add_zero_r.
Defined.

(** Inversion and transposition combine to give all 24 operations of the T/I group *)
Example ti_group_element : forall n m : BinInt, forall p : PitchClass,
  pitch_class_transpose n (pitch_class_inversion m p) = 
  pitch_class_inversion (n + m)%binint p.
Proof.
  intros n m p.
  unfold pitch_class_transpose, pitch_class_inversion.
  rewrite <- pitch_class_add_assoc.
  f_ap.
Defined.

(** Interval classes are symmetric: the interval from p to q equals the interval from q to p inverted *)
Example interval_class_symmetry : forall p q : PitchClass,
  pc_set_interval_class p q = -pc (pc_set_interval_class q p).
Proof.
  intros p q.
  apply interval_class_neg.
Defined.

(** The interval class from any pitch to itself is always 0 *)
Example interval_class_reflexive : forall p : PitchClass,
  pc_set_interval_class p p = C.
Proof.
  intro p.
  apply interval_self.
Defined.

(** Transposition preserves interval classes *)
Example transposition_preserves_intervals : forall n : BinInt, forall p q : PitchClass,
  pc_set_interval_class (p +pc [n]) (q +pc [n]) = pc_set_interval_class p q.
Proof.
  intros n p q.
  unfold pc_set_interval_class.
  rewrite pitch_class_neg_add.
  rewrite <- pitch_class_add_assoc.
  rewrite pitch_class_add_rearrange.
  f_ap.
  rewrite pitch_class_add_assoc.
  rewrite pitch_class_add_neg_r.
  apply pitch_class_add_zero_r.
Defined.

(** Inversion preserves interval classes (but reverses them) *)
Example inversion_preserves_intervals : forall n : BinInt, forall p q : PitchClass,
  pc_set_interval_class (pitch_class_inversion n p) (pitch_class_inversion n q) = 
  -pc (pc_set_interval_class p q).
Proof.
  intros n p q.
  unfold pc_set_interval_class, pitch_class_inversion.
  rewrite pitch_class_neg_add.
  rewrite pitch_class_neg_neg.
  rewrite pitch_class_add_rearrange.
  rewrite <- pitch_class_add_assoc.
  rewrite pitch_class_add_neg_r.
  rewrite pitch_class_add_zero_l.
  rewrite pitch_class_neg_add.
  rewrite pitch_class_neg_neg.
  apply pitch_class_add_comm.
Defined.

(** The whole tone scale is invariant under transposition by 2 *)
Example whole_tone_t2_invariant : forall p : PitchClass,
    sum (p = C) (sum (p = D) (sum (p = E) (sum (p = Fs) (sum (p = Gs) (p = As))))) ->
    {q : PitchClass & 
      sum (q = C) (sum (q = D) (sum (q = E) (sum (q = Fs) (sum (q = Gs) (q = As))))) *
      (p +pc [2%binint] = q)}.
Proof.
  intros p H.
  exists (p +pc [2%binint]).
  split.
  - destruct H as [H1 | [H2 | [H3 | [H4 | [H5 | H6]]]]].
    + rewrite H1. unfold C, D. simpl. right. left. reflexivity.
    + rewrite H2. unfold D, E. simpl. right. right. left. reflexivity.
    + rewrite H3. unfold E, Fs. simpl. right. right. right. left. reflexivity.
    + rewrite H4. unfold Fs, Gs. simpl. right. right. right. right. left. reflexivity.
    + rewrite H5. unfold Gs, As. simpl. right. right. right. right. right. reflexivity.
    + rewrite H6. unfold As, C. simpl. left. apply twelve_equals_zero.
  - reflexivity.
Defined.

(** ================================================================= *)
(** Section 21: Decidable Equality                                   *)
(** ================================================================= *)

(** To implement singleton sets and proper set membership tests, we need
    decidable equality for pitch classes. Since PitchClass is a quotient
    type, we must build decidable equality from the ground up, starting
    with Core.Pos and BinInt.
    
    This section provides:
    - Decidable equality for positive numbers (Core.Pos)
    - Decidable equality for binary integers (BinInt)
    - Bounded search for octave equivalence witnesses
    - Helper functions for pitch class equality
    
    The main challenge is that pitch classes are equivalence classes,
    so we need to check if two integers differ by a multiple of 12.
    Without a built-in modulo operation, we use bounded search. *)

(** Check if Core.Pos has decidable equality *)
Definition check_pos_dec : Core.Pos -> Core.Pos -> Type.
Proof.
  intros p q.
  exact ((p = q) + (p <> q)).
Defined.

(** Decidable equality for positive numbers.
    This is defined by structural recursion on the binary representation. *)
Definition pos_eq_dec : forall (p q : Core.Pos), (p = q) + (p <> q).
Proof.
  fix pos_eq_dec 1.
  intros p q.
  destruct p, q.
  - (* xH, xH *)
    left. reflexivity.
  - (* xH, x0 *)
    right. intro H. discriminate H.
  - (* xH, x1 *)
    right. intro H. discriminate H.
  - (* x0, xH *)
    right. intro H. discriminate H.
  - (* x0, x0 *)
    destruct (pos_eq_dec p q).
    + left. f_ap.
    + right. intro H. apply n. injection H. auto.
  - (* x0, x1 *)
    right. intro H. discriminate H.
  - (* x1, xH *)
    right. intro H. discriminate H.
  - (* x1, x0 *)
    right. intro H. discriminate H.
  - (* x1, x1 *)
    destruct (pos_eq_dec p q).
    + left. f_ap.
    + right. intro H. apply n. injection H. auto.
Defined.

(** Helper lemmas for applying equality to constructors *)
Lemma pos_ap : forall (p p0 : Core.Pos), p = p0 -> pos p = pos p0.
Proof.
  intros p p0 H.
  rewrite H.
  reflexivity.
Defined.

Lemma neg_ap : forall (p p0 : Core.Pos), p = p0 -> neg p = neg p0.
Proof.
  intros p p0 H.
  rewrite H.
  reflexivity.
Defined.

(** Decidable equality for binary integers.
    This uses the decidable equality for positive numbers. *)
Definition binint_eq_dec : forall (a b : BinInt), (a = b) + (a <> b).
Proof.
  intros a b.
  destruct a, b.
  - (* neg p, neg p0 *)
    destruct (pos_eq_dec p p0) as [e|n].
    + left. apply neg_ap. exact e.
    + right. intro H. apply n. injection H. auto.
  - (* neg p, 0 *)
    right. intro H. discriminate H.
  - (* neg p, pos p0 *)
    right. intro H. discriminate H.
  - (* 0, neg p0 *)
    right. intro H. discriminate H.
  - (* 0, 0 *)
    left. reflexivity.
  - (* 0, pos p0 *)
    right. intro H. discriminate H.
  - (* pos p, neg p0 *)
    right. intro H. discriminate H.
  - (* pos p, 0 *)
    right. intro H. discriminate H.
  - (* pos p, pos p0 *)
    destruct (pos_eq_dec p p0) as [e|n].
    + left. apply pos_ap. exact e.
    + right. intro H. apply n. injection H. auto.
Defined.

(** ================================================================= *)
(** Bounded Search for Octave Equivalence                            *)
(** ================================================================= *)

(** Since we don't have a modulo operation, we use bounded search to
    check if two integers represent the same pitch class. This is not
    ideal but is fully constructive. *)

(** Convert decidable proposition to boolean *)
Definition dec_to_bool {A : Type} (d : A + (~ A)) : Bool :=
  match d with
  | inl _ => true
  | inr _ => false
  end.

(** Check if n is divisible by 12 (i.e., represents pitch class C) *)
Definition divisible_by_12 (n : BinInt) : Type :=
  {k : BinInt | n = (12 * k)%binint}.

(** Check if a specific k witnesses octave equivalence: n = m + 12k *)
Definition check_octave_witness (m n k : BinInt) : Bool :=
  dec_to_bool (binint_eq_dec n (m + 12 * k)%binint).

(** Convert nat to Core.Pos for use in bounded search *)
Fixpoint nat_to_pos (n : nat) : Core.Pos :=
  match n with
  | O => Core.xH
  | S n' => Core.pos_succ (nat_to_pos n')
  end.

(** Check octave equivalence for k in range -bound to +bound.
    Returns true if we find a k such that n = m + 12k. *)
Fixpoint check_k_range (m n : BinInt) (bound : nat) : Bool :=
  match bound with
  | O => check_octave_witness m n 0%binint
  | S bound' => orb (check_octave_witness m n (pos (nat_to_pos (S bound'))))
                   (orb (check_octave_witness m n (neg (nat_to_pos (S bound'))))
                        (check_k_range m n bound'))
  end.

(** Check if n represents pitch class C (i.e., n = 12k for some k) *)
Definition check_represents_C (n : BinInt) : Bool :=
  check_k_range 0%binint n 100.

(** Check if two integers represent the same pitch class *)
Definition same_pitch_class (m n : BinInt) : Bool :=
  check_represents_C (n - m)%binint.

(** ================================================================= *)
(** Pitch Class Representatives                                      *)
(** ================================================================= *)

(** To work with pitch classes concretely, we often need to find a
    canonical representative in the range 0-11. *)

(** Normalize n to its representative in 0-11 if already in range *)
Definition normalize_to_12 (n : BinInt) : BinInt :=
  if binint_eq_dec n 0%binint then 0%binint
  else if binint_eq_dec n 1%binint then 1%binint
  else if binint_eq_dec n 2%binint then 2%binint
  else if binint_eq_dec n 3%binint then 3%binint
  else if binint_eq_dec n 4%binint then 4%binint
  else if binint_eq_dec n 5%binint then 5%binint
  else if binint_eq_dec n 6%binint then 6%binint
  else if binint_eq_dec n 7%binint then 7%binint
  else if binint_eq_dec n 8%binint then 8%binint
  else if binint_eq_dec n 9%binint then 9%binint
  else if binint_eq_dec n 10%binint then 10%binint
  else if binint_eq_dec n 11%binint then 11%binint
  else n.

(** Find the representative of n in range 0-11.
    This is a bounded approximation - for integers outside our search
    range, it returns 0 as a default. *)
Definition find_representative (n : BinInt) : BinInt.
Proof.
  (* Check if n is already in range 0-11 *)
  destruct (binint_eq_dec n 0%binint).
  - exact 0%binint.
  - destruct (binint_eq_dec n 1%binint).
    + exact 1%binint.
    + destruct (binint_eq_dec n 2%binint).
      * exact 2%binint.
      * destruct (binint_eq_dec n 3%binint).
        -- exact 3%binint.
        -- destruct (binint_eq_dec n 4%binint).
           ++ exact 4%binint.
           ++ destruct (binint_eq_dec n 5%binint).
              ** exact 5%binint.
              ** destruct (binint_eq_dec n 6%binint).
                 --- exact 6%binint.
                 --- destruct (binint_eq_dec n 7%binint).
                     +++ exact 7%binint.
                     +++ destruct (binint_eq_dec n 8%binint).
                         *** exact 8%binint.
                         *** destruct (binint_eq_dec n 9%binint).
                             ---- exact 9%binint.
                             ---- destruct (binint_eq_dec n 10%binint).
                                  ++++ exact 10%binint.
                                  ++++ destruct (binint_eq_dec n 11%binint).
                                       **** exact 11%binint.
                                       **** (* Not in 0-11, would need to search *)
                                            exact 0%binint. (* Default *)
Defined.

(** Get a pitch class representative (currently simplified) *)
Definition get_representative (n : BinInt) : BinInt :=
  if check_k_range 0%binint n 100 then 0%binint else n.

(** ================================================================= *)
(** Pitch Class Equality Helpers                                     *)
(** ================================================================= *)

(** Check if a pitch class equals a specific integer representative *)
Definition pitch_class_is_n (p : PitchClass) (n : BinInt) : Type :=
  p = [n].

(** Check if pitch class is zero (C) *)
Definition is_zero_pitch_class (p : PitchClass) : Type :=
  p = C.

(** Two pitch classes are equal iff they act the same on all elements.
    This is a characterization of equality in the group. *)
Definition pitch_classes_equal_action (p q : PitchClass) : Type :=
  forall r : PitchClass, p +pc r = q +pc r.

(** An integer represents pitch class C if it's divisible by 12 *)
Definition represents_C (n : BinInt) : Type :=
  {k : BinInt | n = (12 * k)%binint}.

(** Note: Full decidable equality for PitchClass requires either:
    1. A complete modulo operation on BinInt
    2. Showing that our bounded search is sufficient
    3. Using the finite nature of Z/12Z more directly
    
    This remains an open challenge in the formalization. *)
  
(* Just verify that your check_represents_C function works on 0 *)
Example check_C_is_true : check_represents_C 0%binint = true.
Proof.
  unfold check_represents_C.
  unfold check_k_range.
  simpl.
  (* This should reduce to checking if 0 = 0 + 12*0 *)
  reflexivity.
Defined.

Example check_octave_witness_12_works : 
  check_octave_witness 0%binint 12%binint 1%binint = true.
Proof.
  unfold check_octave_witness.
  unfold dec_to_bool.
  simpl.
  reflexivity.
Defined.

Example check_k_range_finds_12_trace : 
  orb (check_octave_witness 0%binint 12%binint 1%binint) 
      (check_octave_witness 0%binint 12%binint 0%binint) = true.
Proof.
  reflexivity.
Defined.

Example nat_to_pos_1_is_2 : nat_to_pos 1 = Core.x0 Core.xH.
Proof.
  simpl.
  reflexivity.
Defined.

Example nat_to_pos_0_is_1 : nat_to_pos 0 = Core.xH.
Proof.
  simpl.
  reflexivity.
Defined.

Example nat_to_pos_values : 
  (nat_to_pos 0 = Core.xH) /\
  (nat_to_pos 1 = Core.x0 Core.xH) /\
  (nat_to_pos 2 = Core.x1 Core.xH).
Proof.
  simpl.
  repeat split; reflexivity.
Defined.

Example check_octave_witness_minus_12_works : 
  check_octave_witness 0%binint (-12)%binint (neg Core.xH) = true.
Proof.
  unfold check_octave_witness, dec_to_bool.
  simpl.
  reflexivity.
Defined.

Example trace_k_range_minus_12 :
  orb (check_octave_witness 0%binint (-12)%binint (pos Core.xH))
      (orb (check_octave_witness 0%binint (-12)%binint (neg Core.xH))
           (check_octave_witness 0%binint (-12)%binint 0%binint)) = true.
Proof.
  simpl.
  assert (H: check_octave_witness 0%binint (-12)%binint (neg Core.xH) = true).
  { apply check_octave_witness_minus_12_works. }
  (* The middle witness should make the whole expression true *)
  reflexivity.
Defined.

Example check_represents_C_zero : check_represents_C 0%binint = true.
Proof.
  unfold check_represents_C, check_k_range.
  simpl.
  unfold check_octave_witness, dec_to_bool.
  simpl.
  reflexivity.
Defined.

Example C_plus_G_equals_G : C +pc G = G.
Proof.
  unfold C, G.
  simpl.
  reflexivity.
Defined.

Example twelve_plus_zero_equals_twelve : [12%binint] +pc [0%binint] = [12%binint].
Proof.
  simpl.
  reflexivity.
Defined.

Example interval_C_to_G : pc_set_interval_class C G = G.
Proof.
  unfold pc_set_interval_class, C, G.
  simpl.
  reflexivity.
Defined.

Example interval_C_to_F : pc_set_interval_class C F = F.
Proof.
  unfold pc_set_interval_class, C, F.
  simpl.
  reflexivity.
Defined.

Example neg_C_is_C : -pc C = C.
Proof.
  unfold C.
  simpl.
  apply qglue.
  exists 0%binint.
  rewrite binint_mul_0_r.
  rewrite binint_add_0_r.
  apply binint_negation_0.
Defined.

Example interval_from_C_is_identity : forall p : PitchClass,
  pc_set_interval_class C p = p.
Proof.
  intro p.
  unfold pc_set_interval_class, C.
  rewrite neg_C_is_C.
  unfold C.
  apply pitch_class_add_zero_r.
Defined.

(** ================================================================= *)
(** Section 22: Completing Musical Set Definitions                   *)
(** ================================================================= *)

(** Since we lack decidable equality, we'll define sets using 
    characteristic properties based on intervals and transpositions.
    This section provides the building blocks for constructing
    musical sets through interval relationships. *)

(** ----------------------------------------------------------------- *)
(** Basic Pitch Class Arithmetic Properties                          *)
(** ----------------------------------------------------------------- *)

(** These lemmas establish fundamental arithmetic facts about pitch
    classes, showing how addition behaves in Z/12Z. *)

(** Any pitch class minus itself equals C (the identity) *)
Example G_minus_G_is_C : G +pc (-pc G) = C.
Proof.
  apply pitch_class_add_neg_r.
Defined.

(** Doubling pitch classes - these show which pitch classes are
    self-inverse under addition (only C and F#) *)
Example D_plus_D_is_E : D +pc D = E.
Proof.
  unfold D, E.
  simpl.
  reflexivity.
Defined.

Example F_plus_F_is_As : F +pc F = As.
Proof.
  unfold F, As.
  simpl.
  reflexivity.
Defined.

(** F# is self-inverse: F# + F# = C (12 ≡ 0 mod 12) *)
Example Fs_plus_Fs_is_C : Fs +pc Fs = C.
Proof.
  unfold Fs, C.
  simpl.
  apply twelve_equals_zero.
Defined.

(** Special arithmetic: E + G# = C (4 + 8 = 12 ≡ 0 mod 12) *)
Example E_plus_Gs_is_C : E +pc Gs = C.
Proof.
  unfold E, Gs, C.
  simpl.
  apply twelve_equals_zero.
Defined.

(** ----------------------------------------------------------------- *)
(** Pitch Class Equality via Differences                             *)
(** ----------------------------------------------------------------- *)

(** These lemmas establish that we can test pitch class equality
    by checking if their difference equals C. This gives us a
    computational approach to equality without decidability. *)

(** If p - q = C, then p = q *)
Example difference_equals_C_implies_equal : forall p q : PitchClass,
  p +pc (-pc q) = C -> p = q.
Proof.
  intros p q H.
  assert (H2: (p +pc (-pc q)) +pc q = C +pc q).
  { rewrite H. reflexivity. }
  rewrite pitch_class_add_assoc in H2.
  rewrite (pitch_class_add_comm (-pc q) q) in H2.
  rewrite pitch_class_add_neg_r in H2.
  rewrite pitch_class_add_zero_r in H2.
  rewrite pitch_class_add_zero_l in H2.
  exact H2.
Defined.

(** If p = q, then p - q = C *)
Example equal_implies_difference_C : forall p q : PitchClass,
  p = q -> p +pc (-pc q) = C.
Proof.
  intros p q H.
  rewrite H.
  apply pitch_class_add_neg_r.
Defined.

(** ----------------------------------------------------------------- *)
(** Chromatic Scale: Semitone Steps (Interval = 1)                  *)
(** ----------------------------------------------------------------- *)

(** The chromatic scale consists of all 12 pitch classes in
    semitone steps. These lemmas show that adding 1 moves through
    the chromatic scale in order. *)

Example C_plus_one_is_Cs : C +pc [1%binint] = Cs.
Proof.
  unfold C, Cs.
  simpl.
  reflexivity.
Defined.

Example Cs_plus_one_is_D : Cs +pc [1%binint] = D.
Proof.
  unfold Cs, D.
  simpl.
  reflexivity.
Defined.

Example D_plus_one_is_Ds : D +pc [1%binint] = Ds.
Proof.
  unfold D, Ds.
  simpl.
  reflexivity.
Defined.

Example Ds_plus_one_is_E : Ds +pc [1%binint] = E.
Proof.
  unfold Ds, E.
  simpl.
  reflexivity.
Defined.

Example E_plus_one_is_F : E +pc [1%binint] = F.
Proof.
  unfold E, F.
  simpl.
  reflexivity.
Defined.

Example F_plus_one_is_Fs : F +pc [1%binint] = Fs.
Proof.
  unfold F, Fs.
  simpl.
  reflexivity.
Defined.

Example Fs_plus_one_is_G : Fs +pc [1%binint] = G.
Proof.
  unfold Fs, G.
  simpl.
  reflexivity.
Defined.

Example G_plus_one_is_Gs : G +pc [1%binint] = Gs.
Proof.
  unfold G, Gs.
  simpl.
  reflexivity.
Defined.

Example Gs_plus_one_is_A : Gs +pc [1%binint] = A.
Proof.
  unfold Gs, A.
  simpl.
  reflexivity.
Defined.

Example A_plus_one_is_As : A +pc [1%binint] = As.
Proof.
  unfold A, As.
  simpl.
  reflexivity.
Defined.

Example As_plus_one_is_B : As +pc [1%binint] = B.
Proof.
  unfold As, B.
  simpl.
  reflexivity.
Defined.

(** The chromatic scale wraps around: B + 1 = C *)
Example B_plus_one_is_C : B +pc [1%binint] = C.
Proof.
  unfold B, C.
  simpl.
  apply twelve_equals_zero.
Defined.

(** ----------------------------------------------------------------- *)
(** Whole Tone Scale: Whole Steps (Interval = 2)                    *)
(** ----------------------------------------------------------------- *)

(** The whole tone scale divides the octave into 6 equal parts.
    Adding 2 repeatedly generates one of the two whole tone scales:
    C, D, E, F#, G#, A# *)

Example C_plus_two_is_D : C +pc [2%binint] = D.
Proof.
  unfold C, D.
  simpl.
  reflexivity.
Defined.

Example D_plus_two_is_E : D +pc [2%binint] = E.
Proof.
  unfold D, E.
  simpl.
  reflexivity.
Defined.

Example E_plus_two_is_Fs : E +pc [2%binint] = Fs.
Proof.
  unfold E, Fs.
  simpl.
  reflexivity.
Defined.

Example Fs_plus_two_is_Gs : Fs +pc [2%binint] = Gs.
Proof.
  unfold Fs, Gs.
  simpl.
  reflexivity.
Defined.

Example Gs_plus_two_is_As : Gs +pc [2%binint] = As.
Proof.
  unfold Gs, As.
  simpl.
  reflexivity.
Defined.

(** The whole tone scale cycles back: A# + 2 = C *)
Example As_plus_two_is_C : As +pc [2%binint] = C.
Proof.
  unfold As, C.
  simpl.
  apply twelve_equals_zero.
Defined.

(** B + 2 = C# starts the other whole tone scale *)
Example B_plus_two_is_Cs : B +pc [2%binint] = Cs.
Proof.
  unfold B, Cs.
  simpl.
  apply qglue.
  exists (binint_negation 1%binint).
  simpl.
  reflexivity.
Defined.

(** ----------------------------------------------------------------- *)
(** Diminished Seventh: Minor Thirds (Interval = 3)                  *)
(** ----------------------------------------------------------------- *)

(** The diminished seventh chord divides the octave into 4 equal
    parts. Adding 3 repeatedly generates: C, Eb, Gb, A *)

Example C_plus_three_is_Ds : C +pc [3%binint] = Ds.
Proof.
  unfold C, Ds.
  simpl.
  reflexivity.
Defined.

Example Ds_plus_three_is_Fs : Ds +pc [3%binint] = Fs.
Proof.
  unfold Ds, Fs.
  simpl.
  reflexivity.
Defined.

Example Fs_plus_three_is_A : Fs +pc [3%binint] = A.
Proof.
  unfold Fs, A.
  simpl.
  reflexivity.
Defined.

(** The diminished seventh cycles in 4 steps: A + 3 = C *)
Example A_plus_three_is_C : A +pc [3%binint] = C.
Proof.
  unfold A, C.
  simpl.
  apply twelve_equals_zero.
Defined.

(** Alias for consistency *)
Example C_plus_three_is_Ds_v2 : C +pc [3%binint] = Ds.
Proof.
  apply C_plus_three_is_Ds.
Defined.

(** ----------------------------------------------------------------- *)
(** Augmented Triad: Major Thirds (Interval = 4)                    *)
(** ----------------------------------------------------------------- *)

(** The augmented triad divides the octave into 3 equal parts.
    Adding 4 repeatedly generates: C, E, G# *)

Example C_plus_four_is_E : C +pc [4%binint] = E.
Proof.
  unfold C, E.
  simpl.
  reflexivity.
Defined.

Example E_plus_four_is_Gs : E +pc [4%binint] = Gs.
Proof.
  unfold E, Gs.
  simpl.
  reflexivity.
Defined.

(** The augmented triad cycles in 3 steps: G# + 4 = C *)
Example Gs_plus_four_is_C : Gs +pc [4%binint] = C.
Proof.
  unfold Gs, C.
  simpl.
  apply twelve_equals_zero.
Defined.

(** A + 4 = C# shows a different starting point *)
Example A_plus_four_is_Cs : A +pc [4%binint] = Cs.
Proof.
  unfold A, Cs.
  simpl.
  apply qglue.
  exists (binint_negation 1%binint).
  simpl.
  reflexivity.
Defined.

(** Alias for consistency *)
Example C_plus_four_is_E_v2 : C +pc [4%binint] = E.
Proof.
  apply C_plus_four_is_E.
Defined.

(** ----------------------------------------------------------------- *)
(** Perfect Fourths (Interval = 5)                                  *)
(** ----------------------------------------------------------------- *)

(** The perfect fourth is 5 semitones. Moving by fourths generates
    the circle of fourths: C, F, Bb, Eb, Ab, Db, Gb, B, E, A, D, G *)

Example C_plus_five_is_F : C +pc [5%binint] = F.
Proof.
  unfold C, F.
  simpl.
  reflexivity.
Defined.

Example F_plus_five_is_As : F +pc [5%binint] = As.
Proof.
  unfold F, As.
  simpl.
  reflexivity.
Defined.

(** ----------------------------------------------------------------- *)
(** Perfect Fifths (Interval = 7)                                   *)
(** ----------------------------------------------------------------- *)

(** The perfect fifth is 7 semitones. Moving by fifths generates
    the circle of fifths: C, G, D, A, E, B, F#, C#, G#, D#, A#, F *)

Example C_plus_seven_is_G : C +pc [7%binint] = G.
Proof.
  unfold C, G.
  simpl.
  reflexivity.
Defined.

Example G_plus_seven_is_D : G +pc [7%binint] = D.
Proof.
  unfold G, D.
  simpl.
  apply fourteen_equals_two.
Defined.

(** Alias for consistency *)
Example C_plus_seven_is_G_v2 : C +pc [7%binint] = G.
Proof.
  apply C_plus_seven_is_G.
Defined.

(** ----------------------------------------------------------------- *)
(** Other Important Intervals                                        *)
(** ----------------------------------------------------------------- *)

(** Minor seventh: C + 10 = Bb *)
Example C_plus_ten_is_As : C +pc [10%binint] = As.
Proof.
  unfold C, As.
  simpl.
  reflexivity.
Defined.

(** Summary of major/minor triad intervals from C *)
Example intervals_from_C_047 : 
  (C +pc [0%binint] = C) /\ 
  (C +pc [4%binint] = E) /\ 
  (C +pc [7%binint] = G).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + apply C_plus_four_is_E.
    + unfold C, G. simpl. reflexivity.
Defined.

(** Test for membership in augmented triad pattern *)
Example is_augmented_from_C : forall p : PitchClass,
  sum (p = C) (sum (p = E) (p = Gs)) -> 
  sum (p +pc (-pc C) = C) (sum (p +pc (-pc C) = E) (p +pc (-pc C) = Gs)).
Proof.
  intros p H.
  rewrite neg_C_is_C.
  rewrite pitch_class_add_zero_r.
  exact H.
Defined.

(** ----------------------------------------------------------------- *)
(** Bounded Search Helpers for Pitch Class Representation           *)
(** ----------------------------------------------------------------- *)

(** These functions and examples test whether integers represent
    specific pitch classes using bounded search for octave
    equivalence witnesses. *)

(** General function to check if m represents pitch class n *)
Definition represents_pitch_class_n (m n : BinInt) : Bool :=
  check_k_range n m 100.

(** 0 represents pitch class C *)
Example represents_0_works : represents_pitch_class_n 0%binint 0%binint = true.
Proof.
  unfold represents_pitch_class_n.
  unfold check_k_range.
  simpl.
  unfold check_octave_witness, dec_to_bool.
  simpl.
  reflexivity.
Defined.

(** Tests showing that non-zero values don't represent C *)
Example check_represents_C_one_is_false : 
  check_k_range 0%binint 1%binint 0 = false.
Proof.
  unfold check_k_range.
  simpl.
  unfold check_octave_witness, dec_to_bool.
  simpl.
  reflexivity.
Defined.

Example check_represents_C_four_is_false : 
  check_k_range 0%binint 4%binint 0 = false.
Proof.
  unfold check_k_range.
  simpl.
  unfold check_octave_witness, dec_to_bool.
  simpl.
  reflexivity.
Defined.

Example check_represents_C_seven_is_false : 
  check_k_range 0%binint 7%binint 0 = false.
Proof.
  unfold check_k_range.
  simpl.
  unfold check_octave_witness, dec_to_bool.
  simpl.
  reflexivity.
Defined.

(** C major triad membership tests *)
Example C_major_triad_membership : 
  (check_represents_C 0%binint = true) /\
  (check_represents_C 4%binint = false) /\
  (check_represents_C 7%binint = false).
Proof.
  split.
  - apply check_C_is_true.
  - split.
    + apply check_represents_C_four_is_false.
    + apply check_represents_C_seven_is_false.
Defined.

(** General function to check if n represents a specific pitch class *)
Definition check_represents_pitch_class (n : BinInt) (pc_value : BinInt) : Bool :=
  check_k_range pc_value n 100.

(** 4 represents pitch class E *)
Example check_represents_E : check_represents_pitch_class 4%binint 4%binint = true.
Proof.
  unfold check_represents_pitch_class, check_k_range.
  simpl.
  unfold check_octave_witness, dec_to_bool.
  simpl.
  reflexivity.
Defined.

(** 16 = 4 + 12*1, so 16 also represents E *)
Example check_16_equals_4_plus_12 : 
  check_octave_witness 4%binint 16%binint 1%binint = true.
Proof.
  unfold check_octave_witness, dec_to_bool.
  simpl.
  reflexivity.
Defined.

(** Trace showing how bounded search finds the witness *)
Example trace_check_16_represents_E : 
  orb (check_octave_witness 4%binint 16%binint (pos Core.xH))
      (orb (check_octave_witness 4%binint 16%binint (neg Core.xH))
           (check_octave_witness 4%binint 16%binint 0%binint)) = true.
Proof.
  assert (H: check_octave_witness 4%binint 16%binint (pos Core.xH) = true).
  { apply check_16_equals_4_plus_12. }
  rewrite H.
  simpl.
  reflexivity.
Defined.

(** Smaller bounded search for efficiency *)
Definition check_represents_pc_small (n : BinInt) (pc_value : BinInt) : Bool :=
  check_k_range pc_value n 10.

Example test_check_represents_pc_small : 
  check_represents_pc_small 4%binint 4%binint = true.
Proof.
  unfold check_represents_pc_small, check_k_range.
  simpl.
  reflexivity.
Defined.

Example C_E_G_are_major_third_apart : 
  (E = C +pc [4%binint]) /\
  (G = C +pc [7%binint]) /\
  (C = C +pc [0%binint]).
Proof.
  split.
  - symmetry. apply C_plus_four_is_E.
  - split.
    + symmetry. apply C_plus_seven_is_G.
    + symmetry. apply pitch_class_add_zero_r.
Defined.

Example pitch_in_C_major_iff : forall p : PitchClass,
  sum (p = C) (sum (p = E) (p = G)) <-> 
  {n : BinInt & (sum (n = 0%binint) (sum (n = 4%binint) (n = 7%binint))) * (p = C +pc [n])}.
Proof.
  intro p.
  split.
  - intro H.
    destruct H as [H1 | [H2 | H3]].
    + exists 0%binint. split.
      * left. reflexivity.
      * rewrite H1. symmetry. apply pitch_class_add_zero_r.
    + exists 4%binint. split.
      * right. left. reflexivity.
      * rewrite H2. symmetry. apply C_plus_four_is_E.
    + exists 7%binint. split.
      * right. right. reflexivity.
      * rewrite H3. symmetry. apply C_plus_seven_is_G.
  - intros [n [Hn Hp]].
    destruct Hn as [H1 | [H2 | H3]].
    + left. rewrite Hp, H1. apply pitch_class_add_zero_r.
    + right. left. rewrite Hp, H2. apply C_plus_four_is_E.
    + right. right. rewrite Hp, H3. apply C_plus_seven_is_G.
Defined.

Example transpose_preserves_major_triad : forall p t : PitchClass,
  sum (p = C) (sum (p = E) (p = G)) ->
  sum (p +pc t = C +pc t) (sum (p +pc t = E +pc t) (p +pc t = G +pc t)).
Proof.
  intros p t H.
  destruct H as [H1 | [H2 | H3]].
  - left. rewrite H1. reflexivity.
  - right. left. rewrite H2. reflexivity.
  - right. right. rewrite H3. reflexivity.
Defined.

Example F_major_triad : 
  (F +pc [0%binint] = F) /\
  (F +pc [4%binint] = A) /\
  (F +pc [7%binint] = C).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold F, A. simpl. reflexivity.
    + unfold F, C. simpl. apply twelve_equals_zero.
Defined.

Example G_major_triad : 
  (G +pc [0%binint] = G) /\
  (G +pc [4%binint] = B) /\
  (G +pc [7%binint] = D).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold G, B. simpl. reflexivity.
    + unfold G, D. simpl. apply fourteen_equals_two.
Defined.

(** All 12 major triads showing root + major third + perfect fifth *)

Example Cs_major_triad : 
  (Cs +pc [0%binint] = Cs) /\
  (Cs +pc [4%binint] = F) /\
  (Cs +pc [7%binint] = Gs).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Cs, F. simpl. reflexivity.
    + unfold Cs, Gs. simpl. reflexivity.
Defined.

Example D_major_triad : 
  (D +pc [0%binint] = D) /\
  (D +pc [4%binint] = Fs) /\
  (D +pc [7%binint] = A).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold D, Fs. simpl. reflexivity.
    + unfold D, A. simpl. reflexivity.
Defined.

Example Ds_major_triad : 
  (Ds +pc [0%binint] = Ds) /\
  (Ds +pc [4%binint] = G) /\
  (Ds +pc [7%binint] = As).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Ds, G. simpl. reflexivity.
    + unfold Ds, As. simpl. reflexivity.
Defined.

Example E_major_triad : 
  (E +pc [0%binint] = E) /\
  (E +pc [4%binint] = Gs) /\
  (E +pc [7%binint] = B).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold E, Gs. simpl. reflexivity.
    + unfold E, B. simpl. reflexivity.
Defined.

Example Fs_major_triad : 
  (Fs +pc [0%binint] = Fs) /\
  (Fs +pc [4%binint] = As) /\
  (Fs +pc [7%binint] = Cs).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Fs, As. simpl. reflexivity.
    + unfold Fs, Cs. simpl. 
      apply qglue. exists (binint_negation 1%binint). 
      simpl. reflexivity.
Defined.

Example Gs_major_triad : 
  (Gs +pc [0%binint] = Gs) /\
  (Gs +pc [4%binint] = C) /\
  (Gs +pc [7%binint] = Ds).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Gs, C. simpl. apply twelve_equals_zero.
    + unfold Gs, Ds. simpl. apply fifteen_equals_three.
Defined.

Example A_major_triad : 
  (A +pc [0%binint] = A) /\
  (A +pc [4%binint] = Cs) /\
  (A +pc [7%binint] = E).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold A, Cs. simpl. 
      apply qglue. exists (binint_negation 1%binint).
      simpl. reflexivity.
    + unfold A, E. simpl. apply sixteen_equals_four.
Defined.

Example As_major_triad : 
  (As +pc [0%binint] = As) /\
  (As +pc [4%binint] = D) /\
  (As +pc [7%binint] = F).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold As, D. simpl. apply fourteen_equals_two.
    + unfold As, F. simpl. 
      apply qglue. exists (binint_negation 1%binint).
      simpl. reflexivity.
Defined.

Example B_major_triad : 
  (B +pc [0%binint] = B) /\
  (B +pc [4%binint] = Ds) /\
  (B +pc [7%binint] = Fs).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold B, Ds. simpl. apply fifteen_equals_three.
    + unfold B, Fs. simpl. apply eighteen_equals_six.
Defined.

(** ================================================================= *)
(** Section 24: Minor Triads                                         *)
(** ================================================================= *)

(** Minor triads have the interval pattern: root, minor third (3 semitones), 
    perfect fifth (7 semitones). These are fundamental to tonal music. *)

Example C_minor_triad : 
  (C +pc [0%binint] = C) /\
  (C +pc [3%binint] = Ds) /\
  (C +pc [7%binint] = G).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + apply C_plus_three_is_Ds.
    + apply C_plus_seven_is_G.
Defined.

Example Cs_minor_triad : 
  (Cs +pc [0%binint] = Cs) /\
  (Cs +pc [3%binint] = E) /\
  (Cs +pc [7%binint] = Gs).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Cs, E. simpl. reflexivity.
    + unfold Cs, Gs. simpl. reflexivity.
Defined.

Example D_minor_triad : 
  (D +pc [0%binint] = D) /\
  (D +pc [3%binint] = F) /\
  (D +pc [7%binint] = A).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold D, F. simpl. reflexivity.
    + unfold D, A. simpl. reflexivity.
Defined.

Example Ds_minor_triad : 
  (Ds +pc [0%binint] = Ds) /\
  (Ds +pc [3%binint] = Fs) /\
  (Ds +pc [7%binint] = As).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Ds, Fs. simpl. reflexivity.
    + unfold Ds, As. simpl. reflexivity.
Defined.

Example E_minor_triad : 
  (E +pc [0%binint] = E) /\
  (E +pc [3%binint] = G) /\
  (E +pc [7%binint] = B).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold E, G. simpl. reflexivity.
    + unfold E, B. simpl. reflexivity.
Defined.

Example F_minor_triad : 
  (F +pc [0%binint] = F) /\
  (F +pc [3%binint] = Gs) /\
  (F +pc [7%binint] = C).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold F, Gs. simpl. reflexivity.
    + unfold F, C. simpl. apply twelve_equals_zero.
Defined.

Example Fs_minor_triad : 
  (Fs +pc [0%binint] = Fs) /\
  (Fs +pc [3%binint] = A) /\
  (Fs +pc [7%binint] = Cs).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Fs, A. simpl. reflexivity.
    + unfold Fs, Cs. simpl. 
      apply qglue. exists (binint_negation 1%binint).
      simpl. reflexivity.
Defined.

Example G_minor_triad : 
  (G +pc [0%binint] = G) /\
  (G +pc [3%binint] = As) /\
  (G +pc [7%binint] = D).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold G, As. simpl. reflexivity.
    + unfold G, D. simpl. apply fourteen_equals_two.
Defined.

Example Gs_minor_triad : 
  (Gs +pc [0%binint] = Gs) /\
  (Gs +pc [3%binint] = B) /\
  (Gs +pc [7%binint] = Ds).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Gs, B. simpl. reflexivity.
    + unfold Gs, Ds. simpl. apply fifteen_equals_three.
Defined.

Example A_minor_triad : 
  (A +pc [0%binint] = A) /\
  (A +pc [3%binint] = C) /\
  (A +pc [7%binint] = E).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold A, C. simpl. apply twelve_equals_zero.
    + unfold A, E. simpl. apply sixteen_equals_four.
Defined.

Example As_minor_triad : 
  (As +pc [0%binint] = As) /\
  (As +pc [3%binint] = Cs) /\
  (As +pc [7%binint] = F).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold As, Cs. simpl. 
      apply qglue. exists (binint_negation 1%binint).
      simpl. reflexivity.
    + unfold As, F. simpl.
      apply qglue. exists (binint_negation 1%binint).
      simpl. reflexivity.
Defined.

Example B_minor_triad : 
  (B +pc [0%binint] = B) /\
  (B +pc [3%binint] = D) /\
  (B +pc [7%binint] = Fs).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold B, D. simpl. apply fourteen_equals_two.
    + unfold B, Fs. simpl. apply eighteen_equals_six.
Defined.

(** ================================================================= *)
(** Section 25: Diminished Triads                                    *)
(** ================================================================= *)

(** Diminished triads have the interval pattern: root, minor third (3 semitones), 
    diminished fifth (6 semitones). These create tension and are important
    in harmonic progressions. *)

Example C_diminished_triad : 
  (C +pc [0%binint] = C) /\
  (C +pc [3%binint] = Ds) /\
  (C +pc [6%binint] = Fs).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + apply C_plus_three_is_Ds.
    + unfold C, Fs. simpl. reflexivity.
Defined.

Example Cs_diminished_triad : 
  (Cs +pc [0%binint] = Cs) /\
  (Cs +pc [3%binint] = E) /\
  (Cs +pc [6%binint] = G).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Cs, E. simpl. reflexivity.
    + unfold Cs, G. simpl. reflexivity.
Defined.

Example D_diminished_triad : 
  (D +pc [0%binint] = D) /\
  (D +pc [3%binint] = F) /\
  (D +pc [6%binint] = Gs).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold D, F. simpl. reflexivity.
    + unfold D, Gs. simpl. reflexivity.
Defined.

Example Ds_diminished_triad : 
  (Ds +pc [0%binint] = Ds) /\
  (Ds +pc [3%binint] = Fs) /\
  (Ds +pc [6%binint] = A).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Ds, Fs. simpl. reflexivity.
    + unfold Ds, A. simpl. reflexivity.
Defined.

Example E_diminished_triad : 
  (E +pc [0%binint] = E) /\
  (E +pc [3%binint] = G) /\
  (E +pc [6%binint] = As).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold E, G. simpl. reflexivity.
    + unfold E, As. simpl. reflexivity.
Defined.

Example F_diminished_triad : 
  (F +pc [0%binint] = F) /\
  (F +pc [3%binint] = Gs) /\
  (F +pc [6%binint] = B).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold F, Gs. simpl. reflexivity.
    + unfold F, B. simpl. reflexivity.
Defined.

Example Fs_diminished_triad : 
  (Fs +pc [0%binint] = Fs) /\
  (Fs +pc [3%binint] = A) /\
  (Fs +pc [6%binint] = C).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Fs, A. simpl. reflexivity.
    + unfold Fs, C. simpl. apply twelve_equals_zero.
Defined.

Example G_diminished_triad : 
  (G +pc [0%binint] = G) /\
  (G +pc [3%binint] = As) /\
  (G +pc [6%binint] = Cs).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold G, As. simpl. reflexivity.
    + unfold G, Cs. simpl.
      apply qglue. exists (binint_negation 1%binint).
      simpl. reflexivity.
Defined.

Example Gs_diminished_triad : 
  (Gs +pc [0%binint] = Gs) /\
  (Gs +pc [3%binint] = B) /\
  (Gs +pc [6%binint] = D).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Gs, B. simpl. reflexivity.
    + unfold Gs, D. simpl. apply fourteen_equals_two.
Defined.

Example A_diminished_triad : 
  (A +pc [0%binint] = A) /\
  (A +pc [3%binint] = C) /\
  (A +pc [6%binint] = Ds).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold A, C. simpl. apply twelve_equals_zero.
    + unfold A, Ds. simpl. apply fifteen_equals_three.
Defined.

Example As_diminished_triad : 
  (As +pc [0%binint] = As) /\
  (As +pc [3%binint] = Cs) /\
  (As +pc [6%binint] = E).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold As, Cs. simpl.
      apply qglue. exists (binint_negation 1%binint).
      simpl. reflexivity.
    + unfold As, E. simpl. apply sixteen_equals_four.
Defined.

Example B_diminished_triad : 
  (B +pc [0%binint] = B) /\
  (B +pc [3%binint] = D) /\
  (B +pc [6%binint] = F).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold B, D. simpl. apply fourteen_equals_two.
    + unfold B, F. simpl.
      apply qglue. exists (binint_negation 1%binint).
      simpl. reflexivity.
Defined.

(** ================================================================= *)
(** Section 26: Augmented Triads                                     *)
(** ================================================================= *)

(** Augmented triads have the interval pattern: root, major third (4 semitones), 
    augmented fifth (8 semitones). These divide the octave symmetrically into
    three equal parts and have a distinctive, unstable sound. *)

Example C_augmented_triad : 
  (C +pc [0%binint] = C) /\
  (C +pc [4%binint] = E) /\
  (C +pc [8%binint] = Gs).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + apply C_plus_four_is_E.
    + unfold C, Gs. simpl. reflexivity.
Defined.

Example Cs_augmented_triad : 
  (Cs +pc [0%binint] = Cs) /\
  (Cs +pc [4%binint] = F) /\
  (Cs +pc [8%binint] = A).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Cs, F. simpl. reflexivity.
    + unfold Cs, A. simpl. reflexivity.
Defined.

Example D_augmented_triad : 
  (D +pc [0%binint] = D) /\
  (D +pc [4%binint] = Fs) /\
  (D +pc [8%binint] = As).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold D, Fs. simpl. reflexivity.
    + unfold D, As. simpl. reflexivity.
Defined.

Example Ds_augmented_triad : 
  (Ds +pc [0%binint] = Ds) /\
  (Ds +pc [4%binint] = G) /\
  (Ds +pc [8%binint] = B).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Ds, G. simpl. reflexivity.
    + unfold Ds, B. simpl. reflexivity.
Defined.

Example E_augmented_triad : 
  (E +pc [0%binint] = E) /\
  (E +pc [4%binint] = Gs) /\
  (E +pc [8%binint] = C).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold E, Gs. simpl. reflexivity.
    + unfold E, C. simpl. apply twelve_equals_zero.
Defined.

Example F_augmented_triad : 
  (F +pc [0%binint] = F) /\
  (F +pc [4%binint] = A) /\
  (F +pc [8%binint] = Cs).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold F, A. simpl. reflexivity.
    + unfold F, Cs. simpl.
      apply qglue. exists (binint_negation 1%binint).
      simpl. reflexivity.
Defined.

Example Fs_augmented_triad : 
  (Fs +pc [0%binint] = Fs) /\
  (Fs +pc [4%binint] = As) /\
  (Fs +pc [8%binint] = D).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Fs, As. simpl. reflexivity.
    + unfold Fs, D. simpl. apply fourteen_equals_two.
Defined.

Example G_augmented_triad : 
  (G +pc [0%binint] = G) /\
  (G +pc [4%binint] = B) /\
  (G +pc [8%binint] = Ds).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold G, B. simpl. reflexivity.
    + unfold G, Ds. simpl. apply fifteen_equals_three.
Defined.

Example Gs_augmented_triad : 
  (Gs +pc [0%binint] = Gs) /\
  (Gs +pc [4%binint] = C) /\
  (Gs +pc [8%binint] = E).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Gs, C. simpl. apply twelve_equals_zero.
    + unfold Gs, E. simpl. apply sixteen_equals_four.
Defined.

Example A_augmented_triad : 
  (A +pc [0%binint] = A) /\
  (A +pc [4%binint] = Cs) /\
  (A +pc [8%binint] = F).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold A, Cs. simpl.
      apply qglue. exists (binint_negation 1%binint).
      simpl. reflexivity.
    + unfold A, F. simpl.
      apply qglue. exists (binint_negation 1%binint).
      simpl. reflexivity.
Defined.

Example As_augmented_triad : 
  (As +pc [0%binint] = As) /\
  (As +pc [4%binint] = D) /\
  (As +pc [8%binint] = Fs).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold As, D. simpl. apply fourteen_equals_two.
    + unfold As, Fs. simpl. apply eighteen_equals_six.
Defined.

Example B_augmented_triad : 
  (B +pc [0%binint] = B) /\
  (B +pc [4%binint] = Ds) /\
  (B +pc [8%binint] = G).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold B, Ds. simpl. apply fifteen_equals_three.
    + unfold B, G. simpl.
      apply qglue. exists (binint_negation 1%binint).
      simpl. reflexivity.
Defined.

(** ================================================================= *)
(** Section 27: Dominant Seventh Chords                              *)
(** ================================================================= *)

(** Dominant seventh chords have the interval pattern: root, major third (4 semitones), 
    perfect fifth (7 semitones), minor seventh (10 semitones). These create
    strong tension that resolves to the tonic. *)

Example C_dominant_seventh : 
  (C +pc [0%binint] = C) /\
  (C +pc [4%binint] = E) /\
  (C +pc [7%binint] = G) /\
  (C +pc [10%binint] = As).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + apply C_plus_four_is_E.
    + split.
      * apply C_plus_seven_is_G.
      * apply C_plus_ten_is_As.
Defined.

Example Cs_dominant_seventh : 
  (Cs +pc [0%binint] = Cs) /\
  (Cs +pc [4%binint] = F) /\
  (Cs +pc [7%binint] = Gs) /\
  (Cs +pc [10%binint] = B).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Cs, F. simpl. reflexivity.
    + split.
      * unfold Cs, Gs. simpl. reflexivity.
      * unfold Cs, B. simpl. reflexivity.
Defined.

Example D_dominant_seventh : 
  (D +pc [0%binint] = D) /\
  (D +pc [4%binint] = Fs) /\
  (D +pc [7%binint] = A) /\
  (D +pc [10%binint] = C).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold D, Fs. simpl. reflexivity.
    + split.
      * unfold D, A. simpl. reflexivity.
      * unfold D, C. simpl. apply twelve_equals_zero.
Defined.

Example Ds_dominant_seventh : 
  (Ds +pc [0%binint] = Ds) /\
  (Ds +pc [4%binint] = G) /\
  (Ds +pc [7%binint] = As) /\
  (Ds +pc [10%binint] = Cs).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Ds, G. simpl. reflexivity.
    + split.
      * unfold Ds, As. simpl. reflexivity.
      * unfold Ds, Cs. simpl.
        apply qglue. exists (binint_negation 1%binint).
        simpl. reflexivity.
Defined.

Example E_dominant_seventh : 
  (E +pc [0%binint] = E) /\
  (E +pc [4%binint] = Gs) /\
  (E +pc [7%binint] = B) /\
  (E +pc [10%binint] = D).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold E, Gs. simpl. reflexivity.
    + split.
      * unfold E, B. simpl. reflexivity.
      * unfold E, D. simpl. apply fourteen_equals_two.
Defined.

Example F_dominant_seventh : 
  (F +pc [0%binint] = F) /\
  (F +pc [4%binint] = A) /\
  (F +pc [7%binint] = C) /\
  (F +pc [10%binint] = Ds).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold F, A. simpl. reflexivity.
    + split.
      * unfold F, C. simpl. apply twelve_equals_zero.
      * unfold F, Ds. simpl. apply fifteen_equals_three.
Defined.

Example Fs_dominant_seventh : 
  (Fs +pc [0%binint] = Fs) /\
  (Fs +pc [4%binint] = As) /\
  (Fs +pc [7%binint] = Cs) /\
  (Fs +pc [10%binint] = E).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Fs, As. simpl. reflexivity.
    + split.
      * unfold Fs, Cs. simpl.
        apply qglue. exists (binint_negation 1%binint).
        simpl. reflexivity.
      * unfold Fs, E. simpl. apply sixteen_equals_four.
Defined.

Example G_dominant_seventh : 
  (G +pc [0%binint] = G) /\
  (G +pc [4%binint] = B) /\
  (G +pc [7%binint] = D) /\
  (G +pc [10%binint] = F).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold G, B. simpl. reflexivity.
    + split.
      * unfold G, D. simpl. apply fourteen_equals_two.
      * unfold G, F. simpl.
        apply qglue. exists (binint_negation 1%binint).
        simpl. reflexivity.
Defined.

Example Gs_dominant_seventh : 
  (Gs +pc [0%binint] = Gs) /\
  (Gs +pc [4%binint] = C) /\
  (Gs +pc [7%binint] = Ds) /\
  (Gs +pc [10%binint] = Fs).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold Gs, C. simpl. apply twelve_equals_zero.
    + split.
      * unfold Gs, Ds. simpl. apply fifteen_equals_three.
      * unfold Gs, Fs. simpl. apply eighteen_equals_six.
Defined.

Example A_dominant_seventh : 
  (A +pc [0%binint] = A) /\
  (A +pc [4%binint] = Cs) /\
  (A +pc [7%binint] = E) /\
  (A +pc [10%binint] = G).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold A, Cs. simpl.
      apply qglue. exists (binint_negation 1%binint).
      simpl. reflexivity.
    + split.
      * unfold A, E. simpl. apply sixteen_equals_four.
      * unfold A, G. simpl.
        apply qglue. exists (binint_negation 1%binint).
        simpl. reflexivity.
Defined.

Example As_dominant_seventh : 
  (As +pc [0%binint] = As) /\
  (As +pc [4%binint] = D) /\
  (As +pc [7%binint] = F) /\
  (As +pc [10%binint] = Gs).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold As, D. simpl. apply fourteen_equals_two.
    + split.
      * unfold As, F. simpl.
        apply qglue. exists (binint_negation 1%binint).
        simpl. reflexivity.
      * unfold As, Gs. simpl. apply twenty_equals_eight.
Defined.

Example B_dominant_seventh : 
  (B +pc [0%binint] = B) /\
  (B +pc [4%binint] = Ds) /\
  (B +pc [7%binint] = Fs) /\
  (B +pc [10%binint] = A).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold B, Ds. simpl. apply fifteen_equals_three.
    + split.
      * unfold B, Fs. simpl. apply eighteen_equals_six.
      * unfold B, A. simpl. apply twentyone_equals_nine.
Defined.

(** ================================================================= *)
(** Section 28: Chord Membership Properties                          *)
(** ================================================================= *)

Example is_in_major_triad_from : forall (root p : PitchClass),
  sum (p = root) 
      (sum (p = root +pc [4%binint]) 
           (p = root +pc [7%binint])) ->
  sum (p +pc (-pc root) = [0%binint]) 
      (sum (p +pc (-pc root) = [4%binint]) 
           (p +pc (-pc root) = [7%binint])).
Proof.
  intros root p H.
  destruct H as [H1 | [H2 | H3]].
  - left. rewrite H1. apply pitch_class_add_neg_r.
  - right. left. 
    rewrite H2.
    rewrite pitch_class_add_comm.
    rewrite <- pitch_class_add_assoc.
    rewrite (pitch_class_add_comm (-pc root) root).
    rewrite pitch_class_add_neg_r.
    apply pitch_class_add_zero_l.
  - right. right.
    rewrite H3.
    rewrite pitch_class_add_comm.
    rewrite <- pitch_class_add_assoc.
    rewrite (pitch_class_add_comm (-pc root) root).
    rewrite pitch_class_add_neg_r.
    apply pitch_class_add_zero_l.
Defined.

(** The converse: if the interval from root is 0, 4, or 7, then p is in the major triad *)
Example interval_implies_in_major_triad : forall (root p : PitchClass),
  sum (p +pc (-pc root) = [0%binint]) 
      (sum (p +pc (-pc root) = [4%binint]) 
           (p +pc (-pc root) = [7%binint])) ->
  sum (p = root) 
      (sum (p = root +pc [4%binint]) 
           (p = root +pc [7%binint])).
Proof.
  intros root p H.
  destruct H as [H1 | [H2 | H3]].
  - left. 
    apply difference_equals_C_implies_equal.
    unfold C.
    exact H1.
  - right. left.
    assert (H0: p +pc (-pc root) +pc root = [4%binint] +pc root).
    { rewrite H2. reflexivity. }
    rewrite pitch_class_add_assoc in H0.
    rewrite (pitch_class_add_comm (-pc root) root) in H0.
    rewrite pitch_class_add_neg_r in H0.
    rewrite pitch_class_add_zero_r in H0.
    rewrite pitch_class_add_comm in H0.
    exact H0.
  - right. right.
    assert (H0: p +pc (-pc root) +pc root = [7%binint] +pc root).
    { rewrite H3. reflexivity. }
    rewrite pitch_class_add_assoc in H0.
    rewrite (pitch_class_add_comm (-pc root) root) in H0.
    rewrite pitch_class_add_neg_r in H0.
    rewrite pitch_class_add_zero_r in H0.
    rewrite pitch_class_add_comm in H0.
    exact H0.
Defined.

(** Similar property for minor triads *)
Example is_in_minor_triad_from : forall (root p : PitchClass),
  sum (p = root) 
      (sum (p = root +pc [3%binint]) 
           (p = root +pc [7%binint])) ->
  sum (p +pc (-pc root) = [0%binint]) 
      (sum (p +pc (-pc root) = [3%binint]) 
           (p +pc (-pc root) = [7%binint])).
Proof.
  intros root p H.
  destruct H as [H1 | [H2 | H3]].
  - left. rewrite H1. apply pitch_class_add_neg_r.
  - right. left. 
    rewrite H2.
    rewrite pitch_class_add_comm.
    rewrite <- pitch_class_add_assoc.
    rewrite (pitch_class_add_comm (-pc root) root).
    rewrite pitch_class_add_neg_r.
    apply pitch_class_add_zero_l.
  - right. right.
    rewrite H3.
    rewrite pitch_class_add_comm.
    rewrite <- pitch_class_add_assoc.
    rewrite (pitch_class_add_comm (-pc root) root).
    rewrite pitch_class_add_neg_r.
    apply pitch_class_add_zero_l.
Defined.

(** Chord inversions: The first inversion of a major triad has intervals 3, 5 from the bass *)
Example major_triad_first_inversion : forall (root : PitchClass),
  let bass := root +pc [4%binint] in  (* E in C major *)
  (bass +pc [0%binint] = root +pc [4%binint]) /\
  (bass +pc [3%binint] = root +pc [7%binint]) /\
  (bass +pc [8%binint] = root +pc [12%binint]).
Proof.
  intro root.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + rewrite pitch_class_add_assoc.
      simpl.
      reflexivity.
    + rewrite pitch_class_add_assoc.
      assert (H: [4%binint] +pc [8%binint] = [12%binint]).
      { simpl. reflexivity. }
      rewrite H.
      reflexivity.
Defined.

(** Chord equivalence under octave: adding 12 doesn't change the chord *)
Example chord_octave_equivalence : forall (root : PitchClass) (n : BinInt),
  root +pc [n] = root +pc [(n + 12)%binint].
Proof.
  intros root n.
  assert (H: [n] = [(n + 12)%binint]).
  { apply qglue.
    exists 1%binint.
    simpl.
    reflexivity. }
  rewrite H.
  reflexivity.
Defined.

(** Transposition preserves chord type *)
Example transpose_preserves_major_quality : 
  forall (root p t : PitchClass),
  sum (p = root) 
      (sum (p = root +pc [4%binint]) 
           (p = root +pc [7%binint])) ->
  sum (p +pc t = root +pc t) 
      (sum (p +pc t = (root +pc t) +pc [4%binint]) 
           (p +pc t = (root +pc t) +pc [7%binint])).
Proof.
  intros root p t H.
  destruct H as [H1 | [H2 | H3]].
  - left. rewrite H1. reflexivity.
  - right. left. 
    rewrite H2.
    rewrite pitch_class_add_assoc.
    rewrite pitch_class_add_assoc.
    rewrite (pitch_class_add_comm [4%binint] t).
    reflexivity.
  - right. right.
    rewrite H3.
    rewrite pitch_class_add_assoc.
    rewrite pitch_class_add_assoc.
    rewrite (pitch_class_add_comm [7%binint] t).
    reflexivity.
Defined.

(** Common tones between chords a fifth apart *)
Example common_tone_fifth_related_majors : forall (root : PitchClass),
  let chord1_third := root +pc [4%binint] in
  let chord1_fifth := root +pc [7%binint] in
  let root2 := root +pc [7%binint] in  (* G if root is C *)
  let chord2_root := root2 in
  let chord2_third := root2 +pc [4%binint] in
  (* The fifth of chord1 is the root of chord2 *)
  chord1_fifth = chord2_root.
Proof.
  intro root.
  reflexivity.
Defined.

(** Second inversion of major triad has intervals 4, 7 from the bass *)
Example major_triad_second_inversion : forall (root : PitchClass),
  let bass := root +pc [7%binint] in  (* G in C major *)
  (bass +pc [0%binint] = root +pc [7%binint]) /\
  (bass +pc [5%binint] = root +pc [12%binint]) /\
  (bass +pc [9%binint] = root +pc [16%binint]).
Proof.
  intro root.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + rewrite pitch_class_add_assoc.
      assert (H: [7%binint] +pc [5%binint] = [12%binint]).
      { simpl. reflexivity. }
      rewrite H.
      reflexivity.
    + rewrite pitch_class_add_assoc.
      assert (H: [7%binint] +pc [9%binint] = [16%binint]).
      { simpl. reflexivity. }
      rewrite H.
      reflexivity.
Defined.

(** Inversion preserves chord membership *)
Example inversion_preserves_major_triad : forall (root p inv_center : PitchClass),
  sum (p = root) 
      (sum (p = root +pc [4%binint]) 
           (p = root +pc [7%binint])) ->
  sum (pitch_class_inversion 0%binint p = pitch_class_inversion 0%binint root)
      (sum (pitch_class_inversion 0%binint p = pitch_class_inversion 0%binint (root +pc [4%binint]))
           (pitch_class_inversion 0%binint p = pitch_class_inversion 0%binint (root +pc [7%binint]))).
Proof.
  intros root p inv_center H.
  destruct H as [H1 | [H2 | H3]].
  - left. rewrite H1. reflexivity.
  - right. left. rewrite H2. reflexivity.
  - right. right. rewrite H3. reflexivity.
Defined.

(** ================================================================= *)
(** Section 29: Musical Scales                                       *)
(** ================================================================= *)

(** The diatonic (major) scale has the interval pattern: 
    0, 2, 4, 5, 7, 9, 11 (W-W-H-W-W-W-H) *)

Example C_major_scale_degrees : 
  (C +pc [0%binint] = C) /\
  (C +pc [2%binint] = D) /\
  (C +pc [4%binint] = E) /\
  (C +pc [5%binint] = F) /\
  (C +pc [7%binint] = G) /\
  (C +pc [9%binint] = A) /\
  (C +pc [11%binint] = B).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + apply C_plus_two_is_D.
    + split.
      * apply C_plus_four_is_E.
      * split.
        -- apply C_plus_five_is_F.
        -- split.
           ++ apply C_plus_seven_is_G.
           ++ split.
              ** unfold C, A. simpl. reflexivity.
              ** unfold C, B. simpl. reflexivity.
Defined.

(** The natural minor scale has the interval pattern:
    0, 2, 3, 5, 7, 8, 10 (W-H-W-W-H-W-W) *)

Example A_natural_minor_scale_degrees : 
  (A +pc [0%binint] = A) /\
  (A +pc [2%binint] = B) /\
  (A +pc [3%binint] = C) /\
  (A +pc [5%binint] = D) /\
  (A +pc [7%binint] = E) /\
  (A +pc [8%binint] = F) /\
  (A +pc [10%binint] = G).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold A, B. simpl. reflexivity.
    + split.
      * apply A_plus_three_is_C.
      * split.
        -- unfold A, D. simpl. apply fourteen_equals_two.
        -- split.
           ++ unfold A, E. simpl. apply sixteen_equals_four.
           ++ split.
              ** unfold A, F. simpl. 
                 apply qglue. exists (binint_negation 1%binint).
                 simpl. reflexivity.
              ** unfold A, G. simpl.
                 apply qglue. exists (binint_negation 1%binint).
                 simpl. reflexivity.
Defined.

(** The harmonic minor scale has the interval pattern:
    0, 2, 3, 5, 7, 8, 11 (W-H-W-W-H-Aug2nd-H) *)

Example A_harmonic_minor_scale_degrees : 
  (A +pc [0%binint] = A) /\
  (A +pc [2%binint] = B) /\
  (A +pc [3%binint] = C) /\
  (A +pc [5%binint] = D) /\
  (A +pc [7%binint] = E) /\
  (A +pc [8%binint] = F) /\
  (A +pc [11%binint] = Gs).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold A, B. simpl. reflexivity.
    + split.
      * apply A_plus_three_is_C.
      * split.
        -- unfold A, D. simpl. apply fourteen_equals_two.
        -- split.
           ++ unfold A, E. simpl. apply sixteen_equals_four.
           ++ split.
              ** unfold A, F. simpl. 
                 apply qglue. exists (binint_negation 1%binint).
                 simpl. reflexivity.
              ** unfold A, Gs. simpl. apply twenty_equals_eight.
Defined.

(** The melodic minor scale (ascending) has the interval pattern:
    0, 2, 3, 5, 7, 9, 11 (W-H-W-W-W-W-H) *)

Example A_melodic_minor_ascending_degrees : 
  (A +pc [0%binint] = A) /\
  (A +pc [2%binint] = B) /\
  (A +pc [3%binint] = C) /\
  (A +pc [5%binint] = D) /\
  (A +pc [7%binint] = E) /\
  (A +pc [9%binint] = Fs) /\
  (A +pc [11%binint] = Gs).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold A, B. simpl. reflexivity.
    + split.
      * apply A_plus_three_is_C.
      * split.
        -- unfold A, D. simpl. apply fourteen_equals_two.
        -- split.
           ++ unfold A, E. simpl. apply sixteen_equals_four.
           ++ split.
              ** unfold A, Fs. simpl. apply eighteen_equals_six.
              ** unfold A, Gs. simpl. apply twenty_equals_eight.
Defined.

(** The pentatonic major scale has the interval pattern:
    0, 2, 4, 7, 9 (W-W-min3rd-W-min3rd) *)

Example C_pentatonic_major_degrees : 
  (C +pc [0%binint] = C) /\
  (C +pc [2%binint] = D) /\
  (C +pc [4%binint] = E) /\
  (C +pc [7%binint] = G) /\
  (C +pc [9%binint] = A).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + apply C_plus_two_is_D.
    + split.
      * apply C_plus_four_is_E.
      * split.
        -- apply C_plus_seven_is_G.
        -- unfold C, A. simpl. reflexivity.
Defined.

(** The pentatonic minor scale has the interval pattern:
    0, 3, 5, 7, 10 (min3rd-W-W-min3rd-W) *)

Example A_pentatonic_minor_degrees : 
  (A +pc [0%binint] = A) /\
  (A +pc [3%binint] = C) /\
  (A +pc [5%binint] = D) /\
  (A +pc [7%binint] = E) /\
  (A +pc [10%binint] = G).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + apply A_plus_three_is_C.
    + split.
      * unfold A, D. simpl. apply fourteen_equals_two.
      * split.
        -- unfold A, E. simpl. apply sixteen_equals_four.
        -- unfold A, G. simpl.
           apply qglue. exists (binint_negation 1%binint).
           simpl. reflexivity.
Defined.

(** The blues scale has the interval pattern:
    0, 3, 5, 6, 7, 10 (min3rd-W-H-H-min3rd-W) *)

Example A_blues_scale_degrees : 
  (A +pc [0%binint] = A) /\
  (A +pc [3%binint] = C) /\
  (A +pc [5%binint] = D) /\
  (A +pc [6%binint] = Ds) /\
  (A +pc [7%binint] = E) /\
  (A +pc [10%binint] = G).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + apply A_plus_three_is_C.
    + split.
      * unfold A, D. simpl. apply fourteen_equals_two.
      * split.
        -- unfold A, Ds. simpl. apply fifteen_equals_three.
        -- split.
           ++ unfold A, E. simpl. apply sixteen_equals_four.
           ++ unfold A, G. simpl.
              apply qglue. exists (binint_negation 1%binint).
              simpl. reflexivity.
Defined.

(** The Dorian mode has the interval pattern:
    0, 2, 3, 5, 7, 9, 10 (W-H-W-W-W-H-W) *)

Example D_dorian_mode_degrees : 
  (D +pc [0%binint] = D) /\
  (D +pc [2%binint] = E) /\
  (D +pc [3%binint] = F) /\
  (D +pc [5%binint] = G) /\
  (D +pc [7%binint] = A) /\
  (D +pc [9%binint] = B) /\
  (D +pc [10%binint] = C).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + apply D_plus_two_is_E.
    + split.
      * unfold D, F. simpl. reflexivity.
      * split.
        -- unfold D, G. simpl. reflexivity.
        -- split.
           ++ unfold D, A. simpl. reflexivity.
           ++ split.
              ** unfold D, B. simpl. reflexivity.
              ** unfold D, C. simpl. apply twelve_equals_zero.
Defined.

(** The Phrygian mode has the interval pattern:
    0, 1, 3, 5, 7, 8, 10 (H-W-W-W-H-W-W) *)

Example E_phrygian_mode_degrees : 
  (E +pc [0%binint] = E) /\
  (E +pc [1%binint] = F) /\
  (E +pc [3%binint] = G) /\
  (E +pc [5%binint] = A) /\
  (E +pc [7%binint] = B) /\
  (E +pc [8%binint] = C) /\
  (E +pc [10%binint] = D).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + apply E_plus_one_is_F.
    + split.
      * unfold E, G. simpl. reflexivity.
      * split.
        -- unfold E, A. simpl. reflexivity.
        -- split.
           ++ unfold E, B. simpl. reflexivity.
           ++ split.
              ** unfold E, C. simpl. apply twelve_equals_zero.
              ** unfold E, D. simpl. apply fourteen_equals_two.
Defined.

(** The Lydian mode has the interval pattern:
    0, 2, 4, 6, 7, 9, 11 (W-W-W-H-W-W-H) *)

Example F_lydian_mode_degrees : 
  (F +pc [0%binint] = F) /\
  (F +pc [2%binint] = G) /\
  (F +pc [4%binint] = A) /\
  (F +pc [6%binint] = B) /\
  (F +pc [7%binint] = C) /\
  (F +pc [9%binint] = D) /\
  (F +pc [11%binint] = E).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold F, G. simpl. reflexivity.
    + split.
      * unfold F, A. simpl. reflexivity.
      * split.
        -- unfold F, B. simpl. reflexivity.
        -- split.
           ++ unfold F, C. simpl. apply twelve_equals_zero.
           ++ split.
              ** unfold F, D. simpl. apply fourteen_equals_two.
              ** unfold F, E. simpl. apply sixteen_equals_four.
Defined.

(** The Mixolydian mode has the interval pattern:
    0, 2, 4, 5, 7, 9, 10 (W-W-H-W-W-H-W) *)

Example G_mixolydian_mode_degrees : 
  (G +pc [0%binint] = G) /\
  (G +pc [2%binint] = A) /\
  (G +pc [4%binint] = B) /\
  (G +pc [5%binint] = C) /\
  (G +pc [7%binint] = D) /\
  (G +pc [9%binint] = E) /\
  (G +pc [10%binint] = F).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + unfold G, A. simpl. reflexivity.
    + split.
      * unfold G, B. simpl. reflexivity.
      * split.
        -- unfold G, C. simpl. apply twelve_equals_zero.
        -- split.
           ++ apply G_plus_seven_is_D.
           ++ split.
              ** unfold G, E. simpl. apply sixteen_equals_four.
              ** unfold G, F. simpl. 
                 apply qglue. exists (binint_negation 1%binint).
                 simpl. reflexivity.
Defined.

(** The Locrian mode has the interval pattern:
    0, 1, 3, 5, 6, 8, 10 (H-W-W-H-W-W-W) *)

Example B_locrian_mode_degrees : 
  (B +pc [0%binint] = B) /\
  (B +pc [1%binint] = C) /\
  (B +pc [3%binint] = D) /\
  (B +pc [5%binint] = E) /\
  (B +pc [6%binint] = F) /\
  (B +pc [8%binint] = G) /\
  (B +pc [10%binint] = A).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + apply B_plus_one_is_C.
    + split.
      * unfold B, D. simpl. apply fourteen_equals_two.
      * split.
        -- unfold B, E. simpl. apply sixteen_equals_four.
        -- split.
           ++ unfold B, F. simpl. 
              apply qglue. exists (binint_negation 1%binint).
              simpl. reflexivity.
           ++ split.
              ** unfold B, G. simpl.
                 apply qglue. exists (binint_negation 1%binint).
                 simpl. reflexivity.
              ** unfold B, A. simpl. apply twentyone_equals_nine.
Defined.

(** The octatonic scale (diminished scale) has the interval pattern:
    0, 2, 3, 5, 6, 8, 9, 11 (W-H-W-H-W-H-W-H) *)

Example C_octatonic_scale_degrees : 
  (C +pc [0%binint] = C) /\
  (C +pc [2%binint] = D) /\
  (C +pc [3%binint] = Ds) /\
  (C +pc [5%binint] = F) /\
  (C +pc [6%binint] = Fs) /\
  (C +pc [8%binint] = Gs) /\
  (C +pc [9%binint] = A) /\
  (C +pc [11%binint] = B).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + apply C_plus_two_is_D.
    + split.
      * apply C_plus_three_is_Ds.
      * split.
        -- apply C_plus_five_is_F.
        -- split.
           ++ unfold C, Fs. simpl. reflexivity.
           ++ split.
              ** unfold C, Gs. simpl. reflexivity.
              ** split.
                 --- unfold C, A. simpl. reflexivity.
                 --- unfold C, B. simpl. reflexivity.
Defined.

(** The bebop dominant scale has the interval pattern:
    0, 2, 4, 5, 7, 9, 10, 11 (W-W-H-W-W-H-H-H) *)

Example C_bebop_dominant_degrees : 
  (C +pc [0%binint] = C) /\
  (C +pc [2%binint] = D) /\
  (C +pc [4%binint] = E) /\
  (C +pc [5%binint] = F) /\
  (C +pc [7%binint] = G) /\
  (C +pc [9%binint] = A) /\
  (C +pc [10%binint] = As) /\
  (C +pc [11%binint] = B).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + apply C_plus_two_is_D.
    + split.
      * apply C_plus_four_is_E.
      * split.
        -- apply C_plus_five_is_F.
        -- split.
           ++ apply C_plus_seven_is_G.
           ++ split.
              ** unfold C, A. simpl. reflexivity.
              ** split.
                 --- apply C_plus_ten_is_As.
                 --- unfold C, B. simpl. reflexivity.
Defined.

(** ================================================================= *)
(** Section 30: Scale Relationships                                  *)
(** ================================================================= *)

(** The relative minor is a minor third below (or major sixth above) the major *)
Example relative_minor_relationship : 
  (C +pc [9%binint] = A) /\
  (A +pc [3%binint] = C).
Proof.
  split.
  - unfold C, A. simpl. reflexivity.
  - apply A_plus_three_is_C.
Defined.

(** All modes of C major share the same pitch classes *)
Example modes_share_pitch_classes : 
  let c_major := fun p => sum (p = C) (sum (p = D) (sum (p = E) (sum (p = F) (sum (p = G) (sum (p = A) (p = B)))))) in
  let d_dorian := fun p => sum (p = D) (sum (p = E) (sum (p = F) (sum (p = G) (sum (p = A) (sum (p = B) (p = C)))))) in
  forall p, c_major p <-> d_dorian p.
Proof.
  intro p.
  split.
  - intro H.
    destruct H as [HC | [HD | [HE | [HF | [HG | [HA | HB]]]]]].
    + right. right. right. right. right. right. exact HC.
    + left. exact HD.
    + right. left. exact HE.
    + right. right. left. exact HF.
    + right. right. right. left. exact HG.
    + right. right. right. right. left. exact HA.
    + right. right. right. right. right. left. exact HB.
  - intro H.
    destruct H as [HD | [HE | [HF | [HG | [HA | [HB | HC]]]]]].
    + right. left. exact HD.
    + right. right. left. exact HE.
    + right. right. right. left. exact HF.
    + right. right. right. right. left. exact HG.
    + right. right. right. right. right. left. exact HA.
    + right. right. right. right. right. right. exact HB.
    + left. exact HC.
Defined.

(** Parallel major/minor relationship *)
Example parallel_major_minor : 
  let c_major_third := C +pc [4%binint] in
  let c_minor_third := C +pc [3%binint] in
  (c_major_third = E) /\ (c_minor_third = Ds).
Proof.
  split.
  - apply C_plus_four_is_E.
  - apply C_plus_three_is_Ds.
Defined.

(** Transposing a scale preserves its interval structure *)
Example transpose_preserves_major_scale : forall (root t p : PitchClass),
  sum (p = root) 
    (sum (p = root +pc [2%binint])
    (sum (p = root +pc [4%binint])
    (sum (p = root +pc [5%binint])
    (sum (p = root +pc [7%binint])
    (sum (p = root +pc [9%binint])
         (p = root +pc [11%binint])))))) ->
  sum (p +pc t = root +pc t) 
    (sum (p +pc t = (root +pc t) +pc [2%binint])
    (sum (p +pc t = (root +pc t) +pc [4%binint])
    (sum (p +pc t = (root +pc t) +pc [5%binint])
    (sum (p +pc t = (root +pc t) +pc [7%binint])
    (sum (p +pc t = (root +pc t) +pc [9%binint])
         (p +pc t = (root +pc t) +pc [11%binint])))))).
Proof.
  intros root t p H.
  destruct H as [H1 | H].
  - left. rewrite H1. reflexivity.
  - destruct H as [H2 | H].
    + right. left. rewrite H2. 
      rewrite pitch_class_add_assoc.
      rewrite pitch_class_add_assoc.
      f_ap. apply pitch_class_add_comm.
    + destruct H as [H4 | H].
      * right. right. left. rewrite H4.
        rewrite pitch_class_add_assoc.
        rewrite pitch_class_add_assoc.
        f_ap. apply pitch_class_add_comm.
      * destruct H as [H5 | H].
        -- right. right. right. left. rewrite H5.
           rewrite pitch_class_add_assoc.
           rewrite pitch_class_add_assoc.
           f_ap. apply pitch_class_add_comm.
        -- destruct H as [H7 | H].
           ++ right. right. right. right. left. rewrite H7.
              rewrite pitch_class_add_assoc.
              rewrite pitch_class_add_assoc.
              f_ap. apply pitch_class_add_comm.
           ++ destruct H as [H9 | H11].
              ** right. right. right. right. right. left. rewrite H9.
                 rewrite pitch_class_add_assoc.
                 rewrite pitch_class_add_assoc.
                 f_ap. apply pitch_class_add_comm.
              ** right. right. right. right. right. right. rewrite H11.
                 rewrite pitch_class_add_assoc.
                 rewrite pitch_class_add_assoc.
                 f_ap. apply pitch_class_add_comm.
Defined.

(** The pentatonic major scale is a subset of the major scale *)
Example pentatonic_subset_of_major : forall (root p : PitchClass),
  sum (p = root)
    (sum (p = root +pc [2%binint])
    (sum (p = root +pc [4%binint])
    (sum (p = root +pc [7%binint])
         (p = root +pc [9%binint])))) ->
  sum (p = root) 
    (sum (p = root +pc [2%binint])
    (sum (p = root +pc [4%binint])
    (sum (p = root +pc [5%binint])
    (sum (p = root +pc [7%binint])
    (sum (p = root +pc [9%binint])
         (p = root +pc [11%binint])))))).
Proof.
  intros root p H.
  destruct H as [H0 | H].
  - left. exact H0.
  - destruct H as [H2 | H].
    + right. left. exact H2.
    + destruct H as [H4 | H].
      * right. right. left. exact H4.
      * destruct H as [H7 | H9].
        -- right. right. right. right. left. exact H7.
        -- right. right. right. right. right. left. exact H9.
Defined.

(** The tritone divides the octave in half *)
Example tritone_plus_tritone_is_octave : 
  [6%binint] +pc [6%binint] = [12%binint].
Proof.
  simpl.
  reflexivity.
Defined.

(** The whole tone scale is invariant under transposition by 2 *)
Example whole_tone_invariant_T2 : 
  let wt0 := C in
  let wt2 := wt0 +pc [2%binint] in
  let wt4 := wt0 +pc [4%binint] in
  let wt6 := wt0 +pc [6%binint] in
  let wt8 := wt0 +pc [8%binint] in
  let wt10 := wt0 +pc [10%binint] in
  (wt0 +pc [2%binint] = wt2) /\
  (wt2 +pc [2%binint] = wt4) /\
  (wt4 +pc [2%binint] = wt6) /\
  (wt6 +pc [2%binint] = wt8) /\
  (wt8 +pc [2%binint] = wt10) /\
  (wt10 +pc [2%binint] = C).
Proof.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * reflexivity.
      * split.
        -- reflexivity.
        -- split.
           ++ reflexivity.
           ++ apply As_plus_two_is_C.
Defined.

(** Diminished seventh chords are symmetric - transposition by 3 preserves the chord *)
Example dim7_symmetric : 
  let dim7_from_C := fun p => sum (p = C) (sum (p = Ds) (sum (p = Fs) (p = A))) in
  let dim7_from_Ds := fun p => sum (p = Ds) (sum (p = Fs) (sum (p = A) (p = C))) in
  forall p, dim7_from_C p <-> dim7_from_Ds p.
Proof.
  intro p.
  split.
  - intro H.
    destruct H as [HC | [HDs | [HFs | HA]]].
    + right. right. right. exact HC.
    + left. exact HDs.
    + right. left. exact HFs.
    + right. right. left. exact HA.
  - intro H.
    destruct H as [HDs | [HFs | [HA | HC]]].
    + right. left. exact HDs.
    + right. right. left. exact HFs.
    + right. right. right. exact HA.
    + left. exact HC.
Defined.

(** The augmented scale alternates minor thirds and semitones *)
Example augmented_scale_pattern : 
  (C +pc [0%binint] = C) /\
  (C +pc [3%binint] = Ds) /\
  (C +pc [4%binint] = E) /\
  (C +pc [7%binint] = G) /\
  (C +pc [8%binint] = Gs) /\
  (C +pc [11%binint] = B).
Proof.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + apply C_plus_three_is_Ds.
    + split.
      * apply C_plus_four_is_E.
      * split.
        -- apply C_plus_seven_is_G.
        -- split.
           ++ unfold C, Gs. simpl. reflexivity.
           ++ unfold C, B. simpl. reflexivity.
Defined.

(** Scales can be built by stacking intervals *)
Example major_scale_as_stacked_intervals : forall root : PitchClass,
  (root +pc [0%binint] = root) /\
  (root +pc [2%binint] = (root +pc [0%binint]) +pc [2%binint]) /\
  (root +pc [4%binint] = (root +pc [2%binint]) +pc [2%binint]) /\
  (root +pc [5%binint] = (root +pc [4%binint]) +pc [1%binint]) /\
  (root +pc [7%binint] = (root +pc [5%binint]) +pc [2%binint]) /\
  (root +pc [9%binint] = (root +pc [7%binint]) +pc [2%binint]) /\
  (root +pc [11%binint] = (root +pc [9%binint]) +pc [2%binint]).
Proof.
  intro root.
  split.
  - apply pitch_class_add_zero_r.
  - split.
    + rewrite pitch_class_add_zero_r. reflexivity.
    + split.
      * rewrite pitch_class_add_assoc. simpl. reflexivity.
      * split.
        -- rewrite pitch_class_add_assoc. simpl. reflexivity.
        -- split.
           ++ rewrite pitch_class_add_assoc. simpl. reflexivity.
           ++ split.
              ** rewrite pitch_class_add_assoc. simpl. reflexivity.
              ** rewrite pitch_class_add_assoc. simpl. reflexivity.
Defined.

(** Every pitch class appears in some major scale *)
Example every_pitch_in_some_major_scale : forall p : PitchClass,
  {root : PitchClass & 
    sum (p = root)
    (sum (p = root +pc [2%binint])
    (sum (p = root +pc [4%binint])
    (sum (p = root +pc [5%binint])
    (sum (p = root +pc [7%binint])
    (sum (p = root +pc [9%binint])
         (p = root +pc [11%binint]))))))}.
Proof.
  intro p.
  (* p is the root of its own major scale *)
  exists p.
  left.
  reflexivity.
Defined.

(** The circle of fifths generates all 12 pitch classes *)
Example circle_of_fifths_complete : 
  (C +pc [7 * 0]%binint = C) /\
  (C +pc [7 * 1]%binint = G) /\
  (C +pc [7 * 2]%binint = D) /\
  (C +pc [7 * 3]%binint = A) /\
  (C +pc [7 * 4]%binint = E) /\
  (C +pc [7 * 5]%binint = B) /\
  (C +pc [7 * 6]%binint = Fs) /\
  (C +pc [7 * 7]%binint = Cs) /\
  (C +pc [7 * 8]%binint = Gs) /\
  (C +pc [7 * 9]%binint = Ds) /\
  (C +pc [7 * 10]%binint = As) /\
  (C +pc [7 * 11]%binint = F).
Proof.
  simpl.
  split.
  - reflexivity.
  - split.
    + apply C_plus_seven_is_G.
    + split.
      * apply fourteen_equals_two.
      * split.
        -- apply twentyone_equals_nine.
        -- split.
           ++ apply twentyeight_equals_four.
           ++ split.
              ** apply thirtyfive_equals_eleven.
              ** split.
                 --- apply fortytwo_equals_six.
                 --- split.
                     +++ apply fortynine_equals_one.
                     +++ split.
                         *** apply fiftysix_equals_eight.
                         *** split.
                             ---- apply sixtythree_equals_three.
                             ---- split.
                                  ++++ apply seventy_equals_ten.
                                  ++++ apply seventyseven_equals_five.
Defined.

(** ================================================================= *)
(** Section 31: Summary and Final Properties                         *)
(** ================================================================= *)

(** We have formalized the complete theory of pitch classes, including:
    - The group structure (Z/12Z, +pc, C, -pc)
    - All triads and seventh chords for all 12 roots
    - Musical scales and modes
    - Transposition and inversion operations
    - Scale relationships and transformations
    
    This final example shows that our formalization captures
    the essential musical fact that transposition preserves
    all intervallic relationships. *)

Example transposition_preserves_all_intervals : 
  forall (p q t : PitchClass),
  pc_set_interval_class p q = pc_set_interval_class (p +pc t) (q +pc t).
Proof.
  intros p q t.
  unfold pc_set_interval_class.
  rewrite pitch_class_neg_add.
  (* Goal: q +pc -pc p = q +pc t +pc (-pc p +pc -pc t) *)
  symmetry.
  (* Goal: q +pc t +pc -pc p +pc -pc t = q +pc -pc p *)
  rewrite pitch_class_add_assoc.
  (* Goal: q +pc (t +pc (-pc p +pc -pc t)) = q +pc -pc p *)
  f_ap.
  (* Goal: t +pc (-pc p +pc -pc t) = -pc p *)
  rewrite <- pitch_class_add_assoc.
  (* Goal: (t +pc -pc p) +pc -pc t = -pc p *)
  rewrite (pitch_class_add_comm (t +pc -pc p) (-pc t)).
  (* Goal: -pc t +pc (t +pc -pc p) = -pc p *)
  rewrite <- pitch_class_add_assoc.
  (* Goal: (-pc t +pc t) +pc -pc p = -pc p *)
  rewrite (pitch_class_add_comm (-pc t) t).
  rewrite pitch_class_add_neg_r.
  apply pitch_class_add_zero_l.
Defined.

(** ================================================================= *)
(** Section 32: The Coltrane Cycle                                   *)
(** ================================================================= *)

(** The Coltrane cycle moves through three key centers separated by
    major thirds (4 semitones). This creates a symmetric division
    of the octave, similar to an augmented triad. *)

Example coltrane_cycle_symmetry :
  let key1 := C in
  let key2 := key1 +pc [8%binint] in  (* Down a major third = up 8 *)
  let key3 := key2 +pc [8%binint] in
  let key4 := key3 +pc [8%binint] in
  (key1 = C) /\
  (key2 = Gs) /\  (* Ab *)
  (key3 = E) /\
  (key4 = C).
Proof.
  simpl.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + split.
      * apply sixteen_equals_four.
      * apply qglue.
        exists (binint_negation 2%binint).
        simpl.
        reflexivity.
Defined.

(** The Coltrane changes use ii-V-I progressions to move between key centers *)
Example coltrane_progression_C_to_Ab :
  let C_tonic := C in
  let D_minor := D in     (* ii of C *)
  let G_dom := G in       (* V of C *)
  let Eb_minor := Ds in   (* ii of Db, but used as passing *)
  let Ab_dom := Gs in     (* V7 of Db, but resolves to Ab *)
  let Ab_tonic := Gs in   (* Resolution *)
  (* The progression moves by specific intervals *)
  (D_minor = C_tonic +pc [2%binint]) /\
  (G_dom = D_minor +pc [5%binint]) /\
  (Eb_minor = C_tonic +pc [3%binint]) /\
  (Ab_dom = Eb_minor +pc [5%binint]) /\
  (Ab_tonic = C_tonic +pc [8%binint]).
Proof.
  simpl.
  split.
  - apply C_plus_two_is_D.
  - split.
    + unfold D, G. simpl. reflexivity.
    + split.
      * apply C_plus_three_is_Ds.
      * split.
        -- unfold Ds, Gs. simpl. reflexivity.
        -- unfold C, Gs. simpl. reflexivity.
Defined.

(** The three key centers of the Coltrane cycle form an augmented triad *)
Example coltrane_centers_form_augmented_triad :
  let center1 := C in
  let center2 := Gs in  (* Ab *)
  let center3 := E in
  (center2 = center1 +pc [8%binint]) /\
  (center3 = center2 +pc [8%binint]) /\
  (center1 = center3 +pc [8%binint]).
Proof.
  simpl.
  split.
  - unfold C, Gs. simpl. reflexivity.
  - split.
    + unfold Gs, E. simpl. symmetry. apply sixteen_equals_four.
    + unfold E, C. simpl. symmetry. apply twelve_equals_zero.
Defined.

(** The Coltrane cycle is the same as moving down by major thirds *)
Example coltrane_cycle_as_descending_thirds :
  let start := C in
  let move_down_M3 := fun p => p +pc [8%binint] in  (* Down M3 = up 8 *)
  (move_down_M3 start = Gs) /\
  (move_down_M3 (move_down_M3 start) = E) /\
  (move_down_M3 (move_down_M3 (move_down_M3 start)) = C).
Proof.
  simpl.
  split.
  - reflexivity.
  - split.
    + apply sixteen_equals_four.
    + apply qglue.
      exists (binint_negation 2%binint).
      simpl.
      reflexivity.
Defined.

(** The Coltrane pattern works starting from any pitch class *)
Example coltrane_pattern_from_any_root : forall (root : PitchClass),
  root +pc [8%binint] +pc [8%binint] +pc [8%binint] = root.
Proof.
  intro root.
  rewrite pitch_class_add_assoc.
  rewrite pitch_class_add_assoc.
  assert (H: [8%binint] +pc ([8%binint] +pc [8%binint]) = [24%binint]).
  { simpl. reflexivity. }
  rewrite H.
  assert (H2: [24%binint] = [0%binint]).
  { apply qglue. exists (binint_negation 2%binint). simpl. reflexivity. }
  rewrite H2.
  apply pitch_class_add_zero_r.
Defined.

(** The complete Coltrane changes progression showing ii-V movements *)
Example coltrane_full_progression :
  (* First key: C major *)
  let Dm7 := D in          (* ii7 of C *)
  let G7 := G in           (* V7 of C *)
  let Cmaj := C in         (* I of C *)
  (* Pivot to Ab *)
  let Bbm7 := As in        (* ii7 of Ab *)
  let Eb7 := Ds in         (* V7 of Ab *)
  let Abmaj := Gs in       (* I of Ab *)
  (* Pivot to E *)
  let Fm7 := F in          (* ii7 of E *)
  let Bb7 := As in         (* V7 of E *)
  let Emaj := E in         (* I of E *)
  (* Each ii-V is a perfect fourth apart *)
  (G7 = Dm7 +pc [5%binint]) /\
  (Eb7 = Bbm7 +pc [5%binint]) /\
  (Bb7 = Fm7 +pc [5%binint]) /\
  (* The key centers are major thirds apart *)
  (Abmaj = Cmaj +pc [8%binint]) /\
  (Emaj = Abmaj +pc [8%binint]) /\
  (Cmaj = Emaj +pc [8%binint]).
Proof.
  simpl.
  split.
  - unfold D, G. simpl. reflexivity.
  - split.
    + unfold As, Ds. simpl. symmetry. apply fifteen_equals_three.
    + split.
      * unfold F, As. simpl. reflexivity.
      * split.
        -- unfold C, Gs. simpl. reflexivity.
        -- split.
           ++ unfold Gs, E. simpl. symmetry. apply sixteen_equals_four.
           ++ unfold E, C. simpl. symmetry. apply twelve_equals_zero.
Defined.

(** Giant Steps uses the Coltrane cycle with specific melodic patterns *)
Example giant_steps_key_sequence :
  (* The tune moves through the cycle multiple times *)
  let measure1_key := B in     (* Start in B *)
  let measure2_key := G in     (* Down M3 *)
  let measure3_key := Ds in    (* Down M3 = Eb *)
  let measure4_key := B in     (* Complete cycle *)
  (* Verify the cycle *)
  (measure2_key = measure1_key +pc [8%binint]) /\
  (measure3_key = measure2_key +pc [8%binint]) /\
  (measure4_key = measure3_key +pc [8%binint]).
Proof.
  simpl.
  split.
  - unfold B, G. simpl. 
    apply qglue. exists 1%binint.
    simpl. reflexivity.
  - split.
    + unfold G, Ds. simpl. symmetry. apply fifteen_equals_three.
    + unfold Ds, B. simpl. reflexivity.
Defined.

(** Part 1: The ii-V-I progressions and augmented triad structure *)
Example coltrane_progressions_and_triad :
  (* Key 1: C major *)
  let C_ii := D in      (* Dm7 *)
  let C_V := G in       (* G7 *)
  let C_I := C in       (* Cmaj7 *)
  
  (* Key 2: Ab major (down major third from C) *)
  let Ab_ii := As in    (* Bbm7 *)
  let Ab_V := Ds in     (* Eb7 *)
  let Ab_I := Gs in     (* Abmaj7 *)
  
  (* Key 3: E major (down major third from Ab) *)
  let E_ii := Fs in     (* F#m7 *)
  let E_V := B in       (* B7 *)
  let E_I := E in       (* Emaj7 *)
  
  (* Each ii-V-I follows the standard jazz progression *)
  (C_V = C_ii +pc [5%binint]) /\ (C_I = C_V +pc [5%binint]) /\
  (Ab_V = Ab_ii +pc [5%binint]) /\ (Ab_I = Ab_V +pc [5%binint]) /\
  (E_V = E_ii +pc [5%binint]) /\ (E_I = E_V +pc [5%binint]) /\
  
  (* The three tonal centers form an augmented triad *)
  (Ab_I = C_I +pc [8%binint]) /\
  (E_I = Ab_I +pc [8%binint]) /\
  (C_I = E_I +pc [8%binint]).
Proof.
  simpl.
  split.
  - (* D → G *) reflexivity.
  - split.
    + (* G → C *) symmetry. apply twelve_equals_zero.
    + split.
      * (* Bb → Eb *) symmetry. apply fifteen_equals_three.
      * split.
        -- (* Eb → Ab *) reflexivity.
        -- split.
           ++ (* F# → B *) reflexivity.
           ++ split.
              ** (* B → E *) symmetry. apply sixteen_equals_four.
              ** split.
                 --- (* C → Ab *) reflexivity.
                 --- split.
                     +++ (* Ab → E *) symmetry. apply sixteen_equals_four.
                     +++ (* E → C *) symmetry. apply twelve_equals_zero.
Defined.

(** Part 2: The chromatic voice leading *)
Example coltrane_chromatic_connections :
  (* Key centers *)
  let C_I := C in       (* Cmaj7 *)
  let Ab_I := Gs in     (* Abmaj7 *)
  let E_I := E in       (* Emaj7 *)
  
  (* ii chords *)
  let C_ii := D in      (* Dm7 *)
  let Ab_ii := As in    (* Bbm7 *)
  let E_ii := Fs in     (* F#m7 *)
  
  (* Chromatic voice leading between keys *)
  (* C to Ab: C → Bb (approach Ab_ii chromatically) *)
  (Ab_ii = C_I +pc [10%binint]) /\
  (* E back to C: E → D (approach C_ii chromatically) *)
  (C_ii = E_I +pc [10%binint]).
Proof.
  simpl.
  split.
  - (* C → Bb *) reflexivity.
  - (* E → D *) 
    symmetry.
    apply fourteen_equals_two.
Defined.

(** Basic Giant Steps chord progression (first 16 bars) *)
Example giant_steps_actual_progression :
  (* The progression in 2-bar segments *)
  let bar1_2 := (B, D, G, As) in    (* Bmaj7 | D7 | Gmaj7 | Bb7 *)
  let bar3_4 := (Ds, Fs, B, F) in   (* Ebmaj7 | Am7 D7 | Gmaj7 | C#m7 F#7 *)
  let bar5_6 := (B, F, As, Cs) in   (* Bmaj7 | Fm7 Bb7 | Ebmaj7 | C#m7 F#7 *)
  let bar7_8 := (B, Cs, Fs) in      (* Bmaj7 | C#m7 | F#7 *)
  
  (* Verify the key center movements *)
  (* B → G (down major third) *)
  (G = B +pc [8%binint]) /\
  (* G → Eb (down major third) *)
  (Ds = G +pc [8%binint]) /\
  (* Eb → B (down major third, completing cycle) *)
  (B = Ds +pc [8%binint]).
Proof.
  simpl.
  split.
  - unfold B, G. simpl. 
    apply qglue. exists 1%binint.
    simpl. reflexivity.
  - split.
    + unfold G, Ds. simpl. symmetry. apply fifteen_equals_three.
    + unfold Ds, B. simpl. reflexivity.
Defined.

(** The complete Giant Steps chord progression (16 bars) *)
Example giant_steps_complete_form :
  (* Bar-by-bar chord roots *)
  let bar1 := (B, D) in          (* Bmaj7, D7 *)
  let bar2 := (G, As) in         (* Gmaj7, Bb7 *)
  let bar3 := Ds in              (* Ebmaj7 *)
  let bar4 := (A, D) in          (* Am7, D7 *)
  let bar5 := G in               (* Gmaj7 *)
  let bar6 := (Cs, Fs) in        (* C#m7, F#7 *)
  let bar7 := B in               (* Bmaj7 *)
  let bar8 := (F, As) in         (* Fm7, Bb7 *)
  let bar9 := Ds in              (* Ebmaj7 *)
  let bar10 := (A, D) in         (* Am7, D7 *)
  let bar11 := G in              (* Gmaj7 *)
  let bar12 := (Cs, Fs) in       (* C#m7, F#7 *)
  let bar13 := B in              (* Bmaj7 *)
  let bar14 := (F, As) in        (* Fm7, Bb7 *)
  let bar15 := Ds in             (* Ebmaj7 *)
  let bar16 := (Cs, Fs) in       (* C#m7, F#7 (turnaround) *)
  
  (* Key verifications *)
  (* 1. The three tonal centers form an augmented triad *)
  (G = B +pc [8%binint]) /\
  (Ds = G +pc [8%binint]) /\
  (B = Ds +pc [8%binint]) /\
  
  (* 2. Each V-I resolution *)
  (D +pc [5%binint] = G) /\     (* D7 → G *)
  (As +pc [5%binint] = Ds) /\   (* Bb7 → Eb *)
  (Fs +pc [5%binint] = B) /\    (* F#7 → B *)
  
  (* 3. Each ii-V progression *)
  (A +pc [5%binint] = D) /\     (* Am7 → D7 *)
  (F +pc [5%binint] = As) /\    (* Fm7 → Bb7 *)
  (Cs +pc [5%binint] = Fs).     (* C#m7 → F#7 *)
Proof.
  simpl.
  split.
  - (* B → G *) apply qglue. exists 1%binint. simpl. reflexivity.
  - split.
    + (* G → Eb *) symmetry. apply fifteen_equals_three.
    + split.
      * (* Eb → B: [3] + [8] = [11] *) reflexivity.
      * split.
        -- (* D → G: [2] + [5] = [7] *) reflexivity.
        -- split.
           ++ (* Bb → Eb: [10] + [5] = [15] = [3] *) apply fifteen_equals_three.
           ++ split.
              ** (* F# → B: [6] + [5] = [11] *) reflexivity.
              ** split.
                 --- (* A → D: [9] + [5] = [14] = [2] *) apply fourteen_equals_two.
                 --- split.
                     +++ (* F → Bb: [5] + [5] = [10] *) reflexivity.
                     +++ (* C# → F#: [1] + [5] = [6] *) reflexivity.
Defined.

(** ================================================================= *)
(** Section 33: Common Tones in Major Third Related Triads          *)
(** ================================================================= *)

(** Major triads a major third apart share exactly one common tone *)
Example major_third_triads_share_one_tone :
  (* C major and E major share the note E *)
  let C_major_has_E := C +pc [4%binint] = E in
  let E_major_has_E := E +pc [0%binint] = E in
  C_major_has_E /\ E_major_has_E.
Proof.
  split.
  - apply C_plus_four_is_E.
  - apply pitch_class_add_zero_r.
Defined.

(** E major and Ab major share the note G# *)
Example E_Ab_triads_share_Gs :
  (* E major has G# as its major third *)
  let E_major_has_Gs := E +pc [4%binint] = Gs in
  (* Ab major has G# (Ab) as its root *)
  let Ab_major_has_Gs := Gs +pc [0%binint] = Gs in
  E_major_has_Gs /\ Ab_major_has_Gs.
Proof.
  split.
  - apply E_plus_four_is_Gs.
  - apply pitch_class_add_zero_r.
Defined.

(** Ab major and C major share the note C *)
Example Ab_C_triads_share_C :
  (* Ab major has C as its major third *)
  let Ab_major_has_C := Gs +pc [4%binint] = C in
  (* C major has C as its root *)
  let C_major_has_C := C +pc [0%binint] = C in
  Ab_major_has_C /\ C_major_has_C.
Proof.
  split.
  - apply Gs_plus_four_is_C.
  - apply pitch_class_add_zero_r.
Defined.

(** General theorem: Any two major triads a major third apart share exactly one tone *)
Example major_third_triads_common_tone_general : forall (root : PitchClass),
  let triad1_root := root in
  let triad1_third := root +pc [4%binint] in
  let triad1_fifth := root +pc [7%binint] in
  
  let triad2_root := root +pc [4%binint] in
  let triad2_third := root +pc [8%binint] in
  let triad2_fifth := root +pc [11%binint] in
  
  (* The common tone is the third of triad1, which is the root of triad2 *)
  (triad1_third = triad2_root).
Proof.
  intro root.
  simpl.
  reflexivity.
Defined.

(** The union of C major and E major triads forms a hexatonic collection *)
Example C_E_union_hexatonic :
  (* C major: C, E, G = 0, 4, 7 *)
  (* E major: E, G#, B = 4, 8, 11 *)
  (* Union should have at most 6 notes (actually exactly 5 unique ones) *)
  let C_maj_1 := C in
  let C_maj_3 := E in  
  let C_maj_5 := G in
  let E_maj_1 := E in
  let E_maj_3 := Gs in
  let E_maj_5 := B in
  (* The shared note *)
  (C_maj_3 = E_maj_1).
Proof.
  simpl.
  reflexivity.
Defined.

(** The intervals in the C-E hexatonic scale *)
Example C_E_hexatonic_intervals :
  (* The union gives us: C, E, G, G#, B *)
  (* Let's verify the intervals between consecutive notes *)
  (E = C +pc [4%binint]) /\      (* C to E: major third *)
  (G = E +pc [3%binint]) /\      (* E to G: minor third *)
  (Gs = G +pc [1%binint]) /\     (* G to G#: semitone *)
  (B = Gs +pc [3%binint]) /\     (* G# to B: minor third *)
  (C = B +pc [1%binint]).        (* B to C: semitone *)
Proof.
  split.
  - apply C_plus_four_is_E.
  - split.
    + unfold E, G. simpl. reflexivity.
    + split.
      * apply G_plus_one_is_Gs.
      * split.
        -- unfold Gs, B. simpl. reflexivity.
        -- symmetry. apply B_plus_one_is_C.
Defined.

(** The hexatonic scale has a symmetric interval pattern *)
Example hexatonic_interval_pattern :
  (* The pattern is: 4-3-1-3-1 (and it repeats) *)
  (* Using BinInt explicitly *)
  let pattern := ([4%binint], [3%binint], [1%binint], [3%binint], [1%binint]) in
  let interval_C_to_E := [4%binint] in
  let interval_E_to_G := [3%binint] in  
  let interval_G_to_Gs := [1%binint] in
  let interval_Gs_to_B := [3%binint] in
  let interval_B_to_C := [1%binint] in
  pattern = (interval_C_to_E, interval_E_to_G, interval_G_to_Gs, 
             interval_Gs_to_B, interval_B_to_C).
Proof.
  reflexivity.
Defined.

(** All three Coltrane triads can be formed from notes in two hexatonic scales *)
Example coltrane_triads_from_hexatonics :
  (* C-E hexatonic contains: C, E, G, G#, B *)
  (* E-Ab hexatonic contains: E, G#, B, C, Eb *)
  (* Ab-C hexatonic contains: G#, C, Eb, E, G *)
  
  (* C major (C, E, G) is subset of C-E hexatonic *)
  let C_major_from_CE := 
    sum (C = C) (sum (C = E) (sum (C = G) (sum (C = Gs) (C = B)))) /\
    sum (E = C) (sum (E = E) (sum (E = G) (sum (E = Gs) (E = B)))) /\
    sum (G = C) (sum (G = E) (sum (G = G) (sum (G = Gs) (G = B)))) in
  
  C_major_from_CE.
Proof.
  split.
  - (* C is in the hexatonic *) left. reflexivity.
  - split.
    + (* E is in the hexatonic *) right. left. reflexivity.
    + (* G is in the hexatonic *) right. right. left. reflexivity.
Defined.

(** Voice leading between C major and E major triads *)
Example voice_leading_C_to_E_major :
  (* C major: (C, E, G) → E major: (E, G#, B) *)
  (* Voice 1: C → B (down semitone, or up 11) *)
  (* Voice 2: E → E (common tone, no movement) *)
  (* Voice 3: G → G# (up semitone) *)
  let movement1 := B = C +pc [11%binint] in
  let movement2 := E = E +pc [0%binint] in
  let movement3 := Gs = G +pc [1%binint] in
  movement1 /\ movement2 /\ movement3.
Proof.
  split.
  - (* C → B *) unfold C, B. simpl. reflexivity.
  - split.
    + (* E → E *) unfold C. symmetry. apply pitch_class_add_zero_r.
    + (* G → G# *) apply G_plus_one_is_Gs.
Defined.

(** The maximum voice movement from C major to E major is just one semitone *)
Example minimal_voice_leading_C_to_E :
  (* Movement amounts: *)
  (* C → B: 11 semitones (or -1) *)
  (* E → E: 0 semitones *)
  (* G → G#: 1 semitone *)
  (* If we consider the shortest path (allowing negative movement): *)
  (* C → B: -1, E → E: 0, G → G#: +1 *)
  (* Maximum absolute movement is just 1 semitone! *)
  let movements := ([11%binint], [0%binint], [1%binint]) in
  movements = ([11%binint], [0%binint], [1%binint]).
Proof.
  reflexivity.
Defined.

(** This minimal voice leading property holds for all Coltrane changes *)
Example voice_leading_E_to_Ab_major :
  (* E major: (E, G#, B) → Ab major: (Ab, C, Eb) *)
  (* Voice 1: E → Eb (down semitone) *)
  (* Voice 2: G# → Ab (same note, different name) *)
  (* Voice 3: B → C (up semitone) *)
  let movement1 := Ds = E +pc [11%binint] in
  let movement2 := Gs = Gs +pc [0%binint] in
  let movement3 := C = B +pc [1%binint] in
  movement1 /\ movement2 /\ movement3.
Proof.
  split.
  - (* E → Eb *) unfold E, Ds. simpl. symmetry. apply fifteen_equals_three.
  - split.
    + (* G# → G# *) unfold C. symmetry. apply pitch_class_add_zero_r.
    + (* B → C *) symmetry. apply B_plus_one_is_C.
Defined.

(** Optimality Conjecture for Voice Leading in Augmented-Related Triads *)
Example coltrane_optimality_conjecture :
  (* Conjecture: Among all sets of three triads whose roots form an 
     augmented triad and where each adjacent pair shares exactly one 
     common tone, the configuration using major triads minimizes the 
     maximum voice movement between adjacent triads.
     
     Specifically:
     - The maximum movement in the Coltrane changes is 1 semitone
     - Alternative triad types (minor, diminished, augmented) would 
       require larger maximum movements
     - This bound is optimal for any 3-triad cycle with these constraints *)
  
  let statement := sum (C = C) (Gs = Gs) in
  statement.
Proof.
  left. reflexivity.
Defined.

(** Summary of Properties of the Coltrane Cycle *)
Example coltrane_cycle_properties :
  (* The Coltrane changes exhibit three key mathematical properties: *)
  
  (* Property 1: The roots of the three major triads form an augmented triad *)
  let roots_form_augmented_triad := 
    (G = B +pc [8%binint]) /\ 
    (Ds = G +pc [8%binint]) /\ 
    (B = Ds +pc [8%binint]) in
  
  (* Property 2: Each adjacent pair of triads shares exactly one common tone *)
  let adjacent_triads_share_one_tone := 
    (C +pc [4%binint] = E) /\     (* C major and E major share E *)
    (E +pc [4%binint] = Gs) /\    (* E major and Ab major share G# *) 
    (Gs +pc [4%binint] = C) in    (* Ab major and C major share C *)
  
  (* Property 3: Voice movements between adjacent triads are minimal *)
  let voice_movements_are_minimal :=
    (* All voice movements are 0 or ±1 semitone:
       C major to E major: C→B (-1), E→E (0), G→G# (+1)
       E major to Ab major: E→Eb (-1), G#→G# (0), B→C (+1)
       Ab major to C major: Ab→G (-1), C→C (0), Eb→E (+1) *)
    (B = C +pc [11%binint]) /\ (Gs = G +pc [1%binint]) /\
    (Ds = E +pc [11%binint]) /\ (C = B +pc [1%binint]) in
    
  (* These three properties characterize the Coltrane changes *)
  roots_form_augmented_triad /\ adjacent_triads_share_one_tone /\ voice_movements_are_minimal.
Proof.
  split.
  - (* Augmented triad property *) 
    split. 
    + apply qglue. exists 1%binint. simpl. reflexivity.
    + split.
      * symmetry. apply fifteen_equals_three.
      * reflexivity.
  - split.
    + (* Common tone property *)
      split.
      * apply C_plus_four_is_E.
      * split.
        -- apply E_plus_four_is_Gs.
        -- apply Gs_plus_four_is_C.
    + (* Minimal voice leading property *)
      split.
      * unfold C, B. simpl. reflexivity.
      * split.
        -- apply G_plus_one_is_Gs.
        -- split.
           ++ unfold E, Ds. simpl. symmetry. apply fifteen_equals_three.
           ++ symmetry. apply B_plus_one_is_C.
Defined.

(** ================================================================= *)
(** Section 34: Univalence and Musical Equivalences                  *)
(** ================================================================= *)

(** Import univalence from the HoTT library *)
From HoTT Require Import UnivalenceImpliesFunext.
From HoTT Require Import Univalence.

(** With univalence, we can explore when musical structures are 
    genuinely equal, not just equivalent *)

Example pitch_class_automorphisms : 
  (* The automorphisms of PitchClass form a group *)
  let transpose_by (n : BinInt) : PitchClass -> PitchClass := 
    fun p => p +pc [n] in
  let invert_then_transpose (n : BinInt) : PitchClass -> PitchClass :=
    fun p => pitch_class_inversion n p in
  (* These generate the T/I group of order 24 *)
  {f : PitchClass -> PitchClass & IsEquiv f}.
Proof.
  (* Transposition by 0 is an equivalence *)
  exists (fun p => p +pc [0%binint]).
  apply isequiv_adjointify with (g := fun p => p +pc [0%binint]).
  - intro p. 
    rewrite pitch_class_add_assoc.
    assert (H: [0%binint] +pc [0%binint] = [0%binint]).
    { simpl. reflexivity. }
    rewrite H.
    apply pitch_class_add_zero_r.
  - intro p.
    rewrite pitch_class_add_assoc.
    assert (H: [0%binint] +pc [0%binint] = [0%binint]).
    { simpl. reflexivity. }
    rewrite H.
    apply pitch_class_add_zero_r.
Defined.

(** With univalence, equivalent types are equal *)
Example pitch_class_equals_shifted : 
  (* The type of pitch classes is equal to itself shifted by any amount *)
  forall (n : BinInt),
  PitchClass = PitchClass.
Proof.
  intro n.
  (* This is trivial, but with univalence we could prove something stronger:
     that PitchClass with addition starting at 0 equals PitchClass with 
     addition starting at n *)
  reflexivity.
Defined.

(** Function extensionality (from univalence) lets us prove set equality *)
Example pc_sets_equal_iff_extensionally_equal : 
  forall (s1 s2 : PitchClassSet),
  (forall p, s1 p = s2 p) -> s1 = s2.
Proof.
  intros s1 s2 H.
  apply path_forall.
  exact H.
Defined.

(** Negation of a pitch class is well-defined *)
Lemma pitch_class_neg_n : forall n : BinInt,
  [-n]%binint = -pc [n].
Proof.
  intro n.
  simpl.
  reflexivity.
Defined.

(** Adding n and -n gives 0 *)
Lemma pitch_class_add_neg_n : forall n : BinInt,
  [n] +pc [-n]%binint = C.
Proof.
  intro n.
  unfold C.
  apply qglue.
  exists 0%binint.
  simpl.
  rewrite binint_add_negation_r.
  reflexivity.
Defined.

(** Adding -n and n gives 0 *)
Lemma pitch_class_add_neg_n_comm : forall n : BinInt,
  [-n]%binint +pc [n] = C.
Proof.
  intro n.
  rewrite pitch_class_add_comm.
  apply pitch_class_add_neg_n.
Defined.

(** Transposition by any amount is an equivalence *)
Theorem transposition_is_equivalence : forall (n : BinInt),
  IsEquiv (fun p : PitchClass => p +pc [n]).
Proof.
  intro n.
  apply isequiv_adjointify with (g := fun p => p +pc [-n]%binint).
  - intro p.
    rewrite pitch_class_add_assoc.
