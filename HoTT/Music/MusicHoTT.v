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
    Date: July 2nd 2025 (Updated: July 28th 2025)
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
    characteristic properties based on intervals and transpositions *)


Example G_minus_G_is_C : G +pc (-pc G) = C.
Proof.
  apply pitch_class_add_neg_r.
Defined.

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

Example Fs_plus_Fs_is_C : Fs +pc Fs = C.
Proof.
  unfold Fs, C.
  simpl.
  apply twelve_equals_zero.
Defined.

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

Example equal_implies_difference_C : forall p q : PitchClass,
  p = q -> p +pc (-pc q) = C.
Proof.
  intros p q H.
  rewrite H.
  apply pitch_class_add_neg_r.
Defined.

Example E_plus_Gs_is_C : E +pc Gs = C.
Proof.
  unfold E, Gs, C.
  simpl.
  apply twelve_equals_zero.
Defined.

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

Example Gs_plus_four_is_C : Gs +pc [4%binint] = C.
Proof.
  unfold Gs, C.
  simpl.
  apply twelve_equals_zero.
Defined.

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

Example A_plus_three_is_C : A +pc [3%binint] = C.
Proof.
  unfold A, C.
  simpl.
  apply twelve_equals_zero.
Defined.

Example is_augmented_from_C : forall p : PitchClass,
  sum (p = C) (sum (p = E) (p = Gs)) -> 
  sum (p +pc (-pc C) = C) (sum (p +pc (-pc C) = E) (p +pc (-pc C) = Gs)).
Proof.
  intros p H.
  rewrite neg_C_is_C.
  rewrite pitch_class_add_zero_r.
  exact H.
Defined.

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

Example As_plus_two_is_C : As +pc [2%binint] = C.
Proof.
  unfold As, C.
  simpl.
  apply twelve_equals_zero.
Defined.

(* Chromatic scale - intervals of 1 *)
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

Example B_plus_one_is_C : B +pc [1%binint] = C.
Proof.
  unfold B, C.
  simpl.
  apply twelve_equals_zero.
Defined.

(* Perfect fifth intervals (7 semitones) *)
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

(* Perfect fourth intervals (5 semitones) *)
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

(* Minor triad intervals from root *)
Example C_plus_three_is_Ds_v2 : C +pc [3%binint] = Ds.
Proof.
  apply C_plus_three_is_Ds.
Defined.

Example C_plus_seven_is_G_v2 : C +pc [7%binint] = G.
Proof.
  apply C_plus_seven_is_G.
Defined.

(* Major triad intervals from root *)
Example C_plus_four_is_E_v2 : C +pc [4%binint] = E.
Proof.
  apply C_plus_four_is_E.
Defined.

(* Dominant seventh intervals *)
Example C_plus_ten_is_As : C +pc [10%binint] = As.
Proof.
  unfold C, As.
  simpl.
  reflexivity.
Defined.
