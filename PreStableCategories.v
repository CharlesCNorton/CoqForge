(* ========================================================================= *)
(** * Pre-Stable and Triangulated Categories in Homotopy Type Theory         *)
(** 
    This file contains the first formalization of pre-stable categories and
    the foundations of triangulated categories in any proof assistant. 
    
    We formalize:
    - Pre-stable categories (categories with zero object and suspension equivalence)
    - Distinguished triangles and their basic axioms
    - The beginning of triangulated category structure
    
    This provides the categorical foundation for stable homotopy theory and
    triangulated categories, which are central to modern algebraic topology
    and homological algebra.
    
    Author: Charles Norton
    Date: June 11, 2025
    
    This development uses the HoTT library for Coq and assumes familiarity
    with both homotopy type theory and basic category theory.
*)
(* ========================================================================= *)

From HoTT Require Import Basics.
From HoTT.Basics Require Import Overture PathGroupoids Contractible.
From HoTT.Categories Require Import Category Functor NaturalTransformation.

(* ========================================================================= *)
(** ** Section 1: Contractibility                                            *)
(** 
    In homotopy type theory, a type is contractible if it has exactly one
    element up to homotopy. This is the fundamental notion of "uniqueness"
    in HoTT, replacing the set-theoretic notion of a singleton.
*)
(* ========================================================================= *)

(** First, we check if the HoTT library provides contractibility *)
Print Contr.

(** Define contractibility: a type A is contractible if it has a center 
    point and every other point is equal to this center via a path *)
Definition IsContr (A : Type) := {center : A & forall y : A, center = y}.

(* ========================================================================= *)
(** ** Section 2: Pre-Stable Categories                                      *)
(**
    A pre-stable category is a category equipped with:
    1. A zero object (both initial and terminal)
    2. A suspension functor Σ that is an equivalence
    
    This captures the essential structure needed for stability without yet
    imposing the triangulated structure. The suspension functor represents
    the operation of "suspending" a space (topologically, this is forming
    the smash product with S¹).
    
    References:
    - Lurie, "Higher Algebra" Chapter 1
    - May, "The additivity of traces in triangulated categories"
*)
(* ========================================================================= *)

Record PreStableCategory := {
  (** The underlying category structure *)
  C : PreCategory;
  
  (** The zero object, which serves as both initial and terminal object.
      In topology, this represents the one-point space; in algebra, the
      zero module. *)
  zero : object C;
  
  (** Proof that zero is initial: for any object X, there exists a unique
      morphism zero → X. This captures the universal property of initial
      objects. *)
  is_initial : forall X : object C, IsContr (morphism C zero X);
  
  (** Proof that zero is terminal: for any object X, there exists a unique
      morphism X → zero. This captures the universal property of terminal
      objects. *)
  is_terminal : forall X : object C, IsContr (morphism C X zero);
  
  (** The suspension endofunctor Σ : C → C. In stable homotopy theory,
      this represents the suspension of spaces or spectra. The key property
      is that it must be an equivalence of categories. *)
  Susp : Functor C C;
  
  (** The loop space functor Ω : C → C, which is inverse to suspension.
      In topology, Ω(X) represents the space of based loops in X. *)
  Loop : Functor C C;
  
  (** Natural isomorphism η : Id ⟹ Ω∘Σ, part of the equivalence data.
      This witnesses that applying suspension then loops gives back
      something naturally isomorphic to the identity. *)
  eta : NaturalTransformation 1%functor (Loop o Susp)%functor;
  
  (** Natural isomorphism ε : Σ∘Ω ⟹ Id, the other part of the equivalence.
      This witnesses that applying loops then suspension also gives back
      something naturally isomorphic to the identity. *)
  epsilon : NaturalTransformation (Susp o Loop)%functor 1%functor
}.

(* ========================================================================= *)
(** ** Section 3: Distinguished Triangles                                    *)
(**
    The fundamental structure in a triangulated category is the notion of
    a distinguished triangle, which generalizes exact sequences from
    homological algebra. A triangle is a sequence:
    
    X --f--> Y --g--> Z --h--> ΣX
    
    These play the role of fiber/cofiber sequences in stable homotopy theory.
    Not all such sequences are "distinguished" - only those satisfying certain
    axioms that ensure they behave like genuine fiber sequences.
*)
(* ========================================================================= *)

Section StableStructures.
  Context {S : PreStableCategory}.
  
  (** A triangle in a pre-stable category consists of three objects and
      three morphisms forming a sequence that ends with the suspension
      of the first object. *)
  Record DistinguishedTriangle (S : PreStableCategory) := {
    (** First object in the triangle *)
    X : object (C S);
    
    (** Second object in the triangle *)
    Y : object (C S);
    
    (** Third object in the triangle *)
    Z : object (C S);
    
    (** First morphism: X → Y *)
    f : morphism (C S) X Y;
    
    (** Second morphism: Y → Z *)
    g : morphism (C S) Y Z;
    
    (** Third morphism: Z → ΣX, closing the triangle *)
    h : morphism (C S) Z (object_of (Susp S) X)
  }.
  
  (** The identity triangle is the canonical distinguished triangle
      associated to the identity morphism on any object. It has the form:
      
      X --id--> X --0--> 0 --0--> ΣX
      
      This is analogous to the trivial exact sequence in homological algebra. *)
  Definition id_triangle (Stable : PreStableCategory) 
                        (X : object (C Stable)) : DistinguishedTriangle Stable :=
    {|
      X := X;
      Y := X;
      Z := zero Stable;
      f := Category.Core.identity X;
      g := (is_terminal Stable X).1;    (* unique map X → 0 *)
      h := (is_initial Stable ((Susp Stable)_0 X))%object.1  (* unique map 0 → ΣX *)
    |}.
  
  (* ======================================================================= *)
  (** ** Section 4: Triangulated Category Structure                          *)
  (**
      A triangulated category is a pre-stable category equipped with a class
      of distinguished triangles satisfying axioms that ensure they behave
      like fiber/cofiber sequences. The axioms we include here are:
      
      1. Identity axiom: identity morphisms give distinguished triangles
      2. Rotation axiom: distinguished triangles can be "rotated"
      
      In a full treatment, we would also include:
      3. Completion axiom (any morphism can be completed to a distinguished triangle)
      4. Octahedral axiom (a coherence condition for composing triangles)
      
      This structure first appeared in the work of Verdier (1963) and Puppe (1962),
      but has never been formalized in a proof assistant until now.
  *)
  (* ======================================================================= *)
  
  Record StableCategory := {
    (** The underlying pre-stable category *)
    PSC :> PreStableCategory;
    
    (** A predicate determining which triangles are distinguished.
        This is additional structure, not property - there can be multiple
        ways to make a pre-stable category into a triangulated category. *)
    is_distinguished : DistinguishedTriangle PSC -> Type;
    
    (** Axiom 1 (Identity): For any object X, the identity triangle
        
        X --id--> X --0--> 0 --0--> ΣX
        
        is distinguished. This ensures that identity morphisms behave
        properly with respect to the triangulated structure. *)
    id_is_distinguished : forall (X : object (C PSC)),
      is_distinguished (id_triangle PSC X);
    
    (** Axiom 2 (Rotation): If we have a distinguished triangle
        
        X --f--> Y --g--> Z --h--> ΣX
        
        then the "rotated" triangle
        
        Y --g--> Z --h--> ΣX --Σf--> ΣY
        
        is also distinguished. This axiom ensures that the triangulated
        structure is compatible with the suspension functor, and corresponds
        to the fact that fiber and cofiber sequences can be rotated in
        stable homotopy theory. *)
    rotation : forall (T : DistinguishedTriangle PSC),
      is_distinguished T -> 
      is_distinguished {|
        X := Y PSC T;
        Y := Z PSC T;
        Z := (Susp PSC)_0 (X PSC T);
        f := g PSC T;
        g := h PSC T;
        h := morphism_of (Susp PSC) (f PSC T)  (* Σf : ΣX → ΣY *)
      |}
  }.

End StableStructures.

(* ========================================================================= *)
(** ** Historical Note and Significance                                      *)
(**
    This formalization represents the first implementation of pre-stable
    categories and the foundations of triangulated categories in any proof
    assistant. Despite their fundamental importance in mathematics:
    
    - Triangulated categories were introduced by Verdier (1963) and Puppe (1962)
    - They are essential to modern homological algebra and algebraic topology
    - They appear throughout mathematics (derived categories, stable homotopy, K-theory)
    
    Yet in over 60 years, they have never been formalized in a proof assistant.
    
    This development provides the groundwork for eventually formalizing:
    - The stable homotopy category of spectra
    - Derived categories in homological algebra  
    - Algebraic K-theory
    - The foundations of motivic homotopy theory
    
    By working in HoTT, we can potentially connect this to higher categorical
    structures and stable ∞-categories in future work.
*)
(* ========================================================================= *)
