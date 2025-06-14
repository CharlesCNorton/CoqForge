(** * Triangulated Categories in HoTT: Additive Foundations
    
    This file develops the additive category infrastructure needed for
    triangulated categories in Homotopy Type Theory. We formalize zero
    objects, biproducts, and prove that additive functors preserve
    zero morphisms.
    
    Part of a larger formalization of triangulated categories.
    
    Author: Charles Norton
    Date: June 14th 2025
    *)

(** ** Imports *)

From HoTT Require Import Basics.
From HoTT.Basics Require Import Overture PathGroupoids Contractible Equivalences.
From HoTT.Types Require Import Forall Sigma Arrow Paths Sum Prod Unit Empty.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
From HoTT.Categories Require Import InitialTerminalCategory.
From HoTT.Categories.Functor Require Import Identity Composition.
From HoTT.Spaces Require Import Int.

(** ** Zero Objects
    
    A zero object is simultaneously initial and terminal. This is the
    categorical analogue of the zero element in an abelian group.
    *)

Record ZeroObject (C : PreCategory) := {
  zero : object C;
  is_initial : forall X, Contr (morphism C zero X);
  is_terminal : forall X, Contr (morphism C X zero)
}.

(** The zero morphism between any two objects factors uniquely through
    the zero object. *)

Section ZeroMorphism.
  Context {C : PreCategory} (Z : ZeroObject C).
  
  Definition zero_morphism (X Y : object C) : morphism C X Y :=
    (@center _ (@is_initial _ Z Y) o @center _ (@is_terminal _ Z X))%morphism.
    
End ZeroMorphism.

(** ** Biproducts
    
    A biproduct is an object that is simultaneously a product and coproduct.
    This is the categorical generalization of direct sums.
    *)

(** The data of a biproduct: an object with inclusions and projections *)
Record Biproduct {C : PreCategory} (X Y : object C) := {
  biproduct_obj : object C;
  
  (** Inclusion morphisms (coproduct structure) *)
  inl : morphism C X biproduct_obj;
  inr : morphism C Y biproduct_obj;
  
  (** Projection morphisms (product structure) *)
  outl : morphism C biproduct_obj X;
  outr : morphism C biproduct_obj Y
}.

(** The axioms that make a biproduct well-behaved *)
Record IsBiproduct {C : PreCategory} {X Y : object C} 
                   (B : Biproduct X Y) (Z : ZeroObject C) := {
  (** Projection after inclusion gives identity *)
  beta_l : (@outl _ _ _ B o @inl _ _ _ B = 1)%morphism;
  beta_r : (@outr _ _ _ B o @inr _ _ _ B = 1)%morphism;
  
  (** Mixed compositions give zero morphism *)
  mixed_l : (@outl _ _ _ B o @inr _ _ _ B)%morphism = zero_morphism Z Y X;
  mixed_r : (@outr _ _ _ B o @inl _ _ _ B)%morphism = zero_morphism Z X Y
}.

(** Universal property: biproducts satisfy both product and coproduct
    universal properties *)
Record BiproductUniversal {C : PreCategory} {X Y : object C} 
                          (B : Biproduct X Y) := {
  (** Coproduct universal property *)
  coprod_universal : forall (Z : object C) 
    (f : morphism C X Z) (g : morphism C Y Z),
    Contr {h : morphism C (@biproduct_obj _ _ _ B) Z | 
           (h o @inl _ _ _ B = f)%morphism /\ 
           (h o @inr _ _ _ B = g)%morphism};
  
  (** Product universal property *)
  prod_universal : forall (Z : object C) 
    (f : morphism C Z X) (g : morphism C Z Y),
    Contr {h : morphism C Z (@biproduct_obj _ _ _ B) | 
           (@outl _ _ _ B o h = f)%morphism /\ 
           (@outr _ _ _ B o h = g)%morphism}
}.

(** ** Additive Categories
    
    An additive category has a zero object and all binary biproducts.
    *)

Record AdditiveCategory := {
  cat :> PreCategory;
  
  (** Zero object *)
  add_zero : ZeroObject cat;
  
  (** Binary biproducts exist for all pairs of objects *)
  add_biproduct : forall (X Y : object cat), Biproduct X Y;
  
  (** Biproducts satisfy the required axioms *)
  add_biproduct_props : forall (X Y : object cat), 
    IsBiproduct (add_biproduct X Y) add_zero;
  
  (** Biproducts satisfy the universal property *)
  add_biproduct_universal : forall (X Y : object cat),
    BiproductUniversal (add_biproduct X Y)
}.

(** ** Additive Functors
    
    An additive functor preserves the additive structure: zero objects
    and biproducts.
    *)

Record AdditiveFunctor (A B : AdditiveCategory) := {
  add_functor :> Functor A B;
  
  (** Preserves zero object *)
  preserves_zero : 
    object_of add_functor (@zero _ (add_zero A)) = 
    @zero _ (add_zero B);
  
  (** Preserves biproducts *)
  preserves_biproduct : forall (X Y : object A),
    object_of add_functor (@biproduct_obj _ _ _ (add_biproduct A X Y)) =
    @biproduct_obj _ _ _ (add_biproduct B (object_of add_functor X) 
                                         (object_of add_functor Y))
}.

(** ** Uniqueness Lemmas for Initial and Terminal Objects *)

(** Any two morphisms from an initial object are equal *)
Lemma initial_morphism_unique {C : PreCategory} 
  (I : object C) (X : object C)
  (H_initial : Contr (morphism C I X))
  (f g : morphism C I X) : f = g.
Proof.
  transitivity (@center _ H_initial).
  - exact (@contr _ H_initial f)^.
  - exact (@contr _ H_initial g).
Qed.

(** Any two morphisms to a terminal object are equal *)
Lemma terminal_morphism_unique {C : PreCategory} 
  (X : object C) (T : object C)
  (H_terminal : Contr (morphism C X T))
  (f g : morphism C X T) : f = g.
Proof.
  transitivity (@center _ H_terminal).
  - exact (@contr _ H_terminal f)^.
  - exact (@contr _ H_terminal g).
Qed.

(** ** Zero Morphism Properties *)

(** Any morphism factoring through zero equals the zero morphism *)
Lemma morphism_through_zero_is_zero {C : PreCategory} 
  (Z : ZeroObject C) (X Y : object C)
  (f : morphism C X (@zero _ Z))
  (g : morphism C (@zero _ Z) Y) :
  (g o f)%morphism = zero_morphism Z X Y.
Proof.
  unfold zero_morphism.
  apply ap011.
  - apply initial_morphism_unique.
    apply (@is_initial _ Z).
  - apply terminal_morphism_unique.
    apply (@is_terminal _ Z).
Qed.

(** ** Transport Lemmas
    
    These lemmas handle how morphisms behave under transport along
    equalities between objects. They are crucial for the main theorem.
    *)

(** Transport preserves composition *)
Lemma transport_compose_morphism {C : PreCategory}
  {X Y Z W : object C} (p : X = W)
  (f : morphism C X Y) (g : morphism C Y Z) :
  transport (fun U => morphism C U Z) p (g o f)%morphism =
  (g o transport (fun U => morphism C U Y) p f)%morphism.
Proof.
  destruct p; reflexivity.
Qed.

(** Transport distributes over composition in the middle *)
Lemma transport_morphism_compose_middle {C : PreCategory}
  {W X Y Z : object C} (p : W = X)
  (f : morphism C Y W) (g : morphism C Z Y) :
  (transport (fun U => morphism C Y U) p f o g)%morphism =
  transport (fun U => morphism C Z U) p (f o g)%morphism.
Proof.
  destruct p. reflexivity.
Qed.

(** Composition of transported morphisms *)
Lemma transport_compose_both_inverse {C : PreCategory}
  {W X Y Z : object C} (p : W = X)
  (f : morphism C W Z) (g : morphism C Y W) :
  (transport (fun U : object C => morphism C U Z) p f o 
   transport (fun U : object C => morphism C Y U) p g)%morphism =
  (f o g)%morphism.
Proof.
  destruct p. reflexivity.
Qed.

(** ** Transport and Contractibility
    
    These lemmas show how transport interacts with contractible types,
    particularly for initial and terminal morphisms.
    *)

(** Transported morphism from initial object is the unique one *)
Lemma transport_initial_morphism {C : PreCategory}
  (I I' X : object C) (p : I = I')
  (H_initial : Contr (morphism C I X))
  (H_initial' : Contr (morphism C I' X))
  (f : morphism C I X) :
  transport (fun U => morphism C U X) p f = 
  @center _ H_initial'.
Proof.
  apply (@contr _ H_initial' (transport (fun U => morphism C U X) p f))^.
Qed.

(** Transported morphism to terminal object is the unique one *)
Lemma transport_terminal_morphism {C : PreCategory}
  (X T T' : object C) (p : T = T')
  (H_terminal : Contr (morphism C X T))
  (H_terminal' : Contr (morphism C X T'))
  (f : morphism C X T) :
  transport (fun U => morphism C X U) p f = 
  @center _ H_terminal'.
Proof.
  apply (@contr _ H_terminal' (transport (fun U => morphism C X U) p f))^.
Qed.

(** ** General Transport Lemmas
    
    These may be useful for future developments.
    *)

(** Transport along inverse path *)
Lemma transport_inverse_is_inverse {A : Type} {B : A -> Type}
  {x y : A} (p : x = y) (b : B x) :
  transport B p^ (transport B p b) = b.
Proof.
  destruct p. reflexivity.
Qed.

(** Relating transport and its inverse *)
Lemma transport_inverse_eq {A : Type} {P : A -> Type} 
  {x y : A} (p : x = y) (u : P x) (v : P y) :
  transport P p u = v -> u = transport P p^ v.
Proof.
  intro H.
  rewrite <- H.
  destruct p.
  reflexivity.
Qed.

(** Transport along inverse path (reflexivity form) *)
Lemma transport_path_inverse {A : Type} {P : A -> Type}
  {x y : A} (p : x = y) (u : P y) :
  transport P p^ u = transport P p^ u.
Proof.
  reflexivity.
Qed.

(** Morphism equality via transport *)
Lemma morphism_eq_transport_inverse {C : PreCategory}
  {W X Y : object C} (p : W = X)
  (f : morphism C W Y) (g : morphism C X Y) :
  transport (fun Z => morphism C Z Y) p f = g ->
  f = transport (fun Z => morphism C Z Y) p^ g.
Proof.
  intro H.
  rewrite <- H.
  destruct p.
  reflexivity.
Qed.

(** ** Preservation of Initial and Terminal Morphisms
    
    Key lemmas showing that additive functors preserve the uniqueness
    of morphisms to/from zero objects.
    *)

(** Additive functors preserve initial morphisms *)
Lemma functor_preserves_initial_morphism 
  {A B : AdditiveCategory} (F : AdditiveFunctor A B) 
  (Y : object A) :
  transport (fun Z => morphism B Z (object_of F Y)) 
            (preserves_zero A B F)
            (morphism_of F (@center _ (@is_initial _ (add_zero A) Y))) =
  @center _ (@is_initial _ (add_zero B) (object_of F Y)).
Proof.
  apply (@path_contr _ (@is_initial _ (add_zero B) (object_of F Y))).
Qed.

(** Additive functors preserve terminal morphisms *)
Lemma functor_preserves_terminal_morphism 
  {A B : AdditiveCategory} (F : AdditiveFunctor A B) 
  (X : object A) :
  transport (fun Z => morphism B (object_of F X) Z) 
            (preserves_zero A B F)
            (morphism_of F (@center _ (@is_terminal _ (add_zero A) X))) =
  @center _ (@is_terminal _ (add_zero B) (object_of F X)).
Proof.
  apply (@path_contr _ (@is_terminal _ (add_zero B) (object_of F X))).
Qed.

(** ** Main Theorem: Additive Functors Preserve Zero Morphisms
    
    This theorem shows that any functor preserving the additive structure
    automatically preserves zero morphisms.
    *)

Theorem additive_functor_preserves_zero_morphisms 
  {A B : AdditiveCategory} (F : AdditiveFunctor A B) 
  (X Y : object A) :
  morphism_of F (zero_morphism (add_zero A) X Y) = 
  zero_morphism (add_zero B) (object_of F X) (object_of F Y).
Proof.
  unfold zero_morphism.
  rewrite composition_of.
  
  set (p := preserves_zero A B F).
  
  assert (H1: morphism_of F (@center _ (@is_terminal _ (add_zero A) X)) =
              transport (fun Z => morphism B (object_of F X) Z) p^
                       (@center _ (@is_terminal _ (add_zero B) (object_of F X)))).
  {
    apply transport_inverse_eq.
    apply functor_preserves_terminal_morphism.
  }
  
  assert (H2: morphism_of F (@center _ (@is_initial _ (add_zero A) Y)) =
              transport (fun Z => morphism B Z (object_of F Y)) p^
                       (@center _ (@is_initial _ (add_zero B) (object_of F Y)))).
  {
    apply morphism_eq_transport_inverse.
    apply functor_preserves_initial_morphism.
  }
  
  rewrite H1, H2.
  
  (** The composition of transported morphisms simplifies *)
  rewrite <- (transport_compose_both_inverse p^).
  
  reflexivity.
Qed.

(** ** Summary
    
    We have established:
    1. A formalization of additive categories with zero objects and biproducts
    2. The notion of additive functors that preserve this structure
    3. A constructive proof that additive functors preserve zero morphisms
    
    This provides a foundation for further developments in homological
    algebra and triangulated categories within HoTT.
    
    Next steps:
    - Define pre-stable categories using additive functors
    - Construct mapping cones
    - Develop the theory of triangulated categories
    - Provide concrete examples (e.g., chain complexes)
    *)
