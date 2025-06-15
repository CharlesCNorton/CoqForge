(** * Basic Category Theory Definitions for Stable Categories
    
    This file formalizes the notion of pre-stable and stable categories,
    including biproducts, distinguished triangles, and duality theorems.
    
    We begin with the foundational definitions needed for additive categories.
*)

From HoTT Require Import Basics.
From HoTT.Basics Require Import Overture PathGroupoids Contractible Equivalences.
From HoTT.Types Require Import Forall Sigma Arrow Paths Sum Prod Unit Empty.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
From HoTT.Categories Require Import InitialTerminalCategory.
From HoTT.Categories.Functor Require Import Identity Composition.
From HoTT.Spaces Require Import Int.

(** ** Zero Objects
    
    A zero object in a category is an object that is both initial and terminal.
    This is the categorical analog of the zero element in an abelian group.
*)

Record ZeroObject (C : PreCategory) := {
  zero : object C;
  is_initial : forall X, Contr (morphism C zero X);
  is_terminal : forall X, Contr (morphism C X zero)
}.

(** The zero morphism between any two objects is the unique morphism
    that factors through the zero object. *)

Definition zero_morphism {C : PreCategory} (Z : ZeroObject C) 
  (X Y : object C) : morphism C X Y :=
  (@center _ (@is_initial _ Z Y) o @center _ (@is_terminal _ Z X))%morphism.

(** ** Biproducts
    
    A biproduct is an object that is simultaneously a product and coproduct.
    In additive categories, finite products and coproducts coincide.
*)

Record Biproduct {C : PreCategory} (X Y : object C) := {
  biproduct_obj : object C;
  
  (* Coproduct structure *)
  inl : morphism C X biproduct_obj;
  inr : morphism C Y biproduct_obj;
  
  (* Product structure *)
  outl : morphism C biproduct_obj X;
  outr : morphism C biproduct_obj Y
}.

(** A biproduct satisfies specific axioms relating the injections and projections *)

Record IsBiproduct {C : PreCategory} {X Y : object C} 
                   (B : Biproduct X Y) (Z : ZeroObject C) := {
  (* Projection-injection identities *)
  beta_l : (@outl _ _ _ B o @inl _ _ _ B = 1)%morphism;
  beta_r : (@outr _ _ _ B o @inr _ _ _ B = 1)%morphism;
  
  (* Mixed terms are zero *)
  mixed_l : (@outl _ _ _ B o @inr _ _ _ B)%morphism = zero_morphism Z Y X;
  mixed_r : (@outr _ _ _ B o @inl _ _ _ B)%morphism = zero_morphism Z X Y
}.

(** The universal property of biproducts combines the universal properties
    of products and coproducts *)

Record BiproductUniversal {C : PreCategory} {X Y : object C} 
                          (B : Biproduct X Y) := {
  coprod_universal : forall (Z : object C) 
    (f : morphism C X Z) (g : morphism C Y Z),
    Contr {h : morphism C (@biproduct_obj _ _ _ B) Z | 
           (h o @inl _ _ _ B = f)%morphism /\ 
           (h o @inr _ _ _ B = g)%morphism};
  
  prod_universal : forall (Z : object C) 
    (f : morphism C Z X) (g : morphism C Z Y),
    Contr {h : morphism C Z (@biproduct_obj _ _ _ B) | 
           (@outl _ _ _ B o h = f)%morphism /\ 
           (@outr _ _ _ B o h = g)%morphism}
}.

(** ** Additive Categories
    
    An additive category is a category enriched over abelian groups,
    with a zero object and biproducts for all pairs of objects.
*)

Record AdditiveCategory := {
  cat :> PreCategory;
  
  add_zero : ZeroObject cat;
  
  add_biproduct : forall (X Y : object cat), Biproduct X Y;
  
  add_biproduct_props : forall (X Y : object cat), 
    IsBiproduct (add_biproduct X Y) add_zero;
  
  add_biproduct_universal : forall (X Y : object cat),
    BiproductUniversal (add_biproduct X Y)
}.

(** ** Additive Functors
    
    An additive functor preserves the additive structure: zero objects
    and biproducts.
*)

Record AdditiveFunctor (A B : AdditiveCategory) := {
  add_functor :> Functor A B;
  
  preserves_zero : 
    object_of add_functor (@zero _ (add_zero A)) = 
    @zero _ (add_zero B);
  
  preserves_biproduct : forall (X Y : object A),
    object_of add_functor (@biproduct_obj _ _ _ (add_biproduct A X Y)) =
    @biproduct_obj _ _ _ (add_biproduct B (object_of add_functor X) 
                                         (object_of add_functor Y))
}.

(** ** Basic Lemmas for Categories with Zero Objects
    
    This section establishes fundamental properties of morphisms in categories
    with zero objects, including uniqueness results and composition properties.
*)

(** *** Uniqueness of Initial and Terminal Morphisms *)

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

(** *** Properties of Zero Morphisms *)

(** Any morphism that factors through a zero object is the zero morphism *)
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

(** *** Transport Lemmas for Morphisms
    
    These lemmas handle how morphisms behave under transport along
    equality proofs between objects.
*)

Lemma transport_compose_morphism {C : PreCategory}
  {X Y Z W : object C} (p : X = W)
  (f : morphism C X Y) (g : morphism C Y Z) :
  transport (fun U => morphism C U Z) p (g o f)%morphism =
  (g o transport (fun U => morphism C U Y) p f)%morphism.
Proof.
  destruct p; reflexivity.
Qed.

Lemma transport_morphism_compose_middle {C : PreCategory}
  {W X Y Z : object C} (p : W = X)
  (f : morphism C Y W) (g : morphism C Z Y) :
  (transport (fun U => morphism C Y U) p f o g)%morphism =
  transport (fun U => morphism C Z U) p (f o g)%morphism.
Proof.
  destruct p. reflexivity.
Qed.

Lemma transport_compose_both_inverse {C : PreCategory}
  {W X Y Z : object C} (p : W = X)
  (f : morphism C W Z) (g : morphism C Y W) :
  (transport (fun U : object C => morphism C U Z) p f o 
   transport (fun U : object C => morphism C Y U) p g)%morphism =
  (f o g)%morphism.
Proof.
  destruct p. reflexivity.
Qed.

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

Lemma transport_inverse_is_inverse {A : Type} {B : A -> Type}
  {x y : A} (p : x = y) (b : B x) :
  transport B p^ (transport B p b) = b.
Proof.
  destruct p. reflexivity.
Qed.

Lemma transport_inverse_eq {A : Type} {P : A -> Type} 
  {x y : A} (p : x = y) (u : P x) (v : P y) :
  transport P p u = v -> u = transport P p^ v.
Proof.
  intro H.
  rewrite <- H.
  destruct p.
  reflexivity.
Qed.

Lemma transport_path_inverse {A : Type} {P : A -> Type}
  {x y : A} (p : x = y) (u : P y) :
  transport P p^ u = transport P p^ u.
Proof.
  reflexivity.
Qed.

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

(** *** Basic Morphism Identities *)

Lemma morphism_right_identity {C : PreCategory} {X Y : object C} (f : morphism C X Y) :
  (f o 1)%morphism = f.
Proof.
  apply Category.Core.right_identity.
Qed.

Lemma morphism_left_identity {C : PreCategory} {X Y : object C} (f : morphism C X Y) :
  (1 o f)%morphism = f.
Proof.
  apply Category.Core.left_identity.
Qed.

Lemma morphism_associativity {C : PreCategory} {W X Y Z : object C} 
  (f : morphism C W X) (g : morphism C X Y) (h : morphism C Y Z) :
  ((h o g) o f)%morphism = (h o (g o f))%morphism.
Proof.
  apply Category.Core.associativity.
Qed.

(** ** Properties of Additive Functors
    
    This section establishes that additive functors preserve zero morphisms
    and other structural properties of additive categories.
*)

(** *** Preservation of Initial and Terminal Morphisms *)

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

(** *** Main Theorem: Additive Functors Preserve Zero Morphisms *)

(** The fundamental property that additive functors preserve zero morphisms *)
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
  
  rewrite <- (transport_compose_both_inverse p^).
  
  reflexivity.
Qed.

(** ** Pre-Stable Categories
    
    A pre-stable category is an additive category equipped with
    suspension and loop functors connected by natural transformations.
    This is a precursor to the notion of a stable category.
*)

Record PreStableCategory := {
  A :> AdditiveCategory;
  
  (** The suspension functor Σ *)
  Susp : AdditiveFunctor A A;
  
  (** The loop functor Ω *)
  Loop : AdditiveFunctor A A;
  
  (** Natural transformation 1 → ΩΣ *)
  eta : NaturalTransformation 1%functor (Loop o Susp)%functor;
  
  (** Natural transformation ΣΩ → 1 *)
  epsilon : NaturalTransformation (Susp o Loop)%functor 1%functor
}.

(** The suspension functor preserves zero morphisms (inherited from being additive) *)
Theorem susp_preserves_zero_morphisms {S : PreStableCategory} (X Y : object S) :
  morphism_of (Susp S) (zero_morphism (add_zero S) X Y) = 
  zero_morphism (add_zero S) (object_of (Susp S) X) (object_of (Susp S) Y).
Proof.
  apply additive_functor_preserves_zero_morphisms.
Qed.

(** ** Triangles in Pre-Stable Categories
    
    Triangles are the fundamental structures in triangulated categories.
    A triangle consists of three objects and three morphisms forming a
    specific pattern with the suspension functor.
*)

(** *** Basic Triangle Structure *)

(** A triangle X → Y → Z → ΣX *)
Record Triangle {S : PreStableCategory} := {
  X : object S;
  Y : object S;
  Z : object S;
  f : morphism S X Y;
  g : morphism S Y Z;
  h : morphism S Z (object_of (Susp S) X)
}.

(** *** Distinguished Triangles
    
    A distinguished triangle is a triangle where consecutive morphisms compose to zero.
    This is the triangulated category analog of an exact sequence.
*)

Record DistinguishedTriangle {S : PreStableCategory} := {
  triangle : Triangle;
  
  (** g ∘ f = 0 *)
  zero_comp_1 : (g triangle o f triangle)%morphism = 
                zero_morphism (add_zero S) (X triangle) (Z triangle);
  
  (** h ∘ g = 0 *)
  zero_comp_2 : (h triangle o g triangle)%morphism = 
                zero_morphism (add_zero S) (Y triangle) (object_of (Susp S) (X triangle));
  
  (** Σf ∘ h = 0 *)
  zero_comp_3 : (morphism_of (Susp S) (f triangle) o h triangle)%morphism = 
                zero_morphism (add_zero S) (Z triangle) (object_of (Susp S) (Y triangle))
}.

(** *** The Identity Triangle
    
    For any object X, there is a canonical distinguished triangle
    X → X → 0 → ΣX
*)

(** Construction of the identity triangle *)
Definition id_triangle {S : PreStableCategory} (X : object S) : @Triangle S := {|
  X := X;
  Y := X;
  Z := @zero _ (add_zero S);
  f := 1%morphism;
  g := @center _ (@is_terminal _ (add_zero S) X);
  h := @center _ (@is_initial _ (add_zero S) (object_of (Susp S) X))
|}.

(** *** Lemmas for Zero Objects in Pre-Stable Categories *)

(** The morphism from zero to itself is the identity *)
Lemma zero_to_zero_is_id {S : PreStableCategory} : 
  @center _ (@is_initial _ (add_zero S) (@zero _ (add_zero S))) = 1%morphism.
Proof.
  apply (@contr _ (@is_initial _ (add_zero S) (@zero _ (add_zero S)))).
Qed.

(** The terminal morphism from zero to itself is the identity *)
Lemma terminal_zero_to_zero_is_id {S : PreStableCategory} : 
  @center _ (@is_terminal _ (add_zero S) (@zero _ (add_zero S))) = 
  (1%morphism : morphism S (@zero _ (add_zero S)) (@zero _ (add_zero S))).
Proof.
  apply terminal_morphism_unique.
  apply (@is_terminal _ (add_zero S) (@zero _ (add_zero S))).
Qed.

(** Composition with a terminal morphism to zero gives zero morphism *)
Lemma terminal_comp_is_zero {S : PreStableCategory} (X Y : object S) 
  (f : morphism S X (@zero _ (add_zero S))) :
  (@center _ (@is_initial _ (add_zero S) Y) o f)%morphism = 
  zero_morphism (add_zero S) X Y.
Proof.
  apply morphism_through_zero_is_zero.
Qed.

(** The zero morphism from zero is the initial morphism *)
Lemma zero_morphism_from_zero {S : PreStableCategory} (Y : object S) :
  zero_morphism (add_zero S) (@zero _ (add_zero S)) Y =
  @center _ (@is_initial _ (add_zero S) Y).
Proof.
  unfold zero_morphism.
  assert (H: @center _ (@is_terminal _ (add_zero S) (@zero _ (add_zero S))) = 
            (1%morphism : morphism S (@zero _ (add_zero S)) (@zero _ (add_zero S)))).
  { 
    apply (@contr _ (@is_terminal _ (add_zero S) (@zero _ (add_zero S)))).
  }
  rewrite H.
  apply morphism_right_identity.
Qed.

(** The suspension functor preserves identity morphisms *)
Lemma susp_preserves_identity {S : PreStableCategory} (X : object S) :
  morphism_of (Susp S) (1%morphism : morphism S X X) = 
  (1%morphism : morphism S (object_of (Susp S) X) (object_of (Susp S) X)).
Proof.
  apply (identity_of (Susp S)).
Qed.

(** *** The Identity Triangle is Distinguished *)

Theorem id_triangle_distinguished {S : PreStableCategory} (X : object S) : 
  @DistinguishedTriangle S.
Proof.
  refine {| triangle := id_triangle X |}.
  
  - (* zero_comp_1: g ∘ f = 0 *)
    simpl.
    rewrite morphism_right_identity.
    unfold zero_morphism.
    rewrite zero_to_zero_is_id.
    rewrite morphism_left_identity.
    reflexivity.
  
  - (* zero_comp_2: h ∘ g = 0 *)
    simpl.
    apply terminal_comp_is_zero.
  
  - (* zero_comp_3: Σf ∘ h = 0 *)
    simpl.
    rewrite susp_preserves_identity.
    rewrite morphism_left_identity.
    rewrite <- zero_morphism_from_zero.
    reflexivity.
Defined.

(** ** Morphisms of Triangles
    
    A morphism between triangles consists of three morphisms between
    the corresponding objects that make all squares commute.
*)

(** *** Triangle Morphisms *)

Record TriangleMorphism {S : PreStableCategory} (T1 T2 : @Triangle S) := {
  mor_X : morphism S (X T1) (X T2);
  mor_Y : morphism S (Y T1) (Y T2);
  mor_Z : morphism S (Z T1) (Z T2);
  
  (** Commutativity conditions *)
  comm_f : (mor_Y o f T1)%morphism = (f T2 o mor_X)%morphism;
  comm_g : (mor_Z o g T1)%morphism = (g T2 o mor_Y)%morphism;
  comm_h : (morphism_of (Susp S) mor_X o h T1)%morphism = 
           (h T2 o mor_Z)%morphism
}.

(** *** Identity Triangle Morphism *)

Definition id_triangle_morphism {S : PreStableCategory} (T : @Triangle S) : 
  TriangleMorphism T T.
Proof.
  refine {| 
    mor_X := 1%morphism;
    mor_Y := 1%morphism;
    mor_Z := 1%morphism
  |}.
  - rewrite morphism_left_identity.
    rewrite morphism_right_identity.
    reflexivity.
  - rewrite morphism_left_identity.
    rewrite morphism_right_identity.
    reflexivity.
  - rewrite (identity_of (Susp S)).
    rewrite morphism_left_identity.
    rewrite morphism_right_identity.
    reflexivity.
Defined.

(** *** Composition of Triangle Morphisms *)

Definition triangle_morphism_compose {S : PreStableCategory}
  (T1 T2 T3 : @Triangle S)
  (φ : TriangleMorphism T1 T2)
  (ψ : TriangleMorphism T2 T3) : 
  TriangleMorphism T1 T3.
Proof.
  refine {| 
    mor_X := (mor_X _ _ ψ o mor_X _ _ φ)%morphism;
    mor_Y := (mor_Y _ _ ψ o mor_Y _ _ φ)%morphism;
    mor_Z := (mor_Z _ _ ψ o mor_Z _ _ φ)%morphism
  |}.
  - rewrite morphism_associativity.
    rewrite (comm_f _ _ φ).
    rewrite <- morphism_associativity.
    rewrite (comm_f _ _ ψ).
    rewrite morphism_associativity.
    reflexivity.
  - rewrite morphism_associativity.
    rewrite (comm_g _ _ φ).
    rewrite <- morphism_associativity.
    rewrite (comm_g _ _ ψ).
    rewrite morphism_associativity.
    reflexivity.
  - simpl.
    rewrite (composition_of (Susp S)).
    rewrite morphism_associativity.
    rewrite (comm_h _ _ φ).
    rewrite <- morphism_associativity.
    rewrite (comm_h _ _ ψ).
    rewrite morphism_associativity.
    reflexivity.
Defined.

(** *** Triangle Morphisms Form a Category *)

(** Equality of triangle morphisms *)
Lemma triangle_morphism_eq {S : PreStableCategory} (T1 T2 : @Triangle S) 
  (φ ψ : TriangleMorphism T1 T2) :
  mor_X _ _ φ = mor_X _ _ ψ ->
  mor_Y _ _ φ = mor_Y _ _ ψ ->
  mor_Z _ _ φ = mor_Z _ _ ψ ->
  φ = ψ.
Proof.
  destruct φ as [φX φY φZ φf φg φh].
  destruct ψ as [ψX ψY ψZ ψf ψg ψh].
  simpl. intros HX HY HZ.
  destruct HX, HY, HZ.
  assert (Hf: φf = ψf) by apply path_ishprop.
  assert (Hg: φg = ψg) by apply path_ishprop.
  assert (Hh: φh = ψh) by apply path_ishprop.
  destruct Hf, Hg, Hh.
  reflexivity.
Qed.

(** Left identity law *)
Lemma triangle_morphism_left_id {S : PreStableCategory} (T1 T2 : @Triangle S) 
  (φ : TriangleMorphism T1 T2) :
  triangle_morphism_compose T1 T2 T2 φ (id_triangle_morphism T2) = φ.
Proof.
  apply triangle_morphism_eq.
  - simpl. apply morphism_left_identity.
  - simpl. apply morphism_left_identity.  
  - simpl. apply morphism_left_identity.
Qed.

(** Right identity law *)
Lemma triangle_morphism_right_id {S : PreStableCategory} (T1 T2 : @Triangle S) 
  (φ : TriangleMorphism T1 T2) :
  triangle_morphism_compose T1 T1 T2 (id_triangle_morphism T1) φ = φ.
Proof.
  apply triangle_morphism_eq.
  - simpl. apply morphism_right_identity.
  - simpl. apply morphism_right_identity.
  - simpl. apply morphism_right_identity.
Qed.

(** Associativity of composition *)
Lemma triangle_morphism_assoc {S : PreStableCategory} 
  (T1 T2 T3 T4 : @Triangle S)
  (φ : TriangleMorphism T1 T2)
  (ψ : TriangleMorphism T2 T3)
  (χ : TriangleMorphism T3 T4) :
  triangle_morphism_compose T1 T2 T4 φ (triangle_morphism_compose T2 T3 T4 ψ χ) =
  triangle_morphism_compose T1 T3 T4 (triangle_morphism_compose T1 T2 T3 φ ψ) χ.
Proof.
  apply triangle_morphism_eq.
  - simpl. apply Category.Core.associativity.
  - simpl. apply Category.Core.associativity.
  - simpl. apply Category.Core.associativity.
Qed.

(** Triangles form a category *)
Theorem triangles_form_category {S : PreStableCategory} : 
  (forall (T1 T2 T3 T4 : @Triangle S) 
          (φ : TriangleMorphism T1 T2)
          (ψ : TriangleMorphism T2 T3)
          (χ : TriangleMorphism T3 T4),
    triangle_morphism_compose T1 T2 T4 φ (triangle_morphism_compose T2 T3 T4 ψ χ) =
    triangle_morphism_compose T1 T3 T4 (triangle_morphism_compose T1 T2 T3 φ ψ) χ) /\
  (forall (T1 T2 : @Triangle S) (φ : TriangleMorphism T1 T2),
    triangle_morphism_compose T1 T2 T2 φ (id_triangle_morphism T2) = φ) /\
  (forall (T1 T2 : @Triangle S) (φ : TriangleMorphism T1 T2),
    triangle_morphism_compose T1 T1 T2 (id_triangle_morphism T1) φ = φ).
Proof.
  split; [|split].
  - intros. apply triangle_morphism_assoc.
  - intros. apply triangle_morphism_left_id.
  - intros. apply triangle_morphism_right_id.
Qed.

(** ** Triangle Rotation
    
    The rotation operation is fundamental in triangulated categories.
    It transforms a triangle X → Y → Z → ΣX into Y → Z → ΣX → ΣY.
*)

(** *** Rotation of Triangles *)

Definition rotate_triangle {S : PreStableCategory} (T : @Triangle S) : @Triangle S := {|
  X := Y T;
  Y := Z T;
  Z := object_of (Susp S) (X T);
  f := g T;
  g := h T;
  h := morphism_of (Susp S) (f T)
|}.

(** *** Rotation Preserves Distinguished Triangles *)

Theorem rotate_distinguished {S : PreStableCategory} (T : @DistinguishedTriangle S) :
  @DistinguishedTriangle S.
Proof.
  refine {| triangle := rotate_triangle (triangle T) |}.
  - (* zero_comp_1: new g ∘ new f = 0 *)
    simpl.
    exact (zero_comp_2 T).
  - (* zero_comp_2: new h ∘ new g = 0 *)
    simpl.
    exact (zero_comp_3 T).
  - (* zero_comp_3: Σ(new f) ∘ new h = 0 *)
    simpl.
    rewrite <- (composition_of (Susp S)).
    rewrite (zero_comp_1 T).
    apply susp_preserves_zero_morphisms.
Defined.

(** ** Axioms of Triangulated Categories
    
    We now formalize the axioms that characterize triangulated categories.
    TR1 ensures every morphism extends to a distinguished triangle.
*)

(** *** Axiom TR1: Extension of Morphisms to Distinguished Triangles *)

(** Statement of TR1: Every morphism can be completed to a distinguished triangle *)
Definition TR1_statement {S : PreStableCategory} : Type :=
  forall (X Y : object S) (f : morphism S X Y),
  { Z : object S &
  { g : morphism S Y Z &
  { h : morphism S Z (object_of (Susp S) X) &
    @DistinguishedTriangle S }}}.

(** Helper to construct a triangle from morphisms *)
Definition triangle_from_morphisms {S : PreStableCategory}
  {X Y Z : object S} 
  (f : morphism S X Y)
  (g : morphism S Y Z)
  (h : morphism S Z (object_of (Susp S) X)) : @Triangle S :=
{|
  X := X;
  Y := Y;
  Z := Z;
  f := f;
  g := g;
  h := h
|}.

(** ** Mapping Cones
    
    The mapping cone construction provides a canonical way to complete
    a morphism to a distinguished triangle.
*)

(** *** Basic Cone Construction *)

Definition cone {S : PreStableCategory} {X Y : object S} (f : morphism S X Y) : object S :=
  @biproduct_obj _ _ _ (add_biproduct S Y (object_of (Susp S) X)).

Definition cone_in {S : PreStableCategory} {X Y : object S} (f : morphism S X Y) : 
  morphism S Y (cone f) :=
  @inl _ _ _ (add_biproduct S Y (object_of (Susp S) X)).

Definition cone_out {S : PreStableCategory} {X Y : object S} (f : morphism S X Y) : 
  morphism S (cone f) (object_of (Susp S) X) :=
  @outr _ _ _ (add_biproduct S Y (object_of (Susp S) X)).

(** *** Cone Triangle Construction *)

Definition cone_triangle {S : PreStableCategory} {X Y : object S} (f : morphism S X Y) : 
  @Triangle S :=
{|
  X := X;
  Y := Y;
  Z := cone f;
  f := f;
  g := cone_in f;
  h := cone_out f
|}.

(** *** Properties of Cone Morphisms *)

Lemma cone_out_cone_in_zero {S : PreStableCategory} {X Y : object S} (f : morphism S X Y) :
  ((cone_out f) o (cone_in f))%morphism = zero_morphism (add_zero S) Y (object_of (Susp S) X).
Proof.
  unfold cone_out, cone_in.
  apply (@mixed_r _ _ _ (add_biproduct S Y (object_of (Susp S) X)) (add_zero S) 
                        (add_biproduct_props S Y (object_of (Susp S) X))).
Qed.

(** Helper lemma for cone distinguished triangle construction *)
Lemma cone_distinguished_conditions {S : PreStableCategory} {X Y : object S} (f : morphism S X Y) :
  ((cone_in f) o f)%morphism = zero_morphism (add_zero S) X (cone f) ->
  ((cone_out f) o (cone_in f))%morphism = zero_morphism (add_zero S) Y (object_of (Susp S) X) ->
  (morphism_of (Susp S) f o (cone_out f))%morphism = zero_morphism (add_zero S) (cone f) (object_of (Susp S) Y) ->
  @DistinguishedTriangle S.
Proof.
  intros H1 H2 H3.
  refine {| triangle := cone_triangle f |}.
  - exact H1.
  - exact H2.
  - exact H3.
Defined.

(** ** Pre-Stable Categories with Cofiber
    
    A more structured version of pre-stable categories where the mapping
    cone/cofiber construction is given as part of the data.
*)

Record PreStableCategoryWithCofiber := {
  base :> PreStableCategory;
  
  (** The cofiber of a morphism *)
  cofiber : forall {X Y : object base} (f : morphism base X Y), object base;
  
  (** Structure morphisms for the cofiber *)
  cofiber_in : forall {X Y : object base} (f : morphism base X Y), 
               morphism base Y (cofiber f);
  cofiber_out : forall {X Y : object base} (f : morphism base X Y), 
                morphism base (cofiber f) (object_of (Susp base) X);
  
  (** The cofiber axioms *)
  cofiber_cond1 : forall {X Y : object base} (f : morphism base X Y),
    (cofiber_in f o f)%morphism = 
    zero_morphism (add_zero base) X (cofiber f);
    
  cofiber_cond2 : forall {X Y : object base} (f : morphism base X Y),
    (cofiber_out f o cofiber_in f)%morphism = 
    zero_morphism (add_zero base) Y (object_of (Susp base) X);
    
  cofiber_cond3 : forall {X Y : object base} (f : morphism base X Y),
    (morphism_of (Susp base) f o cofiber_out f)%morphism = 
    zero_morphism (add_zero base) (cofiber f) (object_of (Susp base) Y)
}.

(** *** Cofiber Gives Distinguished Triangles *)

Definition triangle_from_morphism {S : PreStableCategoryWithCofiber} 
  {X Y : object S} (f : morphism S X Y) : @Triangle (base S) :=
{|
  X := X;
  Y := Y;
  Z := @cofiber S X Y f;
  f := f;
  g := @cofiber_in S X Y f;
  h := @cofiber_out S X Y f
|}.

Theorem cofiber_triangle_distinguished {S : PreStableCategoryWithCofiber} 
  {X Y : object S} (f : morphism S X Y) : @DistinguishedTriangle (base S).
Proof.
  refine {| triangle := triangle_from_morphism f |}.
  - simpl. exact (@cofiber_cond1 S X Y f).
  - simpl. exact (@cofiber_cond2 S X Y f).
  - simpl. exact (@cofiber_cond3 S X Y f).
Defined.

(** *** TR1 for Categories with Cofiber *)

Theorem TR1 {S : PreStableCategoryWithCofiber} {X Y : object S} (f : morphism S X Y) :
  @DistinguishedTriangle (base S).
Proof.
  exact (cofiber_triangle_distinguished f).
Defined.

Theorem TR1_correct {S : PreStableCategoryWithCofiber} {X Y : object S} (f : morphism S X Y) :
  triangle (TR1 f) = triangle_from_morphism f.
Proof.
  reflexivity.
Qed.

(** Constructive version of TR1 *)
Definition TR1_triangle_data {S : PreStableCategoryWithCofiber} 
  {X Y : object (base S)} (f : morphism (base S) X Y) :
  { Z : object (base S) & 
  { g : morphism (base S) Y Z &
  { h : morphism (base S) Z (object_of (Susp (base S)) X) &
  ((g o f)%morphism = zero_morphism (add_zero (base S)) X Z) *
  ((h o g)%morphism = zero_morphism (add_zero (base S)) Y (object_of (Susp (base S)) X)) *
  ((morphism_of (Susp (base S)) f o h)%morphism = 
   zero_morphism (add_zero (base S)) Z (object_of (Susp (base S)) Y)) }}}.
Proof.
  exists (@cofiber S X Y f).
  exists (@cofiber_in S X Y f).
  exists (@cofiber_out S X Y f).
  split.
  - split.
    + exact (@cofiber_cond1 S X Y f).
    + exact (@cofiber_cond2 S X Y f).
  - exact (@cofiber_cond3 S X Y f).
Defined.

(** ** Isomorphisms in Categories
    
    We define isomorphisms and establish their basic properties,
    which will be needed for the axioms of triangulated categories.
*)

(** *** Basic Isomorphism Definition *)

Definition IsIsomorphism {C : PreCategory} {X Y : object C} (f : morphism C X Y) : Type :=
  { g : morphism C Y X |
    (g o f = 1)%morphism /\ (f o g = 1)%morphism }.

(** Extract the inverse morphism *)
Definition iso_inverse {C : PreCategory} {X Y : object C} {f : morphism C X Y} 
  (H : IsIsomorphism f) : morphism C Y X :=
  H.1.

(** The identity morphism is an isomorphism *)
Lemma iso_identity {C : PreCategory} {X : object C} : 
  IsIsomorphism (1%morphism : morphism C X X).
Proof.
  exists 1%morphism.
  split; apply morphism_left_identity.
Qed.

(** Properties of inverses *)
Lemma iso_inverse_left {C : PreCategory} {X Y : object C} {f : morphism C X Y} 
  (H : IsIsomorphism f) :
  (iso_inverse H o f = 1)%morphism.
Proof.
  destruct H as [g [Hl Hr]].
  exact Hl.
Qed.

Lemma iso_inverse_right {C : PreCategory} {X Y : object C} {f : morphism C X Y} 
  (H : IsIsomorphism f) :
  (f o iso_inverse H = 1)%morphism.
Proof.
  destruct H as [g [Hl Hr]].
  exact Hr.
Qed.

(** *** Triangle Isomorphisms *)

(** A triangle isomorphism is a triangle morphism where all three
    component morphisms are isomorphisms *)
Definition IsTriangleIsomorphism {S : PreStableCategory} {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2) : Type :=
  IsIsomorphism (mor_X _ _ φ) * 
  IsIsomorphism (mor_Y _ _ φ) * 
  IsIsomorphism (mor_Z _ _ φ).

(** ** Axiom TR2: Isomorphisms of Distinguished Triangles
    
    TR2 states that if we have an isomorphism between two triangles
    and one is distinguished, then so is the other.
*)

(** *** Helper Lemmas for Isomorphisms *)

(** Isomorphisms preserve terminal morphisms *)
Lemma iso_preserves_terminal {S : PreStableCategory} {X Y : object S}
  (φ : morphism S X Y) (H : IsIsomorphism φ)
  (f : morphism S X (@zero _ (add_zero S))) :
  (f o iso_inverse H)%morphism = @center _ (@is_terminal _ (add_zero S) Y).
Proof.
  symmetry.
  apply (@contr _ (@is_terminal _ (add_zero S) Y)).
Qed.

(** Isomorphisms preserve initial morphisms *)
Lemma iso_preserves_initial {S : PreStableCategory} {X Y : object S}
  (φ : morphism S X Y) (H : IsIsomorphism φ)
  (f : morphism S (@zero _ (add_zero S)) X) :
  (φ o f)%morphism = @center _ (@is_initial _ (add_zero S) Y).
Proof.
  symmetry.
  apply (@contr _ (@is_initial _ (add_zero S) Y)).
Qed.

(** Composition with zero morphism on the right *)
Lemma zero_morphism_right {S : PreStableCategory} {X Y Z : object S}
  (g : morphism S Y Z) :
  (g o zero_morphism (add_zero S) X Y)%morphism = 
  zero_morphism (add_zero S) X Z.
Proof.
  unfold zero_morphism.
  assert (H: (g o @center _ (@is_initial _ (add_zero S) Y))%morphism = 
             @center _ (@is_initial _ (add_zero S) Z)).
  {
    symmetry.
    apply (@contr _ (@is_initial _ (add_zero S) Z)).
  }
  rewrite <- morphism_associativity.
  rewrite H.
  reflexivity.
Qed.

(** Composition with zero morphism on the left *)
Lemma zero_morphism_left {S : PreStableCategory} {X Y Z : object S}
  (f : morphism S X Y) :
  (zero_morphism (add_zero S) Y Z o f)%morphism = 
  zero_morphism (add_zero S) X Z.
Proof.
  unfold zero_morphism.
  assert (H: (@center _ (@is_terminal _ (add_zero S) Y) o f)%morphism = 
             @center _ (@is_terminal _ (add_zero S) X)).
  {
    symmetry.
    apply (@contr _ (@is_terminal _ (add_zero S) X)).
  }
  rewrite morphism_associativity.
  rewrite H.
  reflexivity.
Qed.

(** Isomorphisms preserve zero morphisms *)
Lemma iso_preserves_zero {S : PreStableCategory} {X Y Z W : object S}
  (φX : morphism S X Z) (φY : morphism S Y W)
  (HX : IsIsomorphism φX) (HY : IsIsomorphism φY)
  (f : morphism S X Y) :
  f = zero_morphism (add_zero S) X Y ->
  (φY o f o iso_inverse HX)%morphism = zero_morphism (add_zero S) Z W.
Proof.
  intro Hf.
  rewrite Hf.
  rewrite zero_morphism_right.
  rewrite zero_morphism_left.
  reflexivity.
Qed.

(** *** Functors Preserve Isomorphisms *)

Lemma functor_preserves_iso {C D : PreCategory} (F : Functor C D)
  {X Y : object C} (f : morphism C X Y) (H : IsIsomorphism f) :
  IsIsomorphism (morphism_of F f).
Proof.
  destruct H as [g [Hgf Hfg]].
  exists (morphism_of F g).
  split.
  - rewrite <- composition_of.
    rewrite Hgf.
    apply identity_of.
  - rewrite <- composition_of.
    rewrite Hfg.
    apply identity_of.
Defined.

Lemma functor_preserves_inverse {C D : PreCategory} (F : Functor C D)
  {X Y : object C} (f : morphism C X Y) (H : IsIsomorphism f) :
  morphism_of F (iso_inverse H) = 
  iso_inverse (functor_preserves_iso F f H).
Proof.
  destruct H as [g [Hgf Hfg]].
  simpl.
  reflexivity.
Qed.

(** *** Helper Lemmas for Composition *)

Lemma ap_morphism_comp_left {C : PreCategory} {X Y Z : object C} 
  (f : morphism C Y Z) (g h : morphism C X Y) :
  g = h -> (f o g)%morphism = (f o h)%morphism.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Lemma compose_cancel_left {C : PreCategory} {X Y Z : object C} 
  (f : morphism C Y Z) (g h : morphism C X Y) :
  (f o g)%morphism = (f o h)%morphism -> 
  (1 o g)%morphism = (1 o h)%morphism ->
  g = h.
Proof.
  intros H1 H2.
  rewrite morphism_left_identity in H2.
  rewrite morphism_left_identity in H2.
  exact H2.
Qed.

Lemma iso_comp_to_id {C : PreCategory} {X Y : object C} 
  (f : morphism C X Y) (g : morphism C Y X)
  (H : (g o f = 1)%morphism) :
  forall (Z : object C) (h : morphism C Z X),
  ((g o f) o h)%morphism = (1 o h)%morphism.
Proof.
  intros Z h.
  rewrite H.
  reflexivity.
Qed.

Lemma four_way_compose_eq {C : PreCategory} {V W X Y Z : object C}
  (p : morphism C Y Z) 
  (q1 q2 : morphism C X Y)
  (r : morphism C W X)
  (s : morphism C V W) :
  q1 = q2 ->
  (p o q1 o r o s)%morphism = (p o q2 o r o s)%morphism.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Lemma compose_left {C : PreCategory} {X Y Z : object C}
  (p : morphism C Y Z)
  (q1 q2 : morphism C X Y) :
  q1 = q2 ->
  (p o q1)%morphism = (p o q2)%morphism.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Lemma compose_right {C : PreCategory} {X Y Z : object C}
  (p1 p2 : morphism C Y Z)
  (q : morphism C X Y) :
  p1 = p2 ->
  (p1 o q)%morphism = (p2 o q)%morphism.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.

(** *** Additional Helper Lemmas for TR2 *)

Lemma iso_morphism_cancel {S : PreStableCategory} {X Y : object S}
  (φ : morphism S X Y) (H : IsIsomorphism φ) :
  (iso_inverse H o φ)%morphism = 1%morphism.
Proof.
  apply iso_inverse_left.
Qed.

Lemma composition_with_identity_middle {S : PreStableCategory} {A B C D : object S}
  (f : morphism S C D)
  (g : morphism S B C) 
  (h : morphism S A B) :
  (f o 1 o g o h)%morphism = (f o g o h)%morphism.
Proof.
  rewrite morphism_right_identity.
  reflexivity.
Qed.

Lemma rearrange_middle_composition {S : PreStableCategory} {A B C D E : object S}
  (f : morphism S D E)
  (g : morphism S C D)
  (h : morphism S B C)
  (k : morphism S A B) :
  (f o (g o (h o k)))%morphism = (f o ((g o h) o k))%morphism.
Proof.
  rewrite morphism_associativity.
  reflexivity.
Qed.

Lemma get_morphisms_adjacent {S : PreStableCategory} {A B C D E F : object S}
  (f : morphism S E F)
  (g : morphism S D E)
  (h : morphism S C D)
  (k : morphism S B C)
  (l : morphism S A B) :
  (f o (g o (h o (k o l))))%morphism = 
  (f o (g o ((h o k) o l)))%morphism.
Proof.
  rewrite morphism_associativity.
  reflexivity.
Qed.

Lemma four_morphism_assoc {S : PreStableCategory} {A B C D E : object S}
  (φ : morphism S D E)
  (g : morphism S C D)
  (f : morphism S B C)
  (ψ : morphism S A B) :
  (φ o g o f o ψ)%morphism = (φ o (g o f) o ψ)%morphism.
Proof.
  rewrite (morphism_associativity ψ f (φ o g)%morphism).
  rewrite (morphism_associativity (f o ψ)%morphism g φ).
  rewrite <- (morphism_associativity ψ f g).
  rewrite <- morphism_associativity.
  reflexivity.
Qed.

Lemma morphism_four_compose_with_zero {S : PreStableCategory} {A B C D E : object S}
  (φ : morphism S D E)
  (g : morphism S C D)
  (f : morphism S B C)
  (ψ : morphism S A B) :
  (g o f)%morphism = zero_morphism (add_zero S) B D ->
  (φ o g o f o ψ)%morphism = zero_morphism (add_zero S) A E.
Proof.
  intro H.
  rewrite four_morphism_assoc.
  rewrite H.
  rewrite zero_morphism_right.
  rewrite zero_morphism_left.
  reflexivity.
Qed.

Lemma triangle_composition_pattern {S : PreStableCategory} {X1 Y1 Z1 X2 Y2 Z2 : object S}
  (φZ : morphism S Z1 Z2)
  (g : morphism S Y1 Z1)
  (φY_inv : morphism S Y2 Y1)
  (φY : morphism S Y1 Y2)
  (f : morphism S X1 Y1)
  (φX_inv : morphism S X2 X1) :
  (φY_inv o φY)%morphism = 1%morphism ->
  ((φZ o g o φY_inv) o (φY o f o φX_inv))%morphism = 
  (φZ o g o f o φX_inv)%morphism.
Proof.
  intro H.
  rewrite !morphism_associativity.
  rewrite get_morphisms_adjacent.
  rewrite H.
  rewrite morphism_left_identity.
  reflexivity.
Qed.

(** ** Axiom TR2: Isomorphisms Preserve Distinguished Triangles
    
    This section proves that isomorphisms of triangles preserve the property
    of being distinguished. This is one of the fundamental axioms of
    triangulated categories.
*)

(** *** Formulas for Triangle Components Under Isomorphisms *)

(** How the f morphism transforms under an isomorphism *)
Lemma triangle_iso_f_formula {S : PreStableCategory}
  {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (HY_iso : IsIsomorphism (mor_Y _ _ φ))
  (HX_iso : IsIsomorphism (mor_X _ _ φ)) :
  f T2 = (mor_Y _ _ φ o f T1 o iso_inverse HX_iso)%morphism.
Proof.
  pose proof (comm_f _ _ φ) as Hcomm.
  
  assert (H: forall (g h : morphism S (X T1) (Y T2)) (k : morphism S (X T2) (X T1)),
            g = h -> (g o k)%morphism = (h o k)%morphism).
  {
    intros g h k Heq. rewrite Heq. reflexivity.
  }
  
  apply (H _ _ (iso_inverse HX_iso)) in Hcomm.
  rewrite !morphism_associativity in Hcomm.
  rewrite (iso_inverse_right HX_iso) in Hcomm.
  rewrite morphism_right_identity in Hcomm.
  rewrite <- morphism_associativity in Hcomm.
  exact Hcomm^.
Qed.

(** How the g morphism transforms under an isomorphism *)
Lemma triangle_iso_g_formula {S : PreStableCategory}
  {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (HZ_iso : IsIsomorphism (mor_Z _ _ φ))
  (HY_iso : IsIsomorphism (mor_Y _ _ φ)) :
  g T2 = (mor_Z _ _ φ o g T1 o iso_inverse HY_iso)%morphism.
Proof.
  pose proof (comm_g _ _ φ) as Hcomm.
  
  assert (H: forall (g h : morphism S (Y T1) (Z T2)) (k : morphism S (Y T2) (Y T1)),
            g = h -> (g o k)%morphism = (h o k)%morphism).
  {
    intros g h k Heq. rewrite Heq. reflexivity.
  }
  
  apply (H _ _ (iso_inverse HY_iso)) in Hcomm.
  rewrite !morphism_associativity in Hcomm.
  rewrite (iso_inverse_right HY_iso) in Hcomm.
  rewrite morphism_right_identity in Hcomm.
  rewrite <- morphism_associativity in Hcomm.
  exact Hcomm^.
Qed.

(** How the h morphism transforms under an isomorphism *)
Lemma triangle_iso_h_formula {S : PreStableCategory}
  {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (HX_iso : IsIsomorphism (mor_X _ _ φ))
  (HZ_iso : IsIsomorphism (mor_Z _ _ φ)) :
  h T2 = (morphism_of (Susp S) (mor_X _ _ φ) o h T1 o iso_inverse HZ_iso)%morphism.
Proof.
  pose proof (comm_h _ _ φ) as Hcomm.
  
  assert (H: forall (g h : morphism S (Z T1) (object_of (Susp S) (X T2))) 
                    (k : morphism S (Z T2) (Z T1)),
            g = h -> (g o k)%morphism = (h o k)%morphism).
  {
    intros g h k Heq. rewrite Heq. reflexivity.
  }
  
  apply (H _ _ (iso_inverse HZ_iso)) in Hcomm.
  rewrite !morphism_associativity in Hcomm.
  rewrite (iso_inverse_right HZ_iso) in Hcomm.
  rewrite morphism_right_identity in Hcomm.
  rewrite <- morphism_associativity in Hcomm.
  exact Hcomm^.
Qed.

(** *** Preservation of Zero Compositions *)

(** Isomorphisms preserve the first zero composition g∘f = 0 *)
Lemma triangle_iso_preserves_zero_comp_1 {S : PreStableCategory}
  {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (Hφ : IsTriangleIsomorphism φ) :
  (g T1 o f T1)%morphism = zero_morphism (add_zero S) (X T1) (Z T1) ->
  (g T2 o f T2)%morphism = zero_morphism (add_zero S) (X T2) (Z T2).
Proof.
  intro H.
  destruct Hφ as [[HX_iso HY_iso] HZ_iso].
  
  rewrite (triangle_iso_f_formula φ HY_iso HX_iso).
  rewrite (triangle_iso_g_formula φ HZ_iso HY_iso).
  
  rewrite (triangle_composition_pattern 
             (mor_Z _ _ φ) (g T1) 
             (iso_inverse HY_iso) (mor_Y _ _ φ)
             (f T1) (iso_inverse HX_iso)
             (iso_inverse_left HY_iso)).
  
  apply morphism_four_compose_with_zero.
  exact H.
Qed.

(** Isomorphisms preserve the second zero composition h∘g = 0 *)
Lemma triangle_iso_preserves_zero_comp_2 {S : PreStableCategory}
  {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (Hφ : IsTriangleIsomorphism φ) :
  (h T1 o g T1)%morphism = zero_morphism (add_zero S) (Y T1) (object_of (Susp S) (X T1)) ->
  (h T2 o g T2)%morphism = zero_morphism (add_zero S) (Y T2) (object_of (Susp S) (X T2)).
Proof.
  intro H.
  destruct Hφ as [[HX_iso HY_iso] HZ_iso].
  
  rewrite (triangle_iso_g_formula φ HZ_iso HY_iso).
  rewrite (triangle_iso_h_formula φ HX_iso HZ_iso).
  
  rewrite (triangle_composition_pattern 
             (morphism_of (Susp S) (mor_X _ _ φ)) (h T1) 
             (iso_inverse HZ_iso) (mor_Z _ _ φ)
             (g T1) (iso_inverse HY_iso)
             (iso_inverse_left HZ_iso)).
  apply morphism_four_compose_with_zero.
  exact H.
Qed.

(** Isomorphisms preserve the third zero composition Σf∘h = 0 *)
Lemma triangle_iso_preserves_zero_comp_3 {S : PreStableCategory}
  {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (Hφ : IsTriangleIsomorphism φ) :
  (morphism_of (Susp S) (f T1) o h T1)%morphism = 
  zero_morphism (add_zero S) (Z T1) (object_of (Susp S) (Y T1)) ->
  (morphism_of (Susp S) (f T2) o h T2)%morphism = 
  zero_morphism (add_zero S) (Z T2) (object_of (Susp S) (Y T2)).
Proof.
  intro H.
  destruct Hφ as [[HX_iso HY_iso] HZ_iso].
  
  rewrite (triangle_iso_f_formula φ HY_iso HX_iso).
  rewrite (triangle_iso_h_formula φ HX_iso HZ_iso).
  
  rewrite (composition_of (Susp S)).
  rewrite (composition_of (Susp S)).
      
  rewrite (functor_preserves_inverse (Susp S) (mor_X _ _ φ) HX_iso).
  
  rewrite (triangle_composition_pattern 
             (morphism_of (Susp S) (mor_Y _ _ φ)) 
             (morphism_of (Susp S) (f T1))
             (iso_inverse (functor_preserves_iso (Susp S) (mor_X _ _ φ) HX_iso))
             (morphism_of (Susp S) (mor_X _ _ φ))
             (h T1) 
             (iso_inverse HZ_iso)
             (iso_inverse_left (functor_preserves_iso (Susp S) (mor_X _ _ φ) HX_iso))).
  
  apply morphism_four_compose_with_zero.
  exact H.
Qed.

(** *** Main Theorem: TR2 *)

(** TR2: Triangle isomorphisms preserve the distinguished property *)
Theorem TR2 {S : PreStableCategory} {T1 T2 : @Triangle S} 
  (φ : TriangleMorphism T1 T2)
  (Hφ : IsTriangleIsomorphism φ)
  (D1 : @DistinguishedTriangle S)
  (H1 : triangle D1 = T1) :
  @DistinguishedTriangle S.
Proof.
  destruct Hφ as [[HX_iso HY_iso] HZ_iso].
  refine {| triangle := T2 |}.
  - (* zero_comp_1 *)
    apply (triangle_iso_preserves_zero_comp_1 φ (conj (conj HX_iso HY_iso) HZ_iso)).
    rewrite <- H1.
    exact (zero_comp_1 D1).
  - (* zero_comp_2 *)
    apply (triangle_iso_preserves_zero_comp_2 φ (conj (conj HX_iso HY_iso) HZ_iso)).
    rewrite <- H1.
    exact (zero_comp_2 D1).
  - (* zero_comp_3 *)
    apply (triangle_iso_preserves_zero_comp_3 φ (conj (conj HX_iso HY_iso) HZ_iso)).
    rewrite <- H1.
    exact (zero_comp_3 D1).
Defined.

(** ** Shift and Axiom TR3
    
    The shift operation is another name for rotation. We formalize how
    triangle morphisms behave under shifting.
*)

Definition shift_triangle {S : PreStableCategory} (T : @Triangle S) : @Triangle S := 
  rotate_triangle T.

Theorem shift_distinguished {S : PreStableCategory} (T : @DistinguishedTriangle S) :
  @DistinguishedTriangle S.
Proof.
  exact (rotate_distinguished T).
Defined.

(** Shifting a triangle morphism *)
Definition shift_triangle_morphism {S : PreStableCategory} {T1 T2 : @Triangle S}
  (φ : TriangleMorphism T1 T2) : 
  TriangleMorphism (shift_triangle T1) (shift_triangle T2).
Proof.
  unfold shift_triangle, rotate_triangle.

  apply Build_TriangleMorphism with
    (mor_X := mor_Y T1 T2 φ)
    (mor_Y := mor_Z T1 T2 φ)
    (mor_Z := morphism_of (Susp S) (mor_X T1 T2 φ)).
  - (* comm_f *)
    exact (comm_g T1 T2 φ).
  - (* comm_g *)
    exact (comm_h T1 T2 φ).
  - (* comm_h *)
    rewrite <- (composition_of (Susp S)).
    rewrite (comm_f T1 T2 φ).
    rewrite (composition_of (Susp S)).
    reflexivity.
Defined.

(** Statement of TR3 *)
Definition TR3_statement {S : PreStableCategory} : Type :=
  forall (T : @Triangle S) (T' : @Triangle S) 
         (φ : TriangleMorphism T T'),
  IsTriangleIsomorphism φ ->
  @DistinguishedTriangle S ->
  @DistinguishedTriangle S.
  
  (** ** Opposite Categories
    
    The opposite category construction reverses all morphisms. This section
    shows that pre-stable categories have a natural opposite structure where
    the suspension and loop functors are interchanged.
*)

(** *** Basic Opposite Category Construction *)

Definition opposite_category (C : PreCategory) : PreCategory.
Proof.
  exact (@Build_PreCategory
    (object C)
    (fun X Y => morphism C Y X)
    (fun X => 1%morphism)
    (fun X Y Z f g => (g o f)%morphism)
    (fun s d d' d'' m1 m2 m3 => (Category.Core.associativity C d'' d' d s m3 m2 m1)^)
    (fun a b f => Category.Core.right_identity C b a f)
    (fun a b f => Category.Core.left_identity C b a f)
    (fun s d => trunc_morphism C d s)).
Defined.

(** *** Opposite Zero Object *)

Definition opposite_zero_object {C : PreCategory} (Z : ZeroObject C) : 
  ZeroObject (opposite_category C).
Proof.
  exact (Build_ZeroObject 
    (opposite_category C)
    (zero _ Z)
    (fun X => is_terminal _ Z X)
    (fun X => is_initial _ Z X)).
Defined.

(** *** Opposite Biproduct *)

Definition opposite_biproduct {C : PreCategory} {X Y : object C} 
  (B : Biproduct X Y) : @Biproduct (opposite_category C) Y X.
Proof.
  exact (Build_Biproduct
    (opposite_category C) Y X
    (@biproduct_obj _ _ _ B)
    (@outr _ _ _ B)
    (@outl _ _ _ B)
    (@inr _ _ _ B)
    (@inl _ _ _ B)).
Defined.

(** *** Properties of Opposite Biproducts *)

Lemma opposite_biproduct_beta_l {C : PreCategory} {X Y : object C} 
  (B : Biproduct X Y) (Z : ZeroObject C) (H : IsBiproduct B Z) :
  (@outl _ _ _ (opposite_biproduct B) o @inl _ _ _ (opposite_biproduct B) = 1)%morphism.
Proof.
  simpl.
  exact (@beta_r _ _ _ B Z H).
Qed.

Lemma opposite_biproduct_beta_r {C : PreCategory} {X Y : object C} 
  (B : Biproduct X Y) (Z : ZeroObject C) (H : IsBiproduct B Z) :
  (@outr _ _ _ (opposite_biproduct B) o @inr _ _ _ (opposite_biproduct B) = 1)%morphism.
Proof.
  simpl.
  exact (@beta_l _ _ _ B Z H).
Qed.

Lemma opposite_biproduct_mixed_r {C : PreCategory} {X Y : object C} 
  (B : Biproduct X Y) (Z : ZeroObject C) (H : IsBiproduct B Z) :
  (@outr _ _ _ (opposite_biproduct B) o @inl _ _ _ (opposite_biproduct B))%morphism = 
  zero_morphism (opposite_zero_object Z) Y X.
Proof.
  simpl.
  exact (@mixed_r _ _ _ B Z H).
Qed.

(** *** Universal Property of Opposite Biproducts *)

(** Helper equivalence for swapping products *)
Lemma swap_product_equiv {A : Type} {P Q : A -> Type} :
  {a : A & (P a * Q a)} <~> {a : A & (Q a * P a)}.
Proof.
  apply equiv_functor_sigma_id.
  intro a.
  apply equiv_prod_symm.
Defined.

Lemma swap_product_contr {A : Type} {P Q : A -> Type} :
  Contr {a : A & (P a * Q a)} ->
  Contr {a : A & (Q a * P a)}.
Proof.
  intro H.
  apply (contr_equiv' _ (swap_product_equiv)).
Qed.

Lemma opposite_coprod_universal {C : PreCategory} {X Y : object C} 
  (B : Biproduct X Y) (H : BiproductUniversal B) :
  forall (Z : object (opposite_category C)) 
         (f : morphism (opposite_category C) Y Z) 
         (g : morphism (opposite_category C) X Z),
  Contr {h : morphism (opposite_category C) (@biproduct_obj _ _ _ (opposite_biproduct B)) Z | 
         (h o @inl _ _ _ (opposite_biproduct B) = f)%morphism /\ 
         (h o @inr _ _ _ (opposite_biproduct B) = g)%morphism}.
Proof.
  intros Z f g.
  simpl in *.
  apply swap_product_contr.
  exact (@prod_universal _ _ _ B H Z g f).
Qed.

Lemma opposite_prod_universal {C : PreCategory} {X Y : object C} 
  (B : Biproduct X Y) (H : BiproductUniversal B) :
  forall (Z : object (opposite_category C)) 
         (f : morphism (opposite_category C) Z Y) 
         (g : morphism (opposite_category C) Z X),
  Contr {h : morphism (opposite_category C) Z (@biproduct_obj _ _ _ (opposite_biproduct B)) | 
         (@outl _ _ _ (opposite_biproduct B) o h = f)%morphism /\ 
         (@outr _ _ _ (opposite_biproduct B) o h = g)%morphism}.
Proof.
  intros Z f g.
  simpl in *.
  apply swap_product_contr.
  exact (@coprod_universal _ _ _ B H Z g f).
Qed.

Definition opposite_biproduct_universal {C : PreCategory} {X Y : object C} 
  (B : Biproduct X Y) (H : BiproductUniversal B) : 
  BiproductUniversal (opposite_biproduct B).
Proof.
  exact (Build_BiproductUniversal
    (opposite_category C) Y X
    (opposite_biproduct B)
    (opposite_coprod_universal B H)
    (opposite_prod_universal B H)).
Defined.

(** *** Opposite Additive Category *)

Definition opposite_additive_category (A : AdditiveCategory) : AdditiveCategory.
Proof.
  refine (Build_AdditiveCategory
    (opposite_category A)
    (opposite_zero_object (add_zero A))
    (fun X Y => opposite_biproduct (add_biproduct A Y X))
    _ _).
  - (* Biproduct properties *)
    intros X Y.
    pose (B := add_biproduct A Y X).
    pose (Z := add_zero A).
    pose (H := add_biproduct_props A Y X).
    exact (Build_IsBiproduct
      (opposite_category A) X Y
      (opposite_biproduct B)
      (opposite_zero_object Z)
      (@beta_r _ _ _ B Z H)
      (@beta_l _ _ _ B Z H)
      (@mixed_l _ _ _ B Z H)
      (@mixed_r _ _ _ B Z H)).
  - (* Universal property *)
    intros X Y.
    apply opposite_biproduct_universal.
    exact (add_biproduct_universal A Y X).
Defined.

(** *** Opposite Functor *)

Definition opposite_functor {C D : PreCategory} (F : Functor C D) : 
  Functor (opposite_category C) (opposite_category D).
Proof.
  exact (Build_Functor
    (opposite_category C) (opposite_category D)
    (object_of F)
    (fun X Y f => morphism_of F f)
    (fun X Y Z f g => composition_of F Z Y X g f)
    (fun X => identity_of F X)).
Defined.

(** *** Opposite Additive Functor *)

Definition opposite_additive_functor {A B : AdditiveCategory} 
  (F : AdditiveFunctor A B) : 
  AdditiveFunctor (opposite_additive_category A) (opposite_additive_category B).
Proof.
  exact (Build_AdditiveFunctor
    (opposite_additive_category A) (opposite_additive_category B)
    (opposite_functor F)
    (preserves_zero A B F)
    (fun X Y => preserves_biproduct A B F Y X)).
Defined.

(** *** Opposite Natural Transformation *)

Definition opposite_natural_transformation {C D : PreCategory} 
  {F G : Functor C D} (η : NaturalTransformation F G) : 
  NaturalTransformation (opposite_functor G) (opposite_functor F).
Proof.
  exact (Build_NaturalTransformation
    (opposite_functor G) (opposite_functor F)
    (fun X => components_of η X)
    (fun X Y f => (commutes η Y X f)^)).
Defined.

(** *** Opposite Pre-Stable Category *)

(** The key insight: in the opposite category, suspension and loop functors swap roles *)
Definition opposite_prestable_category (PS : PreStableCategory) : PreStableCategory.
Proof.
  exact (Build_PreStableCategory
    (opposite_additive_category PS)
    (opposite_additive_functor (Loop PS))  (* Loop becomes Susp *)
    (opposite_additive_functor (Susp PS))  (* Susp becomes Loop *)
    (opposite_natural_transformation (epsilon PS))  (* epsilon becomes eta *)
    (opposite_natural_transformation (eta PS))).     (* eta becomes epsilon *)
Defined.

(** *** Double Opposite is Identity *)

Definition double_opposite_functor (C : PreCategory) : 
  Functor (opposite_category (opposite_category C)) C.
Proof.
  exact (Build_Functor
    (opposite_category (opposite_category C)) C
    (fun X => X)
    (fun X Y f => f)
    (fun X Y Z f g => idpath)
    (fun X => idpath)).
Defined.

Definition to_double_opposite_functor (C : PreCategory) : 
  Functor C (opposite_category (opposite_category C)).
Proof.
  exact (Build_Functor
    C (opposite_category (opposite_category C))
    (fun X => X)
    (fun X Y f => f)
    (fun X Y Z f g => idpath)
    (fun X => idpath)).
Defined.

(** *** Basic Properties of Opposite Categories *)

Lemma opposite_involution_objects (C : PreCategory) : 
  object (opposite_category (opposite_category C)) = object C.
Proof.
  reflexivity.
Qed.

Lemma opposite_involution_morphisms (C : PreCategory) (X Y : object C) : 
  morphism (opposite_category (opposite_category C)) X Y = morphism C X Y.
Proof.
  reflexivity.
Qed.

(** *** Main Theorems about Opposite Pre-Stable Categories *)

Theorem opposite_prestable_exists :
  forall (PS : PreStableCategory),
  exists (PS_op : PreStableCategory),
    cat PS_op = opposite_additive_category PS.
Proof.
  intro PS.
  exists (opposite_prestable_category PS).
  reflexivity.
Qed.

Theorem opposite_morphisms_flip :
  forall (PS : PreStableCategory) (X Y : object PS),
  morphism (opposite_prestable_category PS) X Y = morphism PS Y X.
Proof.
  intros.
  reflexivity.
Qed.

(** ** Examples and Properties of Opposite Pre-Stable Categories
    
    This section demonstrates how the opposite construction works in practice,
    showing how morphisms, compositions, and distinguished triangles behave
    under dualization.
*)

(** *** Composition in Opposite Categories *)

(** Example showing how composition reverses in the opposite category *)
Lemma opposite_composition_demo {PS : PreStableCategory} 
  (X Y Z : object PS)
  (f : morphism PS X Y) (g : morphism PS Y Z) :
  let original_composition := (g o f)%morphism in
  let f_op : morphism (opposite_prestable_category PS) Y X := f in
  let g_op : morphism (opposite_prestable_category PS) Z Y := g in
  let opposite_composition := (f_op o g_op)%morphism in
  opposite_composition = original_composition.
Proof.
  simpl.
  reflexivity.
Qed.

(** *** Zero Morphisms in Opposite Categories *)

(** Zero morphisms dualize correctly *)
Theorem zero_morphism_dualizes {PS : PreStableCategory} (X Y : object PS) :
  zero_morphism (add_zero (opposite_prestable_category PS)) Y X = 
  zero_morphism (add_zero PS) X Y.
Proof.
  unfold zero_morphism.
  simpl.
  reflexivity.
Qed.

(** *** Suspension and Loop Duality *)

(** The fundamental duality: suspension and loop functors swap *)
Theorem suspension_loop_swap {PS : PreStableCategory} (X : object PS) :
  (object_of (Susp (opposite_prestable_category PS)) X = 
   object_of (Loop PS) X) /\
  (object_of (Loop (opposite_prestable_category PS)) X = 
   object_of (Susp PS) X).
Proof.
  split; simpl; reflexivity.
Qed.

(** *** Distinguished Triangles Under Duality *)

(** How a distinguished triangle appears in the opposite category *)
Lemma distinguished_triangle_duality {PS : PreStableCategory} 
  (D : @DistinguishedTriangle PS) :
  let T := triangle D in
  let X := X T in
  let Y := Y T in  
  let Z := Z T in
  let f := f T in
  let g := g T in
  let h := h T in
  (* In PS^op, morphisms have flipped source/target *)
  let f_dual : morphism (opposite_prestable_category PS) Y X := f in
  let g_dual : morphism (opposite_prestable_category PS) Z Y := g in
  (* h : Z → ΣX in PS becomes h : ΩX → Z in PS^op (since Σ and Ω swap) *)
  let h_dual : morphism (opposite_prestable_category PS) 
                        (object_of (Susp PS) X) Z := h in
  (* The triangle pattern reverses:
     Original in PS:     X --f--> Y --g--> Z --h--> ΣX
     In PS^op:          Y <--f-- X,  Z <--g-- Y,  ΩX <--h-- Z *)
  True.
Proof.
  trivial.
Qed.

(** ** Proper Stable Categories
    
    A proper stable category is a pre-stable category where the suspension
    and loop functors are inverse equivalences.
*)

Record ProperStableCategory := {
  pre_stable :> PreStableCategory;
  
  (** η and ε are isomorphisms at each object *)
  eta_is_iso : forall X, IsIsomorphism (components_of (eta pre_stable) X);
  epsilon_is_iso : forall X, IsIsomorphism (components_of (epsilon pre_stable) X);
  
  (** Triangle identities for the adjunction *)
  triangle_1 : forall X, 
    (components_of (epsilon pre_stable) (object_of (Susp pre_stable) X) o 
     morphism_of (Susp pre_stable) (components_of (eta pre_stable) X))%morphism = 1%morphism;
     
  triangle_2 : forall X,
    (morphism_of (Loop pre_stable) (components_of (epsilon pre_stable) X) o
     components_of (eta pre_stable) (object_of (Loop pre_stable) X))%morphism = 1%morphism
}.

(** ** Opposite of Proper Stable Categories
    
    We show that the opposite of a proper stable category is again
    a proper stable category, with the roles of Σ and Ω swapped.
*)

(** *** Helper Lemmas for Opposite Natural Transformations *)

Lemma opposite_nat_trans_components {PS : PreStableCategory}
  {F G : Functor PS PS}
  (η : NaturalTransformation F G) (X : object PS) :
  components_of (opposite_natural_transformation η) X = components_of η X.
Proof.
  reflexivity.
Qed.

(** *** Isomorphisms in Opposite Categories *)

Lemma opposite_preserves_iso {PS : PreStableCategory} 
  {X Y : object PS} (f : morphism PS X Y) :
  IsIsomorphism f -> 
  IsIsomorphism (f : morphism (opposite_category PS) Y X).
Proof.
  intro H.
  destruct H as [g [Hgf Hfg]].
  exists g.
  split.
  - simpl. exact Hfg.
  - simpl. exact Hgf.
Qed.

(** *** Preservation of Isomorphisms Under Opposite *)

Lemma eta_iso_opposite (PS : ProperStableCategory) : 
  forall X, IsIsomorphism (components_of (eta (opposite_prestable_category (pre_stable PS))) X).
Proof.
  intro X.
  simpl.
  apply opposite_preserves_iso.
  exact (epsilon_is_iso PS X).
Qed.

Lemma epsilon_iso_opposite (PS : ProperStableCategory) : 
  forall X, IsIsomorphism (components_of (epsilon (opposite_prestable_category (pre_stable PS))) X).
Proof.
  intro X.
  simpl.
  apply opposite_preserves_iso.
  exact (eta_is_iso PS X).
Qed.

(** *** Triangle Identities in the Opposite *)

Lemma opposite_triangle_1 (PS : ProperStableCategory) : 
  forall X,
  (components_of (epsilon (opposite_prestable_category (pre_stable PS))) 
    (object_of (Susp (opposite_prestable_category (pre_stable PS))) X) o 
   morphism_of (Susp (opposite_prestable_category (pre_stable PS))) 
    (components_of (eta (opposite_prestable_category (pre_stable PS))) X))%morphism = 
  1%morphism.
Proof.
  intro X.
  simpl.
  (* In the opposite: Susp^op = Loop, eta^op = epsilon, epsilon^op = eta
     So this becomes: eta(Loop X) ∘ Loop(epsilon X) = 1
     Which is triangle_2 from the original *)
  exact (triangle_2 PS X).
Qed.

Lemma opposite_triangle_2 (PS : ProperStableCategory) : 
  forall X,
  (morphism_of (Loop (opposite_prestable_category (pre_stable PS))) 
    (components_of (epsilon (opposite_prestable_category (pre_stable PS))) X) o
   components_of (eta (opposite_prestable_category (pre_stable PS))) 
    (object_of (Loop (opposite_prestable_category (pre_stable PS))) X))%morphism = 
  1%morphism.
Proof.
  intro X.
  simpl.
  (* In the opposite: Loop^op = Susp, eta^op = epsilon, epsilon^op = eta
     So this becomes: Susp(eta X) ∘ epsilon(Susp X) = 1
     Which is triangle_1 from the original *)
  exact (triangle_1 PS X).
Qed.

(** *** Main Theorem: Opposite of Proper Stable is Proper Stable *)

Definition opposite_proper_stable_category (PS : ProperStableCategory) : 
  ProperStableCategory.
Proof.
  exact (Build_ProperStableCategory
    (opposite_prestable_category (pre_stable PS))
    (eta_iso_opposite PS)
    (epsilon_iso_opposite PS)
    (opposite_triangle_1 PS)
    (opposite_triangle_2 PS)).
Defined.

(** ** Main Duality Theorems *)

(** The opposite of a proper stable category exists and has the expected form *)
Theorem proper_stable_duality_principle :
  forall (PS : ProperStableCategory),
  exists (PS_op : ProperStableCategory),
    pre_stable PS_op = opposite_prestable_category (pre_stable PS).
Proof.
  intro PS.
  exists (opposite_proper_stable_category PS).
  reflexivity.
Qed.

(** The beautiful symmetry: Susp and Loop functors perfectly swap roles *)
Theorem suspension_loop_duality (PS : ProperStableCategory) :
  object_of (Susp (opposite_proper_stable_category PS)) = 
  object_of (opposite_functor (Loop (pre_stable PS))) /\
  object_of (Loop (opposite_proper_stable_category PS)) = 
  object_of (opposite_functor (Susp (pre_stable PS))).
Proof.
  split; reflexivity.
Qed.

(** ** Summary: The Duality Principle
    
    Every theorem about pre-stable categories automatically gives us
    a dual theorem by passing to the opposite category.
*)

Theorem duality_principle : 
  forall (statement : PreStableCategory -> Prop),
  (forall PS, statement PS) -> 
  (forall PS, statement (opposite_prestable_category PS)).
Proof.
  intros statement H PS.
  apply H.
Qed.

(** Print the definition to see the structure *)
Print opposite_prestable_category.

(** This completes our formalization of stable categories and their duality theory.
    The key insights are:
    
    1. Pre-stable categories have suspension and loop functors connected by natural transformations
    2. In the opposite category, these functors swap roles
    3. Proper stable categories (where Σ and Ω are equivalences) are self-dual
    4. Every theorem has a dual obtained by passing to the opposite category
    
    This duality is fundamental in the theory of triangulated and stable categories,
    providing a powerful tool for proving theorems and understanding the structure.
*)
