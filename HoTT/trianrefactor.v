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

(** * Pre-Stable Categories
    
    A pre-stable category is an additive category equipped with
    suspension and loop functors that are additive and adjoint.
    *)

Record PreStableCategory := {
  (** Underlying additive category *)
  A :> AdditiveCategory;
  
  (** Suspension functor Σ : A → A *)
  Susp : AdditiveFunctor A A;
  
  (** Loop functor Ω : A → A *)
  Loop : AdditiveFunctor A A;
  
  (** Unit of the (Loop ⊣ Susp) adjunction *)
  eta : NaturalTransformation 1%functor (Loop o Susp)%functor;
  
  (** Counit of the (Loop ⊣ Susp) adjunction *)
  epsilon : NaturalTransformation (Susp o Loop)%functor 1%functor
}.

(** * Suspension Preserves Zero Morphisms *)

Theorem susp_preserves_zero_morphisms {S : PreStableCategory} (X Y : object S) :
  morphism_of (Susp S) (zero_morphism (add_zero S) X Y) = 
  zero_morphism (add_zero S) (object_of (Susp S) X) (object_of (Susp S) Y).
Proof.
  (** This follows immediately from our general theorem *)
  apply additive_functor_preserves_zero_morphisms.
Qed.

(** * Triangles in Pre-Stable Categories
    
    A triangle consists of three objects and three morphisms forming:
    X --f--> Y --g--> Z --h--> ΣX
    *)

Section Triangles.
  Context {S : PreStableCategory}.
  
  Record Triangle := {
    X : object S;
    Y : object S;
    Z : object S;
    f : morphism S X Y;
    g : morphism S Y Z;
    h : morphism S Z (object_of (Susp S) X)
  }.
  
End Triangles.

(** * Distinguished Triangles
    
    A distinguished triangle is a triangle where consecutive compositions
    are zero. This captures the exactness property.
    *)

Section DistinguishedTriangles.
  Context {S : PreStableCategory}.
  
  Record DistinguishedTriangle := {
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
  
End DistinguishedTriangles.

(** * The Identity Triangle
    
    For any object X, we have the distinguished triangle:
    X --id--> X --!--> 0 --!--> ΣX
    where ! denotes the unique morphism to/from zero.
    *)

Section IdentityTriangle.
  Context {S : PreStableCategory}.
  
  Definition id_triangle (X : object S) : @Triangle S := {|
    X := X;
    Y := X;
    Z := @zero _ (add_zero S);
    f := 1%morphism;
    g := @center _ (@is_terminal _ (add_zero S) X);
    h := @center _ (@is_initial _ (add_zero S) (object_of (Susp S) X))
  |}.
  
End IdentityTriangle.

(** * Lemmas about zero morphisms
    
    These will help prove the identity triangle is distinguished.
    *)

Section ZeroLemmas.
  Context {S : PreStableCategory}.
  
  (** The unique morphism from 0 to 0 is the identity *)
  Lemma zero_to_zero_is_id : 
    @center _ (@is_initial _ (add_zero S) (@zero _ (add_zero S))) = 1%morphism.
  Proof.
    apply (@contr _ (@is_initial _ (add_zero S) (@zero _ (add_zero S)))).
  Qed.
  
  (** Composition with terminal morphism gives zero morphism *)
  Lemma terminal_comp_is_zero (X Y : object S) 
    (f : morphism S X (@zero _ (add_zero S))) :
    (@center _ (@is_initial _ (add_zero S) Y) o f)%morphism = 
    zero_morphism (add_zero S) X Y.
  Proof.
    apply morphism_through_zero_is_zero.
  Qed.
  
End ZeroLemmas.

(** * Identity laws for morphisms
    
    Basic category theory laws.
    *)

Section MorphismIdentityLaws.
  Context {C : PreCategory}.
  
  Lemma morphism_right_identity {X Y : object C} (f : morphism C X Y) :
    (f o 1)%morphism = f.
  Proof.
    apply Category.Core.right_identity.
  Qed.
  
  Lemma morphism_left_identity {X Y : object C} (f : morphism C X Y) :
    (1 o f)%morphism = f.
  Proof.
    apply Category.Core.left_identity.
  Qed.
  
End MorphismIdentityLaws.

Lemma zero_morphism_from_zero {S : PreStableCategory} (Y : object S) :
  zero_morphism (add_zero S) (@zero _ (add_zero S)) Y =
  @center _ (@is_initial _ (add_zero S) Y).
Proof.
  unfold zero_morphism.
  (* We have: (0→Y) ∘ (0→0)_terminal = (0→Y) *)
  (* We know that any morphism 0→0 is identity *)
  assert (H: @center _ (@is_terminal _ (add_zero S) (@zero _ (add_zero S))) = 
            (1%morphism : morphism S (@zero _ (add_zero S)) (@zero _ (add_zero S)))).
  { 
    (* All morphisms 0→0 are equal, and id is one of them *)
    apply (@contr _ (@is_terminal _ (add_zero S) (@zero _ (add_zero S)))).
  }
  rewrite H.
  apply morphism_right_identity.
Qed.

Lemma terminal_zero_to_zero_is_id {S : PreStableCategory} : 
  @center _ (@is_terminal _ (add_zero S) (@zero _ (add_zero S))) = 
  (1%morphism : morphism S (@zero _ (add_zero S)) (@zero _ (add_zero S))).
Proof.
  (* All morphisms 0 → 0 are equal *)
  apply terminal_morphism_unique.
  apply (@is_terminal _ (add_zero S) (@zero _ (add_zero S))).
Qed.

(** * The Identity Triangle is Distinguished
    
    We prove that for any object X, the triangle X --id--> X --!--> 0 --!--> ΣX
    is distinguished.
    *)

Section IdentityTriangleDistinguished.
  Context {S : PreStableCategory}.
  
  (** Suspension of identity is identity *)
  Lemma susp_preserves_identity (X : object S) :
    morphism_of (Susp S) (1%morphism : morphism S X X) = 
    (1%morphism : morphism S (object_of (Susp S) X) (object_of (Susp S) X)).
  Proof.
    apply (identity_of (Susp S)).
  Qed.
  
  (** Main theorem: The identity triangle is distinguished *)
  Theorem id_triangle_distinguished (X : object S) : 
    @DistinguishedTriangle S.
  Proof.
    refine {| triangle := id_triangle X |}.
    
    (** First condition: g ∘ f = 0, i.e., terminal ∘ id = 0 *)
    - simpl.
      rewrite morphism_right_identity.
      unfold zero_morphism.
      rewrite zero_to_zero_is_id.
      rewrite morphism_left_identity.
      reflexivity.
    
    (** Second condition: h ∘ g = 0, i.e., initial ∘ terminal = 0 *)
    - simpl.
      apply terminal_comp_is_zero.
    
    (** Third condition: Σf ∘ h = 0, i.e., Σ(id) ∘ initial = 0 *)
    - simpl.
      rewrite susp_preserves_identity.
      rewrite morphism_left_identity.
      rewrite <- zero_morphism_from_zero.
      reflexivity.
  Defined.
  
End IdentityTriangleDistinguished.

(** * Triangle Morphisms
    
    A morphism between triangles consists of three morphisms making
    all squares commute.
    *)

Section TriangleMorphism.
  Context {S : PreStableCategory}.
  
  Record TriangleMorphism (T1 T2 : @Triangle S) := {
    mor_X : morphism S (X T1) (X T2);
    mor_Y : morphism S (Y T1) (Y T2);
    mor_Z : morphism S (Z T1) (Z T2);
    
    (** The f-square commutes *)
    comm_f : (mor_Y o f T1)%morphism = (f T2 o mor_X)%morphism;
    
    (** The g-square commutes *)
    comm_g : (mor_Z o g T1)%morphism = (g T2 o mor_Y)%morphism;
    
    (** The h-square commutes (with Σ applied to mor_X) *)
    comm_h : (morphism_of (Susp S) mor_X o h T1)%morphism = 
             (h T2 o mor_Z)%morphism
  }.
  
End TriangleMorphism.

(** * Identity Triangle Morphism
    
    The identity morphism on a triangle has identity components.
    *)

Section IdentityTriangleMorphism.
  Context {S : PreStableCategory}.
  
  Definition id_triangle_morphism (T : @Triangle S) : TriangleMorphism T T.
  Proof.
    refine {| 
      mor_X := 1%morphism;
      mor_Y := 1%morphism;
      mor_Z := 1%morphism
    |}.
    - (* comm_f *) 
      rewrite morphism_left_identity.
      rewrite morphism_right_identity.
      reflexivity.
    - (* comm_g *) 
      rewrite morphism_left_identity.
      rewrite morphism_right_identity.
      reflexivity.
    - (* comm_h *)
      rewrite (identity_of (Susp S)).
      rewrite morphism_left_identity.
      rewrite morphism_right_identity.
      reflexivity.
  Defined.
  
End IdentityTriangleMorphism.

(** * Composition of Triangle Morphisms
    
    Triangle morphisms compose componentwise.
    *)

Section TriangleMorphismComposition.
  Context {S : PreStableCategory}.
  
  Lemma morphism_associativity {W X Y Z : object S} 
    (f : morphism S W X) (g : morphism S X Y) (h : morphism S Y Z) :
    ((h o g) o f)%morphism = (h o (g o f))%morphism.
  Proof.
    apply Category.Core.associativity.
  Qed.
  
  Definition triangle_morphism_compose 
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
    - (* comm_f *)
      rewrite morphism_associativity.
      rewrite (comm_f _ _ φ).
      rewrite <- morphism_associativity.
      rewrite (comm_f _ _ ψ).
      rewrite morphism_associativity.
      reflexivity.
    - (* comm_g *)
      rewrite morphism_associativity.
      rewrite (comm_g _ _ φ).
      rewrite <- morphism_associativity.
      rewrite (comm_g _ _ ψ).
      rewrite morphism_associativity.
      reflexivity.
    - (* comm_h *)
      simpl.
      rewrite (composition_of (Susp S)).
      rewrite morphism_associativity.
      rewrite (comm_h _ _ φ).
      rewrite <- morphism_associativity.
      rewrite (comm_h _ _ ψ).
      rewrite morphism_associativity.
      reflexivity.
  Defined.
  
End TriangleMorphismComposition.

(** * Left Identity Law for Triangle Morphisms *)

Section TriangleMorphismLeftIdentity.
  Context {S : PreStableCategory}.
  
  (** First we need a lemma about equality of triangle morphisms *)
  Lemma triangle_morphism_eq (T1 T2 : @Triangle S) 
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
    (* The commutativity proofs are propositions *)
    assert (Hf: φf = ψf) by apply path_ishprop.
    assert (Hg: φg = ψg) by apply path_ishprop.
    assert (Hh: φh = ψh) by apply path_ishprop.
    destruct Hf, Hg, Hh.
    reflexivity.
  Qed.
  
  (** Left identity law *)
  Lemma triangle_morphism_left_id (T1 T2 : @Triangle S) 
    (φ : TriangleMorphism T1 T2) :
    triangle_morphism_compose T1 T2 T2 φ (id_triangle_morphism T2) = φ.
  Proof.
    apply triangle_morphism_eq.
    - simpl. apply morphism_left_identity.
    - simpl. apply morphism_left_identity.  
    - simpl. apply morphism_left_identity.
  Qed.
  
End TriangleMorphismLeftIdentity.

(** * Right Identity Law for Triangle Morphisms *)

Section TriangleMorphismRightIdentity.
  Context {S : PreStableCategory}.
  
  (** Right identity law *)
  Lemma triangle_morphism_right_id (T1 T2 : @Triangle S) 
    (φ : TriangleMorphism T1 T2) :
    triangle_morphism_compose T1 T1 T2 (id_triangle_morphism T1) φ = φ.
  Proof.
    apply triangle_morphism_eq.
    - simpl. apply morphism_right_identity.
    - simpl. apply morphism_right_identity.
    - simpl. apply morphism_right_identity.
  Qed.
  
End TriangleMorphismRightIdentity.

(** * Associativity Law for Triangle Morphisms *)

(** This is defined outside of sections so it's globally available *)
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

(** * Main Theorem: Triangles Form a Category *)

Theorem triangles_form_category {S : PreStableCategory} : 
  (* Composition is associative *)
  (forall (T1 T2 T3 T4 : @Triangle S) 
          (φ : TriangleMorphism T1 T2)
          (ψ : TriangleMorphism T2 T3)
          (χ : TriangleMorphism T3 T4),
    triangle_morphism_compose T1 T2 T4 φ (triangle_morphism_compose T2 T3 T4 ψ χ) =
    triangle_morphism_compose T1 T3 T4 (triangle_morphism_compose T1 T2 T3 φ ψ) χ) /\
  (* Left identity *)
  (forall (T1 T2 : @Triangle S) (φ : TriangleMorphism T1 T2),
    triangle_morphism_compose T1 T2 T2 φ (id_triangle_morphism T2) = φ) /\
  (* Right identity *)
  (forall (T1 T2 : @Triangle S) (φ : TriangleMorphism T1 T2),
    triangle_morphism_compose T1 T1 T2 (id_triangle_morphism T1) φ = φ).
Proof.
  split; [|split].
  - intros. apply triangle_morphism_assoc.
  - intros. apply triangle_morphism_left_id.
  - intros. apply triangle_morphism_right_id.
Qed.

(** * Rotation of Triangles
    
    Given a triangle X → Y → Z → ΣX, its rotation is Y → Z → ΣX → ΣY.
    *)

Section RotateTriangle.
  Context {S : PreStableCategory}.
  
  Definition rotate_triangle (T : @Triangle S) : @Triangle S := {|
    X := Y T;
    Y := Z T;
    Z := object_of (Susp S) (X T);
    f := g T;
    g := h T;
    h := morphism_of (Susp S) (f T)
  |}.
  
End RotateTriangle.

(** * Rotation Preserves Distinguished Triangles
    
    Theorem TR2: If T is distinguished, then its rotation is distinguished.
    *)

Section RotateDistinguished.
  Context {S : PreStableCategory}.
  
  Theorem rotate_distinguished (T : @DistinguishedTriangle S) :
    @DistinguishedTriangle S.
  Proof.
    refine {| triangle := rotate_triangle (triangle T) |}.
    - (* zero_comp_1: h ∘ g = 0 in rotated triangle *)
      simpl.
      exact (zero_comp_2 T).
    - (* zero_comp_2: Σf ∘ h = 0 in rotated triangle *)
      simpl.
      exact (zero_comp_3 T).
    - (* zero_comp_3: Σg ∘ Σf = 0 in rotated triangle *)
      simpl.
      rewrite <- (composition_of (Susp S)).
      rewrite (zero_comp_1 T).
      apply susp_preserves_zero_morphisms.
  Defined.
  
End RotateDistinguished.

(** * TR1: Existence of Distinguished Triangles
    
    For any morphism f : X → Y, there exists a distinguished triangle
    of the form X → Y → Z → ΣX.
    *)

Section TR1.
  Context {S : PreStableCategory}.
  
  (** The statement of TR1: every morphism extends to a distinguished triangle *)
  Definition TR1_statement : Type :=
    forall (X Y : object S) (f : morphism S X Y),
    { Z : object S &
    { g : morphism S Y Z &
    { h : morphism S Z (object_of (Susp S) X) &
      @DistinguishedTriangle S }}}.
  
  (** Helper: The triangle constructed from f, g, h *)
  Definition triangle_from_morphisms 
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
  
End TR1.

(** * Mapping Cone Construction
    
    The cone of a morphism f : X → Y is the biproduct Y ⊕ ΣX.
    *)

Section MappingCone.
  Context {S : PreStableCategory}.
  
  (** The cone object is the biproduct Y ⊕ ΣX *)
  Definition cone {X Y : object S} (f : morphism S X Y) : object S :=
    @biproduct_obj _ _ _ (add_biproduct S Y (object_of (Susp S) X)).
  
  (** The inclusion Y → Cone(f) *)
  Definition cone_in {X Y : object S} (f : morphism S X Y) : 
    morphism S Y (cone f) :=
    @inl _ _ _ (add_biproduct S Y (object_of (Susp S) X)).
  
  (** The projection Cone(f) → ΣX *)
  Definition cone_out {X Y : object S} (f : morphism S X Y) : 
    morphism S (cone f) (object_of (Susp S) X) :=
    @outr _ _ _ (add_biproduct S Y (object_of (Susp S) X)).
  
End MappingCone.

(** * Cone Triangle
    
    The triangle X → Y → Cone(f) → ΣX constructed from a morphism f.
    *)

Section ConeTriangle.
  Context {S : PreStableCategory}.
  
  (** The cone triangle for a morphism f : X → Y *)
  Definition cone_triangle {X Y : object S} (f : morphism S X Y) : @Triangle S :=
  {|
    X := X;
    Y := Y;
    Z := cone f;
    f := f;
    g := cone_in f;
    h := cone_out f
  |}.
  
End ConeTriangle.

(** * Cone Triangle is Distinguished
    
    We attempt to prove that the cone triangle is distinguished.
    *)

Section ConeDistinguished.
  Context {S : PreStableCategory}.
  
  (** First, let's check what we need to prove *)
  Lemma cone_distinguished_conditions {X Y : object S} (f : morphism S X Y) :
    (* Condition 1: cone_in ∘ f = 0 *)
    ((cone_in f) o f)%morphism = zero_morphism (add_zero S) X (cone f) ->
    (* Condition 2: cone_out ∘ cone_in = 0 *)
    ((cone_out f) o (cone_in f))%morphism = zero_morphism (add_zero S) Y (object_of (Susp S) X) ->
    (* Condition 3: Σf ∘ cone_out = 0 *)
    (morphism_of (Susp S) f o (cone_out f))%morphism = zero_morphism (add_zero S) (cone f) (object_of (Susp S) Y) ->
    @DistinguishedTriangle S.
  Proof.
    intros H1 H2 H3.
    refine {| triangle := cone_triangle f |}.
    - exact H1.
    - exact H2.
    - exact H3.
  Defined.
  
  (** Condition 2 follows from biproduct axioms *)
  Lemma cone_out_cone_in_zero {X Y : object S} (f : morphism S X Y) :
    ((cone_out f) o (cone_in f))%morphism = zero_morphism (add_zero S) Y (object_of (Susp S) X).
  Proof.
    unfold cone_out, cone_in.
    apply (@mixed_r _ _ _ (add_biproduct S Y (object_of (Susp S) X)) (add_zero S) 
                          (add_biproduct_props S Y (object_of (Susp S) X))).
  Qed.
  
End ConeDistinguished.

(** * Conditions 1 and 3 for Cone Triangle
    
    Let's examine what conditions 1 and 3 require.
    *)

Section ConeConditions13.
  Context {S : PreStableCategory}.
  
  (** Condition 1: cone_in ∘ f should equal zero *)
  Lemma cone_condition_1_statement {X Y : object S} (f : morphism S X Y) :
    Type.
  Proof.
    exact (((cone_in f) o f)%morphism = zero_morphism (add_zero S) X (cone f)).
  Defined.
  
  (** Let's see what cone_in ∘ f actually is *)
  Lemma cone_in_f_unfold {X Y : object S} (f : morphism S X Y) :
    ((cone_in f) o f)%morphism = 
    (@inl _ _ _ (add_biproduct S Y (object_of (Susp S) X)) o f)%morphism.
  Proof.
    reflexivity.
  Qed.
  
  (** For condition 1 to hold, we need inl ∘ f = 0, which is NOT generally true *)
  
  (** Condition 3: Σf ∘ cone_out should equal zero *)
  Lemma cone_condition_3_statement {X Y : object S} (f : morphism S X Y) :
    Type.
  Proof.
    exact ((morphism_of (Susp S) f o (cone_out f))%morphism = 
           zero_morphism (add_zero S) (cone f) (object_of (Susp S) Y)).
  Defined.
  
  (** Let's see what Σf ∘ cone_out actually is *)
  Lemma susp_f_cone_out_unfold {X Y : object S} (f : morphism S X Y) :
    (morphism_of (Susp S) f o (cone_out f))%morphism =
    (morphism_of (Susp S) f o @outr _ _ _ (add_biproduct S Y (object_of (Susp S) X)))%morphism.
  Proof.
    reflexivity.
  Qed.
  
End ConeConditions13.

(** * The h Morphism for the Cone Triangle
    
    We need to define h : Cone(f) → ΣX carefully using the universal property.
    *)

Section ConeHMorphism.
  Context {S : PreStableCategory}.
  
  (** First component: Y → ΣX should be zero *)
  Definition cone_h_component1 {X Y : object S} (f : morphism S X Y) :
    morphism S Y (object_of (Susp S) X).
  Proof.
    exact (zero_morphism (add_zero S) Y (object_of (Susp S) X)).
  Defined.
  
  (** Second component: ΣX → ΣX via identity *)
  Definition cone_h_component2 {X Y : object S} (f : morphism S X Y) :
    morphism S (object_of (Susp S) X) (object_of (Susp S) X).
  Proof.
    exact 1%morphism.
  Defined.
  
End ConeHMorphism.

(** * Constructing h via Universal Property of Biproduct
    
    Use the coproduct universal property to get h : Cone(f) → ΣX.
    *)

Section ConeHUniversal.
  Context {S : PreStableCategory}.
  
  Definition cone_h {X Y : object S} (f : morphism S X Y) : 
    morphism S (cone f) (object_of (Susp S) X).
  Proof.
    unfold cone.
    (* Apply the coproduct part of the biproduct universal property *)
    destruct (add_biproduct_universal S Y (object_of (Susp S) X)) as [coprod_univ prod_univ].
    (* Now apply coprod_univ *)
    pose (univ := coprod_univ (object_of (Susp S) X)
                              (cone_h_component1 f)
                              (cone_h_component2 f)).
    (* Extract the morphism using .1 *)
    exact ((@center _ univ).1).
  Defined.
  
End ConeHUniversal.

(** * Proper Cone Triangle with Correct h Morphism
    
    Now we can define the cone triangle using our constructed h.
    *)

Section ProperConeTriangle.
  Context {S : PreStableCategory}.
  
  (** The proper cone triangle for a morphism f : X → Y *)
  Definition proper_cone_triangle {X Y : object S} (f : morphism S X Y) : @Triangle S :=
  {|
    X := X;
    Y := Y;
    Z := cone f;
    f := f;
    g := cone_in f;
    h := cone_h f
  |}.
  
End ProperConeTriangle.
