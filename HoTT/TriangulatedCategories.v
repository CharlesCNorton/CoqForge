(** * Triangulated Categories in HoTT
    
    This development formalizes the theory of triangulated categories using
    the Homotopy Type Theory library. We construct pre-stable and triangulated
    categories from first principles, proving key properties constructively
    without relying on axioms (except for one fundamental property about
    suspension functors).
    
    Key contributions:
    - Distinguished triangles with built-in zero composition proofs
    - Rotation theorem for triangulated categories  
    - Triangle morphisms form a category
    - All proofs are constructive except susp_preserves_zero
    
    Author: [Your name]
    Date: [Date]
    *)

From HoTT Require Import Basics.
From HoTT.Basics Require Import Overture PathGroupoids Contractible Equivalences.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
From HoTT.Types Require Import Forall Sigma Arrow Paths.

(** We use the HoTT definition of contractibility *)
Definition IsContr (A : Type) := Contr A.

(** * Pre-Stable Categories
    
    A pre-stable category is a category equipped with:
    - A zero object (both initial and terminal)
    - Suspension and loop functors
    - Natural transformations relating identity with Loop∘Susp and Susp∘Loop
    
    This structure is fundamental for stable homotopy theory.
    *)
Record PreStableCategory := {
  C : PreCategory;
  zero : object C;
  
  (** The zero object is initial *)
  is_initial : forall X : object C, IsContr (morphism C zero X);
  
  (** The zero object is terminal *)
  is_terminal : forall X : object C, IsContr (morphism C X zero);
  
  (** Suspension functor Σ : C → C *)
  Susp : Functor C C;
  
  (** Loop functor Ω : C → C *)
  Loop : Functor C C;
  
  (** Unit of the (Loop ⊣ Susp) adjunction *)
  eta : NaturalTransformation 1%functor (Loop o Susp)%functor;
  
  (** Counit of the (Loop ⊣ Susp) adjunction *)
  epsilon : NaturalTransformation (Susp o Loop)%functor 1%functor
}.

(** * Triangulated Structure
    
    We develop the theory of triangulated categories over a pre-stable category.
    The main definitions are:
    - Zero morphisms
    - Triangles and distinguished triangles
    - Triangle morphisms and their composition
    - Rotation of triangles
    *)
Section TriangulatedStructure.
  Context {S : PreStableCategory}.

  (** ** Zero Morphisms
      
      The zero morphism X → Y is the unique composition X → 0 → Y
      through the zero object.
      *)
  Definition zero_morphism (X Y : object (C S)) : morphism (C S) X Y :=
    (@center _ (is_initial S Y) o @center _ (is_terminal S X))%morphism.

  (** Any morphism factoring through zero equals the zero morphism *)
  Lemma zero_morphism_unique (X Y : object (C S)) 
        (f : morphism (C S) X (zero S)) 
        (g : morphism (C S) (zero S) Y) :
    (g o f)%morphism = zero_morphism X Y.
  Proof.
    unfold zero_morphism.
    apply (ap011 (fun u v => (u o v)%morphism)).
    - exact (contr g)^.  (* g equals the canonical 0 → Y *)
    - exact (contr f)^.  (* f equals the canonical X → 0 *)
  Qed.

  (** ** Triangles
      
      A triangle consists of three objects and three morphisms forming:
      X --f--> Y --g--> Z --h--> ΣX
      *)
  Record Triangle := {
    X : object (C S);
    Y : object (C S);
    Z : object (C S);
    f : morphism (C S) X Y;
    g : morphism (C S) Y Z;
    h : morphism (C S) Z (object_of (Susp S) X)
  }.
  
  (** ** Distinguished Triangles
      
      A distinguished triangle is a triangle where consecutive compositions
      are zero. This captures the essential property of exact sequences
      in the triangulated setting.
      *)
  Record DistinguishedTriangle := {
    triangle : Triangle;
    
    (** g ∘ f = 0 *)
    zero_comp_1 : (g triangle o f triangle)%morphism = 
                  zero_morphism (X triangle) (Z triangle);
    
    (** h ∘ g = 0 *)
    zero_comp_2 : (h triangle o g triangle)%morphism = 
                  zero_morphism (Y triangle) (object_of (Susp S) (X triangle));
    
    (** Σf ∘ h = 0 *)
    zero_comp_3 : (morphism_of (Susp S) (f triangle) o h triangle)%morphism = 
                  zero_morphism (Z triangle) (object_of (Susp S) (Y triangle))
  }.
  
  (** ** The Identity Triangle
      
      For any object X, we have the distinguished triangle:
      X --id--> X --!--> 0 --!--> ΣX
      where ! denotes the unique morphism to/from zero.
      *)
  Definition id_triangle (X : object (C S)) : Triangle := {|
    X := X;
    Y := X;
    Z := zero S;
    f := 1%morphism;
    g := @center _ (is_terminal S X);    (* unique X → 0 *)
    h := @center _ (is_initial S (object_of (Susp S) X))  (* unique 0 → ΣX *)
  |}.
  
  (** The unique morphism 0 → 0 from is_initial is the identity *)
  Lemma zero_to_zero_is_id : 
    @center _ (is_initial S (zero S)) = 1%morphism.
  Proof.
    apply (@contr _ (is_initial S (zero S))).
  Qed.
  
  (** The initial and terminal structures on zero give the same morphism 0 → 0 *)
  Lemma zero_to_zero_initial_terminal : 
    @center _ (is_initial S (zero S)) = @center _ (is_terminal S (zero S)).
  Proof.
    apply (contr _).
  Qed.

  (** ** Proof that the identity triangle is distinguished
      
      This is a fundamental result showing that identity morphisms
      give rise to distinguished triangles.
      *)
  Definition id_distinguished (X : object (C S)) : DistinguishedTriangle.
  Proof.
    refine {| triangle := id_triangle X |}.
    - (* zero_comp_1: id ; ! = 0 *)
      simpl.
      rewrite right_identity.
      unfold zero_morphism.
      rewrite zero_to_zero_is_id.
      rewrite left_identity.
      reflexivity.
    - (* zero_comp_2: ! ; ! = 0 *)
      simpl.
      apply zero_morphism_unique.
    - (* zero_comp_3: Σ(id) ; ! = 0 *)
      simpl.
      assert (H: morphism_of (Susp S) (1%morphism : morphism (C S) X X) = 
                (1%morphism : morphism (C S) (object_of (Susp S) X) (object_of (Susp S) X))).
      { apply identity_of. }
      rewrite H.
      rewrite left_identity.
      unfold zero_morphism.
      rewrite <- zero_to_zero_initial_terminal.
      rewrite zero_to_zero_is_id.
      rewrite right_identity.
      reflexivity.
  Defined.
  
  (** ** Triangle Morphisms
      
      A morphism between triangles consists of three morphisms making
      all squares commute.
      *)
  Record TriangleMorphism (T1 T2 : Triangle) := {
    mor_X : morphism (C S) (X T1) (X T2);
    mor_Y : morphism (C S) (Y T1) (Y T2);
    mor_Z : morphism (C S) (Z T1) (Z T2);
    
    (** The f-square commutes *)
    comm_f : (mor_Y o f T1)%morphism = (f T2 o mor_X)%morphism;
    
    (** The g-square commutes *)
    comm_g : (mor_Z o g T1)%morphism = (g T2 o mor_Y)%morphism;
    
    (** The h-square commutes (with Σ applied to mor_X) *)
    comm_h : (morphism_of (Susp S) mor_X o h T1)%morphism = (h T2 o mor_Z)%morphism
  }.
  
  (** ** Helper Lemmas for Triangle Morphism Composition
      
      These lemmas verify that composition of triangle morphisms
      preserves the commutativity conditions.
      *)
  
  (** Composition preserves f-commutativity *)
  Lemma triangle_compose_f_helper 
        (T1 T2 T3 : Triangle)
        (φ : TriangleMorphism T1 T2)
        (ψ : TriangleMorphism T2 T3) :
    (mor_Y _ _ ψ o mor_Y _ _ φ o f T1)%morphism = 
    (f T3 o mor_X _ _ ψ o mor_X _ _ φ)%morphism.
  Proof.
    rewrite (associativity (C S)).
    rewrite (comm_f _ _ φ).
    transitivity ((mor_Y _ _ ψ o f T2) o mor_X _ _ φ)%morphism.
    - rewrite <- (associativity (C S)). reflexivity.
    - rewrite (comm_f _ _ ψ).
      rewrite (associativity (C S)).
      reflexivity.
  Qed.
  
  (** Composition preserves h-commutativity (using functoriality of Susp) *)
  Lemma triangle_compose_h_helper 
        (T1 T2 T3 : Triangle)
        (φ : TriangleMorphism T1 T2)
        (ψ : TriangleMorphism T2 T3) :
    ((morphism_of (Susp S) (mor_X _ _ ψ o mor_X _ _ φ)) o h T1)%morphism = 
    (h T3 o (mor_Z _ _ ψ o mor_Z _ _ φ))%morphism.
  Proof.
    (* Use functoriality of Susp *)
    assert (Hfunct: morphism_of (Susp S) (mor_X _ _ ψ o mor_X _ _ φ) =
                    (morphism_of (Susp S) (mor_X _ _ ψ) o morphism_of (Susp S) (mor_X _ _ φ))%morphism).
    { 
      rewrite <- (@composition_of _ _ (Susp S) _ _ _ (mor_X _ _ φ) (mor_X _ _ ψ)).
      reflexivity.
    }
    rewrite Hfunct.
    rewrite (associativity (C S)).
    rewrite (comm_h _ _ φ).
    rewrite <- (associativity (C S)).
    rewrite (comm_h _ _ ψ).
    rewrite (associativity (C S)).
    reflexivity.
  Qed.
  
  (** ** Composition of Triangle Morphisms
      
      Triangle morphisms compose componentwise, and the composition
      preserves all commutativity conditions.
      *)
  Definition triangle_morphism_compose 
        (T1 T2 T3 : Triangle)
        (φ : TriangleMorphism T1 T2)
        (ψ : TriangleMorphism T2 T3) :
    TriangleMorphism T1 T3.
  Proof.
    apply Build_TriangleMorphism with
      (mor_X := (mor_X _ _ ψ o mor_X _ _ φ)%morphism)
      (mor_Y := (mor_Y _ _ ψ o mor_Y _ _ φ)%morphism)
      (mor_Z := (mor_Z _ _ ψ o mor_Z _ _ φ)%morphism).
    - (* comm_f *) 
      rewrite <- (associativity (C S)).
      apply (triangle_compose_f_helper T1 T2 T3 φ ψ).
    - (* comm_g *) 
      rewrite (associativity (C S)).
      rewrite (comm_g _ _ φ).
      transitivity ((mor_Z _ _ ψ o g T2) o mor_Y _ _ φ)%morphism.
      + rewrite <- (associativity (C S)). reflexivity.
      + rewrite (comm_g _ _ ψ).
        rewrite (associativity (C S)).
        reflexivity.
    - (* comm_h *)
      apply (triangle_compose_h_helper T1 T2 T3 φ ψ).
  Defined.
  
  (** ** Rotation of Triangles
      
      The rotation operation is fundamental in triangulated categories.
      Given a triangle X → Y → Z → ΣX, its rotation is Y → Z → ΣX → ΣY.
      *)
  Definition rotate_triangle (T : Triangle) : Triangle := {|
    X := Y T;
    Y := Z T;
    Z := object_of (Susp S) (X T);
    f := g T;
    g := h T;
    h := morphism_of (Susp S) (f T)
  |}.
  
  (** ** Fundamental Axiom
      
      The suspension functor preserves zero morphisms. This should ideally
      be part of the structure of a stable category, but we axiomatize it
      here for simplicity.
      *)
  Axiom susp_preserves_zero : forall (X Y : object (C S)),
    morphism_of (Susp S) (zero_morphism X Y) = 
    zero_morphism (object_of (Susp S) X) (object_of (Susp S) Y).
    
  (** ** Rotation Theorem
      
      A fundamental result: rotation preserves the property of being
      a distinguished triangle. This is one of the key axioms (TR2)
      of triangulated categories.
      *)
  Theorem rotate_distinguished (T : DistinguishedTriangle) :
    DistinguishedTriangle.
  Proof.
    refine {| triangle := rotate_triangle (triangle T) |}.
    - (* zero_comp_1: h ∘ g = 0 *)
      simpl. exact (zero_comp_2 T).
    - (* zero_comp_2: Σf ∘ h = 0 *)
      simpl. exact (zero_comp_3 T).
    - (* zero_comp_3: Σg ∘ Σf = 0 *)
      simpl.
      rewrite <- (composition_of (Susp S) _ _ _ (f (triangle T)) (g (triangle T))).
      rewrite (zero_comp_1 T).
      apply susp_preserves_zero.
  Defined.
  
  (** ** Identity Triangle Morphism
      
      The identity morphism on a triangle has identity components.
      *)
  Definition id_triangle_morphism (T : Triangle) : TriangleMorphism T T.
  Proof.
    apply Build_TriangleMorphism with
      (mor_X := 1%morphism)
      (mor_Y := 1%morphism)
      (mor_Z := 1%morphism).
    - (* comm_f *) rewrite left_identity. rewrite right_identity. reflexivity.
    - (* comm_g *) rewrite left_identity. rewrite right_identity. reflexivity.
    - (* comm_h *) rewrite (identity_of (Susp S)). rewrite left_identity. rewrite right_identity. reflexivity.
  Defined.
  
  (** ** Triangle Morphism Equality
      
      Two triangle morphisms are equal when all their components are equal.
      The proof obligations are propositions, so we can use proof irrelevance.
      *)
  Lemma triangle_morphism_eq (T1 T2 : Triangle) (φ ψ : TriangleMorphism T1 T2) :
    mor_X _ _ φ = mor_X _ _ ψ ->
    mor_Y _ _ φ = mor_Y _ _ ψ ->
    mor_Z _ _ φ = mor_Z _ _ ψ ->
    φ = ψ.
  Proof.
    destruct φ as [φX φY φZ φf φg φh].
    destruct ψ as [ψX ψY ψZ ψf ψg ψh].
    simpl. intros HX HY HZ.
    destruct HX, HY, HZ.
    (* Proof obligations are propositions *)
    assert (Hf: φf = ψf) by apply path_ishprop.
    assert (Hg: φg = ψg) by apply path_ishprop.
    assert (Hh: φh = ψh) by apply path_ishprop.
    destruct Hf, Hg, Hh.
    reflexivity.
  Qed.
  
  (** ** Category Laws for Triangle Morphisms
      
      We prove that triangles with their morphisms form a category.
      *)
  
  (** Left identity law *)
  Lemma triangle_morphism_left_id (T1 T2 : Triangle) (φ : TriangleMorphism T1 T2) :
    triangle_morphism_compose T1 T2 T2 φ (id_triangle_morphism T2) = φ.
  Proof.
    apply triangle_morphism_eq.
    - simpl. apply left_identity.
    - simpl. apply left_identity.
    - simpl. apply left_identity.
  Qed.
  
  (** Right identity law *)
  Lemma triangle_morphism_right_id (T1 T2 : Triangle) (φ : TriangleMorphism T1 T2) :
    triangle_morphism_compose T1 T1 T2 (id_triangle_morphism T1) φ = φ.
  Proof.
    apply triangle_morphism_eq.
    - simpl. apply right_identity.
    - simpl. apply right_identity.
    - simpl. apply right_identity.
  Qed.
  
  (** Associativity law *)
  Lemma triangle_morphism_assoc (T1 T2 T3 T4 : Triangle) 
        (φ : TriangleMorphism T1 T2)
        (ψ : TriangleMorphism T2 T3)
        (χ : TriangleMorphism T3 T4) :
    triangle_morphism_compose T1 T2 T4 φ (triangle_morphism_compose T2 T3 T4 ψ χ) =
    triangle_morphism_compose T1 T3 T4 (triangle_morphism_compose T1 T2 T3 φ ψ) χ.
  Proof.
    apply triangle_morphism_eq.
    - simpl. apply associativity.
    - simpl. apply associativity.
    - simpl. apply associativity.
  Qed.
  
  (** ** Main Theorem: Triangles Form a Category
      
      This theorem packages the category laws into a single statement,
      establishing that triangles with their morphisms satisfy all the
      requirements of a category.
      *)
  Theorem triangles_form_category : 
    (* Composition is associative *)
    (forall (T1 T2 T3 T4 : Triangle) 
            (φ : TriangleMorphism T1 T2)
            (ψ : TriangleMorphism T2 T3)
            (χ : TriangleMorphism T3 T4),
      triangle_morphism_compose T1 T2 T4 φ (triangle_morphism_compose T2 T3 T4 ψ χ) =
      triangle_morphism_compose T1 T3 T4 (triangle_morphism_compose T1 T2 T3 φ ψ) χ) /\
    (* Left identity *)
    (forall (T1 T2 : Triangle) (φ : TriangleMorphism T1 T2),
      triangle_morphism_compose T1 T2 T2 φ (id_triangle_morphism T2) = φ) /\
    (* Right identity *)
    (forall (T1 T2 : Triangle) (φ : TriangleMorphism T1 T2),
      triangle_morphism_compose T1 T1 T2 (id_triangle_morphism T1) φ = φ).
  Proof.
    split; [|split].
    - exact triangle_morphism_assoc.
    - exact triangle_morphism_left_id.
    - exact triangle_morphism_right_id.
  Qed.
  
End TriangulatedStructure.

(** * Summary
    
    We have formalized the basic theory of triangulated categories in HoTT:
    
    1. Pre-stable categories with zero objects and suspension/loop functors
    2. Distinguished triangles defined by zero composition properties
    3. The identity triangle is distinguished (constructive proof)
    4. Triangle morphisms and their composition
    5. Rotation preserves distinguished triangles
    6. Triangles form a category
    
    The development is mostly constructive, with only one axiom
    (susp_preserves_zero) that should ideally be part of the
    definition of a stable category.
    
    Future work could include:
    - The octahedral axiom (TR4)
    - Mapping cone construction
    - Localization and derived categories
    - Connection to stable ∞-categories
    *)
