From HoTT Require Import Basics.
From HoTT.Basics Require Import Overture PathGroupoids Contractible Equivalences.
From HoTT.Types Require Import Forall Sigma Arrow Paths Sum Prod Unit Empty.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
From HoTT.Categories Require Import InitialTerminalCategory.
From HoTT.Categories.Functor Require Import Identity Composition.
From HoTT.Spaces Require Import Int.

Record ZeroObject (C : PreCategory) := {
  zero : object C;
  is_initial : forall X, Contr (morphism C zero X);
  is_terminal : forall X, Contr (morphism C X zero)
}.

Section ZeroMorphism.
  Context {C : PreCategory} (Z : ZeroObject C).
  
  Definition zero_morphism (X Y : object C) : morphism C X Y :=
    (@center _ (@is_initial _ Z Y) o @center _ (@is_terminal _ Z X))%morphism.
    
End ZeroMorphism.

Record Biproduct {C : PreCategory} (X Y : object C) := {
  biproduct_obj : object C;
  
  inl : morphism C X biproduct_obj;
  inr : morphism C Y biproduct_obj;
  
  outl : morphism C biproduct_obj X;
  outr : morphism C biproduct_obj Y
}.

Record IsBiproduct {C : PreCategory} {X Y : object C} 
                   (B : Biproduct X Y) (Z : ZeroObject C) := {
  beta_l : (@outl _ _ _ B o @inl _ _ _ B = 1)%morphism;
  beta_r : (@outr _ _ _ B o @inr _ _ _ B = 1)%morphism;
  
  mixed_l : (@outl _ _ _ B o @inr _ _ _ B)%morphism = zero_morphism Z Y X;
  mixed_r : (@outr _ _ _ B o @inl _ _ _ B)%morphism = zero_morphism Z X Y
}.

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

Record AdditiveCategory := {
  cat :> PreCategory;
  
  add_zero : ZeroObject cat;
  
  add_biproduct : forall (X Y : object cat), Biproduct X Y;
  
  add_biproduct_props : forall (X Y : object cat), 
    IsBiproduct (add_biproduct X Y) add_zero;
  
  add_biproduct_universal : forall (X Y : object cat),
    BiproductUniversal (add_biproduct X Y)
}.

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

Lemma initial_morphism_unique {C : PreCategory} 
  (I : object C) (X : object C)
  (H_initial : Contr (morphism C I X))
  (f g : morphism C I X) : f = g.
Proof.
  transitivity (@center _ H_initial).
  - exact (@contr _ H_initial f)^.
  - exact (@contr _ H_initial g).
Qed.

Lemma terminal_morphism_unique {C : PreCategory} 
  (X : object C) (T : object C)
  (H_terminal : Contr (morphism C X T))
  (f g : morphism C X T) : f = g.
Proof.
  transitivity (@center _ H_terminal).
  - exact (@contr _ H_terminal f)^.
  - exact (@contr _ H_terminal g).
Qed.

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

Record PreStableCategory := {
  A :> AdditiveCategory;
  
  Susp : AdditiveFunctor A A;
  
  Loop : AdditiveFunctor A A;
  
  eta : NaturalTransformation 1%functor (Loop o Susp)%functor;
  
  epsilon : NaturalTransformation (Susp o Loop)%functor 1%functor
}.

Theorem susp_preserves_zero_morphisms {S : PreStableCategory} (X Y : object S) :
  morphism_of (Susp S) (zero_morphism (add_zero S) X Y) = 
  zero_morphism (add_zero S) (object_of (Susp S) X) (object_of (Susp S) Y).
Proof.
  apply additive_functor_preserves_zero_morphisms.
Qed.

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

Section DistinguishedTriangles.
  Context {S : PreStableCategory}.
  
  Record DistinguishedTriangle := {
    triangle : Triangle;
    
    zero_comp_1 : (g triangle o f triangle)%morphism = 
                  zero_morphism (add_zero S) (X triangle) (Z triangle);
    
    zero_comp_2 : (h triangle o g triangle)%morphism = 
                  zero_morphism (add_zero S) (Y triangle) (object_of (Susp S) (X triangle));
    
    zero_comp_3 : (morphism_of (Susp S) (f triangle) o h triangle)%morphism = 
                  zero_morphism (add_zero S) (Z triangle) (object_of (Susp S) (Y triangle))
  }.
  
End DistinguishedTriangles.

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

Section ZeroLemmas.
  Context {S : PreStableCategory}.
  
  Lemma zero_to_zero_is_id : 
    @center _ (@is_initial _ (add_zero S) (@zero _ (add_zero S))) = 1%morphism.
  Proof.
    apply (@contr _ (@is_initial _ (add_zero S) (@zero _ (add_zero S)))).
  Qed.
  
  Lemma terminal_comp_is_zero (X Y : object S) 
    (f : morphism S X (@zero _ (add_zero S))) :
    (@center _ (@is_initial _ (add_zero S) Y) o f)%morphism = 
    zero_morphism (add_zero S) X Y.
  Proof.
    apply morphism_through_zero_is_zero.
  Qed.
  
End ZeroLemmas.

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
  assert (H: @center _ (@is_terminal _ (add_zero S) (@zero _ (add_zero S))) = 
            (1%morphism : morphism S (@zero _ (add_zero S)) (@zero _ (add_zero S)))).
  { 
    apply (@contr _ (@is_terminal _ (add_zero S) (@zero _ (add_zero S)))).
  }
  rewrite H.
  apply morphism_right_identity.
Qed.

Lemma terminal_zero_to_zero_is_id {S : PreStableCategory} : 
  @center _ (@is_terminal _ (add_zero S) (@zero _ (add_zero S))) = 
  (1%morphism : morphism S (@zero _ (add_zero S)) (@zero _ (add_zero S))).
Proof.
  apply terminal_morphism_unique.
  apply (@is_terminal _ (add_zero S) (@zero _ (add_zero S))).
Qed.

Section IdentityTriangleDistinguished.
  Context {S : PreStableCategory}.
  
  Lemma susp_preserves_identity (X : object S) :
    morphism_of (Susp S) (1%morphism : morphism S X X) = 
    (1%morphism : morphism S (object_of (Susp S) X) (object_of (Susp S) X)).
  Proof.
    apply (identity_of (Susp S)).
  Qed.
  
  Theorem id_triangle_distinguished (X : object S) : 
    @DistinguishedTriangle S.
  Proof.
    refine {| triangle := id_triangle X |}.
    
    - simpl.
      rewrite morphism_right_identity.
      unfold zero_morphism.
      rewrite zero_to_zero_is_id.
      rewrite morphism_left_identity.
      reflexivity.
    
    - simpl.
      apply terminal_comp_is_zero.
    
    - simpl.
      rewrite susp_preserves_identity.
      rewrite morphism_left_identity.
      rewrite <- zero_morphism_from_zero.
      reflexivity.
  Defined.
  
End IdentityTriangleDistinguished.

Section TriangleMorphism.
  Context {S : PreStableCategory}.
  
  Record TriangleMorphism (T1 T2 : @Triangle S) := {
    mor_X : morphism S (X T1) (X T2);
    mor_Y : morphism S (Y T1) (Y T2);
    mor_Z : morphism S (Z T1) (Z T2);
    
    comm_f : (mor_Y o f T1)%morphism = (f T2 o mor_X)%morphism;
    
    comm_g : (mor_Z o g T1)%morphism = (g T2 o mor_Y)%morphism;
    
    comm_h : (morphism_of (Susp S) mor_X o h T1)%morphism = 
             (h T2 o mor_Z)%morphism
  }.
  
End TriangleMorphism.

Section IdentityTriangleMorphism.
  Context {S : PreStableCategory}.
  
  Definition id_triangle_morphism (T : @Triangle S) : TriangleMorphism T T.
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
  
End IdentityTriangleMorphism.

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
  
End TriangleMorphismComposition.

Section TriangleMorphismLeftIdentity.
  Context {S : PreStableCategory}.
  
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
    assert (Hf: φf = ψf) by apply path_ishprop.
    assert (Hg: φg = ψg) by apply path_ishprop.
    assert (Hh: φh = ψh) by apply path_ishprop.
    destruct Hf, Hg, Hh.
    reflexivity.
  Qed.
  
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

Section TriangleMorphismRightIdentity.
  Context {S : PreStableCategory}.
  
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

Section RotateDistinguished.
  Context {S : PreStableCategory}.
  
  Theorem rotate_distinguished (T : @DistinguishedTriangle S) :
    @DistinguishedTriangle S.
  Proof.
    refine {| triangle := rotate_triangle (triangle T) |}.
    - simpl.
      exact (zero_comp_2 T).
    - simpl.
      exact (zero_comp_3 T).
    - simpl.
      rewrite <- (composition_of (Susp S)).
      rewrite (zero_comp_1 T).
      apply susp_preserves_zero_morphisms.
  Defined.
  
End RotateDistinguished.

Section TR1.
  Context {S : PreStableCategory}.
  
  Definition TR1_statement : Type :=
    forall (X Y : object S) (f : morphism S X Y),
    { Z : object S &
    { g : morphism S Y Z &
    { h : morphism S Z (object_of (Susp S) X) &
      @DistinguishedTriangle S }}}.
  
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

Section MappingCone.
  Context {S : PreStableCategory}.
  
  Definition cone {X Y : object S} (f : morphism S X Y) : object S :=
    @biproduct_obj _ _ _ (add_biproduct S Y (object_of (Susp S) X)).
  
  Definition cone_in {X Y : object S} (f : morphism S X Y) : 
    morphism S Y (cone f) :=
    @inl _ _ _ (add_biproduct S Y (object_of (Susp S) X)).
  
  Definition cone_out {X Y : object S} (f : morphism S X Y) : 
    morphism S (cone f) (object_of (Susp S) X) :=
    @outr _ _ _ (add_biproduct S Y (object_of (Susp S) X)).
  
End MappingCone.

Section ConeTriangle.
  Context {S : PreStableCategory}.
  
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

Section ConeDistinguished.
  Context {S : PreStableCategory}.
  
  Lemma cone_distinguished_conditions {X Y : object S} (f : morphism S X Y) :
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
  
  Lemma cone_out_cone_in_zero {X Y : object S} (f : morphism S X Y) :
    ((cone_out f) o (cone_in f))%morphism = zero_morphism (add_zero S) Y (object_of (Susp S) X).
  Proof.
    unfold cone_out, cone_in.
    apply (@mixed_r _ _ _ (add_biproduct S Y (object_of (Susp S) X)) (add_zero S) 
                          (add_biproduct_props S Y (object_of (Susp S) X))).
  Qed.
  
End ConeDistinguished.

Section ConeConditions13.
  Context {S : PreStableCategory}.
  
  Lemma cone_condition_1_statement {X Y : object S} (f : morphism S X Y) :
    Type.
  Proof.
    exact (((cone_in f) o f)%morphism = zero_morphism (add_zero S) X (cone f)).
  Defined.
  
  Lemma cone_in_f_unfold {X Y : object S} (f : morphism S X Y) :
    ((cone_in f) o f)%morphism = 
    (@inl _ _ _ (add_biproduct S Y (object_of (Susp S) X)) o f)%morphism.
  Proof.
    reflexivity.
  Qed.
  
  Lemma cone_condition_3_statement {X Y : object S} (f : morphism S X Y) :
    Type.
  Proof.
    exact ((morphism_of (Susp S) f o (cone_out f))%morphism = 
           zero_morphism (add_zero S) (cone f) (object_of (Susp S) Y)).
  Defined.
  
  Lemma susp_f_cone_out_unfold {X Y : object S} (f : morphism S X Y) :
    (morphism_of (Susp S) f o (cone_out f))%morphism =
    (morphism_of (Susp S) f o @outr _ _ _ (add_biproduct S Y (object_of (Susp S) X)))%morphism.
  Proof.
    reflexivity.
  Qed.
  
End ConeConditions13.

Section ConeHMorphism.
  Context {S : PreStableCategory}.
  
  Definition cone_h_component1 {X Y : object S} (f : morphism S X Y) :
    morphism S Y (object_of (Susp S) X).
  Proof.
    exact (zero_morphism (add_zero S) Y (object_of (Susp S) X)).
  Defined.
  
  Definition cone_h_component2 {X Y : object S} (f : morphism S X Y) :
    morphism S (object_of (Susp S) X) (object_of (Susp S) X).
  Proof.
    exact 1%morphism.
  Defined.
  
End ConeHMorphism.

Section ConeHUniversal.
  Context {S : PreStableCategory}.
  
  Definition cone_h {X Y : object S} (f : morphism S X Y) : 
    morphism S (cone f) (object_of (Susp S) X).
  Proof.
    unfold cone.
    destruct (add_biproduct_universal S Y (object_of (Susp S) X)) as [coprod_univ prod_univ].
    pose (univ := coprod_univ (object_of (Susp S) X)
                              (cone_h_component1 f)
                              (cone_h_component2 f)).
    exact ((@center _ univ).1).
  Defined.
  
End ConeHUniversal.

Section ProperConeTriangle.
  Context {S : PreStableCategory}.
  
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

Section ConeCondition2Check.
  Context {S : PreStableCategory}.
  
  Lemma cone_h_satisfies_universal {X Y : object S} (f : morphism S X Y) :
    ((cone_h f o @inl _ _ _ (add_biproduct S Y (object_of (Susp S) X)))%morphism = 
     cone_h_component1 f) /\
    ((cone_h f o @inr _ _ _ (add_biproduct S Y (object_of (Susp S) X)))%morphism = 
     cone_h_component2 f).
  Proof.
    unfold cone_h.
    destruct (add_biproduct_universal S Y (object_of (Susp S) X)) as [coprod_univ prod_univ].
    pose (univ := coprod_univ (object_of (Susp S) X)
                              (cone_h_component1 f)
                              (cone_h_component2 f)).
    exact ((@center _ univ).2).
  Qed.
  
End ConeCondition2Check.

Section ConeHConeIn.
  Context {S : PreStableCategory}.
  
  Lemma cone_h_cone_in {X Y : object S} (f : morphism S X Y) :
    (cone_h f o cone_in f)%morphism = cone_h_component1 f.
  Proof.
    unfold cone_in.
    destruct (cone_h_satisfies_universal f) as [H1 H2].
    exact H1.
  Qed.
  
End ConeHConeIn.

Section ConeCondition2.
  Context {S : PreStableCategory}.
  
  Lemma cone_condition_2 {X Y : object S} (f : morphism S X Y) :
    (cone_h f o cone_in f)%morphism = zero_morphism (add_zero S) Y (object_of (Susp S) X).
  Proof.
    rewrite cone_h_cone_in.
    unfold cone_h_component1.
    reflexivity.
  Qed.
  
End ConeCondition2.

Section ProjectionZeroLemma.
  Context {S : PreStableCategory}.
  
  Lemma outl_zero_is_zero {X Y Z : object S} :
    (@outl _ _ _ (add_biproduct S Y Z) o 
     zero_morphism (add_zero S) X (@biproduct_obj _ _ _ (add_biproduct S Y Z)))%morphism = 
    zero_morphism (add_zero S) X Y.
  Proof.
    unfold zero_morphism.
    rewrite <- morphism_associativity.
    (* Apply ap to the function (λ f, f ∘ terminal) *)
    apply (ap (fun f => (f o @center _ (@is_terminal _ (add_zero S) X))%morphism)).
    (* Now prove: outl ∘ initial = initial *)
    apply initial_morphism_unique.
    apply (@is_initial _ (add_zero S) Y).
  Qed.
  
End ProjectionZeroLemma.

Section CompleteInlFNotZero.
  Context {S : PreStableCategory}.
  
  Lemma inl_f_not_zero {X Y : object S} (f : morphism S X Y) :
    ((@inl _ _ _ (add_biproduct S Y (object_of (Susp S) X)) o f)%morphism = 
     zero_morphism (add_zero S) X (cone f)) ->
    f = zero_morphism (add_zero S) X Y.
  Proof.
    intro H.
    assert (Hcomp : ((@outl _ _ _ (add_biproduct S Y (object_of (Susp S) X)) o 
                      @inl _ _ _ (add_biproduct S Y (object_of (Susp S) X))) o f)%morphism = 
                    (@outl _ _ _ (add_biproduct S Y (object_of (Susp S) X)) o 
                     zero_morphism (add_zero S) X (cone f))%morphism).
    {
      rewrite <- H.
      rewrite morphism_associativity.
      reflexivity.
    }
    rewrite (@beta_l _ _ _ (add_biproduct S Y (object_of (Susp S) X)) (add_zero S) 
                           (add_biproduct_props S Y (object_of (Susp S) X))) in Hcomp.
    rewrite morphism_left_identity in Hcomp.
    rewrite outl_zero_is_zero in Hcomp.
    exact Hcomp.
  Qed.
  
End CompleteInlFNotZero.

Section ConstructiveConeData.
  Context {S : PreStableCategory}.
  
  Lemma cone_morphism_components {X Y : object S} (f : morphism S X Y)
    (j : morphism S Y (cone f)) :
    exists (α : morphism S Y Y) (β : morphism S Y (object_of (Susp S) X)),
      ((@outl _ _ _ (add_biproduct S Y (object_of (Susp S) X)) o j)%morphism = α) /\
      ((@outr _ _ _ (add_biproduct S Y (object_of (Susp S) X)) o j)%morphism = β).
  Proof.
    exists (@outl _ _ _ (add_biproduct S Y (object_of (Susp S) X)) o j)%morphism.
    exists (@outr _ _ _ (add_biproduct S Y (object_of (Susp S) X)) o j)%morphism.
    split; reflexivity.
  Qed.
  
End ConstructiveConeData.

Section ConeInRequirements.
  Context {S : PreStableCategory}.
  
  Lemma cone_in_requirements {X Y : object S} (f : morphism S X Y)
    (α : morphism S Y Y) (β : morphism S Y (object_of (Susp S) X)) :
    α = 1%morphism ->
    { j : morphism S Y (cone f) |
      (@outl _ _ _ (add_biproduct S Y (object_of (Susp S) X)) o j)%morphism = α /\
      (@outr _ _ _ (add_biproduct S Y (object_of (Susp S) X)) o j)%morphism = β }.
  Proof.
    intro H_alpha.
    pose (bpu := add_biproduct_universal S Y (object_of (Susp S) X)).
    pose (univ := @prod_universal _ _ _ (add_biproduct S Y (object_of (Susp S) X)) bpu Y α β).
    destruct (@center _ univ) as [j [Hj1 Hj2]].
    exists j.
    exact (conj Hj1 Hj2).
  Qed.
  
End ConeInRequirements.

Section ConeInZeroAnalysis.
  Context {S : PreStableCategory}.
  
  Lemma outr_zero_is_zero_local {X Y Z : object S} :
    (@outr _ _ _ (add_biproduct S Y Z) o 
     zero_morphism (add_zero S) X (@biproduct_obj _ _ _ (add_biproduct S Y Z)))%morphism = 
    zero_morphism (add_zero S) X Z.
  Proof.
    unfold zero_morphism.
    rewrite <- morphism_associativity.
    apply (ap (fun f => (f o @center _ (@is_terminal _ (add_zero S) X))%morphism)).
    apply initial_morphism_unique.
    apply (@is_initial _ (add_zero S) Z).
  Qed.
  
  Lemma cone_in_zero_condition {X Y : object S} (f : morphism S X Y)
    (β : morphism S Y (object_of (Susp S) X)) :
    let bpu := add_biproduct_universal S Y (object_of (Susp S) X) in
    let univ := @prod_universal _ _ _ (add_biproduct S Y (object_of (Susp S) X)) bpu Y 1%morphism β in
    let j := (@center _ univ).1 in
    (j o f = zero_morphism (add_zero S) X (cone f))%morphism ->
    (f = zero_morphism (add_zero S) X Y) /\ 
    (β o f = zero_morphism (add_zero S) X (object_of (Susp S) X))%morphism.
  Proof.
    intros bpu univ j H.
    destruct (@center _ univ) as [j' [Hj1 Hj2]].
    simpl in j.
    assert (Hjeq : j = j') by reflexivity.
    split.
    -
      assert (Houtl : ((@outl _ _ _ (add_biproduct S Y (object_of (Susp S) X)) o j) o f)%morphism = 
                      (@outl _ _ _ (add_biproduct S Y (object_of (Susp S) X)) o 
                       zero_morphism (add_zero S) X (cone f))%morphism).
      {
        rewrite <- H.
        rewrite morphism_associativity.
        reflexivity.
      }
      rewrite Hjeq in Houtl.
      rewrite Hj1 in Houtl.
      rewrite morphism_left_identity in Houtl.
      rewrite outl_zero_is_zero in Houtl.
      exact Houtl.
    - 
      assert (Houtr : ((@outr _ _ _ (add_biproduct S Y (object_of (Susp S) X)) o j) o f)%morphism = 
                      (@outr _ _ _ (add_biproduct S Y (object_of (Susp S) X)) o 
                       zero_morphism (add_zero S) X (cone f))%morphism).
      {
        rewrite <- H.
        rewrite morphism_associativity.
        reflexivity.
      }
      rewrite Hjeq in Houtr.
      rewrite Hj2 in Houtr.
      rewrite outr_zero_is_zero_local in Houtr.
      exact Houtr.
  Qed.
  
End ConeInZeroAnalysis.

Section PreStableCategoryWithCofiber.

  Record PreStableCategoryWithCofiber := {
    base :> PreStableCategory;
    
    cofiber : forall {X Y : object base} (f : morphism base X Y), object base;
    
    cofiber_in : forall {X Y : object base} (f : morphism base X Y), 
                 morphism base Y (cofiber f);
    cofiber_out : forall {X Y : object base} (f : morphism base X Y), 
                  morphism base (cofiber f) (object_of (Susp base) X);
    
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

End PreStableCategoryWithCofiber.

Section TR1FromCofiber.
  Context (S : PreStableCategoryWithCofiber).
  
  Definition triangle_from_morphism {X Y : object S} (f : morphism S X Y) : 
    @Triangle (base S) :=
  {|
    X := X;
    Y := Y;
    Z := @cofiber S X Y f;
    f := f;
    g := @cofiber_in S X Y f;
    h := @cofiber_out S X Y f
  |}.
  
End TR1FromCofiber.

Section CofiberTriangleDistinguished.
  Context (S : PreStableCategoryWithCofiber).
  
  Theorem cofiber_triangle_distinguished {X Y : object S} (f : morphism S X Y) :
    @DistinguishedTriangle (base S).
  Proof.
    refine {| triangle := triangle_from_morphism S f |}.
    - (* zero_comp_1: g ∘ f = 0 *)
      simpl.
      exact (@cofiber_cond1 S X Y f).
    - (* zero_comp_2: h ∘ g = 0 *)
      simpl.
      exact (@cofiber_cond2 S X Y f).
    - (* zero_comp_3: Σf ∘ h = 0 *)
      simpl.
      exact (@cofiber_cond3 S X Y f).
  Defined.
  
End CofiberTriangleDistinguished.

Section TR1Theorem.
  Context (S : PreStableCategoryWithCofiber).
  
  Theorem TR1 {X Y : object S} (f : morphism S X Y) :
    @DistinguishedTriangle (base S).
  Proof.
    exact (cofiber_triangle_distinguished S f).
  Defined.
  
End TR1Theorem.

Section TR1Verification.
  Context (S : PreStableCategoryWithCofiber).
  
  Theorem TR1_correct {X Y : object S} (f : morphism S X Y) :
    triangle (TR1 S f) = triangle_from_morphism S f.
  Proof.
    reflexivity.
  Qed.
  
End TR1Verification.

Section TR1ConstructiveTest.
  Context (S : PreStableCategoryWithCofiber).
  
  Definition TR1_triangle_data {X Y : object (base S)} (f : morphism (base S) X Y) :
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
  
End TR1ConstructiveTest.

Section IsomorphismDefinition.
  Context {C : PreCategory}.
  
  Definition IsIsomorphism {X Y : object C} (f : morphism C X Y) : Type :=
    { g : morphism C Y X |
      (g o f = 1)%morphism /\ (f o g = 1)%morphism }.
  
End IsomorphismDefinition.

Section IsomorphismInverse.
  Context {C : PreCategory}.
  
  Definition iso_inverse {X Y : object C} {f : morphism C X Y} 
    (H : IsIsomorphism f) : morphism C Y X :=
    H.1.

  Lemma iso_identity {X : object C} : IsIsomorphism (1%morphism : morphism C X X).
  Proof.
    exists 1%morphism.
    split; apply morphism_left_identity.
  Qed.
  
  Lemma iso_inverse_left {X Y : object C} {f : morphism C X Y} 
    (H : IsIsomorphism f) :
    (iso_inverse H o f = 1)%morphism.
  Proof.
    destruct H as [g [Hl Hr]].
    exact Hl.
  Qed.
  
  Lemma iso_inverse_right {X Y : object C} {f : morphism C X Y} 
    (H : IsIsomorphism f) :
    (f o iso_inverse H = 1)%morphism.
  Proof.
    destruct H as [g [Hl Hr]].
    exact Hr.
  Qed.
  
End IsomorphismInverse.

Section TriangleIsomorphism.
  Context {S : PreStableCategory}.
  
  Definition IsTriangleIsomorphism {T1 T2 : @Triangle S} 
    (φ : TriangleMorphism T1 T2) : Type :=
    IsIsomorphism (mor_X _ _ φ) * 
    IsIsomorphism (mor_Y _ _ φ) * 
    IsIsomorphism (mor_Z _ _ φ).
    
End TriangleIsomorphism.

Section TR3.
  Context {S : PreStableCategory}.
  
  Definition TR3_statement : Type :=
    forall (T : @Triangle S) (T' : @Triangle S) 
           (φ : TriangleMorphism T T'),
    IsTriangleIsomorphism φ ->
    @DistinguishedTriangle S ->
    @DistinguishedTriangle S.
    
End TR3.

Section IsoComposeHelper.
  Context {C : PreCategory}.
  
  Lemma ap_morphism_comp_left {X Y Z : object C} 
    (f : morphism C Y Z) (g h : morphism C X Y) :
    g = h -> (f o g)%morphism = (f o h)%morphism.
  Proof.
    intro H.
    rewrite H.
    reflexivity.
  Qed.
  
End IsoComposeHelper.

Section IsoComposeHelper2.
  Context {C : PreCategory}.
  
  Lemma compose_cancel_left {X Y Z : object C} 
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
  
End IsoComposeHelper2.

Section IsoComposeHelper3.
  Context {C : PreCategory}.
  
  Lemma iso_comp_to_id {X Y : object C} 
    (f : morphism C X Y) (g : morphism C Y X)
    (H : (g o f = 1)%morphism) :
    forall (Z : object C) (h : morphism C Z X),
    ((g o f) o h)%morphism = (1 o h)%morphism.
  Proof.
    intros Z h.
    rewrite H.
    reflexivity.
  Qed.
  
End IsoComposeHelper3.

Section FourWayComposeHelper.
  Context {C : PreCategory}.
  
  Lemma four_way_compose_eq {V W X Y Z : object C}
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
  
End FourWayComposeHelper.

Section ComposeBothSidesHelper.
  Context {C : PreCategory}.
  
  Lemma compose_left {X Y Z : object C}
    (p : morphism C Y Z)
    (q1 q2 : morphism C X Y) :
    q1 = q2 ->
    (p o q1)%morphism = (p o q2)%morphism.
  Proof.
    intro H.
    rewrite H.
    reflexivity.
  Qed.
  
End ComposeBothSidesHelper.

Section ComposeRightHelper.
  Context {C : PreCategory}.
  
  Lemma compose_right {X Y Z : object C}
    (p1 p2 : morphism C Y Z)
    (q : morphism C X Y) :
    p1 = p2 ->
    (p1 o q)%morphism = (p2 o q)%morphism.
  Proof.
    intro H.
    rewrite H.
    reflexivity.
  Qed.
  
End ComposeRightHelper.

Section ShiftTriangle.
  Context {S : PreStableCategory}.
  
  (* The shift of a triangle is its rotation *)
  Definition shift_triangle (T : @Triangle S) : @Triangle S := 
    rotate_triangle T.
  
  (* Shift preserves distinguished triangles *)
  Theorem shift_distinguished (T : @DistinguishedTriangle S) :
    @DistinguishedTriangle S.
  Proof.
    exact (rotate_distinguished T).
  Defined.
  
  Definition shift_triangle_morphism {T1 T2 : @Triangle S}
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
    
End ShiftTriangle.

Section TR2.
  Context {S : PreStableCategory}.
  
  Lemma iso_preserves_terminal {X Y : object S}
    (φ : morphism S X Y) (H : IsIsomorphism φ)
    (f : morphism S X (@zero _ (add_zero S))) :
    (f o iso_inverse H)%morphism = @center _ (@is_terminal _ (add_zero S) Y).
  Proof.
    symmetry.
    apply (@contr _ (@is_terminal _ (add_zero S) Y)).
  Qed.
  
  Lemma iso_preserves_initial {X Y : object S}
    (φ : morphism S X Y) (H : IsIsomorphism φ)
    (f : morphism S (@zero _ (add_zero S)) X) :
    (φ o f)%morphism = @center _ (@is_initial _ (add_zero S) Y).
  Proof.
    symmetry.
    apply (@contr _ (@is_initial _ (add_zero S) Y)).
  Qed.
  
  Lemma zero_morphism_right {X Y Z : object S}
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
  
  Lemma zero_morphism_left {X Y Z : object S}
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
  
  Lemma iso_preserves_zero {X Y Z W : object S}
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
  
End TR2.

Section FunctorPreservesIso.
  Context {C D : PreCategory} (F : Functor C D).
  
  Lemma functor_preserves_iso {X Y : object C} 
    (f : morphism C X Y) (H : IsIsomorphism f) :
    IsIsomorphism (morphism_of F f).
  Proof.
    destruct H as [g [Hgf Hfg]].
    exists (morphism_of F g).
    split.
    - (* F(g) ∘ F(f) = F(g ∘ f) = F(1) = 1 *)
      rewrite <- composition_of.
      rewrite Hgf.
      apply identity_of.
    - (* F(f) ∘ F(g) = F(f ∘ g) = F(1) = 1 *)
      rewrite <- composition_of.
      rewrite Hfg.
      apply identity_of.
  Defined.
  
End FunctorPreservesIso.

Section TR2Helpers.
  Context {S : PreStableCategory}.
  
  Lemma triangle_iso_f_formula 
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
  
  
  Lemma triangle_iso_g_formula 
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
  
Lemma iso_morphism_cancel {X Y : object S}
    (φ : morphism S X Y) (H : IsIsomorphism φ) :
    (iso_inverse H o φ)%morphism = 1%morphism.
  Proof.
    apply iso_inverse_left.
  Qed.
  
Lemma composition_with_identity_middle {A B C D : object S}
    (f : morphism S C D)
    (g : morphism S B C) 
    (h : morphism S A B) :
    (f o 1 o g o h)%morphism = (f o g o h)%morphism.
  Proof.
    rewrite morphism_right_identity.
    reflexivity.
  Qed.
  
Lemma rearrange_middle_composition {A B C D E : object S}
    (f : morphism S D E)
    (g : morphism S C D)
    (h : morphism S B C)
    (k : morphism S A B) :
    (f o (g o (h o k)))%morphism = (f o ((g o h) o k))%morphism.
  Proof.
    rewrite morphism_associativity.
    reflexivity.
  Qed.
  
Lemma get_morphisms_adjacent {A B C D E F : object S}
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
  
Lemma four_morphism_assoc {A B C D E : object S}
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
  
Lemma morphism_four_compose_with_zero {A B C D E : object S}
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
  
Lemma triangle_composition_pattern {X1 Y1 Z1 X2 Y2 Z2 : object S}
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
  
Lemma triangle_iso_preserves_zero_comp_1 
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

  Lemma triangle_iso_h_formula 
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
  
  Lemma triangle_iso_preserves_zero_comp_2 
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
  
  Lemma functor_preserves_inverse {C D : PreCategory} (F : Functor C D)
    {X Y : object C} (f : morphism C X Y) (H : IsIsomorphism f) :
    morphism_of F (iso_inverse H) = 
    iso_inverse (functor_preserves_iso F f H).
  Proof.
    destruct H as [g [Hgf Hfg]].
    simpl.
    assert (Hinv1: (morphism_of F g o morphism_of F f = 1)%morphism).
    {
      rewrite <- composition_of.
      rewrite Hgf.
      apply identity_of.
    }
    assert (Hinv2: (morphism_of F f o morphism_of F g = 1)%morphism).
    {
      rewrite <- composition_of.
      rewrite Hfg.
      apply identity_of.
    }
    reflexivity.
  Qed.
  
(* Helper: Triangle isomorphism preserves zero composition 3 *)
  Lemma triangle_iso_preserves_zero_comp_3 
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
    
    (* Use our formulas *)
    rewrite (triangle_iso_f_formula φ HY_iso HX_iso).
    rewrite (triangle_iso_h_formula φ HX_iso HZ_iso).
    
    (* Now Σ(f T2) = Σ(mor_Y φ o f T1 o iso_inverse HX_iso) *)
    rewrite (composition_of (Susp S)).
    rewrite (composition_of (Susp S)).
    
    (* Now we have: (Σ(mor_Y) o Σ(f T1) o Σ(iso_inverse HX_iso)) o (Σ(mor_X) o h T1 o iso_inverse HZ_iso) *)
    
    (* Use functor_preserves_inverse *)
    rewrite (functor_preserves_inverse (Susp S) (mor_X _ _ φ) HX_iso).
    
    (* Now use our pattern lemma *)
    rewrite (triangle_composition_pattern 
               (morphism_of (Susp S) (mor_Y _ _ φ)) 
               (morphism_of (Susp S) (f T1))
               (iso_inverse (functor_preserves_iso (Susp S) (mor_X _ _ φ) HX_iso))
               (morphism_of (Susp S) (mor_X _ _ φ))
               (h T1) 
               (iso_inverse HZ_iso)
               (iso_inverse_left (functor_preserves_iso (Susp S) (mor_X _ _ φ) HX_iso))).
    
    (* Now we have: Σ(mor_Y) o Σ(f T1) o h T1 o iso_inverse HZ_iso *)
    (* Apply the four morphism zero lemma *)
    apply morphism_four_compose_with_zero.
    exact H.
  Qed.

(* TR2: Isomorphic triangles preserve distinguished property *)
  Theorem TR2 {T1 T2 : @Triangle S} 
    (φ : TriangleMorphism T1 T2)
    (Hφ : IsTriangleIsomorphism φ)
    (D1 : @DistinguishedTriangle S)
    (H1 : triangle D1 = T1) :
    @DistinguishedTriangle S.
  Proof.
    (* Construct the distinguished triangle with T2 *)
    destruct Hφ as [[HX_iso HY_iso] HZ_iso].
    refine {| triangle := T2 |}.
    - (* zero_comp_1: g T2 ∘ f T2 = 0 *)
      apply (triangle_iso_preserves_zero_comp_1 φ (conj (conj HX_iso HY_iso) HZ_iso)).
      rewrite <- H1.
      exact (zero_comp_1 D1).
    - (* zero_comp_2: h T2 ∘ g T2 = 0 *)
      apply (triangle_iso_preserves_zero_comp_2 φ (conj (conj HX_iso HY_iso) HZ_iso)).
      rewrite <- H1.
      exact (zero_comp_2 D1).
    - (* zero_comp_3: Σf T2 ∘ h T2 = 0 *)
      apply (triangle_iso_preserves_zero_comp_3 φ (conj (conj HX_iso HY_iso) HZ_iso)).
      rewrite <- H1.
      exact (zero_comp_3 D1).
  Defined.
