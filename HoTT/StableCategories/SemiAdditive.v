(** * Semi-additive categories

    Categories with zero objects and biproducts, which automatically 
    have commutative monoid structure on hom-sets.
    
    This file proves that any category with a zero object and biproducts
    for all pairs of objects has a canonical commutative monoid structure
    on its hom-sets, where addition is defined via the biproduct structure.
*)

From HoTT Require Import Basics Types.
From HoTT.Categories Require Import Category Functor.
From HoTT.Categories.Additive Require Import ZeroObjects Biproducts.
From HoTT.Classes.interfaces Require Import abstract_algebra canonical_names.

(** ** Definition of semi-additive category *)

Class SemiAdditiveCategory := {
  cat : PreCategory;
  semiadditive_zero :: ZeroObject cat;
  semiadditive_biproduct : forall (X Y : object cat), Biproduct X Y
}.

Coercion cat : SemiAdditiveCategory >-> PreCategory.

(** ** Morphism addition via biproducts 

    The key insight is that morphism addition can be defined using the
    diagonal morphism X → X⊕X, the biproduct morphism, and the 
    codiagonal morphism Y⊕Y → Y. *)

Section MorphismAddition.
  Context (C : SemiAdditiveCategory) (X Y : object C).
  
  (** Addition of morphisms f,g : X → Y is defined as:
      X → X⊕X → Y⊕Y → Y
      where the middle map applies f to the left component and g to the right. *)
  Definition morphism_addition : SgOp (morphism C X Y).
  Proof.
    intros f g.
    refine (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o _)%morphism.
    refine (biproduct_prod_mor (semiadditive_biproduct Y Y) _ _ _ o _)%morphism.
    - exact (f o outl (biproduct_data (semiadditive_biproduct X X)))%morphism.
    - exact (g o outr (biproduct_data (semiadditive_biproduct X X)))%morphism.
    - exact (biproduct_prod_mor (semiadditive_biproduct X X) X 1%morphism 1%morphism).
  Defined.
  
  (** The zero morphism is the unit for addition. *)
  Definition morphism_zero : MonUnit (morphism C X Y)
    := @zero_morphism C semiadditive_zero X Y.
    
End MorphismAddition.

(** Make the operations instances for typeclass search. *)
#[export] Instance morphism_sgop (C : SemiAdditiveCategory) (X Y : object C) 
  : SgOp (morphism C X Y) 
  := morphism_addition C X Y.

#[export] Instance morphism_monunit (C : SemiAdditiveCategory) (X Y : object C) 
  : MonUnit (morphism C X Y) 
  := morphism_zero C X Y.

(** ** Notation for morphism addition *)

Notation "f + g" := (morphism_addition _ _ _ f g) : morphism_scope.

(** ** Basic biproduct properties

    These lemmas capture the fundamental relationships between
    diagonal/codiagonal morphisms and projections/injections. *)

Section BiproductBasics.
  Context (C : SemiAdditiveCategory).

  (** Projecting after diagonal gives identity *)
  Lemma diagonal_outl (X : object C) :
    (outl (biproduct_data (semiadditive_biproduct X X)) o 
     biproduct_prod_mor (semiadditive_biproduct X X) X 1%morphism 1%morphism)%morphism = 
    1%morphism.
  Proof.
    apply biproduct_prod_beta_l.
  Qed.

  Lemma diagonal_outr (X : object C) :
    (outr (biproduct_data (semiadditive_biproduct X X)) o 
     biproduct_prod_mor (semiadditive_biproduct X X) X 1%morphism 1%morphism)%morphism = 
    1%morphism.
  Proof.
    apply biproduct_prod_beta_r.
  Qed.

  (** Codiagonal after injection gives identity *)
  Lemma inl_codiagonal (Y : object C) :
    (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
     Biproducts.inl (biproduct_data (semiadditive_biproduct Y Y)))%morphism = 
    1%morphism.
  Proof.
    apply biproduct_coprod_beta_l.
  Qed.

  Lemma inr_codiagonal (Y : object C) :
    (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
     Biproducts.inr (biproduct_data (semiadditive_biproduct Y Y)))%morphism = 
    1%morphism.
  Proof.
    apply biproduct_coprod_beta_r.
  Qed.

End BiproductBasics.

(** ** Zero morphism properties 

    These lemmas show how zero morphisms interact with biproduct structures. *)

Section ZeroMorphismProperties.
  Context (C : SemiAdditiveCategory).

  (** Zero morphism through projection is zero *)
  Lemma zero_through_proj_left (X Y : object C) :
    ((zero_morphism X Y) o outl (biproduct_data (semiadditive_biproduct X X)))%morphism = 
    zero_morphism (biproduct_obj (biproduct_data (semiadditive_biproduct X X))) Y.
  Proof.
    unfold zero_morphism.
    rewrite Category.Core.associativity.
    f_ap.
    apply path_contr.
  Qed.

  Lemma zero_through_proj_right (X Y : object C) :
    ((zero_morphism X Y) o outr (biproduct_data (semiadditive_biproduct X X)))%morphism = 
    zero_morphism (biproduct_obj (biproduct_data (semiadditive_biproduct X X))) Y.
  Proof.
    unfold zero_morphism.
    rewrite Category.Core.associativity.
    f_ap.
    apply path_contr.
  Qed.

  (** Biproduct morphisms preserve zero in components *)
  Lemma biproduct_mor_zero_left (X Y : object C) (f : morphism C X Y) :
    biproduct_prod_mor (semiadditive_biproduct Y Y) 
      (biproduct_obj (biproduct_data (semiadditive_biproduct X X)))
      ((zero_morphism X Y) o outl (biproduct_data (semiadditive_biproduct X X)))
      (f o outr (biproduct_data (semiadditive_biproduct X X)))
    = biproduct_prod_mor (semiadditive_biproduct Y Y)
      (biproduct_obj (biproduct_data (semiadditive_biproduct X X)))
      (zero_morphism (biproduct_obj (biproduct_data (semiadditive_biproduct X X))) Y)
      (f o outr (biproduct_data (semiadditive_biproduct X X))).
  Proof.
    f_ap.
    apply zero_through_proj_left.
  Qed.

  Lemma biproduct_mor_zero_right (X Y : object C) (f : morphism C X Y) :
    biproduct_prod_mor (semiadditive_biproduct Y Y) 
      (biproduct_obj (biproduct_data (semiadditive_biproduct X X)))
      (f o outl (biproduct_data (semiadditive_biproduct X X)))
      ((zero_morphism X Y) o outr (biproduct_data (semiadditive_biproduct X X)))
    = biproduct_prod_mor (semiadditive_biproduct Y Y)
      (biproduct_obj (biproduct_data (semiadditive_biproduct X X)))
      (f o outl (biproduct_data (semiadditive_biproduct X X)))
      (zero_morphism (biproduct_obj (biproduct_data (semiadditive_biproduct X X))) Y).
  Proof.
    f_ap.
    apply zero_through_proj_right.
  Qed.

End ZeroMorphismProperties.

(** ** Biproduct morphism properties

    These lemmas establish key facts about morphisms built using biproducts. *)

Section BiproductMorphismProperties.
  Context (C : SemiAdditiveCategory).

  (** Projection of biproduct morphism extracts the component *)
  Lemma biproduct_prod_proj_r (X Y Z : object C) 
    (f g : morphism C Z Y) (h : morphism C X Z) :
    (outr (biproduct_data (semiadditive_biproduct Y Y)) o 
     (biproduct_prod_mor (semiadditive_biproduct Y Y) Z f g o h))%morphism =
    (g o h)%morphism.
  Proof.
    rewrite <- Category.Core.associativity.
    rewrite biproduct_prod_beta_r.
    reflexivity.
  Qed.

  (** Composing through diagonal/codiagonal preserves morphisms *)
  Lemma compose_through_diagonal_right (X Y : object C) (g : morphism C X Y) :
    ((g o outr (biproduct_data (semiadditive_biproduct X X))) o 
     biproduct_prod_mor (semiadditive_biproduct X X) X 1%morphism 1%morphism)%morphism = g.
  Proof.
    rewrite Category.Core.associativity.
    rewrite diagonal_outr.
    apply Category.Core.right_identity.
  Qed.

  Lemma compose_through_diagonal_left (X Y : object C) (f : morphism C X Y) :
    ((f o outl (biproduct_data (semiadditive_biproduct X X))) o 
     biproduct_prod_mor (semiadditive_biproduct X X) X 1%morphism 1%morphism)%morphism = f.
  Proof.
    rewrite Category.Core.associativity.
    rewrite diagonal_outl.
    apply Category.Core.right_identity.
  Qed.

  (** Mixed projection/injection combinations *)
  Lemma proj_inj_mixed_lr (Y Z : object C) (h : morphism C Z Y) :
    ((outl (biproduct_data (semiadditive_biproduct Y Y)) o
      Biproducts.inr (biproduct_data (semiadditive_biproduct Y Y))) o h)%morphism =
    zero_morphism Z Y.
  Proof.
    rewrite (mixed_l (biproduct_is (semiadditive_biproduct Y Y))).
    apply zero_morphism_left.
  Qed.

  Lemma proj_inj_mixed_rl (Y Z : object C) (h : morphism C Z Y) :
    ((outr (biproduct_data (semiadditive_biproduct Y Y)) o
      Biproducts.inl (biproduct_data (semiadditive_biproduct Y Y))) o h)%morphism =
    zero_morphism Z Y.
  Proof.
    rewrite (mixed_r (biproduct_is (semiadditive_biproduct Y Y))).
    apply zero_morphism_left.
  Qed.

  (** Matched projection/injection combinations *)
  Lemma proj_inj_matched_l (Y Z : object C) (h : morphism C Z Y) :
    ((outl (biproduct_data (semiadditive_biproduct Y Y)) o
      Biproducts.inl (biproduct_data (semiadditive_biproduct Y Y))) o h)%morphism = h.
  Proof.
    rewrite (beta_l (biproduct_is (semiadditive_biproduct Y Y))).
    apply Category.Core.left_identity.
  Qed.

  Lemma proj_inj_matched_r (Y Z : object C) (h : morphism C Z Y) :
    ((outr (biproduct_data (semiadditive_biproduct Y Y)) o
      Biproducts.inr (biproduct_data (semiadditive_biproduct Y Y))) o h)%morphism = h.
  Proof.
    rewrite (beta_r (biproduct_is (semiadditive_biproduct Y Y))).
    apply Category.Core.left_identity.
  Qed.

End BiproductMorphismProperties.

(** ** Uniqueness of biproduct morphisms

    These lemmas establish the universal property of biproducts
    and uniqueness of morphisms. *)

Section BiproductUniqueness.
  Context (C : SemiAdditiveCategory).

  (** Every morphism into a biproduct is uniquely determined by its projections *)
  Lemma biproduct_morphism_unique (Y Z : object C)
    (h : morphism C Z (biproduct_obj (biproduct_data (semiadditive_biproduct Y Y))))
    (f g : morphism C Z Y) :
    (outl (biproduct_data (semiadditive_biproduct Y Y)) o h = f)%morphism ->
    (outr (biproduct_data (semiadditive_biproduct Y Y)) o h = g)%morphism ->
    h = biproduct_prod_mor (semiadditive_biproduct Y Y) Z f g.
  Proof.
    intros Hl Hr.
    set (contr_instance := prod_universal (biproduct_universal (semiadditive_biproduct Y Y)) Z f g).
    set (c := @center _ contr_instance).
    change (h = pr1 c).
    set (hpair := (h; (Hl, Hr)) : {h : morphism C Z _ & _}).
    exact (ap pr1 (@path_contr _ contr_instance hpair c)).
  Qed.

  (** Special cases: biproduct morphisms with zero components *)
  Lemma biproduct_zero_right_is_inl (Y Z : object C) (h : morphism C Z Y) :
    biproduct_prod_mor (semiadditive_biproduct Y Y) Z h (zero_morphism Z Y) =
    (Biproducts.inl (biproduct_data (semiadditive_biproduct Y Y)) o h)%morphism.
  Proof.
    symmetry.
    apply biproduct_morphism_unique.
    - rewrite <- Category.Core.associativity. apply proj_inj_matched_l.
    - rewrite <- Category.Core.associativity. apply proj_inj_mixed_rl.
  Qed.

  Lemma biproduct_zero_left_is_inr (Y Z : object C) (h : morphism C Z Y) :
    biproduct_prod_mor (semiadditive_biproduct Y Y) Z (zero_morphism Z Y) h =
    (Biproducts.inr (biproduct_data (semiadditive_biproduct Y Y)) o h)%morphism.
  Proof.
    symmetry.
    apply biproduct_morphism_unique.
    - rewrite <- Category.Core.associativity. apply proj_inj_mixed_lr.
    - rewrite <- Category.Core.associativity. apply proj_inj_matched_r.
  Qed.

End BiproductUniqueness.

(** ** Identity laws for morphism addition

    The main results showing that zero is a left and right identity. *)

Section IdentityLaws.
  Context (C : SemiAdditiveCategory).

  (** Helper: codiagonal of zero/morphism simplifies *)
  Lemma codiagonal_zero_right (Y Z : object C) (h : morphism C Z Y) :
    (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
     biproduct_prod_mor (semiadditive_biproduct Y Y) Z (zero_morphism Z Y) h)%morphism = h.
  Proof.
    rewrite biproduct_zero_left_is_inr.
    rewrite <- Category.Core.associativity.
    rewrite inr_codiagonal.
    apply Category.Core.left_identity.
  Qed.

  Lemma codiagonal_zero_left (Y Z : object C) (h : morphism C Z Y) :
    (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
     biproduct_prod_mor (semiadditive_biproduct Y Y) Z h (zero_morphism Z Y))%morphism = h.
  Proof.
    rewrite biproduct_zero_right_is_inl.
    rewrite <- Category.Core.associativity.
    rewrite inl_codiagonal.
    apply Category.Core.left_identity.
  Qed.

  (** Zero is a left identity for morphism addition *)
  Theorem zero_left_identity (X Y : object C) (f : morphism C X Y) :
    morphism_addition C X Y (zero_morphism X Y) f = f.
  Proof.
    unfold morphism_addition.
    rewrite biproduct_mor_zero_left.
    set (X2 := semiadditive_biproduct X X).
    set (Y2 := semiadditive_biproduct Y Y).
    rewrite <- Category.Core.associativity.
    rewrite codiagonal_zero_right.
    apply compose_through_diagonal_right.
  Qed.

  (** Zero is a right identity for morphism addition *)
  Theorem zero_right_identity (X Y : object C) (f : morphism C X Y) :
    morphism_addition C X Y f (zero_morphism X Y) = f.
  Proof.
    unfold morphism_addition.
    rewrite biproduct_mor_zero_right.
    set (X2 := semiadditive_biproduct X X).
    set (Y2 := semiadditive_biproduct Y Y).
    rewrite <- Category.Core.associativity.
    rewrite codiagonal_zero_left.
    apply compose_through_diagonal_left.
  Qed.

End IdentityLaws.

(** ** Helper lemmas for basic biproduct operations *)

Section BiproductHelpers.
  Context (C : SemiAdditiveCategory).

  (** Projecting right after injecting right gives identity *)
  Lemma outr_after_inr (A B : object C) :
    (outr (biproduct_data (semiadditive_biproduct A B)) o 
     Biproducts.inr (biproduct_data (semiadditive_biproduct A B)))%morphism = 
    1%morphism.
  Proof.
    apply (beta_r (biproduct_is (semiadditive_biproduct A B))).
  Qed.

  (** Projecting left after injecting left gives identity *)
  Lemma outl_after_inl (A B : object C) :
    (outl (biproduct_data (semiadditive_biproduct A B)) o 
     Biproducts.inl (biproduct_data (semiadditive_biproduct A B)))%morphism = 
    1%morphism.
  Proof.
    apply (beta_l (biproduct_is (semiadditive_biproduct A B))).
  Qed.

  (** Projecting right after injecting left gives zero *)
  Lemma outr_after_inl (A B : object C) :
    (outr (biproduct_data (semiadditive_biproduct A B)) o 
     Biproducts.inl (biproduct_data (semiadditive_biproduct A B)))%morphism = 
    zero_morphism A B.
  Proof.
    apply (mixed_r (biproduct_is (semiadditive_biproduct A B))).
  Qed.

  (** Helper: left projection after biproduct morphism *)
  Lemma outl_biproduct_prod (A B D : object C) (f : morphism C D A) (g : morphism C D B) :
    (outl (biproduct_data (semiadditive_biproduct A B)) o 
     biproduct_prod_mor (semiadditive_biproduct A B) D f g)%morphism = f.
  Proof.
    apply biproduct_prod_beta_l.
  Qed.

  (** Helper: right projection after biproduct morphism *)
  Lemma outr_biproduct_prod (A B D : object C) (f : morphism C D A) (g : morphism C D B) :
    (outr (biproduct_data (semiadditive_biproduct A B)) o 
     biproduct_prod_mor (semiadditive_biproduct A B) D f g)%morphism = g.
  Proof.
    apply biproduct_prod_beta_r.
  Qed.

  (** Composition of biproduct morphisms *)
  Lemma biproduct_comp_general (W X Y Z : object C)
    (f : morphism C W X) (g : morphism C W Y) (h : morphism C Z W) :
    (biproduct_prod_mor (semiadditive_biproduct X Y) W f g o h)%morphism =
    biproduct_prod_mor (semiadditive_biproduct X Y) Z (f o h) (g o h).
  Proof.
    set (XY := semiadditive_biproduct X Y).
    set (bp_univ := prod_universal (biproduct_universal XY) Z (f o h) (g o h)).
    set (lhs := (biproduct_prod_mor XY W f g o h)%morphism).
    assert (Hl : (outl (biproduct_data XY) o lhs)%morphism = (f o h)%morphism).
    { unfold lhs. 
      rewrite <- Category.Core.associativity.
      rewrite biproduct_prod_beta_l.
      reflexivity. }
    assert (Hr : (outr (biproduct_data XY) o lhs)%morphism = (g o h)%morphism).
    { unfold lhs.
      rewrite <- Category.Core.associativity.
      rewrite biproduct_prod_beta_r.
      reflexivity. }
    exact (ap pr1 (@path_contr _ bp_univ (lhs; (Hl, Hr)) (@center _ bp_univ))).
  Qed.

  (** Full simplification of morphism addition *)
  Lemma morphism_addition_simplify (X Y : object C) 
    (f g : morphism C X Y) :
    morphism_addition C X Y f g = 
    (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
     biproduct_prod_mor (semiadditive_biproduct Y Y) X f g)%morphism.
  Proof.
    unfold morphism_addition.
    f_ap.
    rewrite biproduct_comp_general.
    f_ap.
    - rewrite compose_through_diagonal_left. reflexivity.
    - rewrite compose_through_diagonal_right. reflexivity.
  Qed.

End BiproductHelpers.

(** ** Swap morphism for biproducts *)

Section BiproductSwap.
  Context (C : SemiAdditiveCategory).

  (** The swap morphism for biproducts *)
  Lemma biproduct_swap (A : object C) :
    {swap : morphism C (biproduct_obj (biproduct_data (semiadditive_biproduct A A)))
                       (biproduct_obj (biproduct_data (semiadditive_biproduct A A))) &
     (outl (biproduct_data (semiadditive_biproduct A A)) o swap = 
      outr (biproduct_data (semiadditive_biproduct A A)))%morphism /\
     (outr (biproduct_data (semiadditive_biproduct A A)) o swap = 
      outl (biproduct_data (semiadditive_biproduct A A)))%morphism}.
  Proof.
    exists (biproduct_prod_mor (semiadditive_biproduct A A) 
             (biproduct_obj (biproduct_data (semiadditive_biproduct A A)))
             (outr (biproduct_data (semiadditive_biproduct A A)))
             (outl (biproduct_data (semiadditive_biproduct A A)))).
    split.
    - apply biproduct_prod_beta_l.
    - apply biproduct_prod_beta_r.
  Defined.

  (** Swapping components of a biproduct morphism *)
  Lemma biproduct_prod_swap (A B : object C) 
    (f g : morphism C A B) :
    biproduct_prod_mor (semiadditive_biproduct B B) A g f = 
    ((pr1 (biproduct_swap B)) o biproduct_prod_mor (semiadditive_biproduct B B) A f g)%morphism.
  Proof.
    symmetry.
    apply biproduct_morphism_unique.
    - rewrite <- Category.Core.associativity.
      rewrite (fst (pr2 (biproduct_swap B))).
      apply biproduct_prod_beta_r.
    - rewrite <- Category.Core.associativity.
      rewrite (snd (pr2 (biproduct_swap B))).
      apply biproduct_prod_beta_l.
  Qed.

(** Swap composed with left injection gives right injection *)
Lemma swap_inl (Y : object C) :
  ((biproduct_swap Y).1 o Biproducts.inl (biproduct_data (semiadditive_biproduct Y Y)))%morphism = 
  Biproducts.inr (biproduct_data (semiadditive_biproduct Y Y)).
Proof.
  unfold biproduct_swap. simpl.
  rewrite biproduct_comp_general.
  rewrite outl_after_inl.
  rewrite outr_after_inl.
  rewrite biproduct_zero_left_is_inr.
  rewrite Category.Core.right_identity.
  reflexivity.
Qed.

(** Swap composed with right injection gives left injection *)
Lemma swap_inr (Y : object C) :
  ((biproduct_swap Y).1 o Biproducts.inr (biproduct_data (semiadditive_biproduct Y Y)))%morphism = 
  Biproducts.inl (biproduct_data (semiadditive_biproduct Y Y)).
Proof.
  unfold biproduct_swap. simpl.
  rewrite biproduct_comp_general.
  rewrite (mixed_l (biproduct_is (semiadditive_biproduct Y Y))).
  rewrite outr_after_inr.
  rewrite biproduct_zero_right_is_inl.
  rewrite Category.Core.right_identity.
  reflexivity.
Qed.


  (** The codiagonal is invariant under swapping *)
  Lemma codiagonal_swap_invariant (Y : object C) :
    (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
     pr1 (biproduct_swap Y))%morphism = 
    biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism.
  Proof.
    apply (biproduct_coprod_unique (semiadditive_biproduct Y Y)).
    - rewrite Category.Core.associativity.
      rewrite swap_inl.
      apply biproduct_coprod_beta_r.
    - rewrite Category.Core.associativity.
      rewrite swap_inr.
      apply biproduct_coprod_beta_l.
  Qed.
  
  

End BiproductSwap.

(** ** Commutative Theorem *)

(** Commutativity of morphism addition *)
Theorem morphism_addition_commutative (C : SemiAdditiveCategory) (X Y : object C)
  : Commutative (@morphism_addition C X Y).
Proof.
  intros f g.
  rewrite !morphism_addition_simplify.
  rewrite (biproduct_prod_swap C X Y f g).
  rewrite <- Category.Core.associativity.
  rewrite codiagonal_swap_invariant.
  reflexivity.
Qed.

(** ** Associativity of morphism addition *)

Section Associativity.
  Context (C : SemiAdditiveCategory).

  Local Notation obj := (object C).
  Local Notation hom := (morphism C).

  (* Shorthands for frequently used biproduct structure on Y ⊕ Y and variants *)
  Local Definition YY (Y : obj) : Biproduct Y Y := semiadditive_biproduct Y Y.
  Local Definition YYYL (Y : obj) : Biproduct (biproduct_obj (biproduct_data (YY Y))) Y
    := semiadditive_biproduct (biproduct_obj (biproduct_data (YY Y))) Y.
  Local Definition YYYR (Y : obj) : Biproduct Y (biproduct_obj (biproduct_data (YY Y)))
    := semiadditive_biproduct Y (biproduct_obj (biproduct_data (YY Y))).
    
Lemma biproduct_prod_compose_left
  (X Y Z : object C)
  (f : morphism C Z X) (g : morphism C Z Y)
  (a : morphism C X X) (b : morphism C Y Y)
: (biproduct_prod_mor (semiadditive_biproduct X Y)
     (biproduct_obj (biproduct_data (semiadditive_biproduct X Y)))
     (a o outl (biproduct_data (semiadditive_biproduct X Y)))
     (b o outr (biproduct_data (semiadditive_biproduct X Y)))
    o biproduct_prod_mor (semiadditive_biproduct X Y) Z f g)%morphism
  =
  biproduct_prod_mor (semiadditive_biproduct X Y) Z (a o f) (b o g).
Proof.
  set (B := semiadditive_biproduct X Y).
  set (lhs :=
         (biproduct_prod_mor B
             (biproduct_obj (biproduct_data B))
             (a o outl (biproduct_data B))
             (b o outr (biproduct_data B))
          o biproduct_prod_mor B Z f g)%morphism).
  assert (Hl :
      (outl (biproduct_data B) o lhs)%morphism = (a o f)%morphism).
  { rewrite <- Category.Core.associativity.
    rewrite biproduct_prod_beta_l.
    rewrite Category.Core.associativity.
    rewrite biproduct_prod_beta_l.
    reflexivity. }
  assert (Hr :
      (outr (biproduct_data B) o lhs)%morphism = (b o g)%morphism).
  { rewrite <- Category.Core.associativity.
    rewrite biproduct_prod_beta_r.
    rewrite Category.Core.associativity.
    rewrite biproduct_prod_beta_r.
    reflexivity. }
  set (U := prod_universal (biproduct_universal B) Z (a o f) (b o g)).
  change (lhs = (biproduct_prod_mor B Z (a o f) (b o g))).
  exact (ap pr1 (@path_contr _ U (lhs; (Hl, Hr)) (@center _ U))).
Qed.

Lemma codiagonal_after_componentwise
  (Y Z : object C)
  (f g : morphism C Z Y)
  (a b : morphism C Y Y)
: (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism
     o biproduct_prod_mor (semiadditive_biproduct Y Y)
         (biproduct_obj (biproduct_data (semiadditive_biproduct Y Y)))
         ((a o outl (biproduct_data (semiadditive_biproduct Y Y)))%morphism)
         ((b o outr (biproduct_data (semiadditive_biproduct Y Y)))%morphism)
     o biproduct_prod_mor (semiadditive_biproduct Y Y) Z f g)%morphism
  =
  morphism_addition C Z Y ((a o f)%morphism) ((b o g)%morphism).
Proof.
  set (B := semiadditive_biproduct Y Y).
  set (P := biproduct_prod_mor B Z f g).
  change
    ((biproduct_coprod_mor B Y 1%morphism 1%morphism
       o biproduct_prod_mor B (biproduct_obj (biproduct_data B))
           ((a o outl (biproduct_data B))%morphism)
           ((b o outr (biproduct_data B))%morphism)
       o P)%morphism
     =
     morphism_addition C Z Y ((a o f)%morphism) ((b o g)%morphism)).
  rewrite Category.Core.associativity.
  rewrite (@morphism_addition_simplify C Z Y ((a o f)%morphism) ((b o g)%morphism)).
  apply (ap (fun k => (biproduct_coprod_mor B Y 1%morphism 1%morphism o k)%morphism)).
  rewrite (@biproduct_comp_general C
             (biproduct_obj (biproduct_data B)) Y Y Z
             (a o outl (biproduct_data B))
             (b o outr (biproduct_data B))
             P).
  apply ap011.
  - rewrite Category.Core.associativity.
    apply (ap (fun t => (a o t)%morphism)).
    apply outl_biproduct_prod.
  - rewrite Category.Core.associativity.
    apply (ap (fun t => (b o t)%morphism)).
    apply outr_biproduct_prod.
Qed.

Lemma componentwise_after_prod
  (Y Z : object C)
  (f g : morphism C Z Y)
  (a b : morphism C Y Y)
  : (biproduct_prod_mor (semiadditive_biproduct Y Y)
       (biproduct_obj (biproduct_data (semiadditive_biproduct Y Y)))
       (a o outl (biproduct_data (semiadditive_biproduct Y Y)))
       (b o outr (biproduct_data (semiadditive_biproduct Y Y)))
     o biproduct_prod_mor (semiadditive_biproduct Y Y) Z f g)%morphism
    =
    biproduct_prod_mor (semiadditive_biproduct Y Y) Z (a o f) (b o g).
Proof.
  set (B := semiadditive_biproduct Y Y).
  set (P := biproduct_prod_mor B Z f g).
rewrite (@biproduct_comp_general C
           (biproduct_obj (biproduct_data B)) Y Y Z
           (a o outl (biproduct_data B))
           (b o outr (biproduct_data B))
           P).
  rewrite !Category.Core.associativity.
  rewrite (biproduct_prod_beta_l B Z f g).
  rewrite (biproduct_prod_beta_r B Z f g).
  reflexivity.
Qed.

Lemma codiagonal_postcompose
  (Y : object C) (a : morphism C Y Y) :
  (a o biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism)%morphism
  =
  biproduct_coprod_mor (semiadditive_biproduct Y Y) Y a a.
Proof.
  set (B := semiadditive_biproduct Y Y).
  apply (biproduct_coprod_unique B Y a a).
  - rewrite Category.Core.associativity.
    rewrite inl_codiagonal.
    apply Category.Core.right_identity.
  - rewrite Category.Core.associativity.
    rewrite inr_codiagonal.
    apply Category.Core.right_identity.
Qed.

Lemma diagonal_precompose
  (X W : object C) (a : morphism C W X) :
  (biproduct_prod_mor (semiadditive_biproduct X X) X 1%morphism 1%morphism o a)%morphism
  =
  biproduct_prod_mor (semiadditive_biproduct X X) W a a.
Proof.
rewrite (@biproduct_comp_general _ X X X W 1%morphism 1%morphism a).
  rewrite !Category.Core.left_identity.
  reflexivity.
Qed.

Lemma addition_precompose
  (X Y W : object C) (f g : morphism C X Y) (a : morphism C W X) :
  (morphism_addition C X Y f g o a)%morphism
  =
  morphism_addition C W Y (f o a)%morphism (g o a)%morphism.
Proof.
  rewrite (@morphism_addition_simplify C X Y f g).
  rewrite (@morphism_addition_simplify C W Y (f o a)%morphism (g o a)%morphism).
  rewrite Category.Core.associativity.
  rewrite (@biproduct_comp_general C X Y Y W f g a).
  reflexivity.
Qed.

Lemma codiagonal_postcompose_any
  (Y Y' : object C) (a : morphism C Y Y') :
  (a o biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism)%morphism
  =
  biproduct_coprod_mor (semiadditive_biproduct Y Y) Y' a a.
Proof.
  set (B := semiadditive_biproduct Y Y).
  apply (biproduct_coprod_unique B Y' a a).
  - rewrite Category.Core.associativity.
    rewrite inl_codiagonal.
    apply Category.Core.right_identity.
  - rewrite Category.Core.associativity.
    rewrite inr_codiagonal.
    apply Category.Core.right_identity.
Qed.


Lemma biproduct_pair_naturality
  (X Y Y' : object C) (a : morphism C Y Y')
  (f g : morphism C X Y) :
  biproduct_prod_mor (semiadditive_biproduct Y' Y') X (a o f) (a o g)
  =
  (biproduct_prod_mor (semiadditive_biproduct Y' Y')
     (biproduct_obj (biproduct_data (semiadditive_biproduct Y Y)))
     (a o outl (biproduct_data (semiadditive_biproduct Y Y)))
     (a o outr (biproduct_data (semiadditive_biproduct Y Y)))
   o biproduct_prod_mor (semiadditive_biproduct Y Y) X f g)%morphism.
Proof.
  symmetry.
  apply (biproduct_morphism_unique C Y' X).
  - rewrite <- Category.Core.associativity.
    rewrite biproduct_prod_beta_l.
    rewrite Category.Core.associativity.
    rewrite biproduct_prod_beta_l.
    reflexivity.
  - rewrite <- Category.Core.associativity.
    rewrite biproduct_prod_beta_r.
    rewrite Category.Core.associativity.
    rewrite biproduct_prod_beta_r.
    reflexivity.
Qed.

Lemma codiagonal_pair_inl
  (Y Y' : object C) (a b : morphism C Y Y') :
  (biproduct_coprod_mor (semiadditive_biproduct Y' Y') Y' 1%morphism 1%morphism
   o (biproduct_prod_mor (semiadditive_biproduct Y' Y')
        (biproduct_obj (biproduct_data (semiadditive_biproduct Y Y)))
        (a o outl (biproduct_data (semiadditive_biproduct Y Y)))
        (b o outr (biproduct_data (semiadditive_biproduct Y Y)))
      o Biproducts.inl (biproduct_data (semiadditive_biproduct Y Y))))%morphism
  = a.
Proof.
  set (BY  := semiadditive_biproduct Y Y).
  set (BY' := semiadditive_biproduct Y' Y').

  (* reassociate so [coprod ∘ prod] forms a single block *)
  rewrite <- Category.Core.associativity.

  (* turn [coprod ∘ prod] into addition *)
  rewrite <- (@morphism_addition_simplify C
               (biproduct_obj (biproduct_data BY)) Y'
               (a o outl (biproduct_data BY))
               (b o outr (biproduct_data BY))).

  (* precompose the addition by [inl] (positional args) *)
  rewrite (@addition_precompose
             (biproduct_obj (biproduct_data BY))  (* X *)
             Y'                                   (* Y *)
             Y                                    (* W *)
             ((a o outl (biproduct_data BY))%morphism)  (* f *)
             ((b o outr (biproduct_data BY))%morphism)  (* g *)
             (Biproducts.inl (biproduct_data BY))).     (* a *)

  (* compare components, then use right-identity of + *)
  transitivity (morphism_addition C Y Y' a (zero_morphism Y Y')).
  - apply ap011.
    + rewrite Category.Core.associativity.
      rewrite outl_after_inl.
      apply Category.Core.right_identity.
    + rewrite Category.Core.associativity.
      rewrite outr_after_inl.
      apply zero_morphism_right.
  - apply zero_right_identity.
Qed.
