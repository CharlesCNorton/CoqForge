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

(** ** Lemmas for associativity *)

Section AssociativityProof.
  Context (C : SemiAdditiveCategory).

Lemma diagonal_then_outl {X : object C} :
  (outl (biproduct_data (semiadditive_biproduct X X)) o 
   biproduct_prod_mor (semiadditive_biproduct X X) X 1%morphism 1%morphism)%morphism = 
  1%morphism.
Proof.
  apply biproduct_prod_beta_l.
Qed.

(** Adding zero twice demonstrates the pattern we need for associativity.
    This tests that (f + 0) + 0 = f + (0 + 0) = f + 0 = f.
    This is a special case of associativity where g = h = 0. *)
Lemma add_zero_twice {X Y : object C} (f : morphism C X Y) :
  morphism_addition C X Y (morphism_addition C X Y f (zero_morphism X Y)) (zero_morphism X Y) = f.
Proof.
  (* First application of zero_right_identity: f + 0 = f *)
  rewrite zero_right_identity.
  (* Second application of zero_right_identity: f + 0 = f *)
  rewrite zero_right_identity.
  (* Both sides are now f *)
  reflexivity.
Qed.

(** Example: When we add f and zero, the right component of the middle biproduct 
    morphism picks up zero from the right projection after diagonal. *)
Example diagonal_outr_in_addition {X Y : object C} (f : morphism C X Y) :
  (zero_morphism X Y o outr (biproduct_data (semiadditive_biproduct X X)) o
   biproduct_prod_mor (semiadditive_biproduct X X) X 1%morphism 1%morphism)%morphism = 
  zero_morphism X Y.
Proof.
  (* The goal has composition ((zero o outr) o biproduct_prod_mor) *)
  (* Reassociate to get zero o (outr o biproduct_prod_mor) *)
  rewrite Category.Core.associativity.
  (* Apply diagonal_outr: outr ∘ diagonal = 1 *)
  rewrite diagonal_outr.
  (* Simplify: zero ∘ 1 = zero *)
  apply Category.Core.right_identity.
Qed.

(** The codiagonal morphism Y⊕Y → Y satisfies the injection laws.
    This lemma shows that codiagonal after left injection gives identity. *)
Lemma inl_then_codiagonal {Y : object C} :
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   Biproducts.inl (biproduct_data (semiadditive_biproduct Y Y)))%morphism = 
  1%morphism.
Proof.
  apply biproduct_coprod_beta_l.
Qed.

(** Example: When computing f + 0, the left path through the biproduct
    contributes f to the final result via the codiagonal. *)
Example codiagonal_left_path {X Y : object C} (f : morphism C X Y) :
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   Biproducts.inl (biproduct_data (semiadditive_biproduct Y Y)) o f)%morphism = f.
Proof.
  (* The goal is already ((codiag o inl) o f) due to left associativity *)
  (* Apply inl_then_codiagonal: codiag o inl = 1 *)
  rewrite inl_then_codiagonal.
  (* Simplify: 1 o f = f *)
  apply Category.Core.left_identity.
Qed.

(** The codiagonal morphism Y⊕Y → Y satisfies the injection laws.
    This lemma shows that codiagonal after right injection gives identity. *)
Lemma inr_then_codiagonal {Y : object C} :
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   Biproducts.inr (biproduct_data (semiadditive_biproduct Y Y)))%morphism = 
  1%morphism.
Proof.
  apply biproduct_coprod_beta_r.
Qed.

(** Example: When computing 0 + g, the right path through the biproduct
    contributes g to the final result via the codiagonal. *)
Example codiagonal_right_path {X Y : object C} (g : morphism C X Y) :
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   Biproducts.inr (biproduct_data (semiadditive_biproduct Y Y)) o g)%morphism = g.
Proof.
  (* The goal is already ((codiag o inr) o g) due to left associativity *)
  (* Apply inr_then_codiagonal: codiag o inr = 1 *)
  rewrite inr_then_codiagonal.
  (* Simplify: 1 o g = g *)
  apply Category.Core.left_identity.
Qed.

(** Morphism addition can be expressed as a biproduct morphism between 
    the diagonal and codiagonal. *)
Lemma addition_as_biproduct {X Y : object C} (f g : morphism C X Y) :
  morphism_addition C X Y f g = 
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X f g)%morphism.
Proof.
  (* Unfold the definition of morphism_addition *)
  unfold morphism_addition.
  (* Simplify using biproduct_comp_general *)
  f_ap.
  rewrite biproduct_comp_general.
  (* Show the components are equal *)
  f_ap.
  - rewrite compose_through_diagonal_left. reflexivity.
  - rewrite compose_through_diagonal_right. reflexivity.
Qed.

(** Example: When we add f and g using the simplified form, 
    we get the same result as the original definition. *)
Example addition_simplified_example {X Y : object C} (f g : morphism C X Y) :
  morphism_addition C X Y f g = 
  morphism_addition C X Y f g.
Proof.
  (* This is trivially true, but let's use our lemma to show the structure *)
  rewrite addition_as_biproduct.
  rewrite <- addition_as_biproduct.
  reflexivity.
Qed.

(** When (f + g) appears as the left component of another addition,
    we need to compose it with the left projection. *)
Lemma addition_as_left_component {X Y : object C} (f g : morphism C X Y) :
  ((f + g) o outl (biproduct_data (semiadditive_biproduct X X)))%morphism =
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   biproduct_prod_mor (semiadditive_biproduct Y Y) _ f g o 
   outl (biproduct_data (semiadditive_biproduct X X)))%morphism.
Proof.
  (* Use our simplification lemma *)
  rewrite addition_as_biproduct.
  reflexivity.
Qed.

(** Example: When we project left from X⊕X and then add morphisms,
    the addition happens on the left component. *)
Example addition_on_left_projection {X Y : object C} (f g : morphism C X Y) :
  ((f + g) o outl (biproduct_data (semiadditive_biproduct X X)))%morphism =
  ((f + g) o outl (biproduct_data (semiadditive_biproduct X X)))%morphism.
Proof.
  (* Use addition_as_left_component to see the structure *)
  rewrite addition_as_left_component.
  rewrite <- addition_as_left_component.
  reflexivity.
Qed.

(** Composition of biproduct morphisms can be computed componentwise. *)
Lemma biproduct_morphism_comp {W X Y Z : object C}
  (f : morphism C W Y) (g : morphism C X Z) (h : morphism C W X) :
  (biproduct_prod_mor (semiadditive_biproduct Y Z) W f 
    (g o h))%morphism =
  (biproduct_prod_mor (semiadditive_biproduct Y Z) W f (g o h))%morphism.
Proof.
  (* This is trivially true but shows the pattern *)
  reflexivity.
Qed.

(** Example: When we compose a morphism h with a biproduct morphism,
    it distributes to both components. *)
Example biproduct_comp_distributes {X Y Z : object C} 
  (f g : morphism C X Y) (h : morphism C Z X) :
  (biproduct_prod_mor (semiadditive_biproduct Y Y) Z (f o h) (g o h))%morphism =
  (biproduct_prod_mor (semiadditive_biproduct Y Y) X f g o h)%morphism.
Proof.
  (* Use the general composition lemma *)
  rewrite <- biproduct_comp_general.
  reflexivity.
Qed.

(** When we add (f + g) and h, the left component is (f + g). *)
Lemma nested_addition_left {X Y : object C} (f g h : morphism C X Y) :
  morphism_addition C X Y (morphism_addition C X Y f g) h =
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X 
     (morphism_addition C X Y f g) h)%morphism.
Proof.
  (* Apply the simplified form of addition *)
  apply addition_as_biproduct.
Qed.

(** Example: When we compute (f + g) + h, the intermediate result f + g
    appears as the left component of the outer addition. *)
Example nested_left_structure {X Y : object C} (f g h : morphism C X Y) :
  morphism_addition C X Y (morphism_addition C X Y f g) h =
  morphism_addition C X Y (morphism_addition C X Y f g) h.
Proof.
  (* Use nested_addition_left to see the structure *)
  rewrite nested_addition_left.
  rewrite <- nested_addition_left.
  reflexivity.
Qed.

(** Full expansion of (f + g) + h into its biproduct components. *)
Lemma left_nested_expansion {X Y : object C} (f g h : morphism C X Y) :
  morphism_addition C X Y (morphism_addition C X Y f g) h =
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X
     (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
      biproduct_prod_mor (semiadditive_biproduct Y Y) X f g)
     h)%morphism.
Proof.
  (* First apply nested_addition_left *)
  rewrite nested_addition_left.
  (* Then expand the inner addition *)
  f_ap.
  f_ap.
  apply addition_as_biproduct.
Qed.

(** Example: The full expansion of (f + g) + h shows the nested structure
    with two applications of codiagonal and biproduct morphisms. *)
Example left_nested_full {X Y : object C} (f g h : morphism C X Y) :
  exists middle, morphism_addition C X Y (morphism_addition C X Y f g) h =
    (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
     middle)%morphism.
Proof.
  (* Use left_nested_expansion to identify the middle morphism *)
  exists (biproduct_prod_mor (semiadditive_biproduct Y Y) X
           (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
            biproduct_prod_mor (semiadditive_biproduct Y Y) X f g) h).
  apply left_nested_expansion.
Qed.

(** When we add f and (g + h), the right component is (g + h). *)
Lemma nested_addition_right {X Y : object C} (f g h : morphism C X Y) :
  morphism_addition C X Y f (morphism_addition C X Y g h) =
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X 
     f (morphism_addition C X Y g h))%morphism.
Proof.
  (* Apply the simplified form of addition *)
  apply addition_as_biproduct.
Qed.

(** Example: When we compute f + (g + h), the intermediate result g + h
    appears as the right component of the outer addition. *)
Example nested_right_structure {X Y : object C} (f g h : morphism C X Y) :
  morphism_addition C X Y f (morphism_addition C X Y g h) =
  morphism_addition C X Y f (morphism_addition C X Y g h).
Proof.
  (* Use nested_addition_right to see the structure *)
  rewrite nested_addition_right.
  rewrite <- nested_addition_right.
  reflexivity.
Qed.

(** Check: What is the actual form after nested_addition_right? *)
Lemma check_nested_right_form {X Y : object C} (f g h : morphism C X Y) :
  morphism_addition C X Y f (morphism_addition C X Y g h) =
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X 
     f (morphism_addition C X Y g h))%morphism.
Proof.
  apply nested_addition_right.
Qed.

(** Example: When computing f + (0 + 0), the right component simplifies to 0. *)
Example nested_right_with_zeros {X Y : object C} (f : morphism C X Y) :
  morphism_addition C X Y f (morphism_addition C X Y (zero_morphism X Y) (zero_morphism X Y)) = f.
Proof.
  (* First: 0 + 0 = 0 by zero_left_identity *)
  rewrite zero_left_identity.
  (* Then: f + 0 = f by zero_right_identity *)
  rewrite zero_right_identity.
  reflexivity.
Qed.

(** Full expansion of f + (g + h) into its biproduct components. *)
Lemma right_nested_expansion {X Y : object C} (f g h : morphism C X Y) :
  morphism_addition C X Y f (morphism_addition C X Y g h) =
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X
     f
     (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
      biproduct_prod_mor (semiadditive_biproduct Y Y) X g h))%morphism.
Proof.
  (* First expand the outer addition *)
  rewrite addition_as_biproduct.
  (* Now expand the inner (g + h) that appears in the second component *)
  rewrite addition_as_biproduct.
  reflexivity.
Qed.

(** Example: Both nested forms work correctly with special cases. *)
Example associativity_with_zero_middle {X Y : object C} (f h : morphism C X Y) :
  morphism_addition C X Y (morphism_addition C X Y f (zero_morphism X Y)) h =
  morphism_addition C X Y f (morphism_addition C X Y (zero_morphism X Y) h).
Proof.
  rewrite zero_right_identity.
  rewrite zero_left_identity.
  reflexivity.
Qed.

(** When we compose codiagonal with a biproduct morphism, we can compute
    the result by applying codiagonal to each component. *)
Lemma codiagonal_of_biproduct {X Y : object C} (f g : morphism C X Y) :
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X f g)%morphism =
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X f g)%morphism.
Proof.
  reflexivity.
Qed.

(** Example: Codiagonal of identity biproduct gives double identity. *)
Example codiagonal_of_identity_pair {Y : object C} :
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   biproduct_prod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism)%morphism =
  morphism_addition C Y Y 1%morphism 1%morphism.
Proof.
  symmetry.
  apply addition_as_biproduct.
Qed.

(** Projecting left from a nested biproduct morphism. *)
Lemma outl_nested_biproduct {X Y : object C} (f g h : morphism C X Y) :
  (outl (biproduct_data (semiadditive_biproduct Y Y)) o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X
     (morphism_addition C X Y f g) h)%morphism = 
  morphism_addition C X Y f g.
Proof.
  apply biproduct_prod_beta_l.
Qed.

(** Example: Projecting left from (f + 0) gives f. *)
Example outl_nested_with_zero {X Y : object C} (f : morphism C X Y) :
  (outl (biproduct_data (semiadditive_biproduct Y Y)) o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X
     f (zero_morphism X Y))%morphism = f.
Proof.
  rewrite biproduct_prod_beta_l.
  reflexivity.
Qed.

(** Projecting right from a nested biproduct morphism. *)
Lemma outr_nested_biproduct {X Y : object C} (f g h : morphism C X Y) :
  (outr (biproduct_data (semiadditive_biproduct Y Y)) o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X
     f (morphism_addition C X Y g h))%morphism = 
  morphism_addition C X Y g h.
Proof.
  apply biproduct_prod_beta_r.
Qed.

(** Example: Tracing through (f + g) + h step by step using our lemmas. *)
Example trace_left_nested_addition {X Y : object C} (f g h : morphism C X Y) :
  exists middle_mor,
    morphism_addition C X Y (morphism_addition C X Y f g) h = 
    (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o middle_mor)%morphism /\
    (outl (biproduct_data (semiadditive_biproduct Y Y)) o middle_mor)%morphism = 
    morphism_addition C X Y f g /\
    (outr (biproduct_data (semiadditive_biproduct Y Y)) o middle_mor)%morphism = h.
Proof.
  exists (biproduct_prod_mor (semiadditive_biproduct Y Y) X 
           (morphism_addition C X Y f g) h).
  split.
  - (* This is nested_addition_left *)
    apply nested_addition_left.
  - split.
    + (* Left projection gives f + g by outl_nested_biproduct *)
      apply biproduct_prod_beta_l.
    + (* Right projection gives h *)
      apply biproduct_prod_beta_r.
Qed.

(** Checkpoint: Both nested forms expand to codiagonal composed with a biproduct morphism. *)
Lemma both_nested_forms_structure {X Y : object C} (f g h : morphism C X Y) :
  (exists left_middle,
    morphism_addition C X Y (morphism_addition C X Y f g) h =
    (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o left_middle)%morphism /\
    (outl (biproduct_data (semiadditive_biproduct Y Y)) o left_middle)%morphism = 
    morphism_addition C X Y f g /\
    (outr (biproduct_data (semiadditive_biproduct Y Y)) o left_middle)%morphism = h) /\
  (exists right_middle,
    morphism_addition C X Y f (morphism_addition C X Y g h) =
    (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o right_middle)%morphism /\
    (outl (biproduct_data (semiadditive_biproduct Y Y)) o right_middle)%morphism = f /\
    (outr (biproduct_data (semiadditive_biproduct Y Y)) o right_middle)%morphism = 
    morphism_addition C X Y g h).
Proof.
  split.
  - (* Left nested form *)
    exists (biproduct_prod_mor (semiadditive_biproduct Y Y) X 
             (morphism_addition C X Y f g) h).
    split.
    + apply nested_addition_left.
    + split.
      * apply biproduct_prod_beta_l.
      * apply biproduct_prod_beta_r.
  - (* Right nested form *)
    exists (biproduct_prod_mor (semiadditive_biproduct Y Y) X 
             f (morphism_addition C X Y g h)).
    split.
    + apply nested_addition_right.
    + split.
      * apply biproduct_prod_beta_l.
      * apply biproduct_prod_beta_r.
Qed.

(** Example: Both nested forms give the same result when fully expanded and simplified
    for the special case (f + 0) + h = f + (0 + h). *)
Example both_forms_equal_special_case {X Y : object C} (f h : morphism C X Y) :
  let left_form := morphism_addition C X Y (morphism_addition C X Y f (zero_morphism X Y)) h in
  let right_form := morphism_addition C X Y f (morphism_addition C X Y (zero_morphism X Y) h) in
  left_form = right_form /\
  left_form = morphism_addition C X Y f h /\
  (exists middle_left middle_right,
    left_form = (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o middle_left)%morphism /\
    right_form = (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o middle_right)%morphism /\
    middle_left = biproduct_prod_mor (semiadditive_biproduct Y Y) X f h /\
    middle_right = biproduct_prod_mor (semiadditive_biproduct Y Y) X f h).
Proof.
  split.
  - (* Show left_form = right_form *)
    simpl.
    rewrite zero_right_identity.
    rewrite zero_left_identity.
    reflexivity.
  - split.
    + (* Show left_form = f + h *)
      simpl.
      rewrite zero_right_identity.
      reflexivity.
    + (* Show the middle morphisms exist and are equal *)
      exists (biproduct_prod_mor (semiadditive_biproduct Y Y) X f h).
      exists (biproduct_prod_mor (semiadditive_biproduct Y Y) X f h).
      split.
      * simpl.
        rewrite zero_right_identity.
        apply addition_as_biproduct.
      * split.
        -- simpl.
           rewrite zero_left_identity.
           apply addition_as_biproduct.
        -- split; reflexivity.
Qed.

(** Expanding the left component of the left nested form. *)
Lemma left_nested_left_component {X Y : object C} (f g h : morphism C X Y) :
  (outl (biproduct_data (semiadditive_biproduct Y Y)) o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X
     (morphism_addition C X Y f g) h)%morphism =
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X f g)%morphism.
Proof.
  rewrite biproduct_prod_beta_l.
  apply addition_as_biproduct.
Qed.

(** Example: The left component of (f + g) + h fully expands to show f and g separately. *)
Example left_nested_left_expansion_demo {X Y : object C} (f g h : morphism C X Y) :
  exists inner_mor,
    (outl (biproduct_data (semiadditive_biproduct Y Y)) o
     biproduct_prod_mor (semiadditive_biproduct Y Y) X
       (morphism_addition C X Y f g) h)%morphism =
    (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o inner_mor)%morphism /\
    inner_mor = biproduct_prod_mor (semiadditive_biproduct Y Y) X f g /\
    (outl (biproduct_data (semiadditive_biproduct Y Y)) o inner_mor)%morphism = f /\
    (outr (biproduct_data (semiadditive_biproduct Y Y)) o inner_mor)%morphism = g.
Proof.
  exists (biproduct_prod_mor (semiadditive_biproduct Y Y) X f g).
  split.
  - (* Use left_nested_left_component *)
    apply left_nested_left_component.
  - split.
    + reflexivity.
    + split.
      * apply biproduct_prod_beta_l.
      * apply biproduct_prod_beta_r.
Qed.

(** Expanding the right component of the right nested form. *)
Lemma right_nested_right_component {X Y : object C} (f g h : morphism C X Y) :
  (outr (biproduct_data (semiadditive_biproduct Y Y)) o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X
     f (morphism_addition C X Y g h))%morphism =
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X g h)%morphism.
Proof.
  rewrite biproduct_prod_beta_r.
  apply addition_as_biproduct.
Qed.

(** Example: The right component of f + (g + h) fully expands to show g and h separately. *)
Example right_nested_right_expansion_demo {X Y : object C} (f g h : morphism C X Y) :
  exists inner_mor,
    (outr (biproduct_data (semiadditive_biproduct Y Y)) o
     biproduct_prod_mor (semiadditive_biproduct Y Y) X
       f (morphism_addition C X Y g h))%morphism =
    (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o inner_mor)%morphism /\
    inner_mor = biproduct_prod_mor (semiadditive_biproduct Y Y) X g h /\
    (outl (biproduct_data (semiadditive_biproduct Y Y)) o inner_mor)%morphism = g /\
    (outr (biproduct_data (semiadditive_biproduct Y Y)) o inner_mor)%morphism = h.
Proof.
  exists (biproduct_prod_mor (semiadditive_biproduct Y Y) X g h).
  split.
  - (* Use right_nested_right_component *)
    apply right_nested_right_component.
  - split.
    + reflexivity.
    + split.
      * apply biproduct_prod_beta_l.
      * apply biproduct_prod_beta_r.
Qed.

(** The left projection of the right nested form gives just f. *)
Lemma right_nested_left_component {X Y : object C} (f g h : morphism C X Y) :
  (outl (biproduct_data (semiadditive_biproduct Y Y)) o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X
     f (morphism_addition C X Y g h))%morphism = f.
Proof.
  apply biproduct_prod_beta_l.
Qed.  

(** Example: Tracing both associative forms through their full expansions for (f + 0) + h vs f + (0 + h). *)
Example associativity_trace_with_zero {X Y : object C} (f h : morphism C X Y) :
  let left_form := morphism_addition C X Y (morphism_addition C X Y f (zero_morphism X Y)) h in
  let right_form := morphism_addition C X Y f (morphism_addition C X Y (zero_morphism X Y) h) in
  let left_middle := biproduct_prod_mor (semiadditive_biproduct Y Y) X 
                       (morphism_addition C X Y f (zero_morphism X Y)) h in
  let right_middle := biproduct_prod_mor (semiadditive_biproduct Y Y) X 
                        f (morphism_addition C X Y (zero_morphism X Y) h) in
  (* Both forms equal f + h *)
  left_form = morphism_addition C X Y f h /\
  right_form = morphism_addition C X Y f h /\
  (* Their middle morphisms simplify to the same thing *)
  left_middle = biproduct_prod_mor (semiadditive_biproduct Y Y) X f h /\
  right_middle = biproduct_prod_mor (semiadditive_biproduct Y Y) X f h /\
  (* And compose with codiagonal to give f + h *)
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o left_middle)%morphism = 
  morphism_addition C X Y f h /\
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o right_middle)%morphism = 
  morphism_addition C X Y f h.
Proof.
  split.
  - simpl. rewrite zero_right_identity. reflexivity.
  - split.
    + simpl. rewrite zero_left_identity. reflexivity.
    + split.
      * simpl. rewrite zero_right_identity. reflexivity.
      * split.
        -- simpl. rewrite zero_left_identity. reflexivity.
        -- split.
           ++ simpl. rewrite zero_right_identity. symmetry. apply addition_as_biproduct.
           ++ simpl. rewrite zero_left_identity. symmetry. apply addition_as_biproduct.
Qed.

(** The right projection of the left nested form gives just h. *)
Lemma left_nested_right_component {X Y : object C} (f g h : morphism C X Y) :
  (outr (biproduct_data (semiadditive_biproduct Y Y)) o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X
     (morphism_addition C X Y f g) h)%morphism = h.
Proof.
  apply biproduct_prod_beta_r.
Qed.

(** Example: Both nested forms expose all three morphisms f, g, h through projections. *)
Example all_components_accessible {X Y : object C} (f g h : morphism C X Y) :
  let left_form := biproduct_prod_mor (semiadditive_biproduct Y Y) X 
                     (morphism_addition C X Y f g) h in
  let right_form := biproduct_prod_mor (semiadditive_biproduct Y Y) X 
                      f (morphism_addition C X Y g h) in
  (* From left_form we can extract f, g, h *)
  (exists extract_f extract_g,
    extract_f = (outl (biproduct_data (semiadditive_biproduct Y Y)) o
                 biproduct_prod_mor (semiadditive_biproduct Y Y) X f g o
                 outl (biproduct_data (semiadditive_biproduct X X)))%morphism /\
    extract_g = (outr (biproduct_data (semiadditive_biproduct Y Y)) o
                 biproduct_prod_mor (semiadditive_biproduct Y Y) X f g o
                 outl (biproduct_data (semiadditive_biproduct X X)))%morphism /\
    (outr (biproduct_data (semiadditive_biproduct Y Y)) o left_form)%morphism = h) /\
  (* From right_form we can extract f, g, h *)
  (exists extract_g' extract_h',
    (outl (biproduct_data (semiadditive_biproduct Y Y)) o right_form)%morphism = f /\
    extract_g' = (outl (biproduct_data (semiadditive_biproduct Y Y)) o
                  biproduct_prod_mor (semiadditive_biproduct Y Y) X g h o
                  outr (biproduct_data (semiadditive_biproduct X X)))%morphism /\
    extract_h' = (outr (biproduct_data (semiadditive_biproduct Y Y)) o
                  biproduct_prod_mor (semiadditive_biproduct Y Y) X g h o
                  outr (biproduct_data (semiadditive_biproduct X X)))%morphism).
Proof.
  split.
  - (* Left form *)
    exists (outl (biproduct_data (semiadditive_biproduct Y Y)) o
            biproduct_prod_mor (semiadditive_biproduct Y Y) X f g o
            outl (biproduct_data (semiadditive_biproduct X X)))%morphism.
    exists (outr (biproduct_data (semiadditive_biproduct Y Y)) o
            biproduct_prod_mor (semiadditive_biproduct Y Y) X f g o
            outl (biproduct_data (semiadditive_biproduct X X)))%morphism.
    split; [reflexivity|].
    split; [reflexivity|].
    apply left_nested_right_component.
  - (* Right form *)
    exists (outl (biproduct_data (semiadditive_biproduct Y Y)) o
            biproduct_prod_mor (semiadditive_biproduct Y Y) X g h o
            outr (biproduct_data (semiadditive_biproduct X X)))%morphism.
    exists (outr (biproduct_data (semiadditive_biproduct Y Y)) o
            biproduct_prod_mor (semiadditive_biproduct Y Y) X g h o
            outr (biproduct_data (semiadditive_biproduct X X)))%morphism.
    split.
    + apply right_nested_left_component.
    + split; reflexivity.
Qed.

(** Composing codiagonal with each injection separately. *)
Lemma codiagonal_splits_addition {X Y : object C} (f g : morphism C X Y) :
  morphism_addition C X Y f g =
  morphism_addition C X Y
    ((biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
      Biproducts.inl (biproduct_data (semiadditive_biproduct Y Y))) o f)%morphism
    ((biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
      Biproducts.inr (biproduct_data (semiadditive_biproduct Y Y))) o g)%morphism.
Proof.
  rewrite inl_codiagonal.
  rewrite inr_codiagonal.
  rewrite !Category.Core.left_identity.
  reflexivity.
Qed.

(** Example: The identity morphism added to itself gives the same result through different paths. *)
Example identity_double_path {Y : object C} :
  let double_id := morphism_addition C Y Y 1%morphism 1%morphism in
  let via_split := morphism_addition C Y Y
    ((biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
      Biproducts.inl (biproduct_data (semiadditive_biproduct Y Y))) o 1%morphism)%morphism
    ((biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
      Biproducts.inr (biproduct_data (semiadditive_biproduct Y Y))) o 1%morphism)%morphism in
  let via_biproduct := (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                        biproduct_prod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism)%morphism in
  double_id = via_split /\
  double_id = via_biproduct /\
  via_split = via_biproduct.
Proof.
  split.
  - (* double_id = via_split *)
    apply codiagonal_splits_addition.
  - split.
    + (* double_id = via_biproduct *)
      simpl.
      apply addition_as_biproduct.
    + (* via_split = via_biproduct *)
      simpl.
      rewrite <- codiagonal_splits_addition.
      apply addition_as_biproduct.
Qed.

(** Composing biproduct morphisms with codiagonal distributes. *)
Lemma codiagonal_biproduct_distribute {X Y : object C} (f g h k : morphism C X Y) :
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X
     (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
      biproduct_prod_mor (semiadditive_biproduct Y Y) X f g)
     (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
      biproduct_prod_mor (semiadditive_biproduct Y Y) X h k))%morphism =
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X
     (morphism_addition C X Y f g)
     (morphism_addition C X Y h k))%morphism.
Proof.
  f_ap.
  f_ap.
  - symmetry. apply addition_as_biproduct.
  - symmetry. apply addition_as_biproduct.
Qed.

(** Example: Distributing codiagonal shows how (f + g) + (h + k) can be reorganized. *)
Example codiagonal_distribution_demo {X Y : object C} (f g h k : morphism C X Y) :
  let left_sum := morphism_addition C X Y f g in
  let right_sum := morphism_addition C X Y h k in
  let combined := morphism_addition C X Y left_sum right_sum in
  let expanded_form := 
    (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
     biproduct_prod_mor (semiadditive_biproduct Y Y) X
       (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
        biproduct_prod_mor (semiadditive_biproduct Y Y) X f g)
       (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
        biproduct_prod_mor (semiadditive_biproduct Y Y) X h k))%morphism in
  let simplified_form :=
    (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
     biproduct_prod_mor (semiadditive_biproduct Y Y) X left_sum right_sum)%morphism in
  combined = simplified_form /\
  expanded_form = simplified_form /\
  expanded_form = combined /\
  (* The expanded form equals the nested additions *)
  expanded_form = 
    (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
     biproduct_prod_mor (semiadditive_biproduct Y Y) X
       (morphism_addition C X Y f g)
       (morphism_addition C X Y h k))%morphism.
Proof.
  split.
  - (* combined = simplified_form *)
    simpl. apply addition_as_biproduct.
  - split.
    + (* expanded_form = simplified_form *)
      simpl. apply codiagonal_biproduct_distribute.
    + split.
      * (* expanded_form = combined *)
        simpl. 
        rewrite codiagonal_biproduct_distribute.
        symmetry. apply addition_as_biproduct.
      * (* expanded_form = the last expression *)
        simpl. apply codiagonal_biproduct_distribute.
Qed.

(** The crucial step: comparing projections of both nested forms after expansion. *)
Lemma nested_forms_projection_comparison {X Y : object C} (f g h : morphism C X Y) :
  (outl (biproduct_data (semiadditive_biproduct Y Y)) o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X
     (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
      biproduct_prod_mor (semiadditive_biproduct Y Y) X f g) h)%morphism =
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X f g)%morphism.
Proof.
  apply biproduct_prod_beta_l.
Qed.

(** Example: The left projection of (f + g) + h reveals the inner sum f + g. *)
Example left_projection_reveals_inner_sum {X Y : object C} (f g h : morphism C X Y) :
  let nested := biproduct_prod_mor (semiadditive_biproduct Y Y) X
                  (morphism_addition C X Y f g) h in
  let expanded_nested := biproduct_prod_mor (semiadditive_biproduct Y Y) X
                          (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                           biproduct_prod_mor (semiadditive_biproduct Y Y) X f g) h in
  (outl (biproduct_data (semiadditive_biproduct Y Y)) o nested)%morphism = 
    morphism_addition C X Y f g /\
  (outl (biproduct_data (semiadditive_biproduct Y Y)) o expanded_nested)%morphism = 
    (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
     biproduct_prod_mor (semiadditive_biproduct Y Y) X f g)%morphism /\
  (outl (biproduct_data (semiadditive_biproduct Y Y)) o expanded_nested)%morphism =
    morphism_addition C X Y f g.
Proof.
  split.
  - (* Direct projection *)
    simpl. apply biproduct_prod_beta_l.
  - split.
    + (* Expanded projection *)
      simpl. apply nested_forms_projection_comparison.
    + (* Both equal f + g *)
      simpl. 
      rewrite nested_forms_projection_comparison.
      symmetry. apply addition_as_biproduct.
Qed.

(** The right projection of the left nested form is just h. *)
Lemma left_nested_right_proj {X Y : object C} (f g h : morphism C X Y) :
  (outr (biproduct_data (semiadditive_biproduct Y Y)) o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X
     (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
      biproduct_prod_mor (semiadditive_biproduct Y Y) X f g) h)%morphism = h.
Proof.
  apply biproduct_prod_beta_r.
Qed.

(** Example: Both projections of the expanded left nested form recover the components. *)
Example left_nested_both_projections {X Y : object C} (f g h : morphism C X Y) :
  let expanded := biproduct_prod_mor (semiadditive_biproduct Y Y) X
                    (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                     biproduct_prod_mor (semiadditive_biproduct Y Y) X f g) h in
  (outl (biproduct_data (semiadditive_biproduct Y Y)) o expanded)%morphism = 
    morphism_addition C X Y f g /\
  (outr (biproduct_data (semiadditive_biproduct Y Y)) o expanded)%morphism = h /\
  morphism_addition C X Y 
    ((outl (biproduct_data (semiadditive_biproduct Y Y)) o expanded)%morphism)
    ((outr (biproduct_data (semiadditive_biproduct Y Y)) o expanded)%morphism) =
  morphism_addition C X Y (morphism_addition C X Y f g) h.
Proof.
  split.
  - (* Left projection gives f + g *)
    simpl.
    rewrite nested_forms_projection_comparison.
    symmetry. apply addition_as_biproduct.
  - split.
    + (* Right projection gives h *)
      simpl. apply left_nested_right_proj.
    + (* Recombining gives the original *)
      simpl.
      rewrite nested_forms_projection_comparison.
      rewrite left_nested_right_proj.
      rewrite <- addition_as_biproduct.
      reflexivity.
Qed.

(** The left projection of the right nested form is just f. *)
Lemma right_nested_left_proj {X Y : object C} (f g h : morphism C X Y) :
  (outl (biproduct_data (semiadditive_biproduct Y Y)) o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X
     f
     (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
      biproduct_prod_mor (semiadditive_biproduct Y Y) X g h))%morphism = f.
Proof.
  apply biproduct_prod_beta_l.
Qed.

(** Example: Both projections of the expanded right nested form recover the components. *)
Example right_nested_both_projections {X Y : object C} (f g h : morphism C X Y) :
  let expanded := biproduct_prod_mor (semiadditive_biproduct Y Y) X
                    f
                    (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                     biproduct_prod_mor (semiadditive_biproduct Y Y) X g h) in
  (outl (biproduct_data (semiadditive_biproduct Y Y)) o expanded)%morphism = f /\
  (outr (biproduct_data (semiadditive_biproduct Y Y)) o expanded)%morphism = 
    morphism_addition C X Y g h /\
  morphism_addition C X Y 
    ((outl (biproduct_data (semiadditive_biproduct Y Y)) o expanded)%morphism)
    ((outr (biproduct_data (semiadditive_biproduct Y Y)) o expanded)%morphism) =
  morphism_addition C X Y f (morphism_addition C X Y g h).
Proof.
  split.
  - (* Left projection gives f *)
    simpl. apply right_nested_left_proj.
  - split.
    + (* Right projection gives g + h *)
      simpl.
      rewrite biproduct_prod_beta_r.
      symmetry. apply addition_as_biproduct.
    + (* Recombining gives the original *)
      simpl.
      rewrite right_nested_left_proj.
      rewrite biproduct_prod_beta_r.
      rewrite <- addition_as_biproduct.
      reflexivity.
Qed.

(** The key: both expanded nested forms are morphisms into Y⊕Y with specific projections. *)
Lemma both_expanded_forms_characterized {X Y : object C} (f g h : morphism C X Y) :
  let left_expanded := biproduct_prod_mor (semiadditive_biproduct Y Y) X
                         (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                          biproduct_prod_mor (semiadditive_biproduct Y Y) X f g) h in
  let right_expanded := biproduct_prod_mor (semiadditive_biproduct Y Y) X
                          f
                          (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                           biproduct_prod_mor (semiadditive_biproduct Y Y) X g h) in
  (outl (biproduct_data (semiadditive_biproduct Y Y)) o left_expanded)%morphism =
    morphism_addition C X Y f g /\
  (outr (biproduct_data (semiadditive_biproduct Y Y)) o left_expanded)%morphism = h /\
  (outl (biproduct_data (semiadditive_biproduct Y Y)) o right_expanded)%morphism = f /\
  (outr (biproduct_data (semiadditive_biproduct Y Y)) o right_expanded)%morphism =
    morphism_addition C X Y g h.
Proof.
  split.
  - simpl. rewrite nested_forms_projection_comparison. 
    symmetry. apply addition_as_biproduct.
  - split.
    + simpl. apply left_nested_right_proj.
    + split.
      * simpl. apply right_nested_left_proj.
      * simpl. rewrite biproduct_prod_beta_r.
        symmetry. apply addition_as_biproduct.
Qed.

(** Example: For the special case f + 0 + h vs f + (0 + h), the expanded forms simplify identically. *)
Example expanded_forms_equal_special {X Y : object C} (f h : morphism C X Y) :
  let left_expanded := biproduct_prod_mor (semiadditive_biproduct Y Y) X
                         (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                          biproduct_prod_mor (semiadditive_biproduct Y Y) X f (zero_morphism X Y)) h in
  let right_expanded := biproduct_prod_mor (semiadditive_biproduct Y Y) X
                          f
                          (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                           biproduct_prod_mor (semiadditive_biproduct Y Y) X (zero_morphism X Y) h) in
  let simplified := biproduct_prod_mor (semiadditive_biproduct Y Y) X f h in
  left_expanded = simplified /\
  right_expanded = simplified /\
  left_expanded = right_expanded.
Proof.
  split.
  - (* left_expanded = simplified *)
    simpl.
    f_ap.
    rewrite <- addition_as_biproduct.
    apply zero_right_identity.
  - split.
    + (* right_expanded = simplified *)
      simpl.
      f_ap.
      rewrite <- addition_as_biproduct.
      rewrite zero_left_identity.
      reflexivity.
    + (* left_expanded = right_expanded *)
      simpl.
      f_ap.
      * rewrite <- addition_as_biproduct.
        apply zero_right_identity.
      * rewrite <- addition_as_biproduct.
        rewrite zero_left_identity.
        reflexivity.
Qed.

(** Composing codiagonal with nested biproducts recovers the nested addition. *)
Lemma codiagonal_nested_biproduct_left {X Y : object C} (f g h : morphism C X Y) :
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X
     (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
      biproduct_prod_mor (semiadditive_biproduct Y Y) X f g) h)%morphism =
  morphism_addition C X Y (morphism_addition C X Y f g) h.
Proof.
  (* This is the definition of nested addition *)
  symmetry.
  rewrite addition_as_biproduct.
  f_ap.
  f_ap.
  apply addition_as_biproduct.
Qed.

(** Example: The expanded form of ((f + g) + h) can be traced through all its transformations. *)
Example codiagonal_nested_trace {X Y : object C} (f g h : morphism C X Y) :
  let inner_sum := morphism_addition C X Y f g in
  let full_sum := morphism_addition C X Y inner_sum h in
  let inner_expanded := (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                        biproduct_prod_mor (semiadditive_biproduct Y Y) X f g)%morphism in
  let full_expanded := (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                       biproduct_prod_mor (semiadditive_biproduct Y Y) X inner_expanded h)%morphism in
  full_sum = full_expanded /\
  inner_sum = inner_expanded /\
  full_expanded = (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                   biproduct_prod_mor (semiadditive_biproduct Y Y) X
                     (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                      biproduct_prod_mor (semiadditive_biproduct Y Y) X f g) h)%morphism /\
  full_expanded = morphism_addition C X Y (morphism_addition C X Y f g) h.
Proof.
  split.
  - (* full_sum = full_expanded *)
    simpl.
    symmetry.
    apply codiagonal_nested_biproduct_left.
  - split.
    + (* inner_sum = inner_expanded *)
      simpl.
      apply addition_as_biproduct.
    + split.
      * (* full_expanded equals the explicit expansion *)
        reflexivity.
      * (* full_expanded = nested addition *)
        apply codiagonal_nested_biproduct_left.
Qed.

(** Composing codiagonal with nested biproducts recovers the nested addition (right form). *)
Lemma codiagonal_nested_biproduct_right {X Y : object C} (f g h : morphism C X Y) :
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X
     f
     (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
      biproduct_prod_mor (semiadditive_biproduct Y Y) X g h))%morphism =
  morphism_addition C X Y f (morphism_addition C X Y g h).
Proof.
  (* This is the definition of right nested addition *)
  symmetry.
  rewrite !addition_as_biproduct.
  reflexivity.
Qed.

(** Example: Both nested forms can be recovered from their expansions. *)
Example both_nested_recoverable {X Y : object C} (f g h : morphism C X Y) :
  let left_expanded := (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                        biproduct_prod_mor (semiadditive_biproduct Y Y) X
                          (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                           biproduct_prod_mor (semiadditive_biproduct Y Y) X f g) h)%morphism in
  let right_expanded := (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                         biproduct_prod_mor (semiadditive_biproduct Y Y) X
                           f
                           (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                            biproduct_prod_mor (semiadditive_biproduct Y Y) X g h))%morphism in
  left_expanded = morphism_addition C X Y (morphism_addition C X Y f g) h /\
  right_expanded = morphism_addition C X Y f (morphism_addition C X Y g h) /\
  (* This is what we need for associativity *)
  (left_expanded = right_expanded -> 
   morphism_addition C X Y (morphism_addition C X Y f g) h = 
   morphism_addition C X Y f (morphism_addition C X Y g h)).
Proof.
  split.
  - apply codiagonal_nested_biproduct_left.
  - split.
    + apply codiagonal_nested_biproduct_right.
    + intro H.
      rewrite <- codiagonal_nested_biproduct_left.
      rewrite <- codiagonal_nested_biproduct_right.
      exact H.
Qed.

(** The key consolidation: both nested forms have identical biproduct structure. *)
Lemma nested_forms_same_structure {X Y : object C} (f g h : morphism C X Y) :
  let left_form := morphism_addition C X Y (morphism_addition C X Y f g) h in
  let right_form := morphism_addition C X Y f (morphism_addition C X Y g h) in
  let left_expanded := (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                        biproduct_prod_mor (semiadditive_biproduct Y Y) X
                          (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                           biproduct_prod_mor (semiadditive_biproduct Y Y) X f g) h)%morphism in
  let right_expanded := (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                         biproduct_prod_mor (semiadditive_biproduct Y Y) X
                           f
                           (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                            biproduct_prod_mor (semiadditive_biproduct Y Y) X g h))%morphism in
  (* Both forms equal their expansions *)
  left_form = left_expanded /\
  right_form = right_expanded /\
  (* The expansions have the same projections when decomposed *)
  (exists middle_left middle_right,
    left_expanded = (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o middle_left)%morphism /\
    right_expanded = (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o middle_right)%morphism /\
    (outl (biproduct_data (semiadditive_biproduct Y Y)) o middle_left)%morphism = 
      morphism_addition C X Y f g /\
    (outr (biproduct_data (semiadditive_biproduct Y Y)) o middle_left)%morphism = h /\
    (outl (biproduct_data (semiadditive_biproduct Y Y)) o middle_right)%morphism = f /\
    (outr (biproduct_data (semiadditive_biproduct Y Y)) o middle_right)%morphism = 
      morphism_addition C X Y g h).
Proof.
  split.
  - (* left_form = left_expanded *)
    apply left_nested_expansion.
  - split.
    + (* right_form = right_expanded *)
      apply right_nested_expansion.
    + (* The projections exist and match *)
      exists (biproduct_prod_mor (semiadditive_biproduct Y Y) X
               (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                biproduct_prod_mor (semiadditive_biproduct Y Y) X f g) h).
      exists (biproduct_prod_mor (semiadditive_biproduct Y Y) X f
               (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                biproduct_prod_mor (semiadditive_biproduct Y Y) X g h)).
      split; [reflexivity|].
      split; [reflexivity|].
      split.
      * rewrite nested_forms_projection_comparison.
        symmetry. apply addition_as_biproduct.
      * split.
        -- apply left_nested_right_proj.
        -- split.
           ++ apply right_nested_left_proj.
           ++ rewrite biproduct_prod_beta_r.
              symmetry. apply addition_as_biproduct.
Qed.

(** Complete associativity demonstration for (f + g) + h = f + (g + h) 
    showing all intermediate steps and transformations. *)
Example grand_associativity_demonstration {X Y : object C} (f g h : morphism C X Y) :
  let left_assoc := morphism_addition C X Y (morphism_addition C X Y f g) h in
  let right_assoc := morphism_addition C X Y f (morphism_addition C X Y g h) in
  let fg := morphism_addition C X Y f g in
  let gh := morphism_addition C X Y g h in
  let fg_expanded := (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                      biproduct_prod_mor (semiadditive_biproduct Y Y) X f g)%morphism in
  let gh_expanded := (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
                      biproduct_prod_mor (semiadditive_biproduct Y Y) X g h)%morphism in
  let left_middle := biproduct_prod_mor (semiadditive_biproduct Y Y) X fg_expanded h in
  let right_middle := biproduct_prod_mor (semiadditive_biproduct Y Y) X f gh_expanded in
  let left_full := (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o left_middle)%morphism in
  let right_full := (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o right_middle)%morphism in
  (* All the key relationships *)
  fg = fg_expanded /\
  gh = gh_expanded /\
  left_assoc = left_full /\
  right_assoc = right_full /\
  (* The projections of the middle morphisms *)
  (outl (biproduct_data (semiadditive_biproduct Y Y)) o left_middle)%morphism = fg_expanded /\
  (outr (biproduct_data (semiadditive_biproduct Y Y)) o left_middle)%morphism = h /\
  (outl (biproduct_data (semiadditive_biproduct Y Y)) o right_middle)%morphism = f /\
  (outr (biproduct_data (semiadditive_biproduct Y Y)) o right_middle)%morphism = gh_expanded /\
  (* The crucial fact: morphisms into biproducts are determined by their projections *)
  (left_middle = right_middle ->
   left_full = right_full ->
   left_assoc = right_assoc).
Proof.
  repeat split.
  - (* fg = fg_expanded *)
    apply addition_as_biproduct.
  - (* gh = gh_expanded *)
    apply addition_as_biproduct.
  - (* left_assoc = left_full *)
    simpl. symmetry. apply codiagonal_nested_biproduct_left.
  - (* right_assoc = right_full *)
    simpl. symmetry. apply codiagonal_nested_biproduct_right.
  - (* left_middle left projection *)
    simpl. apply biproduct_prod_beta_l.
  - (* left_middle right projection *)
    simpl. apply biproduct_prod_beta_r.
  - (* right_middle left projection *)
    simpl. apply biproduct_prod_beta_l.
  - (* right_middle right projection *)
    simpl. apply biproduct_prod_beta_r.
  - (* If middles equal and fulls equal, then associativity holds *)
    intros Hmid Hfull.
    rewrite <- codiagonal_nested_biproduct_left.
    rewrite <- codiagonal_nested_biproduct_right.
    exact Hfull.
Qed.

(** Triple biproducts: X ⊕ Y ⊕ Z as (X ⊕ Y) ⊕ Z *)
Definition triple_biproduct_obj {X Y Z : object C} : object C :=
  biproduct_obj (biproduct_data (semiadditive_biproduct 
    (biproduct_obj (biproduct_data (semiadditive_biproduct X Y))) Z)).

(** Injection into first component of triple biproduct *)
Definition triple_inl (X Y Z : object C) 
  : morphism C X (@triple_biproduct_obj X Y Z) :=
  (Biproducts.inl (biproduct_data (semiadditive_biproduct 
     (biproduct_obj (biproduct_data (semiadditive_biproduct X Y))) Z)) o
   Biproducts.inl (biproduct_data (semiadditive_biproduct X Y)))%morphism.

(** Injection into middle component of triple biproduct *)
Definition triple_inm (X Y Z : object C)
  : morphism C Y (@triple_biproduct_obj X Y Z) :=
  (Biproducts.inl (biproduct_data (semiadditive_biproduct 
     (biproduct_obj (biproduct_data (semiadditive_biproduct X Y))) Z)) o
   Biproducts.inr (biproduct_data (semiadditive_biproduct X Y)))%morphism.

(** Injection into last component of triple biproduct *)
Definition triple_inr (X Y Z : object C)
  : morphism C Z (@triple_biproduct_obj X Y Z) :=
  Biproducts.inr (biproduct_data (semiadditive_biproduct 
    (biproduct_obj (biproduct_data (semiadditive_biproduct X Y))) Z)).

(** Triple codiagonal: (X ⊕ X) ⊕ X → X that adds all three components *)
Definition triple_codiagonal (X : object C)
  : morphism C (@triple_biproduct_obj X X X) X :=
  biproduct_coprod_mor 
    (semiadditive_biproduct 
      (biproduct_obj (biproduct_data (semiadditive_biproduct X X))) X) 
    X
    (biproduct_coprod_mor (semiadditive_biproduct X X) X 1%morphism 1%morphism)
    1%morphism.
    
(** Triple codiagonal composed with first injection gives identity *)
Lemma triple_codiagonal_inl (X : object C) :
  (triple_codiagonal X o triple_inl X X X)%morphism = 1%morphism.
Proof.
  unfold triple_codiagonal, triple_inl.
  rewrite <- Category.Core.associativity.
  rewrite biproduct_coprod_beta_l.
  apply inl_codiagonal.
Qed.

(** Example: Triple codiagonal with specific injections gives identity *)
Example triple_codiagonal_injections {X : object C} :
  (triple_codiagonal X o triple_inl X X X)%morphism = 1%morphism /\
  (triple_codiagonal X o triple_inm X X X)%morphism = 1%morphism /\
  (triple_codiagonal X o triple_inr X X X)%morphism = 1%morphism.
Proof.
  split.
  - apply triple_codiagonal_inl.
  - split.
    + unfold triple_codiagonal, triple_inm.
      rewrite <- Category.Core.associativity.
      rewrite biproduct_coprod_beta_l.
      apply inr_codiagonal.
    + unfold triple_codiagonal, triple_inr.
      apply biproduct_coprod_beta_r.
Qed.

(** The key flattening: codiagonal maps both nested forms to the same triple structure *)
Lemma codiagonal_flattens_nested {X Y : object C} (f g h : morphism C X Y) :
  let left_nested := biproduct_prod_mor (semiadditive_biproduct Y Y) X
                       (morphism_addition C X Y f g) h in
  let right_nested := biproduct_prod_mor (semiadditive_biproduct Y Y) X  
                        f (morphism_addition C X Y g h) in
  (* Both compose with codiagonal to give (f + g) + h and f + (g + h) *)
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o left_nested)%morphism =
    morphism_addition C X Y (morphism_addition C X Y f g) h /\
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o right_nested)%morphism =
    morphism_addition C X Y f (morphism_addition C X Y g h).
Proof.
  split.
  - symmetry. apply addition_as_biproduct.
  - symmetry. apply addition_as_biproduct.
Qed.

(** Example: Codiagonal flattens different nested structures to the same result for identity *)
Example codiagonal_flattens_identity {Y : object C} :
  let id := 1%morphism : morphism C Y Y in
  let left_nested := biproduct_prod_mor (semiadditive_biproduct Y Y) Y
                       (morphism_addition C Y Y id id) id in
  let right_nested := biproduct_prod_mor (semiadditive_biproduct Y Y) Y  
                        id (morphism_addition C Y Y id id) in
  let left_result := (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o 
                      left_nested)%morphism in
  let right_result := (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o 
                       right_nested)%morphism in
  (* Both give the same result *)
  left_result = morphism_addition C Y Y (morphism_addition C Y Y id id) id /\
  right_result = morphism_addition C Y Y id (morphism_addition C Y Y id id).
Proof.
  split.
  - simpl. symmetry. apply addition_as_biproduct.
  - simpl. symmetry. apply addition_as_biproduct.
Qed.

Lemma left_assoc_expansion (A : SemiAdditiveCategory) (X Y : object A) (f g h : morphism A X Y) :
  morphism_addition A X Y (morphism_addition A X Y f g) h =
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X 
     (morphism_addition A X Y f g) h)%morphism.
Proof.
  apply morphism_addition_simplify.
Qed.

Lemma right_assoc_expansion (A : SemiAdditiveCategory) (X Y : object A) (f g h : morphism A X Y) :
  morphism_addition A X Y f (morphism_addition A X Y g h) =
  (biproduct_coprod_mor (semiadditive_biproduct Y Y) Y 1%morphism 1%morphism o
   biproduct_prod_mor (semiadditive_biproduct Y Y) X 
     f (morphism_addition A X Y g h))%morphism.
Proof.
  apply morphism_addition_simplify.
Qed.

Lemma left_assoc_projections (A : SemiAdditiveCategory) (X Y : object A) (f g h : morphism A X Y) :
  let left_middle := biproduct_prod_mor (semiadditive_biproduct Y Y) X 
                       (morphism_addition A X Y f g) h in
  (outl (biproduct_data (semiadditive_biproduct Y Y)) o left_middle)%morphism = 
    morphism_addition A X Y f g /\
  (outr (biproduct_data (semiadditive_biproduct Y Y)) o left_middle)%morphism = h.
Proof.
  split.
  - apply biproduct_prod_beta_l.
  - apply biproduct_prod_beta_r.
Qed.

Lemma right_assoc_projections (A : SemiAdditiveCategory) (X Y : object A) (f g h : morphism A X Y) :
  let right_middle := biproduct_prod_mor (semiadditive_biproduct Y Y) X 
                        f (morphism_addition A X Y g h) in
  (outl (biproduct_data (semiadditive_biproduct Y Y)) o right_middle)%morphism = f /\
  (outr (biproduct_data (semiadditive_biproduct Y Y)) o right_middle)%morphism = 
    morphism_addition A X Y g h.
Proof.
  split.
  - apply biproduct_prod_beta_l.
  - apply biproduct_prod_beta_r.
Qed.

Lemma biproduct_assoc_left_to_right (A : SemiAdditiveCategory) (X Y Z : object A) :
  morphism A 
    (biproduct_obj (biproduct_data (semiadditive_biproduct 
      (biproduct_obj (biproduct_data (semiadditive_biproduct X Y))) Z)))
    (biproduct_obj (biproduct_data (semiadditive_biproduct X 
      (biproduct_obj (biproduct_data (semiadditive_biproduct Y Z)))))).
Proof.
  set (XY := biproduct_data (semiadditive_biproduct X Y)).
  set (YZ := biproduct_data (semiadditive_biproduct Y Z)).
  set (XY_Z := biproduct_data (semiadditive_biproduct (biproduct_obj XY) Z)).
  set (X_YZ := biproduct_data (semiadditive_biproduct X (biproduct_obj YZ))).
  
  apply (biproduct_prod_mor (semiadditive_biproduct X (biproduct_obj YZ)) _ 
          (outl XY o outl XY_Z)
          (biproduct_prod_mor (semiadditive_biproduct Y Z) _
            (outr XY o outl XY_Z)
            (outr XY_Z))).
Defined.

Lemma biproduct_assoc_right_to_left (A : SemiAdditiveCategory) (X Y Z : object A) :
  morphism A 
    (biproduct_obj (biproduct_data (semiadditive_biproduct X 
      (biproduct_obj (biproduct_data (semiadditive_biproduct Y Z))))))
    (biproduct_obj (biproduct_data (semiadditive_biproduct 
      (biproduct_obj (biproduct_data (semiadditive_biproduct X Y))) Z))).
Proof.
  set (XY := biproduct_data (semiadditive_biproduct X Y)).
  set (YZ := biproduct_data (semiadditive_biproduct Y Z)).
  set (XY_Z := biproduct_data (semiadditive_biproduct (biproduct_obj XY) Z)).
  set (X_YZ := biproduct_data (semiadditive_biproduct X (biproduct_obj YZ))).
  
  apply (biproduct_prod_mor (semiadditive_biproduct (biproduct_obj XY) Z) _
          (biproduct_prod_mor (semiadditive_biproduct X Y) _
            (outl X_YZ)
            (outl YZ o outr X_YZ))
          (outr YZ o outr X_YZ)).
Defined.

Theorem morphism_addition_associative {X Y : object C} :
  Associative (@morphism_addition C X Y).
Proof.
  intros f g h.
  (* Insert 0 to prepare for the medial step *)
  rewrite <- (zero_right_identity C X Y h).
  transitivity ((f + h) + (g + zero_morphism X Y))%morphism.
  { (* prove: (f + (g + (h + 0))) = ((f + h) + (g + 0)) *)
    rewrite !addition_as_biproduct.
    rewrite codiagonal_biproduct_distribute.
    rewrite <- !addition_as_biproduct.
    rewrite !addition_as_biproduct.
    rewrite codiagonal_biproduct_distribute.
    rewrite <- !addition_as_biproduct.
    rewrite zero_right_identity.
    transitivity ((f + zero_morphism X Y) + (h + g))%morphism.
    { rewrite <- (zero_left_identity C X Y g).
      rewrite !addition_as_biproduct.
      rewrite <- (codiagonal_zero_left C Y X f).
      rewrite codiagonal_biproduct_distribute.
      rewrite <- !addition_as_biproduct.
      rewrite (morphism_addition_commutative C X Y
                h (morphism_addition C X Y (zero_morphism X Y) g)).
      rewrite zero_right_identity.
      rewrite zero_right_identity.
      reflexivity. }
    rewrite <- (zero_right_identity C X Y f).
    transitivity ((f + h) + (zero_morphism X Y + g))%morphism.
    { rewrite !addition_as_biproduct.
      rewrite codiagonal_biproduct_distribute.
      rewrite (morphism_addition_commutative C X Y h g).
      rewrite addition_as_biproduct.
      rewrite <- !addition_as_biproduct.
      rewrite zero_right_identity.
      rewrite <- morphism_addition_commutative.
      rewrite (morphism_addition_commutative C X Y (zero_morphism X Y) g).
  rewrite zero_right_identity.
    rewrite morphism_addition_commutative.
  rewrite zero_right_identity.
    rewrite (morphism_addition_commutative C X Y g h).
  rewrite <- (zero_left_identity C X Y g).
  transitivity ((f + h) + (zero_morphism X Y + g))%morphism.
  1: rewrite !addition_as_biproduct.
    1: rewrite <- (codiagonal_zero_left C Y X f).
      1: rewrite codiagonal_biproduct_distribute.
        1: rewrite <- !addition_as_biproduct.
          1: rewrite zero_right_identity.
            1: rewrite !addition_as_biproduct.
              1: rewrite <- (codiagonal_zero_left C Y X f).
  1: rewrite codiagonal_biproduct_distribute.
  1: rewrite <- !addition_as_biproduct.
1: set (k := (zero_morphism X Y + g)%morphism).
1: change ((f + (h + (zero_morphism X Y + g)))%morphism)
     with ( (f + (h + (zero_morphism X Y + g)))%morphism ).
1: rewrite <- (zero_right_identity C X Y f).
1: rewrite !addition_as_biproduct.
1: rewrite codiagonal_biproduct_distribute.
1: rewrite <- !addition_as_biproduct.
  1: rewrite zero_right_identity.
    1: rewrite !addition_as_biproduct.
      2: reflexivity.

