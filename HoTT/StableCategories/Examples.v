  (** * Examples of Stable Category Theory Structures

      This module provides concrete examples for the abstract structures
      defined in our formalization, built incrementally from the simplest
      to more complex.
  *)

  From HoTT Require Import Basics Types Categories.
  From HoTT.Categories Require Import Category.

  Require Import ZeroObjects.

  (** * Example 1: The Simplest Zero Object *)

  Module SimplestZeroObject.

    (** The one-object, one-morphism category. *)
    Definition OneCat : PreCategory.
    Proof.
      simple refine (@Build_PreCategory
        Unit                          (* Type of objects *)
        (fun _ _ => Unit)            (* Morphism type *)
        (fun _ => tt)                (* Identity *)
        (fun _ _ _ _ _ => tt)        (* Composition *)
        _ _ _ _).                    
      - (* associativity *)
        intros s d d' d'' m1 m2 m3.
        destruct m1, m2, m3.
        reflexivity.
      - (* left identity *)  
        intros a b f.
        destruct a, b, f.
        reflexivity.
      - (* right identity *)
        intros a b f.
        destruct a, b, f.
        reflexivity.
    Defined.

      (** The unique object is a zero object. *)
      Theorem one_object_is_zero : ZeroObject OneCat.
      Proof.
        simple refine (Build_ZeroObject OneCat tt _ _).
      Defined.

    (** Verify the zero morphism is what we expect. *)
    Lemma zero_morphism_is_tt : 
      zero_morphism one_object_is_zero tt tt = tt.
    Proof.
      reflexivity.
    Qed.

  End SimplestZeroObject.

  (** * Example 2: A Category with Biproducts *)

  Module SimpleBiproductCategory.

  Require Import Biproducts.

    (** A two-object category with biproducts. 
        Objects: {0, 1} where 0 is zero object
        Morphisms: only identities and unique morphisms to/from 0 *)
    
    Inductive TwoObj : Type := Zero | One.
    
    Definition TwoMor (X Y : TwoObj) : Type :=
      match X, Y with
      | Zero, _ => Unit    (* unique morphism from zero *)
      | _, Zero => Unit    (* unique morphism to zero *)
      | One, One => Unit   (* identity on One *)
      end.
    
    Definition two_id (X : TwoObj) : TwoMor X X :=
      match X with
      | Zero => tt
      | One => tt
      end.
    
    Definition two_comp {X Y Z : TwoObj} (g : TwoMor Y Z) (f : TwoMor X Y) : TwoMor X Z.
    Proof.
      destruct X, Y, Z; try exact tt.
    Defined.
    
  Definition TwoCat : PreCategory.
  Proof.
    simple refine (@Build_PreCategory
      TwoObj
      TwoMor
      two_id
      (@two_comp)
      _ _ _ _).
    - (* associativity *)
      intros s d d' d'' m1 m2 m3.
      destruct s, d, d', d''; 
      try destruct m1; try destruct m2; try destruct m3; 
      reflexivity.
    - (* left identity *)
      intros a b f.
      destruct a, b; destruct f; reflexivity.
    - (* right identity *)
      intros a b f.
      destruct a, b; destruct f; reflexivity.
    - (* truncation: morphisms form a set *)
      intros s d.
      destruct s, d; apply _.
  Defined.
    
  (** Zero is the zero object. *)
  Theorem two_zero : ZeroObject TwoCat.
  Proof.
    simple refine (Build_ZeroObject TwoCat Zero _ _).
    - (* Zero is initial: unique morphism from Zero to any Y *)
      intro Y.
      destruct Y.
      + (* Y = Zero *)
        apply Build_Contr with (center := tt).
        intro f.
        unfold morphism in f; simpl in f.
        destruct f; reflexivity.
      + (* Y = One *)
        apply Build_Contr with (center := tt).
        intro f.
        unfold morphism in f; simpl in f.
        destruct f; reflexivity.
  Defined.
    
  (** The biproduct of One and One exists (it's One). *)
  Definition one_plus_one : @Biproduct TwoCat One One two_zero.
  Proof.
    (* Biproduct data *)
    pose (bdata := Build_BiproductData TwoCat One One One tt tt tt tt).
    
    (* Biproduct axioms *)
    assert (bis : IsBiproduct bdata two_zero).
    {
      simple refine (Build_IsBiproduct _ _ _ _ _ _ _ _ _).
      - reflexivity.  (* outl ∘ inl = id *)
      - reflexivity.  (* outr ∘ inr = id *)
      - reflexivity.  (* outl ∘ inr = 0 *)
      - reflexivity.  (* outr ∘ inl = 0 *)
    }
    

  (* Universal property *)
  assert (buni : HasBiproductUniversal bdata).
  {
    simple refine (Build_HasBiproductUniversal _ _ _ _ _ _).
    - (* Coproduct universal *)
      intros Z f g.
      destruct Z.
      + (* Z = Zero *)
        destruct f, g.
        apply Build_Contr with (center := (tt; (idpath, idpath))).
        intros [h' [p q]].
        apply path_sigma_uncurried.
        exists (match h' with tt => idpath end).
        simpl.
        apply path_prod; apply path_ishprop.
      + (* Z = One *)
        destruct f, g.
        apply Build_Contr with (center := (tt; (idpath, idpath))).
        intros [h' [p q]].
        apply path_sigma_uncurried.
        exists (match h' with tt => idpath end).
        simpl.
        apply path_prod; apply path_ishprop.
    - (* Product universal *)
      intros Z f g.
      destruct Z.
      + (* Z = Zero *)
        destruct f, g.
        apply Build_Contr with (center := (tt; (idpath, idpath))).
        intros [h' [p q]].
        apply path_sigma_uncurried.
        exists (match h' with tt => idpath end).
        simpl.
        apply path_prod; apply path_ishprop.
      + (* Z = One *)
        destruct f, g.
        apply Build_Contr with (center := (tt; (idpath, idpath))).
        intros [h' [p q]].
        apply path_sigma_uncurried.
        exists (match h' with tt => idpath end).
        simpl.
        apply path_prod; apply path_ishprop.
  }
exact (Build_Biproduct _ _ _ _ bdata bis buni).
  Defined.

End SimpleBiproductCategory.

Module TwoCatAdditive.
  Import SimpleBiproductCategory.
  Require Import Biproducts.
  Require Import AdditiveCategories.
  
  (* First prove all biproducts exist *)
  Definition two_all_biproducts (X Y : object TwoCat) : Biproduct X Y two_zero.
  Proof.
    destruct X, Y.
    - (* Zero ⊕ Zero = Zero *)
      pose (bdata := Build_BiproductData TwoCat Zero Zero Zero tt tt tt tt).
assert (bis : IsBiproduct bdata two_zero).
      {
        simple refine (Build_IsBiproduct _ _ _ _ _ _ _ _ _).
        - (* outl ∘ inl = id *) reflexivity.
        - (* outr ∘ inr = id *) reflexivity.
        - (* outl ∘ inr = 0 *) reflexivity.
        - (* outr ∘ inl = 0 *) reflexivity.
      }
assert (buni : HasBiproductUniversal bdata).
      {
        simple refine (Build_HasBiproductUniversal _ _ _ _ _ _).
        - (* Coproduct universal *)
          intros W f g.
          destruct W.
          + (* W = Zero *)
            destruct f, g.
            apply Build_Contr with (center := (tt; (idpath, idpath))).
            intros [h' [p q]].
            apply path_sigma_uncurried.
            exists (match h' with tt => idpath end).
            simpl.
            apply path_prod; apply path_ishprop.
          + (* W = One *)
            destruct f, g.
            apply Build_Contr with (center := (tt; (idpath, idpath))).
            intros [h' [p q]].
            apply path_sigma_uncurried.
            exists (match h' with tt => idpath end).
            simpl.
            apply path_prod; apply path_ishprop.
}
      exact (Build_Biproduct _ _ _ _ bdata bis buni).
- (* Zero ⊕ One = One *)
      pose (bdata := Build_BiproductData TwoCat Zero One One tt tt tt tt).
      assert (bis : IsBiproduct bdata two_zero).
      {
        simple refine (Build_IsBiproduct _ _ _ _ _ _ _ _ _).
        - (* outl ∘ inl = id *) reflexivity.
        - (* outr ∘ inr = id *) reflexivity.
        - (* outl ∘ inr = 0 *) reflexivity.
        - (* outr ∘ inl = 0 *) reflexivity.
      }
assert (buni : HasBiproductUniversal bdata).
      {
        simple refine (Build_HasBiproductUniversal _ _ _ _ _ _).
        - (* Coproduct universal *)
          intros W f g.
          destruct W.
          + (* W = Zero *)
            destruct f, g.
            apply Build_Contr with (center := (tt; (idpath, idpath))).
            intros [h' [p q]].
            apply path_sigma_uncurried.
            exists (match h' with tt => idpath end).
            simpl.
            apply path_prod; apply path_ishprop.
          + (* W = One *)
            destruct f, g.
            apply Build_Contr with (center := (tt; (idpath, idpath))).
            intros [h' [p q]].
            apply path_sigma_uncurried.
            exists (match h' with tt => idpath end).
            simpl.
            apply path_prod; apply path_ishprop.
- (* Product universal *)
          intros W f g.
          destruct W.
          + (* W = Zero *)
            destruct f, g.
            apply Build_Contr with (center := (tt; (idpath, idpath))).
            intros [h' [p q]].
            apply path_sigma_uncurried.
            exists (match h' with tt => idpath end).
            simpl.
            apply path_prod; apply path_ishprop.
          + (* W = One *)
            destruct f, g.
            apply Build_Contr with (center := (tt; (idpath, idpath))).
            intros [h' [p q]].
            apply path_sigma_uncurried.
            exists (match h' with tt => idpath end).
            simpl.
            apply path_prod; apply path_ishprop.
      }
      exact (Build_Biproduct _ _ _ _ bdata bis buni).
- (* One ⊕ Zero = One *)
      pose (bdata := Build_BiproductData TwoCat One Zero One tt tt tt tt).
      assert (bis : IsBiproduct bdata two_zero).
      {
        simple refine (Build_IsBiproduct _ _ _ _ _ _ _ _ _).
        - (* outl ∘ inl = id *) reflexivity.
        - (* outr ∘ inr = id *) reflexivity.
        - (* outl ∘ inr = 0 *) reflexivity.
        - (* outr ∘ inl = 0 *) reflexivity.
      }
assert (buni : HasBiproductUniversal bdata).
      {
        simple refine (Build_HasBiproductUniversal _ _ _ _ _ _).
        - (* Coproduct universal *)
          intros W f g.
          destruct W.
          + (* W = Zero *)
            destruct f, g.
            apply Build_Contr with (center := (tt; (idpath, idpath))).
            intros [h' [p q]].
            apply path_sigma_uncurried.
            exists (match h' with tt => idpath end).
            simpl.
            apply path_prod; apply path_ishprop.
          + (* W = One *)
            destruct f, g.
            apply Build_Contr with (center := (tt; (idpath, idpath))).
            intros [h' [p q]].
            apply path_sigma_uncurried.
            exists (match h' with tt => idpath end).
            simpl.
            apply path_prod; apply path_ishprop.
        - (* Product universal *)
          intros W f g.
          destruct W.
          + (* W = Zero *)
            destruct f, g.
            apply Build_Contr with (center := (tt; (idpath, idpath))).
            intros [h' [p q]].
            apply path_sigma_uncurried.
            exists (match h' with tt => idpath end).
            simpl.
            apply path_prod; apply path_ishprop.
          + (* W = One *)
            destruct f, g.
            apply Build_Contr with (center := (tt; (idpath, idpath))).
            intros [h' [p q]].
            apply path_sigma_uncurried.
            exists (match h' with tt => idpath end).
            simpl.
            apply path_prod; apply path_ishprop.
      }
      exact (Build_Biproduct _ _ _ _ bdata bis buni).
- (* One ⊕ One = One *)
      exact one_plus_one.
  Defined.

Definition TwoAdditive : AdditiveCategory.
  Proof.
    exact (Build_AdditiveCategory TwoCat two_zero two_all_biproducts).
  Defined.

End TwoCatAdditive.

Module ChainComplexExample.
  From HoTT Require Import Basics Types.
  Require Import ZeroObjects Biproducts AdditiveCategories PreStableCategories.
  
  Section ChainComplexes.
    Context `{Funext}.
    
    (* First, we need abelian groups *)
    Record AbelianGroup : Type := {
      carrier : Type;
      zero : carrier;
      plus : carrier -> carrier -> carrier;
      neg : carrier -> carrier
    }.
    
    (* Group axioms *)
    Record AbelianGroup_laws (G : AbelianGroup) : Type := {
      plus_assoc : forall x y z : carrier G, 
        plus G x (plus G y z) = plus G (plus G x y) z;
      plus_zero_l : forall x : carrier G, plus G (zero G) x = x;
      plus_zero_r : forall x : carrier G, plus G x (zero G) = x;
      plus_neg_l : forall x : carrier G, plus G (neg G x) x = zero G;
      plus_neg_r : forall x : carrier G, plus G x (neg G x) = zero G;
      plus_comm : forall x y : carrier G, plus G x y = plus G y x
    }.
    
    (* Complete abelian group with laws and set requirement *)
    Record AbelianGroupWithLaws : Type := {
      group : AbelianGroup;
      laws : AbelianGroup_laws group;
      carrier_is_set : IsHSet (carrier group)
    }.
    
    (* Group homomorphisms *)
    Record GroupHom (G H : AbelianGroupWithLaws) : Type := {
      hom_map : carrier (group G) -> carrier (group H);
      hom_zero : hom_map (zero (group G)) = zero (group H);
      hom_plus : forall x y : carrier (group G), 
        hom_map (plus (group G) x y) = plus (group H) (hom_map x) (hom_map y)
    }.
    
    (* Helper: In a set, all paths between two elements are equal *)
    Lemma path_hset {A : Type} {HSet : IsHSet A} (x y : A) (p q : x = y) : p = q.
    Proof.
      apply path_ishprop.
    Qed.

  (* Identity homomorphism *)
    Definition id_hom (G : AbelianGroupWithLaws) : GroupHom G G.
    Proof.
      refine (Build_GroupHom G G (fun x => x) _ _).
      - (* hom_zero *) reflexivity.
      - (* hom_plus *) intros x y. reflexivity.
    Defined.

(* Helper: In an HSet, all paths between two elements are equal *)
    Lemma hset_path_unique {A : Type} (HA : IsHSet A) {x y : A} (p q : x = y) : p = q.
    Proof.
      apply path_ishprop.
    Qed.

(* Two homomorphisms are equal if their underlying functions are equal *)
    Lemma GroupHom_eq {G K : AbelianGroupWithLaws} (f g : GroupHom G K) :
      hom_map G K f = hom_map G K g -> f = g.
    Proof.
      intro p.
      destruct f as [f_map f_zero f_plus].
      destruct g as [g_map g_zero g_plus].
      simpl in p.
      destruct p.
      (* Now f_map = g_map definitionally *)
      assert (Hz : f_zero = g_zero).
      {
        apply hset_path_unique.
        apply (carrier_is_set K).
      }
      assert (Hp : f_plus = g_plus).
      {
        apply path_forall; intro x.
        apply path_forall; intro y.
        apply hset_path_unique.
        apply (carrier_is_set K).
      }
      destruct Hz, Hp.
      reflexivity.
    Qed.

(* Composition of homomorphisms *)
    Definition comp_hom {A B C : AbelianGroupWithLaws} 
      (g : GroupHom B C) (f : GroupHom A B) : GroupHom A C.
    Proof.
      refine (Build_GroupHom A C 
        (fun x => hom_map B C g (hom_map A B f x)) _ _).
      - (* hom_zero *)
        rewrite (hom_zero A B f).
        rewrite (hom_zero B C g).
        reflexivity.
      - (* hom_plus *)
        intros x y.
        rewrite (hom_plus A B f).
        rewrite (hom_plus B C g).
        reflexivity.
    Defined.

(* The property of being a group homomorphism is a proposition *)
    Lemma IsGroupHom_HProp (A B : AbelianGroupWithLaws) 
      (f : carrier (group A) -> carrier (group B)) :
      IsHProp ((f (zero (group A)) = zero (group B)) * 
               (forall x y, f (plus (group A) x y) = plus (group B) (f x) (f y))).
    Proof.
      (* First show the components are props *)
      assert (H1 : IsHProp (f (zero (group A)) = zero (group B))).
      { 
        apply hprop_allpath.
        intros p q.
        apply hset_path_unique.
        apply (carrier_is_set B).
      }
      assert (H2 : IsHProp (forall x y, f (plus (group A) x y) = plus (group B) (f x) (f y))).
      {
        apply hprop_allpath.
        intros p q.
        apply path_forall. intro x.
        apply path_forall. intro y.
        apply hset_path_unique.
        apply (carrier_is_set B).
      }
      (* Now the product *)
      apply istrunc_prod; assumption.
    Qed.

(* GroupHom is equivalent to a sigma type *)
    Definition GroupHom_to_sig (A B : AbelianGroupWithLaws) (h : GroupHom A B) :
      {f : carrier (group A) -> carrier (group B) & 
       (f (zero (group A)) = zero (group B)) * 
       (forall x y, f (plus (group A) x y) = plus (group B) (f x) (f y))}.
    Proof.
      exists (hom_map A B h).
      split.
      - apply (hom_zero A B h).
      - apply (hom_plus A B h).
    Defined.

(* Sigma type to GroupHom *)
    Definition sig_to_GroupHom (A B : AbelianGroupWithLaws) 
      (s : {f : carrier (group A) -> carrier (group B) & 
            (f (zero (group A)) = zero (group B)) * 
            (forall x y, f (plus (group A) x y) = plus (group B) (f x) (f y))}) 
      : GroupHom A B.
    Proof.
      destruct s as [f [hz hp]].
      exact (Build_GroupHom A B f hz hp).
    Defined.

(* They are inverses *)
    Lemma GroupHom_sig_equiv_sect (A B : AbelianGroupWithLaws) (h : GroupHom A B) :
      sig_to_GroupHom A B (GroupHom_to_sig A B h) = h.
    Proof.
      destruct h as [f hz hp].
      reflexivity.
    Qed.

(* The other inverse *)
    Lemma GroupHom_sig_equiv_retr (A B : AbelianGroupWithLaws) 
      (s : {f : carrier (group A) -> carrier (group B) & 
            (f (zero (group A)) = zero (group B)) * 
            (forall x y, f (plus (group A) x y) = plus (group B) (f x) (f y))}) :
      GroupHom_to_sig A B (sig_to_GroupHom A B s) = s.
    Proof.
      destruct s as [f [hz hp]].
      reflexivity.
    Qed.

(* The equivalence *)
    Definition GroupHom_sig_equiv (A B : AbelianGroupWithLaws) :
      GroupHom A B <~> 
      {f : carrier (group A) -> carrier (group B) & 
       (f (zero (group A)) = zero (group B)) * 
       (forall x y, f (plus (group A) x y) = plus (group B) (f x) (f y))}.
    Proof.
      apply (equiv_adjointify 
        (GroupHom_to_sig A B)
        (sig_to_GroupHom A B)).
      - intro s. apply GroupHom_sig_equiv_retr.
      - intro h. apply GroupHom_sig_equiv_sect.
    Defined.

(* Helper: Function types are HSets when codomain is *)
Lemma fun_is_hset `{Funext} (A B : Type) (HB : IsHSet B) : IsHSet (A -> B).
Proof.
  change (IsTrunc 0 (A -> B)).
  apply istrunc_forall.
Qed.

(* Helper: Product types are HSets when both components are *)
Lemma prod_is_hset (A B : Type) (HA : IsHSet A) (HB : IsHSet B) : IsHSet (A * B).
Proof.
  apply istrunc_prod; assumption.
Qed.

(* Helper: Sigma types are HSets when base is HSet and fibers are HProps *)
Lemma sig_is_hset_from_hprop (A : Type) (P : A -> Type) 
  (HA : IsHSet A) (HP : forall a, IsHProp (P a)) : IsHSet (sig P).
Proof.
  apply istrunc_sigma.
Qed.

(* Helper: Paths in sets are HProps *)
Lemma path_ishprop_hset (A : Type) (HA : IsHSet A) (x y : A) : IsHProp (x = y).
Proof.
  exact (HA x y).
Qed.

(* Helper: Product of HProps is HProp *)
Lemma prod_hprop (A B : Type) (HA : IsHProp A) (HB : IsHProp B) : IsHProp (A * B).
Proof.
  change (IsTrunc (-1) (A * B)).
  apply istrunc_prod; assumption.
Qed.

(* Helper: Forall over HProps is HProp *)
Lemma forall_hprop `{Funext} (A : Type) (P : A -> Type) 
  (HP : forall a, IsHProp (P a)) : IsHProp (forall a, P a).
Proof.
  change (IsTrunc (-1) (forall a, P a)).
  apply istrunc_forall.
Qed.

(* Helper: The GroupHom property is an HProp for any function *)
Lemma GroupHom_property_is_hprop `{Funext} (A B : AbelianGroupWithLaws) 
  (f : carrier (group A) -> carrier (group B)) :
  IsHProp ((f (zero (group A)) = zero (group B)) * 
           (forall x y, f (plus (group A) x y) = plus (group B) (f x) (f y))).
Proof.
  apply prod_hprop.
  - (* First component is HProp *)
    apply path_ishprop_hset.
    apply (carrier_is_set B).
  - (* Second component is HProp *)
    apply forall_hprop. intro x.
    apply forall_hprop. intro y.
    apply path_ishprop_hset.
    apply (carrier_is_set B).
Qed.

(* Now we can prove GroupHom is an HSet *)
Global Instance GroupHom_IsHSet `{Funext} (A B : AbelianGroupWithLaws) : IsHSet (GroupHom A B).
Proof.
  (* First show the sigma type is an HSet *)
  assert (HSig : IsHSet {f : carrier (group A) -> carrier (group B) & 
                         (f (zero (group A)) = zero (group B)) * 
                         (forall x y, f (plus (group A) x y) = plus (group B) (f x) (f y))}).
  {
    apply sig_is_hset_from_hprop.
    - (* Base type is HSet *)
      apply fun_is_hset.
      apply (carrier_is_set B).
    - (* Fibers are HProps *)
      intro f.
      apply GroupHom_property_is_hprop.
  }
  (* Now use the equivalence *)
  exact (istrunc_equiv_istrunc _ (GroupHom_sig_equiv A B)^-1).
Qed.

(* The zero homomorphism *)
Definition zero_hom (A B : AbelianGroupWithLaws) : GroupHom A B.
Proof.
  refine (Build_GroupHom A B (fun _ => zero (group B)) _ _).
  - (* hom_zero *) reflexivity.
  - (* hom_plus *) 
    intros x y.
    symmetry.
    apply (plus_zero_l (group B) (laws B)).
Defined.

(* Composition is associative *)
Lemma comp_hom_assoc {A B C D : AbelianGroupWithLaws}
  (h : GroupHom C D) (g : GroupHom B C) (f : GroupHom A B) :
  comp_hom h (comp_hom g f) = comp_hom (comp_hom h g) f.
Proof.
  apply GroupHom_eq.
  reflexivity.
Qed.

(* Composition with identity on the left *)
Lemma comp_hom_id_left {A B : AbelianGroupWithLaws} (f : GroupHom A B) :
  comp_hom (id_hom B) f = f.
Proof.
  apply GroupHom_eq.
  reflexivity.
Qed.

(* Composition with identity on the right *)
Lemma comp_hom_id_right {A B : AbelianGroupWithLaws} (f : GroupHom A B) :
  comp_hom f (id_hom A) = f.
Proof.
  apply GroupHom_eq.
  reflexivity.
Qed.

(* The category of abelian groups *)
Definition AbGroupCat `{Funext} : PreCategory.
Proof.
  refine (@Build_PreCategory
    AbelianGroupWithLaws
    GroupHom
    id_hom
    (fun A B C => comp_hom)
    _ _ _ _).
  - (* associativity *)
    intros A B C D f g h.
    symmetry.
    apply comp_hom_assoc.
  - (* left identity *)
    intros A B f.
    apply comp_hom_id_left.
  - (* right identity *)
    intros A B f.
    apply comp_hom_id_right.
Defined.

(* The trivial abelian group *)
Definition TrivialGroup : AbelianGroupWithLaws.
Proof.
  refine (Build_AbelianGroupWithLaws
    (Build_AbelianGroup Unit tt (fun _ _ => tt) (fun _ => tt))
    _ _).
  - (* laws *)
    refine (Build_AbelianGroup_laws _ _ _ _ _ _ _).
    + (* plus_assoc *) intros x y z. destruct x, y, z. reflexivity.
    + (* plus_zero_l *) intros x. destruct x. reflexivity.
    + (* plus_zero_r *) intros x. destruct x. reflexivity.
    + (* plus_neg_l *) intros x. destruct x. reflexivity.
    + (* plus_neg_r *) intros x. destruct x. reflexivity.
    + (* plus_comm *) intros x y. destruct x, y. reflexivity.
Defined.

(* TrivialGroup is the zero object in AbGroupCat *)
Theorem TrivialGroup_is_zero : ZeroObject AbGroupCat.
Proof.
  refine (Build_ZeroObject AbGroupCat TrivialGroup _ _).
  - (* initial *)
    intro X.
    simple refine (Build_Contr _ _ _).
    + (* center: the zero morphism *)
      simple refine (Build_GroupHom TrivialGroup X (fun _ => zero (group X)) _ _).
      * (* hom_zero *)
        reflexivity.
      * (* hom_plus *)
        intros x y.
        simpl.
        symmetry.
        apply (plus_zero_l (group X) (laws X)).
    + (* contr: uniqueness *)
      intro f.
      apply GroupHom_eq.
      apply path_forall. intro x.
      destruct x.
      simpl.
      symmetry.
      exact (hom_zero TrivialGroup X f).
  - (* terminal *)
    intro X.
    simple refine (Build_Contr _ _ _).
    + (* center *)
      simple refine (Build_GroupHom X TrivialGroup (fun _ => tt) _ _).
      * (* hom_zero *)
        reflexivity.
      * (* hom_plus *)
        intros x y. reflexivity.
    + (* contr: uniqueness *)
      intro f.
      apply GroupHom_eq.
      apply path_forall. intro x.
      destruct (hom_map X TrivialGroup f x).
      reflexivity.
Defined.

(* Direct sum of abelian groups *)
Definition DirectSum (A B : AbelianGroupWithLaws) : AbelianGroupWithLaws.
Proof.
  refine (Build_AbelianGroupWithLaws
    (Build_AbelianGroup 
      (carrier (group A) * carrier (group B))
      (zero (group A), zero (group B))
      (fun p1 p2 => (plus (group A) (fst p1) (fst p2), 
                     plus (group B) (snd p1) (snd p2)))
      (fun p => (neg (group A) (fst p), neg (group B) (snd p))))
    _ _).
  - (* laws *)
    refine (Build_AbelianGroup_laws _ _ _ _ _ _ _).
    + (* plus_assoc *)
      intros [a1 b1] [a2 b2] [a3 b3].
      simpl.
      f_ap.
      * apply (plus_assoc (group A) (laws A)).
      * apply (plus_assoc (group B) (laws B)).
    + (* plus_zero_l *)
      intros [a b].
      simpl.
      f_ap.
      * apply (plus_zero_l (group A) (laws A)).
      * apply (plus_zero_l (group B) (laws B)).
    + (* plus_zero_r *)
      intros [a b].
      simpl.
      f_ap.
      * apply (plus_zero_r (group A) (laws A)).
      * apply (plus_zero_r (group B) (laws B)).
    + (* plus_neg_l *)
      intros [a b].
      simpl.
      f_ap.
      * apply (plus_neg_l (group A) (laws A)).
      * apply (plus_neg_l (group B) (laws B)).
    + (* plus_neg_r *)
      intros [a b].
      simpl.
      f_ap.
      * apply (plus_neg_r (group A) (laws A)).
      * apply (plus_neg_r (group B) (laws B)).
    + (* plus_comm *)
      intros [a1 b1] [a2 b2].
      simpl.
      f_ap.
      * apply (plus_comm (group A) (laws A)).
      * apply (plus_comm (group B) (laws B)).
  - (* carrier_is_set *)
    apply prod_is_hset.
    + apply (carrier_is_set A).
    + apply (carrier_is_set B).
Defined.

(* First projection from direct sum *)
Definition proj1 (A B : AbelianGroupWithLaws) : GroupHom (DirectSum A B) A.
Proof.
  refine (Build_GroupHom (DirectSum A B) A fst _ _).
  - (* hom_zero *)
    reflexivity.
  - (* hom_plus *)
    intros [a1 b1] [a2 b2].
    reflexivity.
Defined.

(* Second projection from direct sum *)
Definition proj2 (A B : AbelianGroupWithLaws) : GroupHom (DirectSum A B) B.
Proof.
  refine (Build_GroupHom (DirectSum A B) B snd _ _).
  - (* hom_zero *)
    reflexivity.
  - (* hom_plus *)
    intros [a1 b1] [a2 b2].
    reflexivity.
Defined.

(* First injection into direct sum *)
Definition inj1 (A B : AbelianGroupWithLaws) : GroupHom A (DirectSum A B).
Proof.
  refine (Build_GroupHom A (DirectSum A B) (fun a => (a, zero (group B))) _ _).
  - (* hom_zero *)
    reflexivity.
  - (* hom_plus *)
    intros a1 a2.
    simpl.
    f_ap.
    symmetry.
    apply (plus_zero_l (group B) (laws B)).
Defined.

(* Second injection into direct sum *)
Definition inj2 (A B : AbelianGroupWithLaws) : GroupHom B (DirectSum A B).
Proof.
  refine (Build_GroupHom B (DirectSum A B) (fun b => (zero (group A), b)) _ _).
  - (* hom_zero *)
    reflexivity.
  - (* hom_plus *)
    intros b1 b2.
    simpl.
    f_ap.
    symmetry.
    apply (plus_zero_l (group A) (laws A)).
Defined.

(* Chain complexes over abelian groups *)
Record ChainComplex := {
  ob : nat -> AbelianGroupWithLaws;
  diff : forall n, GroupHom (ob (S n)) (ob n);
  diff_squared : forall n, 
    comp_hom (diff n) (diff (S n)) = zero_hom (ob (S (S n))) (ob n)
}.

(* Chain maps between chain complexes *)
Record ChainMap (C D : ChainComplex) := {
  map_ob : forall n, GroupHom (ob C n) (ob D n);
  map_commutes : forall n,
    comp_hom (map_ob n) (diff C n) = comp_hom (diff D n) (map_ob (S n))
}.

(* Identity chain map *)
Definition id_chain_map (C : ChainComplex) : ChainMap C C.
Proof.
  refine (Build_ChainMap C C (fun n => id_hom (ob C n)) _).
  intro n.
  rewrite comp_hom_id_left.
  rewrite comp_hom_id_right.
  reflexivity.
Defined.

 (* Composition of chain maps *)
Definition comp_chain_map {A B C : ChainComplex} 
  (g : ChainMap B C) (f : ChainMap A B) : ChainMap A C.
Proof.
  refine (Build_ChainMap A C 
    (fun n => comp_hom (map_ob B C g n) (map_ob A B f n)) _).
  intro n.
  rewrite <- comp_hom_assoc.
  rewrite (map_commutes A B f n).
  rewrite comp_hom_assoc.
  rewrite (map_commutes B C g n).
  rewrite <- comp_hom_assoc.
  reflexivity.
Defined.

(* Chain maps are equal if their components are equal *)
Lemma ChainMap_eq {C D : ChainComplex} (f g : ChainMap C D) :
  (forall n, map_ob C D f n = map_ob C D g n) -> f = g.
Proof.
  intro Heq.
  destruct f as [f_ob f_comm].
  destruct g as [g_ob g_comm].
  simpl in Heq.
  assert (Hob : f_ob = g_ob).
  {
    apply path_forall.
    exact Heq.
  }
  destruct Hob.
  f_ap.
  apply path_forall. intro n.
  apply path_ishprop.
Qed.

(* Composition of chain maps is associative *)
Lemma comp_chain_map_assoc {A B C D : ChainComplex}
  (h : ChainMap C D) (g : ChainMap B C) (f : ChainMap A B) :
  comp_chain_map h (comp_chain_map g f) = comp_chain_map (comp_chain_map h g) f.
Proof.
  apply ChainMap_eq.
  intro n.
  simpl.
  apply comp_hom_assoc.
Qed.

(* Composition with identity on the left *)
Lemma comp_chain_map_id_left {A B : ChainComplex} (f : ChainMap A B) :
  comp_chain_map (id_chain_map B) f = f.
Proof.
  apply ChainMap_eq.
  intro n.
  simpl.
  apply comp_hom_id_left.
Qed.

(* Composition with identity on the right *)
Lemma comp_chain_map_id_right {A B : ChainComplex} (f : ChainMap A B) :
  comp_chain_map f (id_chain_map A) = f.
Proof.
  apply ChainMap_eq.
  intro n.
  simpl.
  apply comp_hom_id_right.
Qed.

(* Helper: ChainMap forms a set *)
Instance ChainMap_IsHSet `{Funext} (C D : ChainComplex) : IsHSet (ChainMap C D).
Proof.
  (* ChainMap is equivalent to a sigma type *)
  assert (equiv_to_sig : ChainMap C D <~> 
    {f : forall n, GroupHom (ob C n) (ob D n) &
     forall n, comp_hom (f n) (diff C n) = comp_hom (diff D n) (f (S n))}).
  {
    apply (equiv_adjointify
      (fun cm => (map_ob C D cm; map_commutes C D cm))
      (fun p => Build_ChainMap C D p.1 p.2)).
    - (* Section *)
      intros [f Hf].
      reflexivity.
    - (* Retraction *)
      intros [f Hf].
      reflexivity.
  }
  (* Use the equivalence *)
  apply (istrunc_equiv_istrunc _ equiv_to_sig^-1).
Qed.

(* The category of chain complexes *)
Definition ChainComplexCat `{Funext} : PreCategory.
Proof.
  simple refine (@Build_PreCategory
    ChainComplex
    ChainMap
    id_chain_map
    (fun A B C => comp_chain_map)
    _ _ _ _).
  - (* associativity *)
    intros A B C D f g h.
    unfold comp_chain_map.
    apply ChainMap_eq.
    intro n.
    simpl.
    symmetry.
    apply comp_hom_assoc.
  - (* left identity *)
    intros A B f.
    apply comp_chain_map_id_left.
  - (* right identity *)
    intros A B f.
    apply comp_chain_map_id_right.
Defined.

(* The shift functor on chain complexes *)
Definition ShiftComplex (C : ChainComplex) : ChainComplex.
Proof.
  refine (Build_ChainComplex
    (fun n => ob C (S n))
    (fun n => diff C (S n))
    _).
  intro n.
  apply (diff_squared C (S n)).
Defined.

(* The shift functor on chain maps *)
Definition ShiftMap {C D : ChainComplex} (f : ChainMap C D) : ChainMap (ShiftComplex C) (ShiftComplex D).
Proof.
  refine (Build_ChainMap (ShiftComplex C) (ShiftComplex D)
    (fun n => map_ob C D f (S n))
    _).
  intro n.
  simpl.
  apply (map_commutes C D f (S n)).
Defined.
