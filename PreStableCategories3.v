From HoTT Require Import Basics.
From HoTT.Basics Require Import Overture PathGroupoids Contractible.
From HoTT.Categories Require Import Category Functor NaturalTransformation.

Print Contr.

Definition IsContr (A : Type) := {center : A & forall y : A, center = y}.
Record PreStableCategory := {
  C : PreCategory;
  zero : object C;
  is_initial : forall X : object C, IsContr (morphism C zero X);
  is_terminal : forall X : object C, IsContr (morphism C X zero);
  Susp : Functor C C;
  Loop : Functor C C;
  eta : NaturalTransformation 1%functor (Loop o Susp)%functor;
  epsilon : NaturalTransformation (Susp o Loop)%functor 1%functor
}.
Section StableStructures.
  Context {S : PreStableCategory}.

  Record DistinguishedTriangle (S : PreStableCategory) := {
    X : object (C S);
    Y : object (C S);
    Z : object (C S);
    f : morphism (C S) X Y;
    g : morphism (C S) Y Z;
    h : morphism (C S) Z (object_of (Susp S) X)
  }.

  Definition id_triangle (Stable : PreStableCategory) 
                        (X : object (C Stable)) : DistinguishedTriangle Stable :=
    {|
      X := X;
      Y := X;
      Z := zero Stable;
      f := Category.Core.identity X;
      g := (is_terminal Stable X).1;
      h := (is_initial Stable ((Susp Stable)_0 X))%object.1
    |}.

  Theorem zero_morphism_unique (X Y : object (C S)) 
          (f g : morphism (C S) X Y) :
    (exists (h : morphism (C S) X (zero S)) (k : morphism (C S) (zero S) Y), 
     f = (k o h)%morphism) ->
    (exists (h' : morphism (C S) X (zero S)) (k' : morphism (C S) (zero S) Y), 
     g = (k' o h')%morphism) ->
    f = g.
  Proof.
    intros [h [k Hf]] [h' [k' Hg]].
    assert (Heq_h : h = h').
    { destruct (is_terminal S X) as [center H_terminal].
      exact ((H_terminal h)^ @ (H_terminal h')). }
    assert (Heq_k : k = k').
    { destruct (is_initial S Y) as [center H_initial].
      exact ((H_initial k)^ @ (H_initial k')). }
    rewrite Hf, Hg, Heq_h, Heq_k.
    reflexivity.
  Qed.

  Record StableCategory := {
    PSC :> PreStableCategory;
    is_distinguished : DistinguishedTriangle PSC -> Type;
    id_is_distinguished : forall (X : object (C PSC)),
      is_distinguished (id_triangle PSC X);
    rotation : forall (T : DistinguishedTriangle PSC),
      is_distinguished T -> 
      is_distinguished {|
        X := Y PSC T;
        Y := Z PSC T;
        Z := (Susp PSC)_0 (X PSC T);
        f := g PSC T;
        g := h PSC T;
        h := morphism_of (Susp PSC) (f PSC T)
      |}
  }.
End StableStructures.

Section ChainComplexExample.

From HoTT.Spaces Require Import Int.
From HoTT.Basics Require Import Trunc.
  Check IsHSet.

Definition int_pred (n : Int) : Int :=
    match n with
    | Int.neg p => Int.neg (succ_pos p)
    | Int.zero => Int.neg one
    | Int.pos (succ_pos p) => Int.pos p
    | Int.pos one => Int.zero
    end.
    
Record ChainComplex := {
    chain_obj : Int -> Type;
    chain_zero : forall n : Int, chain_obj n;  (* Zero element at each degree *)
    chain_diff : forall n : Int, chain_obj n -> chain_obj (int_pred n);
    chain_diff_squared : forall n : Int, forall x : chain_obj n, 
      chain_diff (int_pred n) (chain_diff n x) = chain_zero (int_pred (int_pred n))
  }.
  
Record ChainMap (C D : ChainComplex) := {
    map_component : forall n : Int, chain_obj C n -> chain_obj D n;
    map_commutes : forall n : Int, forall x : chain_obj C n,
      map_component (int_pred n) (chain_diff C n x) = 
      chain_diff D n (map_component n x)
  }.

Definition int_succ (n : Int) : Int :=
    match n with
    | Int.neg (succ_pos p) => Int.neg p
    | Int.neg one => Int.zero
    | Int.zero => Int.pos one
    | Int.pos p => Int.pos (succ_pos p)
    end.

Record AbGroup := {
    carrier : Type;
    ab_zero : carrier;
    plus : carrier -> carrier -> carrier;
    neg : carrier -> carrier;
    plus_assoc : forall x y z, plus x (plus y z) = plus (plus x y) z;
    plus_zero_l : forall x, plus ab_zero x = x;
    plus_neg_l : forall x, plus (neg x) x = ab_zero;
    plus_comm : forall x y, plus x y = plus y x
  }.

Definition IsGroupHom {G H : AbGroup} (f : carrier G -> carrier H) : Type :=
  (forall x y : carrier G, f (plus G x y) = plus H (f x) (f y)) *
  (f (ab_zero G) = ab_zero H).

End ChainComplexExample.
