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
    chain_zero : forall n : Int, chain_obj n;
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

Record ChainComplex' := {
  chain_group : Int -> AbGroup;
  chain_diff' : forall n : Int, 
    carrier (chain_group n) -> carrier (chain_group (int_pred n));
  chain_diff_group_hom : forall n : Int, 
    IsGroupHom (chain_diff' n);
  chain_diff_squared' : forall n : Int, forall x : carrier (chain_group n),
    chain_diff' (int_pred n) (chain_diff' n x) = 
    ab_zero (chain_group (int_pred (int_pred n)))
}.

Record ChainMap' (C D : ChainComplex') := {
  map_component' : forall n : Int, 
    carrier (chain_group C n) -> carrier (chain_group D n);
  map_is_group_hom : forall n : Int,
    IsGroupHom (map_component' n);
  map_commutes' : forall n : Int, forall x : carrier (chain_group C n),
    map_component' (int_pred n) (chain_diff' C n x) = 
    chain_diff' D n (map_component' n x)
}.

Lemma int_pred_succ : forall n : Int, int_pred (int_succ n) = n.
Proof.
  intro n.
  destruct n as [p | | p].
  - destruct p; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Definition transport_pred_succ {D : ChainComplex'} {n : Int} 
  : carrier (chain_group D (int_pred (int_succ n))) -> carrier (chain_group D n) :=
  transport (fun m => carrier (chain_group D m)) (int_pred_succ n).

Lemma int_succ_pred : forall n : Int, int_succ (int_pred n) = n.
Proof.
  intro n.
  destruct n as [p | | p].
  - reflexivity.
  - reflexivity.
  - destruct p; reflexivity.
Qed.

Definition transport_succ_pred {D : ChainComplex'} {n : Int} 
  : carrier (chain_group D (int_succ (int_pred n))) -> carrier (chain_group D n) :=
  transport (fun m => carrier (chain_group D m)) (int_succ_pred n).

Definition ChainHomotopic' {C D : ChainComplex'} (f g : ChainMap' C D) : Type :=
  {h : forall n : Int, carrier (chain_group C n) -> carrier (chain_group D (int_succ n)) |
   forall n : Int, forall x : carrier (chain_group C n),
     plus (chain_group D n) 
          (map_component' C D f n x)
          (plus (chain_group D n)
                (transport_pred_succ (chain_diff' D (int_succ n) (h n x)))
                (transport_succ_pred (h (int_pred n) (chain_diff' C n x)))) = 
     map_component' C D g n x}.

Definition id_chain_map (C : ChainComplex') : ChainMap' C C := {|
  map_component' := fun n x => x;
  map_is_group_hom := fun n => (fun _ _ => idpath, idpath);
  map_commutes' := fun n x => idpath
|}.

Definition compose_chain_maps {A B C : ChainComplex'} 
  (g : ChainMap' B C) (f : ChainMap' A B) : ChainMap' A C := {|
  map_component' := fun n x => map_component' B C g n (map_component' A B f n x);
  map_is_group_hom := fun n => 
    let (f_hom, f_zero) := map_is_group_hom A B f n in
    let (g_hom, g_zero) := map_is_group_hom B C g n in
    ((fun x y => ap (map_component' B C g n) (f_hom x y) @ 
                 g_hom (map_component' A B f n x) (map_component' A B f n y)),
     ap (map_component' B C g n) f_zero @ g_zero);
  map_commutes' := fun n x => 
    ap (map_component' B C g (int_pred n)) (map_commutes' A B f n x) @
    map_commutes' B C g n (map_component' A B f n x)
|}.

Definition ChainComplexCategory_obs : Type := ChainComplex'.

Definition ChainComplexCategory_mor (C D : ChainComplexCategory_obs) : Type := ChainMap' C D.

Context `{Funext}.

Lemma chain_map_eq (C D : ChainComplex') (f g : ChainMap' C D) :
  (forall n x, map_component' C D f n x = map_component' C D g n x) -> f = g.
Proof.
  intro Heq.
  destruct f as [f_comp f_hom f_comm].
  destruct g as [g_comp g_hom g_comm].
  simpl in Heq.
  assert (Hcomp : f_comp = g_comp).
  { apply path_forall. intro n.
    apply path_forall. intro x.
    apply Heq. }
  destruct Hcomp.
  assert (f_hom = g_hom).
  { apply path_forall. intro n. apply path_ishprop. }
  destruct H.
  assert (f_comm = g_comm).
  { apply path_forall. intro n. apply path_forall. intro x. apply path_ishprop. }
  destruct H.
  reflexivity.
Qed.

Lemma chain_left_identity (A B : ChainComplex') (f : ChainMap' A B) :
  compose_chain_maps (id_chain_map B) f = f.
Proof.
  apply chain_map_eq.
  intros n x.
  reflexivity.
Qed.

Lemma chain_right_identity (A B : ChainComplex') (f : ChainMap' A B) :
  compose_chain_maps f (id_chain_map A) = f.
Proof.
  apply chain_map_eq.
  intros n x.
  reflexivity.
Qed.

Lemma Unit_hset : IsHSet Unit.
Proof.
  apply hset_decpaths.
  intros [] [].
  left. reflexivity.
Qed.

Definition ZeroCategory : PreCategory := 
  Build_PreCategory'
    (fun (_ _ : Unit) => Unit)
    (fun (_ : Unit) => tt)
    (fun (_ _ _ : Unit) (_ _ : Unit) => tt)
    (fun _ _ _ _ _ _ _ => idpath)
    (fun _ _ _ _ _ _ _ => idpath)
    (fun (a b : Unit) (f : Unit) => match a, b, f with tt, tt, tt => idpath end)
    (fun (a b : Unit) (f : Unit) => match a, b, f with tt, tt, tt => idpath end)
    (fun (x : Unit) => match x with tt => idpath end)
    (fun _ _ => Unit_hset).

Definition zero_obj : object ZeroCategory := tt.

Lemma zero_is_initial : forall X : object ZeroCategory, IsContr (morphism ZeroCategory zero_obj X).
Proof.
  intro X.
  exists tt.
  intro y.
  destruct X, y.
  reflexivity.
Qed.

Lemma zero_is_terminal : forall X : object ZeroCategory, IsContr (morphism ZeroCategory X zero_obj).
Proof.
  intro X.
  exists tt.
  intro y.
  destruct X, y.
  reflexivity.
Qed.

Definition ZeroSusp : Functor ZeroCategory ZeroCategory := 
  Build_Functor ZeroCategory ZeroCategory
    (fun _ => tt)
    (fun _ _ _ => tt)
    (fun _ _ _ _ _ => idpath)
    (fun _ => idpath).

Definition ZeroLoop : Functor ZeroCategory ZeroCategory := 
  Build_Functor ZeroCategory ZeroCategory
    (fun _ => tt)
    (fun _ _ _ => tt)
    (fun _ _ _ _ _ => idpath)
    (fun _ => idpath).

Definition zero_eta : NaturalTransformation 1%functor (ZeroLoop o ZeroSusp)%functor.
Proof.
  unshelve eapply Build_NaturalTransformation.
  - intro x. exact tt.
  - intros. reflexivity.
Defined.

Definition zero_epsilon : NaturalTransformation (ZeroSusp o ZeroLoop)%functor 1%functor.
Proof.
  unshelve eapply Build_NaturalTransformation.
  - intro x. exact tt.
  - intros. reflexivity.
Defined.

Definition ZeroPreStable : PreStableCategory := 
  Build_PreStableCategory
    ZeroCategory
    zero_obj
    zero_is_initial
    zero_is_terminal
    ZeroSusp
    ZeroLoop
    zero_eta
    zero_epsilon.

End ChainComplexExample.
