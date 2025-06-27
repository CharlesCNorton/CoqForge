(** * Section 1: Foundations - Basic Types and Definitions
    
    This section establishes the fundamental types for image processing:
    coordinates, images, labelings, and basic utility functions.
    We keep definitions minimal and focused on core concepts. *)

Require Import Coq.Init.Prelude.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Open Scope nat_scope.

(** ** 1.1 Coordinate System
    
    We represent pixel coordinates as pairs of natural numbers (x, y).
    The origin (0, 0) is at the top-left corner, with x increasing rightward
    and y increasing downward, following standard image processing conventions. *)

Definition coord : Type := nat * nat.

(** Accessor functions for readability *)
Definition coord_x (c : coord) : nat := fst c.
Definition coord_y (c : coord) : nat := snd c.

(** Coordinate equality as a decidable boolean function *)
Definition coord_eqb (c1 c2 : coord) : bool :=
  match c1, c2 with
  | (x1, y1), (x2, y2) => andb (Nat.eqb x1 x2) (Nat.eqb y1 y2)
  end.

(** ** 1.2 Image Representations
    
    We provide two image representations:
    1. Simple images: unbounded functions from coordinates to booleans
    2. Bounded images: images with explicit width and height
    
    Convention: true represents foreground (object) pixels, 
                false represents background pixels *)

Definition simple_image : Type := coord -> bool.

(** The empty image contains no foreground pixels *)
Definition empty_image : simple_image := fun _ => false.

(** Bounded images with explicit dimensions *)
Record bounded_image : Type := mkBoundedImage {
  width : nat;
  height : nat;
  pixels : coord -> bool
}.

(** Check if a coordinate is within bounds *)
Definition in_bounds (img : bounded_image) (c : coord) : bool :=
  andb (Nat.ltb (coord_x c) (width img)) 
       (Nat.ltb (coord_y c) (height img)).

(** Safe pixel access that returns false for out-of-bounds *)
Definition get_pixel (img : bounded_image) (c : coord) : bool :=
  if in_bounds img c then pixels img c else false.

(** Convert bounded image to simple image *)
Definition bounded_to_simple (img : bounded_image) : simple_image :=
  fun c => get_pixel img c.

(** ** 1.3 Labeling Functions
    
    A labeling assigns a natural number label to each coordinate.
    We use 0 to represent "unlabeled" or background pixels.
    Connected foreground pixels should receive the same positive label. *)

Definition labeling : Type := coord -> nat.

(** The empty labeling assigns 0 to all pixels *)
Definition empty_labeling : labeling := fun _ => 0.

(** ** 1.4 Basic Utility Functions *)

(** Absolute difference between natural numbers *)
Definition abs_diff (a b : nat) : nat :=
  if Nat.leb a b then b - a else a - b.

(** ** 1.5 Basic Properties of Foundations *)

(** coord_eqb is reflexive *)
Lemma coord_eqb_refl : forall c,
  coord_eqb c c = true.
Proof.
  intros [x y].
  unfold coord_eqb.
  rewrite !Nat.eqb_refl.
  reflexivity.
Qed.

(** coord_eqb is symmetric *)
Lemma coord_eqb_sym : forall c1 c2,
  coord_eqb c1 c2 = coord_eqb c2 c1.
Proof.
  intros [x1 y1] [x2 y2].
  unfold coord_eqb.
  rewrite (Nat.eqb_sym x1 x2).
  rewrite (Nat.eqb_sym y1 y2).
  reflexivity.
Qed.

(** coord_eqb decides equality *)
Lemma coord_eqb_true_iff : forall c1 c2,
  coord_eqb c1 c2 = true <-> c1 = c2.
Proof.
  intros [x1 y1] [x2 y2].
  unfold coord_eqb.
  rewrite andb_true_iff.
  rewrite !Nat.eqb_eq.
  split.
  - intros [Hx Hy]. f_equal; assumption.
  - intros H. injection H as Hx Hy. auto.
Qed.

(** abs_diff is symmetric *)
Lemma abs_diff_sym : forall a b, 
  abs_diff a b = abs_diff b a.
Proof.
  intros a b.
  unfold abs_diff.
  destruct (Nat.leb a b) eqn:Hab; destruct (Nat.leb b a) eqn:Hba;
  try reflexivity.
  - apply Nat.leb_le in Hab.
    apply Nat.leb_le in Hba.
    assert (a = b) by lia. subst. reflexivity.
  - apply Nat.leb_nle in Hab.
    apply Nat.leb_nle in Hba.
    lia.
Qed.

(** Empty labeling is always zero *)
Lemma empty_labeling_zero : forall c,
  empty_labeling c = 0.
Proof.
  reflexivity.
Qed.

(** get_pixel returns false outside bounds *)
Lemma get_pixel_out_of_bounds : forall img c,
  in_bounds img c = false -> get_pixel img c = false.
Proof.
  intros img c Hout.
  unfold get_pixel.
  rewrite Hout.
  reflexivity.
Qed.

(** Bounded to simple conversion preserves pixel values *)
Lemma bounded_to_simple_spec : forall img c,
  bounded_to_simple img c = get_pixel img c.
Proof.
  reflexivity.
Qed.
