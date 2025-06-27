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

(** * Section 2: Adjacency Theory
    
    This section defines adjacency relations for pixels and establishes their
    fundamental properties. We focus on 4-connectivity and 8-connectivity,
    the two most common adjacency relations in image processing. *)

(** ** 2.1 4-Connectivity (Edge Adjacency)
    
    Two pixels are 4-adjacent if they share an edge, i.e., they differ
    by exactly 1 in either x or y coordinate (but not both).
    
    This gives each pixel up to 4 neighbors:
    - (x-1, y) left
    - (x+1, y) right  
    - (x, y-1) up
    - (x, y+1) down *)

Definition adjacent_4 (c1 c2 : coord) : bool :=
  let x1 := coord_x c1 in
  let y1 := coord_y c1 in
  let x2 := coord_x c2 in
  let y2 := coord_y c2 in
  match Nat.eqb x1 x2 with
  | true => Nat.eqb (abs_diff y1 y2) 1  (* same x, differ by 1 in y *)
  | false => andb (Nat.eqb y1 y2) (Nat.eqb (abs_diff x1 x2) 1)  (* same y, differ by 1 in x *)
  end.

(** ** 2.2 8-Connectivity (Edge or Corner Adjacency)
    
    Two pixels are 8-adjacent if they share an edge or corner, i.e., they differ
    by at most 1 in both x and y coordinates (but not identical).
    
    This gives each pixel up to 8 neighbors, including diagonals. *)

Definition adjacent_8 (c1 c2 : coord) : bool :=
  let x1 := coord_x c1 in
  let y1 := coord_y c1 in
  let x2 := coord_x c2 in
  let y2 := coord_y c2 in
  let dx := abs_diff x1 x2 in
  let dy := abs_diff y1 y2 in
  andb (andb (Nat.leb dx 1) (Nat.leb dy 1)) 
       (negb (andb (Nat.eqb dx 0) (Nat.eqb dy 0))).

(** ** 2.3 Basic Tests for Adjacency *)

Example test_adj4_horiz : adjacent_4 (0, 0) (1, 0) = true. 
Proof. reflexivity. Qed.

Example test_adj4_vert : adjacent_4 (0, 0) (0, 1) = true. 
Proof. reflexivity. Qed.

Example test_adj4_diag : adjacent_4 (0, 0) (1, 1) = false. 
Proof. reflexivity. Qed.

Example test_adj4_self : adjacent_4 (0, 0) (0, 0) = false. 
Proof. reflexivity. Qed.

Example test_adj8_horiz : adjacent_8 (0, 0) (1, 0) = true. 
Proof. reflexivity. Qed.

Example test_adj8_diag : adjacent_8 (0, 0) (1, 1) = true. 
Proof. reflexivity. Qed.

Example test_adj8_self : adjacent_8 (0, 0) (0, 0) = false. 
Proof. reflexivity. Qed.

Example test_adj8_far : adjacent_8 (0, 0) (2, 0) = false. 
Proof. reflexivity. Qed.

(** ** 2.4 Fundamental Properties of Adjacency *)

(** 4-adjacency is symmetric *)
Lemma adjacent_4_sym : forall c1 c2, 
  adjacent_4 c1 c2 = adjacent_4 c2 c1.
Proof.
  intros [x1 y1] [x2 y2].
  unfold adjacent_4; simpl.
  rewrite Nat.eqb_sym, (Nat.eqb_sym y1 y2).
  rewrite (abs_diff_sym y1 y2), (abs_diff_sym x1 x2).
  destruct (Nat.eqb x2 x1); reflexivity.
Qed.

(** 8-adjacency is symmetric *)
Lemma adjacent_8_sym : forall c1 c2,
  adjacent_8 c1 c2 = adjacent_8 c2 c1.
Proof.
  intros [x1 y1] [x2 y2].
  unfold adjacent_8; simpl.
  rewrite (abs_diff_sym x1 x2).
  rewrite (abs_diff_sym y1 y2).
  reflexivity.
Qed.

(** Neither adjacency relation is reflexive *)
Lemma adjacent_4_irrefl : forall c,
  adjacent_4 c c = false.
Proof.
  intros [x y].
  unfold adjacent_4; simpl.
  rewrite Nat.eqb_refl.
  unfold abs_diff.
  rewrite Nat.leb_refl, Nat.sub_diag.
  reflexivity.
Qed.

Lemma adjacent_8_irrefl : forall c,
  adjacent_8 c c = false.
Proof.
  intros [x y].
  unfold adjacent_8; simpl.
  unfold abs_diff.
  rewrite Nat.leb_refl, (Nat.leb_refl y).
  rewrite Nat.sub_diag, (Nat.sub_diag y).
  reflexivity.
Qed.

(** ** 2.5 Relationship Between 4 and 8 Adjacency *)

(** 4-adjacency implies 8-adjacency *)
Theorem adjacent_4_implies_8 : forall c1 c2,
  adjacent_4 c1 c2 = true -> adjacent_8 c1 c2 = true.
Proof.
  intros [x1 y1] [x2 y2] H4.
  unfold adjacent_4 in H4; simpl in H4.
  unfold adjacent_8; simpl.
  destruct (Nat.eqb x1 x2) eqn:Heqx.
  - (* Same x coordinate *)
    apply Nat.eqb_eq in Heqx; subst x2.
    assert (abs_diff x1 x1 = 0).
    { unfold abs_diff. rewrite Nat.leb_refl. lia. }
    rewrite H. simpl.
    assert (abs_diff y1 y2 = 1).
    { apply Nat.eqb_eq. exact H4. }
    rewrite H0. simpl.
    reflexivity.
  - (* Different x, must have same y *)
    apply andb_prop in H4. destruct H4 as [Heqy H1].
    apply Nat.eqb_eq in Heqy; subst y2.
    assert (abs_diff y1 y1 = 0).
    { unfold abs_diff. rewrite Nat.leb_refl. lia. }
    rewrite H. simpl.
    apply Nat.eqb_eq in H1.
    rewrite H1. simpl.
    reflexivity.
Qed.

(** The converse is not true: 8-adjacency does not imply 4-adjacency *)
Example adjacent_8_not_implies_4 : 
  exists c1 c2, adjacent_8 c1 c2 = true /\ adjacent_4 c1 c2 = false.
Proof.
  exists (0, 0), (1, 1).
  split; reflexivity.
Qed.

(** ** 2.6 Adjacency Characterizations *)

(** 4-adjacency can be characterized by unit distance in Manhattan metric *)
Lemma adjacent_4_manhattan : forall c1 c2,
  adjacent_4 c1 c2 = true <-> 
  abs_diff (coord_x c1) (coord_x c2) + abs_diff (coord_y c1) (coord_y c2) = 1.
Proof.
  intros [x1 y1] [x2 y2].
  unfold adjacent_4; simpl.
  split.
  - intros H.
    destruct (Nat.eqb x1 x2) eqn:Hx.
    + apply Nat.eqb_eq in Hx; subst.
      apply Nat.eqb_eq in H.
      rewrite H.
      unfold abs_diff at 1.
      rewrite Nat.leb_refl, Nat.sub_diag.
      reflexivity.
    + apply andb_prop in H.
      destruct H as [Hy H1].
      apply Nat.eqb_eq in Hy; subst.
      apply Nat.eqb_eq in H1.
      rewrite H1.
      unfold abs_diff.
      rewrite Nat.leb_refl, Nat.sub_diag.
      lia.
  - intros H.
    destruct (Nat.eqb x1 x2) eqn:Hx.
    + apply Nat.eqb_eq in Hx; subst.
      unfold abs_diff at 1 in H.
      rewrite Nat.leb_refl, Nat.sub_diag in H.
      simpl in H.
      apply Nat.eqb_eq.
      exact H.
    + apply andb_true_intro.
      split.
      * (* Need to show y1 = y2 *)
        destruct (Nat.eqb y1 y2) eqn:Heqy.
        -- reflexivity.
        -- (* If y1 ≠ y2 and x1 ≠ x2, then sum > 1 *)
           apply Nat.eqb_neq in Hx, Heqy.
           assert (abs_diff x1 x2 > 0).
           { unfold abs_diff. 
             destruct (Nat.leb x1 x2) eqn:Hle.
             - apply Nat.leb_le in Hle. lia.
             - apply Nat.leb_nle in Hle. lia. }
           assert (abs_diff y1 y2 > 0).
           { unfold abs_diff. 
             destruct (Nat.leb y1 y2) eqn:Hle.
             - apply Nat.leb_le in Hle. lia.
             - apply Nat.leb_nle in Hle. lia. }
           lia.
      * (* Need to show abs_diff x1 x2 = 1 *)
        apply Nat.eqb_neq in Hx.
        assert (abs_diff y1 y2 = 0).
        { destruct (abs_diff y1 y2) eqn:E.
          - reflexivity.
          - assert (abs_diff x1 x2 > 0).
            { unfold abs_diff. 
              destruct (Nat.leb x1 x2) eqn:Hle.
              - apply Nat.leb_le in Hle. lia.
              - apply Nat.leb_nle in Hle. lia. }
            lia. }
        unfold abs_diff in H0.
        destruct (Nat.leb y1 y2) eqn:Hley.
        -- apply Nat.leb_le in Hley. 
           assert (y1 = y2) by lia. subst.
           apply Nat.eqb_eq.
           assert (abs_diff x1 x2 + abs_diff y2 y2 = 1) by exact H.
           unfold abs_diff at 2 in H1.
           rewrite Nat.leb_refl, Nat.sub_diag in H1.
           rewrite Nat.add_0_r in H1.
           exact H1.
        -- apply Nat.leb_nle in Hley.
           assert (y1 = y2) by lia. subst.
           apply Nat.eqb_eq.
           assert (abs_diff x1 x2 + abs_diff y2 y2 = 1) by exact H.
           unfold abs_diff at 2 in H1.
           rewrite Nat.leb_refl, Nat.sub_diag in H1.
           rewrite Nat.add_0_r in H1.
           exact H1.
Qed.

Lemma adjacent_8_chebyshev : forall c1 c2,
  adjacent_8 c1 c2 = true <-> 
  Nat.max (abs_diff (coord_x c1) (coord_x c2)) (abs_diff (coord_y c1) (coord_y c2)) = 1.
Proof.
  intros [x1 y1] [x2 y2].
  unfold adjacent_8; simpl.
  split.
  - intros H.
    apply andb_prop in H.
    destruct H as [H1 H2].
    apply andb_prop in H1.
    destruct H1 as [Hdx Hdy].
    apply Nat.leb_le in Hdx, Hdy.
    apply negb_true_iff in H2.
    apply andb_false_iff in H2.
    assert (abs_diff x1 x2 <= 1) by exact Hdx.
    assert (abs_diff y1 y2 <= 1) by exact Hdy.
    assert (abs_diff x1 x2 > 0 \/ abs_diff y1 y2 > 0).
    { destruct H2 as [H2 | H2].
      - apply Nat.eqb_neq in H2. left. lia.
      - apply Nat.eqb_neq in H2. right. lia. }
    destruct H1 as [Hx | Hy].
    + destruct (abs_diff x1 x2) eqn:E; [lia|].
      destruct n; [|lia].
      destruct (abs_diff y1 y2) eqn:E2.
      * rewrite Nat.max_0_r. reflexivity.
      * destruct n; [apply Nat.max_comm|lia].
    + destruct (abs_diff y1 y2) eqn:E; [lia|].
      destruct n; [|lia].
      destruct (abs_diff x1 x2) eqn:E2.
      * rewrite Nat.max_0_l. reflexivity.
      * destruct n; [reflexivity|lia].
  - intros H.
    apply andb_true_intro.
    split.
    + apply andb_true_intro.
      split; apply Nat.leb_le; apply Nat.max_lub_iff in H; lia.
    + apply negb_true_iff.
      apply andb_false_iff.
      destruct (Nat.max_dec (abs_diff x1 x2) (abs_diff y1 y2)) as [Hmax | Hmax].
      * rewrite Hmax in H.
        right. apply Nat.eqb_neq. lia.
      * rewrite Hmax in H.
        left. apply Nat.eqb_neq. lia.
Qed.
