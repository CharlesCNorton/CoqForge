(** * Connected Component Labeling in Coq

    This formalization develops a verified implementation of connected component
    labeling (CCL), a fundamental algorithm in computer vision and image processing.
    
    ** Overview
    
    Connected component labeling assigns unique labels to connected regions of 
    foreground pixels in a binary image. Two pixels belong to the same component
    if and only if there exists a path of foreground pixels connecting them,
    where adjacency is defined by either 4-connectivity or 8-connectivity.
    
    ** Why formalize this?
    
    CCL is ubiquitous in vision systems, yet implementations often contain subtle
    bugs, especially at image boundaries or with complex pixel patterns. A formal
    verification provides confidence for safety-critical applications and serves
    as a foundation for verifying more complex vision algorithms.
*)

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
      assert (abs_diff x1 x2 <= 1 /\ abs_diff y1 y2 <= 1).
      { split.
        - assert (abs_diff x1 x2 <= Nat.max (abs_diff x1 x2) (abs_diff y1 y2)) by apply Nat.le_max_l.
          rewrite H in *. assumption.
        - assert (abs_diff y1 y2 <= Nat.max (abs_diff x1 x2) (abs_diff y1 y2)) by apply Nat.le_max_r.
          rewrite H in *. assumption. }
      destruct H0.
      split; apply Nat.leb_le; assumption.
    + apply negb_true_iff.
      apply andb_false_iff.
      (* Since max = 1, at least one of the distances is 1 *)
      assert (abs_diff x1 x2 = 1 \/ abs_diff y1 y2 = 1).
      { destruct (abs_diff x1 x2) eqn:E1; destruct (abs_diff y1 y2) eqn:E2.
        - (* both 0, max would be 0 *)
          simpl in H. lia.
        - (* x1 x2 = 0, y1 y2 = S n *)
          right. simpl in H. assumption.
        - (* x1 x2 = S n, y1 y2 = 0 *)
          left. 
          rewrite Nat.max_0_r in H.
          exact H.
        - (* both positive *)
          simpl in H.
          destruct n; destruct n0; simpl in H; try lia;
          left; reflexivity. }
      destruct H0.
      * left. apply Nat.eqb_neq. rewrite H0. lia.
      * right. apply Nat.eqb_neq. rewrite H0. lia.
Qed.

(** * Section 3: Connectivity Theory
    
    This section builds upon adjacency relations to define connectivity
    between pixels. We formalize paths, define when pixels are connected,
    and prove that connectivity forms an equivalence relation on foreground
    pixels. *)

(** ** 3.1 Paths in Images
    
    A path is a sequence of coordinates. We represent paths as lists
    and define what makes a path valid in an image. *)

(** Check if consecutive elements in a list are adjacent *)
Fixpoint is_adjacent_path (adj : coord -> coord -> bool) (p : list coord) : bool :=
  match p with
  | [] => true
  | [_] => true
  | c1 :: (c2 :: rest) as tail => andb (adj c1 c2) (is_adjacent_path adj tail)
  end.

(** Check if all coordinates in a path are foreground pixels *)
Fixpoint all_foreground (img : simple_image) (p : list coord) : bool :=
  match p with
  | [] => true
  | c :: rest => andb (img c) (all_foreground img rest)
  end.

(** A valid path has adjacent coordinates and all are foreground *)
Definition valid_path (img : simple_image) (adj : coord -> coord -> bool) 
                     (p : list coord) : bool :=
  andb (is_adjacent_path adj p) (all_foreground img p).

(** ** 3.2 Basic Path Properties *)

(** Empty path is always valid *)
Lemma empty_path_valid : forall img adj,
  valid_path img adj [] = true.
Proof.
  reflexivity.
Qed.

(** Single pixel path is valid if pixel is foreground *)
Lemma singleton_path_valid : forall img adj c,
  valid_path img adj [c] = img c.
Proof.
  intros img adj c.
  unfold valid_path.
  simpl.
  rewrite andb_true_r.
  reflexivity.
Qed.

(** Valid path implies all pixels are foreground *)
Lemma valid_path_all_foreground : forall img adj p,
  valid_path img adj p = true -> all_foreground img p = true.
Proof.
  intros img adj p H.
  unfold valid_path in H.
  apply andb_prop in H.
  exact (proj2 H).
Qed.

(** Valid path implies adjacent path *)
Lemma valid_path_adjacent : forall img adj p,
  valid_path img adj p = true -> is_adjacent_path adj p = true.
Proof.
  intros img adj p H.
  unfold valid_path in H.
  apply andb_prop in H.
  exact (proj1 H).
Qed.

(** ** 3.3 Connectivity Relation
    
    Two pixels are connected if there exists a path between them.
    We define this inductively to ensure termination and ease of reasoning. *)

Inductive connected (img : simple_image) (adj : coord -> coord -> bool) 
                   : coord -> coord -> Prop :=
  | connected_refl : forall c, 
      img c = true -> connected img adj c c
  | connected_step : forall c1 c2 c3,
      connected img adj c1 c2 -> 
      img c3 = true -> 
      adj c2 c3 = true -> 
      connected img adj c1 c3.

(** ** 3.4 Basic Connectivity Properties *)

(** Connected pixels must both be foreground *)
Lemma connected_implies_foreground : forall img adj c1 c2,
  connected img adj c1 c2 -> img c1 = true /\ img c2 = true.
Proof.
  intros img adj c1 c2 H.
  induction H.
  - split; assumption.
  - split.
    + exact (proj1 IHconnected).
    + assumption.
Qed.

(** Adjacent foreground pixels are connected *)
Lemma adjacent_implies_connected : forall img adj c1 c2,
  img c1 = true -> img c2 = true -> adj c1 c2 = true ->
  connected img adj c1 c2.
Proof.
  intros img adj c1 c2 H1 H2 Hadj.
  apply connected_step with c1.
  - apply connected_refl. exact H1.
  - exact H2.
  - exact Hadj.
Qed.

(** ** 3.5 Connectivity is Symmetric *)

(** Helper: extend connectivity leftward *)
Lemma connected_extend_left : forall img adj c1 c2 c3,
  img c1 = true ->
  adj c1 c2 = true ->
  connected img adj c2 c3 ->
  connected img adj c1 c3.
Proof.
  intros img adj c1 c2 c3 H_img1 H_adj H_conn.
  induction H_conn.
  - apply adjacent_implies_connected.
    + exact H_img1.
    + exact H.
    + exact H_adj.
  - apply connected_step with c2.
    + apply IHH_conn. exact H_adj.
    + exact H.
    + exact H0.
Qed.

(** Connectivity is symmetric when adjacency is symmetric *)
Theorem connected_symmetric : forall img adj c1 c2,
  (forall a b, adj a b = adj b a) ->
  connected img adj c1 c2 -> connected img adj c2 c1.
Proof.
  intros img adj c1 c2 adj_sym H.
  induction H.
  - apply connected_refl. assumption.
  - apply connected_extend_left with c2.
    + exact H0.
    + rewrite adj_sym. exact H1.
    + exact IHconnected.
Qed.

(** ** 3.6 Connectivity is Transitive *)

Theorem connected_transitive : forall img adj c1 c2 c3,
  connected img adj c1 c2 -> connected img adj c2 c3 -> 
  connected img adj c1 c3.
Proof.
  intros img adj c1 c2 c3 H12 H23.
  induction H23.
  - exact H12.
  - apply connected_step with c2.
    + apply IHconnected. exact H12.
    + exact H.
    + exact H0.
Qed.

(** ** 3.7 Connectivity is an Equivalence Relation *)

(** Main theorem: connectivity is an equivalence relation on foreground pixels *)
Theorem connectivity_equivalence : forall img adj,
  (forall a b, adj a b = adj b a) ->
  (forall c, img c = true -> connected img adj c c) /\
  (forall c1 c2, connected img adj c1 c2 -> connected img adj c2 c1) /\
  (forall c1 c2 c3, connected img adj c1 c2 -> connected img adj c2 c3 -> 
                    connected img adj c1 c3).
Proof.
  intros img adj adj_sym.
  split; [|split].
  - intros c H. apply connected_refl. exact H.
  - intros c1 c2 H. apply connected_symmetric; assumption.
  - intros c1 c2 c3 H12 H23. apply connected_transitive with c2; assumption.
Qed.

(** ** 3.8 Path Construction from Connectivity *)

(** Helper: extract a coordinate from a connectivity proof *)
Definition connected_head {img adj c1 c2} (H : connected img adj c1 c2) : coord := c1.
Definition connected_tail {img adj c1 c2} (H : connected img adj c1 c2) : coord := c2.

(** Every pair of adjacent coordinates forms a valid 2-element path *)
Lemma adjacent_makes_path : forall img adj c1 c2,
  img c1 = true -> img c2 = true -> adj c1 c2 = true ->
  valid_path img adj [c1; c2] = true.
Proof.
  intros img adj c1 c2 H1 H2 Hadj.
  unfold valid_path.
  simpl.
  rewrite H1, H2, Hadj.
  simpl.
  reflexivity.
Qed.

(** ** 3.9 Connected Components *)

(** A connected component is the set of all pixels connected to a given pixel *)
Definition in_same_component (img : simple_image) (adj : coord -> coord -> bool) 
                            (c1 c2 : coord) : Prop :=
  connected img adj c1 c2.

(** Being in the same component is decidable for finite images *)
(* Note: We'll need additional machinery for decidability, 
   so we just state the property for now *)

(** Two components are either disjoint or identical *)
Lemma component_disjoint_or_equal : forall img adj c1 c2 c3,
  (forall a b, adj a b = adj b a) ->
  connected img adj c1 c3 ->
  connected img adj c2 c3 ->
  connected img adj c1 c2.
Proof.
  intros img adj c1 c2 c3 adj_sym H13 H23.
  apply connected_transitive with c3.
  - exact H13.
  - apply connected_symmetric.
    + exact adj_sym.
    + exact H23.
Qed.

(** ** 3.10 Properties of Components in Different Adjacencies *)

(** 4-connectivity implies 8-connectivity *)
Theorem connected_4_implies_8 : forall img c1 c2,
  connected img adjacent_4 c1 c2 ->
  connected img adjacent_8 c1 c2.
Proof.
  intros img c1 c2 H.
  induction H.
  - apply connected_refl. assumption.
  - apply connected_step with c2.
    + exact IHconnected.
    + exact H0.
    + apply adjacent_4_implies_8. exact H1.
Qed.

(** ** 3.11 Maximal Connectivity *)

(** A pixel is maximally connected to another if they share the same component *)
Definition maximally_connected (img : simple_image) (adj : coord -> coord -> bool)
                              (c1 c2 : coord) : Prop :=
  connected img adj c1 c2.

(** Components are maximal connected sets *)
Theorem component_maximality : forall img adj c1 c2 c3,
  (forall a b, adj a b = adj b a) ->
  img c1 = true ->
  img c2 = true ->
  img c3 = true ->
  connected img adj c1 c2 ->
  ~ connected img adj c1 c3 ->
  ~ connected img adj c2 c3.
Proof.
  intros img adj c1 c2 c3 adj_sym H1 H2 H3 H12 H13 H23.
  apply H13.
  apply connected_transitive with c2.
  - exact H12.
  - exact H23.
Qed.

(** * Section 4: Labeling Specifications
    
    This section defines what it means for a labeling to be correct.
    We establish the key properties that any correct connected component
    labeling must satisfy, independent of any particular algorithm. *)

(** ** 4.1 Core Properties of Labelings *)

(** Background pixels must be labeled 0 *)
Definition labels_background (img : simple_image) (l : labeling) : Prop :=
  forall c, img c = false -> l c = 0.

(** Connected pixels must have the same label *)
Definition respects_connectivity (img : simple_image) (adj : coord -> coord -> bool) 
                                (l : labeling) : Prop :=
  forall c1 c2, img c1 = true -> img c2 = true ->
                connected img adj c1 c2 -> l c1 = l c2.

(** Pixels with the same positive label must be connected *)
Definition separates_components (img : simple_image) (adj : coord -> coord -> bool)
                               (l : labeling) : Prop :=
  forall c1 c2, img c1 = true -> img c2 = true ->
                l c1 = l c2 -> l c1 <> 0 -> connected img adj c1 c2.

(** ** 4.2 Correct Labeling Definition *)

(** A correct labeling satisfies all four properties *)
Definition correct_labeling (img : simple_image) (adj : coord -> coord -> bool)
                           (l : labeling) : Prop :=
  labels_background img l /\
  respects_connectivity img adj l /\
  separates_components img adj l /\
  (forall c, img c = true -> l c <> 0).  (* Foreground pixels get positive labels *)

(** ** 4.3 Basic Properties of Correct Labelings *)

(** In a correct labeling, foreground pixels get positive labels *)
Lemma correct_labeling_foreground_positive : forall img adj l c,
  correct_labeling img adj l ->
  img c = true ->
  l c <> 0.
Proof.
  intros img adj l c [Hbg [Hresp [Hsep Hfg_pos]]] Hfg.
  apply Hfg_pos. exact Hfg.
Qed.

(** Connected pixels have equal labels *)
Lemma correct_labeling_connected_same : forall img adj l c1 c2,
  correct_labeling img adj l ->
  connected img adj c1 c2 ->
  l c1 = l c2.
Proof.
  intros img adj l c1 c2 [Hbg [Hresp [Hsep Hfg_pos]]] Hconn.
  assert (H := connected_implies_foreground img adj c1 c2 Hconn).
  destruct H as [H1 H2].
  apply Hresp; [exact H1 | exact H2 | exact Hconn].
Qed.

(** Pixels with same positive label are connected *)
Lemma correct_labeling_same_label_connected : forall img adj l c1 c2,
  correct_labeling img adj l ->
  img c1 = true -> img c2 = true ->
  l c1 = l c2 -> l c1 <> 0 ->
  connected img adj c1 c2.
Proof.
  intros img adj l c1 c2 [Hbg [Hresp Hsep]] H1 H2 Heq Hneq.
  apply Hsep; assumption.
Qed.

(** ** 4.4 Uniqueness Properties *)

(** Labels partition the foreground pixels *)
Theorem label_partition : forall img adj l,
  (forall a b, adj a b = adj b a) ->
  correct_labeling img adj l ->
  forall c1 c2, img c1 = true -> img c2 = true ->
    (l c1 = l c2) <-> (connected img adj c1 c2).
Proof.
  intros img adj l adj_sym Hcorrect c1 c2 H1 H2.
  split.
  - intros Heq.
    destruct (Nat.eq_dec (l c1) 0).
    + (* l c1 = 0, contradiction with foreground *)
      exfalso.
      apply (correct_labeling_foreground_positive img adj l c1 Hcorrect H1).
      exact e.
    + (* l c1 <> 0 *)
      apply correct_labeling_same_label_connected with l; assumption.
  - intros Hconn.
    apply correct_labeling_connected_same with img adj; assumption.
Qed.

(** ** 4.5 Label Equivalence *)

(** Two labelings are equivalent if they assign the same label to connected pixels *)
Definition labelings_equivalent (img : simple_image) (adj : coord -> coord -> bool)
                               (l1 l2 : labeling) : Prop :=
  forall c1 c2, img c1 = true -> img c2 = true ->
    (l1 c1 = l1 c2 <-> l2 c1 = l2 c2).

(** Correct labelings are unique up to relabeling *)
Theorem correct_labelings_equivalent : forall img adj l1 l2,
  (forall a b, adj a b = adj b a) ->
  correct_labeling img adj l1 ->
  correct_labeling img adj l2 ->
  labelings_equivalent img adj l1 l2.
Proof.
  intros img adj l1 l2 adj_sym Hcorr1 Hcorr2.
  intros c1 c2 H1 H2.
  rewrite (label_partition img adj l1 adj_sym Hcorr1 c1 c2 H1 H2).
  rewrite (label_partition img adj l2 adj_sym Hcorr2 c1 c2 H1 H2).
  reflexivity.
Qed.

(** ** 4.6 Properties of Component Labels *)

(** A label is used if some foreground pixel has that label *)
Definition label_used (img : simple_image) (l : labeling) (label : nat) : Prop :=
  exists c, img c = true /\ l c = label.

(** In a correct labeling, label 0 is only for background *)
Lemma label_zero_only_background : forall img adj l,
  correct_labeling img adj l ->
  ~ label_used img l 0.
Proof.
  intros img adj l Hcorr [c [Hfg Hzero]].
  apply (correct_labeling_foreground_positive img adj l c Hcorr Hfg).
  exact Hzero.
Qed.

(** Each component gets exactly one label *)
Theorem one_label_per_component : forall img adj l c1 c2,
  (forall a b, adj a b = adj b a) ->
  correct_labeling img adj l ->
  connected img adj c1 c2 ->
  l c1 = l c2.
Proof.
  intros img adj l c1 c2 adj_sym Hcorr Hconn.
  apply correct_labeling_connected_same with img adj; assumption.
Qed.

(** * Section 5: Abstract Algorithm Specification
    
    This section specifies what any connected component labeling algorithm
    must accomplish, independent of implementation details. We define the
    invariants and properties that characterize correct algorithms. *)

(** ** 5.1 Algorithm Input and Output Specification *)

(** An algorithm takes an image and adjacency relation, produces a labeling *)
Definition ccl_algorithm : Type :=
  forall (img : bounded_image) (adj : coord -> coord -> bool), labeling.

(** An algorithm is correct if it always produces correct labelings *)
Definition algorithm_correct (alg : ccl_algorithm) : Prop :=
  forall img adj, 
    (forall a b, adj a b = adj b a) ->
    correct_labeling (bounded_to_simple img) adj (alg img adj).

(** ** 5.2 Progressive Labeling Invariants *)

(** When processing pixels in order, we maintain partial labelings.
    A partial labeling is correct for processed pixels. *)

(** A region of pixels (e.g., those processed so far) *)
Definition pixel_region : Type := coord -> bool.

(** Restriction of a labeling to a region *)
Definition restrict_labeling (l : labeling) (region : pixel_region) : labeling :=
  fun c => if region c then l c else 0.

(** Restriction of an image to a region *)
Definition restrict_image (img : simple_image) (region : pixel_region) : simple_image :=
  fun c => if region c then img c else false.

(** Helper: get pixel for simple images *)
Definition get_pixel_simple (img : simple_image) (c : coord) : bool := img c.

(** A labeling is correct on a region *)
Definition correct_on_region (img : simple_image) (adj : coord -> coord -> bool)
                            (l : labeling) (region : pixel_region) : Prop :=
  correct_labeling (restrict_image img region) adj (restrict_labeling l region).

(** ** 5.3 Monotonicity Properties *)

(** When we extend the processed region, correctness is preserved *)
Definition region_subset (r1 r2 : pixel_region) : Prop :=
  forall c, r1 c = true -> r2 c = true.

(** Extending a region preserves correctness if done properly *)
Definition preserves_correctness (img : simple_image) (adj : coord -> coord -> bool)
                                (extend : labeling -> pixel_region -> coord -> labeling) : Prop :=
  forall l region c,
    correct_on_region img adj l region ->
    region c = false ->
    get_pixel_simple img c = true ->
    correct_on_region img adj (extend l region c) 
                     (fun c' => orb (region c') (coord_eqb c c')).

(** ** 5.4 Label Assignment Strategies *)

(** When assigning a label to a new pixel, we must maintain correctness *)
Definition valid_label_assignment (img : simple_image) (adj : coord -> coord -> bool)
                                 (l : labeling) (c : coord) (label : nat) : Prop :=
  (* If c is adjacent to a labeled pixel, they must get the same label if connected *)
  forall c', img c' = true -> adj c c' = true -> l c' <> 0 ->
    (connected img adj c c' -> label = l c').

(** ** 5.5 Equivalence Management *)

(** When we discover two labels should be the same (they label connected pixels),
    we need to track this equivalence *)

(** Label equivalence relation *)
Definition label_equiv : Type := nat -> nat -> Prop.

(** A valid equivalence respects connectivity *)
Definition valid_equiv (img : simple_image) (adj : coord -> coord -> bool)
                      (l : labeling) (equiv : label_equiv) : Prop :=
  forall l1 l2, equiv l1 l2 ->
    exists c1 c2, l c1 = l1 /\ l c2 = l2 /\ connected img adj c1 c2.

(** ** 5.6 Algorithm Progress Properties *)

(** An algorithm makes progress by processing pixels *)
Definition makes_progress (process : labeling -> coord -> labeling) : Prop :=
  forall l c, l c = 0 -> (process l c) c <> 0.

(** After processing all pixels, all foreground pixels are labeled *)
Definition complete_labeling (img : simple_image) (l : labeling) : Prop :=
  forall c, img c = true -> l c <> 0.

(** ** 5.7 Two-Phase Algorithm Structure *)

(** Many algorithms follow a two-phase structure:
    1. Initial labeling with possible equivalences
    2. Resolving equivalences to final labels *)

(** Phase 1 produces preliminary labels and equivalences *)
Definition phase1_correct (img : simple_image) (adj : coord -> coord -> bool)
                         (l : labeling) (equiv : label_equiv) : Prop :=
  (* All foreground pixels are labeled *)
  complete_labeling img l /\
  (* Labels respect adjacency *)
  (forall c1 c2, img c1 = true -> img c2 = true -> 
                 adj c1 c2 = true -> l c1 <> 0 -> l c2 <> 0 ->
                 equiv (l c1) (l c2)) /\
  (* Equivalence is valid *)
  valid_equiv img adj l equiv.

(** Phase 2 resolves equivalences *)
Definition phase2_correct (l_initial : labeling) (equiv : label_equiv) 
                         (l_final : labeling) : Prop :=
  forall c, l_initial c <> 0 ->
    (forall c', equiv (l_initial c) (l_initial c') -> 
                l_final c = l_final c').

(** ** 5.8 Scan-Line Processing Invariants *)

(** For algorithms that process pixels row by row *)
Definition processed_up_to (width : nat) (row col : nat) : pixel_region :=
  fun c => match c with
  | (x, y) => orb (Nat.ltb y row) 
                  (andb (Nat.eqb y row) (Nat.ltb x col))
  end.

(** Invariant maintained during row processing *)
Definition row_scan_invariant (img : bounded_image) (adj : coord -> coord -> bool)
                             (l : labeling) (row col : nat) : Prop :=
  correct_on_region (bounded_to_simple img) adj l 
                   (processed_up_to (width img) row col).

(** ** 5.9 Algorithm Termination *)

(** Algorithms must terminate on bounded images *)
Definition algorithm_terminates (alg : ccl_algorithm) : Prop :=
  (* Since we're in Coq, all functions terminate by construction.
     This property is automatically satisfied. *)
  True.

(** ** 5.10 Determinism and Uniqueness *)

(** An algorithm is deterministic - same input gives same output *)
Definition algorithm_deterministic (alg : ccl_algorithm) : Prop :=
  forall img adj, alg img adj = alg img adj.  (* Trivially true in Coq *)

(** While labelings aren't unique, the partition they induce is *)
Definition induces_same_partition (img : simple_image) (adj : coord -> coord -> bool)
                                 (l1 l2 : labeling) : Prop :=
  forall c1 c2, img c1 = true -> img c2 = true ->
    (l1 c1 = l1 c2 <-> l2 c1 = l2 c2).

(** Correct algorithms induce the same partition *)
Theorem correct_algorithms_equivalent : forall alg1 alg2 img adj,
  (forall a b, adj a b = adj b a) ->
  algorithm_correct alg1 ->
  algorithm_correct alg2 ->
  induces_same_partition (bounded_to_simple img) adj (alg1 img adj) (alg2 img adj).
Proof.
  intros alg1 alg2 img adj adj_sym Hcorr1 Hcorr2.
  apply correct_labelings_equivalent.
  - exact adj_sym.
  - apply Hcorr1. exact adj_sym.
  - apply Hcorr2. exact adj_sym.
Qed.

(** * Section 6: Two-Pass Algorithm Implementation
    
    This section implements the classical two-pass connected component labeling
    algorithm. The first pass assigns preliminary labels and records equivalences,
    while the second pass resolves these equivalences to produce final labels. *)

(** ** 6.1 Equivalence Table for Label Merging *)

(** An equivalence table tracks which labels should be merged *)
Definition equiv_table := nat -> nat -> bool.

(** Empty equivalence table - no labels are equivalent *)
Definition empty_equiv : equiv_table := fun _ _ => false.

(** Add an equivalence between two labels *)
Definition add_equiv (e : equiv_table) (l1 l2 : nat) : equiv_table :=
  fun a b => orb (e a b) (orb (andb (Nat.eqb a l1) (Nat.eqb b l2))
                              (andb (Nat.eqb a l2) (Nat.eqb b l1))).

(** ** 6.2 Equivalence Table Properties *)

(** Symmetry of equivalence tables *)
Definition equiv_sym (e : equiv_table) : Prop :=
  forall a b, e a b = e b a.

(** Empty table is symmetric *)
Lemma empty_equiv_sym : equiv_sym empty_equiv.
Proof.
  unfold equiv_sym, empty_equiv.
  reflexivity.
Qed.

(** add_equiv preserves symmetry *)
Lemma add_equiv_preserves_sym : forall e l1 l2,
  equiv_sym e ->
  equiv_sym (add_equiv e l1 l2).
Proof.
  intros e l1 l2 He.
  unfold equiv_sym, add_equiv.
  intros a b.
  rewrite He.
  f_equal.
  rewrite orb_comm.
  f_equal.
  - apply andb_comm.
  - apply andb_comm.
Qed.

(** Well-formedness: label 0 is never equivalent to positive labels *)
Definition equiv_well_formed (e : equiv_table) : Prop :=
  forall l, l > 0 -> e l 0 = false /\ e 0 l = false.

(** Empty table is well-formed *)
Lemma empty_equiv_well_formed : equiv_well_formed empty_equiv.
Proof.
  unfold equiv_well_formed, empty_equiv.
  intros l Hl.
  split; reflexivity.
Qed.

(** ** 6.3 Finding Minimum Equivalent Label *)

(** Find the minimum label equivalent to l *)
Fixpoint find_min_equiv (e : equiv_table) (l : nat) (fuel : nat) : nat :=
  match fuel with
  | O => l
  | S fuel' => 
    let fix scan_labels (n : nat) : nat :=
      match n with
      | O => l
      | S n' => if e l n' then
                  Nat.min n' (scan_labels n')
                else scan_labels n'
      end
    in Nat.min l (scan_labels l)
  end.

(** ** 6.4 First Pass - Row Processing *)

(** Process a single pixel in the first pass *)
Definition process_pixel (img : bounded_image) (adj : coord -> coord -> bool)
                        (labels : labeling) (equiv : equiv_table)
                        (c : coord) (next_label : nat) 
                        : (labeling * equiv_table * nat) :=
  if get_pixel img c then
    let x := coord_x c in
    let y := coord_y c in
    (* Check left neighbor *)
    let left := if x =? 0 then 0 else 
                if adj (x - 1, y) c then labels (x - 1, y) else 0 in
    (* Check up neighbor *)
    let up := if y =? 0 then 0 else
              if adj (x, y - 1) c then labels (x, y - 1) else 0 in
    match left, up with
    | 0, 0 => 
        (* No labeled neighbors - assign new label *)
        ((fun c' => if coord_eqb c c' then next_label else labels c'),
         equiv,
         S next_label)
    | l, 0 | 0, l => 
        (* One labeled neighbor - use its label *)
        ((fun c' => if coord_eqb c c' then l else labels c'),
         equiv,
         next_label)
    | l1, l2 =>
        (* Two labeled neighbors *)
        let label := Nat.min l1 l2 in
        let new_labels := fun c' => if coord_eqb c c' then label else labels c' in
        let new_equiv := if Nat.eqb l1 l2 then equiv else add_equiv equiv l1 l2 in
        (new_labels, new_equiv, next_label)
    end
  else
    (labels, equiv, next_label).

(** Process a row of pixels *)
Fixpoint process_row (img : bounded_image) (adj : coord -> coord -> bool)
                     (labels : labeling) (equiv : equiv_table)
                     (y : nat) (x : nat) (width : nat) (next_label : nat)
                     : (labeling * equiv_table * nat) :=
  match width with
  | O => (labels, equiv, next_label)
  | S width' =>
      if x <? S width' then
        let '(labels', equiv', next') := 
          process_pixel img adj labels equiv (x, y) next_label in
        process_row img adj labels' equiv' y (S x) width' next'
      else
        (labels, equiv, next_label)
  end.

(** Process all rows *)
Fixpoint process_all_rows (img : bounded_image) (adj : coord -> coord -> bool)
                          (labels : labeling) (equiv : equiv_table)
                          (y : nat) (height : nat) (next_label : nat)
                          : (labeling * equiv_table * nat) :=
  match height with
  | O => (labels, equiv, next_label)
  | S height' =>
      if y <? S height' then
        let '(labels', equiv', next') :=
          process_row img adj labels equiv y 0 (width img) next_label in
        process_all_rows img adj labels' equiv' (S y) height' next'
      else
        (labels, equiv, next_label)
  end.

(** Complete first pass *)
Definition first_pass (img : bounded_image) (adj : coord -> coord -> bool) 
                     : (labeling * equiv_table * nat) :=
  process_all_rows img adj empty_labeling empty_equiv 0 (height img) 1.

(** ** 6.5 Second Pass - Resolve Equivalences *)

Definition second_pass (labels : labeling) (equiv : equiv_table) (max_label : nat) 
                      : labeling :=
  fun c => 
    let l := labels c in
    if Nat.eqb l 0 then 0
    else find_min_equiv equiv l max_label.

(** ** 6.6 Complete Two-Pass Algorithm *)

Definition two_pass_ccl (img : bounded_image) (adj : coord -> coord -> bool) : labeling :=
  let '(labels, equiv, max_label) := first_pass img adj in
  second_pass labels equiv max_label.

(** * Section 7: Algorithm Invariants
    
    This section establishes the key invariants maintained by the two-pass
    algorithm. We prove properties about how labels and equivalences evolve
    during processing. *)

(** ** 7.1 Label Update Properties *)

(** Updating a label at one coordinate doesn't affect others *)
Lemma label_update_other : forall (labels : labeling) (c c' : coord) (label : nat),
  c <> c' ->
  (fun x => if coord_eqb c x then label else labels x) c' = labels c'.
Proof.
  intros labels c c' label Hneq.
  simpl.
  destruct (coord_eqb c c') eqn:Heq.
  - apply coord_eqb_true_iff in Heq. 
    contradiction.
  - reflexivity.
Qed.

(** Updating a label at a coordinate gives the new label *)
Lemma label_update_same : forall (labels : labeling) (c : coord) (label : nat),
  (fun x => if coord_eqb c x then label else labels x) c = label.
Proof.
  intros labels c label.
  simpl.
  rewrite coord_eqb_refl.
  reflexivity.
Qed.

(** ** 7.2 Equivalence Table Evolution *)

(** Adding an equivalence preserves existing equivalences *)
Lemma add_equiv_preserves : forall e l1 l2 a b,
  e a b = true -> add_equiv e l1 l2 a b = true.
Proof.
  intros e l1 l2 a b H.
  unfold add_equiv.
  rewrite H.
  reflexivity.
Qed.

(** Adding an equivalence creates the intended equivalence *)
Lemma add_equiv_creates : forall e l1 l2,
  add_equiv e l1 l2 l1 l2 = true.
Proof.
  intros e l1 l2.
  unfold add_equiv.
  rewrite !Nat.eqb_refl.
  simpl.
  rewrite orb_true_r.
  reflexivity.
Qed.

(** Adding an equivalence creates symmetric equivalence *)
Lemma add_equiv_creates_sym : forall e l1 l2,
  add_equiv e l1 l2 l2 l1 = true.
Proof.
  intros e l1 l2.
  unfold add_equiv.
  (* We have: e l2 l1 || ((l2 =? l1) && (l1 =? l2) || (l2 =? l2) && (l1 =? l1)) *)
  (* Since l2 =? l2 = true and l1 =? l1 = true, the last term is true *)
  rewrite !Nat.eqb_refl.
  (* Now: e l2 l1 || ((l2 =? l1) && (l1 =? l2) || true && true) *)
  simpl.
  (* true && true = true, so: e l2 l1 || ((l2 =? l1) && (l1 =? l2) || true) *)
  (* For any X, X || true = true *)
  destruct ((l2 =? l1) && (l1 =? l2)); simpl; 
  rewrite orb_true_r; reflexivity.
Qed.

(** ** 7.3 Process Pixel Properties *)

(** Background pixels remain unlabeled *)
Lemma process_pixel_background : forall img adj labels equiv c next_label,
  get_pixel img c = false ->
  process_pixel img adj labels equiv c next_label = (labels, equiv, next_label).
Proof.
  intros img adj labels equiv c next_label Hbg.
  unfold process_pixel.
  rewrite Hbg.
  reflexivity.
Qed.

(** Processing preserves labels at other coordinates *)
Lemma process_pixel_preserves_other : forall img adj labels equiv c c' next_label,
  c <> c' ->
  let '(labels', _, _) := process_pixel img adj labels equiv c next_label in
  labels' c' = labels c'.
Proof.
  intros img adj labels equiv c c' next_label Hneq.
  unfold process_pixel.
  destruct (get_pixel img c) eqn:Hpix; [|reflexivity].
  (* Now we need to be careful with the pattern matching *)
  remember (if coord_x c =? 0 then 0 else 
            if adj (coord_x c - 1, coord_y c) c then labels (coord_x c - 1, coord_y c) else 0) as left.
  remember (if coord_y c =? 0 then 0 else
            if adj (coord_x c, coord_y c - 1) c then labels (coord_x c, coord_y c - 1) else 0) as up.
  destruct left; destruct up; simpl; apply label_update_other; assumption.
Qed.

(** ** 7.4 Next Label Monotonicity *)

(** Next label never decreases *)
Lemma process_pixel_next_label_mono : forall img adj labels equiv c next_label,
  let '(_, _, next') := process_pixel img adj labels equiv c next_label in
  next' >= next_label.
Proof.
  intros img adj labels equiv c next_label.
  unfold process_pixel.
  destruct (get_pixel img c) eqn:Hpix.
  - (* get_pixel img c = true *)
    remember (if coord_x c =? 0 then 0 else 
              if adj (coord_x c - 1, coord_y c) c then labels (coord_x c - 1, coord_y c) else 0) as left.
    remember (if coord_y c =? 0 then 0 else
              if adj (coord_x c, coord_y c - 1) c then labels (coord_x c, coord_y c - 1) else 0) as up.
    destruct left; destruct up; simpl; lia.
  - (* get_pixel img c = false *)
    simpl. lia.
Qed.

(** Next label is positive if it starts positive *)
Lemma process_pixel_next_label_positive : forall img adj labels equiv c next_label,
  next_label > 0 ->
  let '(_, _, next') := process_pixel img adj labels equiv c next_label in
  next' > 0.
Proof.
  intros img adj labels equiv c next_label Hpos.
  pose proof (process_pixel_next_label_mono img adj labels equiv c next_label).
  destruct (process_pixel img adj labels equiv c next_label) as [[? ?] next'].
  lia.
Qed.

(** ** 7.5 Row Processing Invariants *)

(** Processing a row preserves next_label monotonicity *)
Lemma process_row_next_label_mono : forall img adj labels equiv y x width next_label,
  let '(_, _, next') := process_row img adj labels equiv y x width next_label in
  next' >= next_label.
Proof.
  intros img adj labels equiv y x width.
  revert x labels equiv.
  induction width as [|width' IH]; intros x labels equiv next_label.
  - simpl. lia.
  - simpl.
    destruct (x <? S width') eqn:Hlt; [|lia].
    destruct (process_pixel img adj labels equiv (x, y) next_label) as [[labels' equiv'] next'] eqn:Hpix.
    pose proof (process_pixel_next_label_mono img adj labels equiv (x, y) next_label).
    rewrite Hpix in H.
    pose proof (IH (S x) labels' equiv' next') as H1.
    destruct (process_row img adj labels' equiv' y (S x) width' next') as [[l e] next''].
    lia.
Qed.

(** ** 7.6 Coordinate Bounds *)

(** Processing respects image bounds *)
Definition coords_in_bounds (img : bounded_image) (c : coord) : Prop :=
  coord_x c < width img /\ coord_y c < height img.

(** process_pixel only modifies in-bounds coordinates *)
Lemma process_pixel_out_of_bounds : forall img adj labels equiv c next_label,
  ~ coords_in_bounds img c ->
  get_pixel img c = false.
Proof.
  intros img adj labels equiv c next_label Hout.
  unfold get_pixel, in_bounds, coords_in_bounds in *.
  destruct (coord_x c <? width img) eqn:Hx;
  destruct (coord_y c <? height img) eqn:Hy;
  simpl.
  - apply Nat.ltb_lt in Hx, Hy. exfalso. apply Hout. split; assumption.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** ** 7.7 Empty Labeling Properties *)

(** Empty labeling assigns 0 everywhere *)
Lemma empty_labeling_is_zero : forall c,
  empty_labeling c = 0.
Proof.
  reflexivity.
Qed.

(** ** 7.8 Well-Formed Equivalence Preservation *)

(** add_equiv preserves well-formedness when adding positive labels *)
Lemma add_equiv_preserves_well_formed : forall e l1 l2,
  equiv_well_formed e ->
  l1 > 0 -> l2 > 0 ->
  equiv_well_formed (add_equiv e l1 l2).
Proof.
  intros e l1 l2 Hwf Hl1 Hl2.
  unfold equiv_well_formed in *.
  intros l Hl.
  unfold add_equiv.
  destruct (Hwf l Hl) as [H1 H2].
  split.
  - rewrite H1. simpl.
    destruct (l =? l1) eqn:Heq1.
    + apply Nat.eqb_eq in Heq1. subst.
      rewrite Nat.eqb_refl. simpl.
      destruct (0 =? l2) eqn:Heq2.
      * apply Nat.eqb_eq in Heq2. lia.
      * reflexivity.
    + destruct (l =? l2) eqn:Heq2.
      * apply Nat.eqb_eq in Heq2. subst.
        destruct (0 =? l1) eqn:Heq3.
        -- apply Nat.eqb_eq in Heq3. lia.
        -- reflexivity.
      * reflexivity.
  - rewrite H2. simpl.
    destruct (0 =? l1) eqn:Heq1.
    + apply Nat.eqb_eq in Heq1. lia.
    + destruct (0 =? l2) eqn:Heq2.
      * apply Nat.eqb_eq in Heq2. lia.
      * reflexivity.
Qed.

(** ** 7.9 Basic Properties of find_min_equiv *)

(** find_min_equiv returns input when fuel is 0 *)
Lemma find_min_equiv_fuel_zero : forall e l,
  find_min_equiv e l 0 = l.
Proof.
  reflexivity.
Qed.

(** find_min_equiv never returns 0 for positive input *)
Lemma find_min_equiv_positive : forall e l fuel,
  equiv_well_formed e ->
  l > 0 ->
  find_min_equiv e l fuel > 0.
Proof.
  intros e l fuel Hwf Hl.
  induction fuel as [|fuel' IH].
  - exact Hl.
  - simpl.
    (* The minimum of positive numbers is positive *)
    assert (forall a b, a > 0 -> b > 0 -> Nat.min a b > 0).
    { intros a b Ha Hb. 
      unfold Nat.min.
      destruct (a <=? b); assumption. }
    apply H.
    + exact Hl.
    + (* Need to prove scan_labels returns positive *)
      clear H IH.
      assert (forall n, 
        (fix scan_labels (n : nat) : nat :=
          match n with
          | 0 => l
          | S n' => if e l n' then Nat.min n' (scan_labels n') else scan_labels n'
          end) n > 0).
      { intro n.
        induction n as [|n' IHn].
        - exact Hl.
        - simpl.
          destruct (e l n') eqn:Heq.
          + destruct n'.
            * destruct (Hwf l Hl) as [Hwf1 _].
              rewrite Heq in Hwf1. discriminate.
            * assert (S n' > 0) by lia.
              assert (Nat.min (S n') IHn > 0).
              { unfold Nat.min. destruct (S n' <=? IHn); [exact H | exact IHn]. }
              exact H0.
          + exact IHn. }
      apply H.
Qed.
