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
Fixpoint find_min_equiv (e : equiv_table) (l : nat) (fuel : nat) {struct fuel} : nat :=
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

(** find_min_equiv returns input when fuel is 0 *)
Lemma find_min_equiv_fuel_zero : forall e l,
  find_min_equiv e l 0 = l.
Proof.
  reflexivity.
Qed.

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
Lemma process_pixel_out_of_bounds : forall img c,
  ~ coords_in_bounds img c ->
  get_pixel img c = false.
Proof.
  intros img c Hout.
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
      destruct l1.
      * lia.
      * simpl. 
        destruct l2.
        -- lia.
        -- simpl. rewrite andb_false_r. reflexivity.
    + destruct (l =? l2) eqn:Heq2.
      * apply Nat.eqb_eq in Heq2. subst.
        destruct l1.
        -- lia.
        -- simpl. reflexivity.
      * reflexivity.
  - rewrite H2. simpl.
    destruct l1.
    + lia.
    + destruct l2.
      * lia.
      * simpl. reflexivity.
Qed.

(** ** 7.9 Basic Properties of find_min_equiv *)

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
      destruct a.
      - lia.
      - destruct b.
        + lia.
        + simpl. lia. }
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
              (* Apply the min lemma to S n' and the recursive call *)
              assert (forall a b, a > 0 -> b > 0 -> Nat.min a b > 0).
              { intros a b Ha Hb. 
                destruct a; [lia|].
                destruct b; [lia|].
                simpl. lia. }
              apply H0; [exact H|exact IHn].
          + exact IHn. }
      apply H.
Qed.

(** * Section 8: Bounded Label Generation
    
    This section establishes bounds on the labels generated by the algorithm.
    We prove that the number of labels is bounded by the image size, ensuring
    termination and providing complexity bounds. *)

(** ** 8.1 Label Generation Bounds *)

(** process_pixel increments next_label by at most 1 *)
Lemma process_pixel_increment_bound : forall img adj labels equiv c next_label,
  let '(_, _, next') := process_pixel img adj labels equiv c next_label in
  next' <= S next_label.
Proof.
  intros img adj labels equiv c next_label.
  unfold process_pixel.
  destruct (get_pixel img c) eqn:Hpix.
  - (* Foreground pixel *)
    remember (if coord_x c =? 0 then 0 else 
              if adj (coord_x c - 1, coord_y c) c then labels (coord_x c - 1, coord_y c) else 0) as left.
    remember (if coord_y c =? 0 then 0 else
              if adj (coord_x c, coord_y c - 1) c then labels (coord_x c, coord_y c - 1) else 0) as up.
    destruct left; destruct up; simpl; lia.
  - (* Background pixel *)
    simpl. lia.
Qed.

(** process_pixel generates exactly one new label or none *)
Lemma process_pixel_increment_exact : forall img adj labels equiv c next_label,
  let '(_, _, next') := process_pixel img adj labels equiv c next_label in
  next' = next_label \/ next' = S next_label.
Proof.
  intros img adj labels equiv c next_label.
  unfold process_pixel.
  destruct (get_pixel img c) eqn:Hpix.
  - (* Foreground pixel *)
    remember (if coord_x c =? 0 then 0 else 
              if adj (coord_x c - 1, coord_y c) c then labels (coord_x c - 1, coord_y c) else 0) as left.
    remember (if coord_y c =? 0 then 0 else
              if adj (coord_x c, coord_y c - 1) c then labels (coord_x c, coord_y c - 1) else 0) as up.
    destruct left; destruct up; simpl; auto.
  - (* Background pixel *)
    simpl. auto.
Qed.

(** ** 8.2 Row Processing Bounds *)

(** Helper: Empty width means no increment *)
Lemma process_row_empty_width : forall img adj labels equiv y x next_label,
  process_row img adj labels equiv y x 0 next_label = (labels, equiv, next_label).
Proof.
  intros. reflexivity.
Qed.

(** Helper: Out of bounds means no processing *)
Lemma process_row_out_of_bounds : forall img adj labels equiv y x width next_label,
  x >= width ->
  process_row img adj labels equiv y x width next_label = (labels, equiv, next_label).
Proof.
  intros img adj labels equiv y x width next_label Hbound.
  destruct width.
  - reflexivity.
  - simpl. 
    assert (x <? S width0 = false) by (apply Nat.ltb_nlt; lia).
    rewrite H. reflexivity.
Qed.

(** Helper: Single step bound *)
Lemma process_row_step_bound : forall img adj labels equiv y x width next_label labels' equiv' next',
  x < width ->
  process_pixel img adj labels equiv (x, y) next_label = (labels', equiv', next') ->
  next' <= S next_label.
Proof.
  intros img adj labels equiv y x width next_label labels' equiv' next' Hlt Hpix.
  pose proof (process_pixel_increment_bound img adj labels equiv (x, y) next_label).
  rewrite Hpix in H. exact H.
Qed.

(** Helper: Subtraction arithmetic for successor *)
Lemma width_sub_x_succ : forall width x,
  x <= width ->
  S width - x = S (width - x).
Proof.
  intros width x Hle.
  lia.
Qed.

(** Helper: Subtraction arithmetic for incremented x *)
Lemma width_sub_succ_x : forall width x,
  x < width ->
  width - S x = width - x - 1.
Proof.
  intros width x Hlt.
  lia.
Qed.

(** Helper: Transitivity for bounded increments *)
Lemma bounded_increment_trans : forall a b c d e,
  a <= b + c ->
  b <= S d ->
  c = e - 1 ->
  e > 0 ->
  a <= d + e.
Proof.
  intros a b c d e H1 H2 H3 He.
  rewrite H3 in H1.
  assert (b + (e - 1) <= S d + (e - 1)) by lia.
  assert (S d + (e - 1) = d + S (e - 1)) by lia.
  assert (S (e - 1) = e) by lia.
  lia.
Qed.

(** Helper: Match expression evaluation for x = 0 *)
Lemma match_x_zero : forall width',
  match 0 with | 0 => S width' | S l => width' - l end = S width'.
Proof.
  reflexivity.
Qed.

(** Helper: Match expression evaluation for x = S l *)
Lemma match_x_succ : forall width' l,
  match S l with | 0 => S width' | S l' => width' - l' end = width' - l.
Proof.
  reflexivity.
Qed.

(** Helper: When processing exactly one pixel *)
Lemma single_pixel_bound : forall next' next_label,
  next' <= S next_label ->
  next' <= next_label + 1.
Proof.
  intros. lia.
Qed.

(** Helper: Edge case when x = width' *)
Lemma process_row_edge_case : forall img adj labels equiv y width' next_label,
  let '(_, _, next') := process_pixel img adj labels equiv (width', y) next_label in
  next' <= next_label + 1.
Proof.
  intros.
  destruct (process_pixel img adj labels equiv (width', y) next_label) as [[? ?] next'] eqn:Hpix.
  pose proof (process_pixel_increment_bound img adj labels equiv (width', y) next_label).
  rewrite Hpix in H.
  exact (single_pixel_bound next' next_label H).
Qed.

(** Helper: The match expression always evaluates to 1 *)
Lemma match_width_minus_pred : forall w',
  match w' with | 0 => S w' | S l => w' - l end = 1.
Proof.
  intros w'.
  destruct w' as [|l].
  - reflexivity.
  - assert (S l - l = 1).
    { induction l as [|l' IH].
      - reflexivity.
      - simpl. exact IH. }
    exact H.
Qed.

(** process_row increments next_label by at most the number of pixels processed *)
Lemma process_row_increment_bound : forall img adj labels equiv y x width next_label,
  x <= width ->
  let '(_, _, next') := process_row img adj labels equiv y x width next_label in
  next' <= next_label + (width - x).
Proof.
  intros img adj labels equiv y x width.
  revert x labels equiv.
  induction width as [|width' IH]; intros x labels equiv next_label Hbound.
  - rewrite process_row_empty_width. lia.
  - simpl. destruct (x <? S width') eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      destruct (process_pixel img adj labels equiv (x, y) next_label) as [[labels' equiv'] next'] eqn:Hpix.
      pose proof (process_row_step_bound img adj labels equiv y x (S width') next_label labels' equiv' next' Hlt Hpix).
      destruct (Nat.le_gt_cases (S x) width') as [Hle | Hgt].
      * specialize (IH (S x) labels' equiv' next' Hle).
        destruct (process_row img adj labels' equiv' y (S x) width' next') as [[? ?] next''] eqn:Hrow.
        assert (x < width') by lia.
        (* Simplify the match expression *)
        assert (match x with | 0 => S width' | S l0 => width' - l0 end = S width' - x) by
          (destruct x; reflexivity).
        rewrite H1.
        rewrite (width_sub_succ_x width' x H0) in IH.
        assert (S width' - x = S (width' - x)) by (apply width_sub_x_succ; lia).
        rewrite H2.
        lia.
      * (* S x > width', so x = width' *)
        assert (x = width') by lia.
        subst x.
        assert (S width' >= width') by lia.
        rewrite (process_row_out_of_bounds img adj labels' equiv' y (S width') width' next' H0).
        rewrite match_width_minus_pred.
        exact (single_pixel_bound next' next_label H).
    + (* x >= S width' *)
      apply Nat.ltb_nlt in Hlt.
      assert (x = S width') by lia.
      subst x.
      assert (match S width' with | 0 => S width' | S l => width' - l end = 0).
      { simpl. lia. }
      rewrite H. lia.
Qed.

(** ** 8.3 General Arithmetic Lemmas for Subtraction *)

(** The specific match pattern from our proof *)
Lemma succ_sub_match : forall n m,
  match m with 
  | 0 => S n 
  | S m' => n - m' 
  end = S n - m.
Proof.
  intros n m.
  destruct m.
  - reflexivity.
  - simpl. reflexivity.
Qed.

(** General pattern: processing one element with bounded increment *)
Lemma single_step_bound : forall (f : nat -> nat) (n : nat),
  (forall m, f m <= S m) ->  (* f increments by at most 1 *)
  f n <= n + 1.
Proof.
  intros f n Hf.
  pose proof (Hf n).
  lia.
Qed.

(** Subtraction arithmetic for successor *)
Lemma succ_sub_le : forall n m,
  m <= n ->
  S n - m = S (n - m).
Proof.
  intros n m H.
  lia.
Qed.

(** When incrementing position reaches bound *)
Lemma increment_at_bound : forall n bound,
  n < bound ->
  S n > bound ->
  n = bound.
Proof.
  intros n bound Hlt Hgt.
  lia.
Qed.

(** Bounded recursion with decreasing fuel *)
Lemma bounded_recursion : forall (f : nat -> nat) (start fuel : nat),
  (forall n, f n <= S n) ->  (* single step bound *)
  (forall k n, k <= fuel -> 
    Nat.iter k f n <= n + k) ->  (* iteration bound *)
  start <= fuel ->
  Nat.iter (fuel - start) f start <= fuel.
Proof.
  intros f start fuel Hstep Hiter Hbound.
  pose proof (Hiter (fuel - start) start).
  assert (fuel - start <= fuel) by lia.
  specialize (H H0).
  assert (start + (fuel - start) = fuel) by lia.
  lia.
Qed.

(** Processing a range with out-of-bounds check *)
Lemma range_processing_bound : forall (process : nat -> nat -> nat) (start width init : nat),
  (forall pos n, process pos n <= S n) ->  (* each step increments by at most 1 *)
  (forall pos n, pos >= width -> process pos n = n) ->  (* no-op when out of bounds *)
  start <= width ->
  (fix iter pos fuel n :=
    match fuel with
    | 0 => n
    | S fuel' => 
        if pos <? width then
          iter (S pos) fuel' (process pos n)
        else n
    end) start (width - start) init <= init + (width - start).
Proof.
  intros process start width init Hstep Hout Hbound.
  remember (width - start) as fuel.
  assert (start + fuel = width) as Hsum by lia.
  clear Heqfuel.
  revert start init Hsum Hbound.
  induction fuel as [|fuel' IH]; intros start init Hsum Hbound.
  - simpl. lia.
  - simpl.
    assert (start < width) by lia.
    assert (start <? width = true) by (apply Nat.ltb_lt; exact H).
    rewrite H0.
    pose proof (Hstep start init) as Hstep_init.
    assert (S start + fuel' = width) by lia.
    assert (S start <= width) by lia.
    specialize (IH (S start) (process start init) H1 H2).
    assert (process start init + fuel' <= init + 1 + fuel') by lia.
    assert (init + 1 + fuel' = init + S fuel') by lia.
    lia.
Qed.


(** Helper: process_row preserves positive labels *)
Lemma process_row_next_label_positive : forall img adj labels equiv y x width next_label,
  next_label > 0 ->
  let '(_, _, next') := process_row img adj labels equiv y x width next_label in
  next' > 0.
Proof.
  intros img adj labels equiv y x width.
  revert x labels equiv.
  induction width as [|width' IH]; intros x labels equiv next_label Hpos.
  - simpl. exact Hpos.
  - simpl.
    destruct (x <? S width') eqn:Hlt.
    + destruct (process_pixel img adj labels equiv (x, y) next_label) as [[labels' equiv'] next'] eqn:Hpix.
      pose proof (process_pixel_next_label_positive img adj labels equiv (x, y) next_label Hpos) as H.
      rewrite Hpix in H.
      apply IH. exact H.
    + exact Hpos.
Qed.

(** Helper: process_all_rows preserves positive labels *)
Lemma process_all_rows_next_label_positive : forall img adj labels equiv y height next_label,
  next_label > 0 ->
  let '(_, _, next') := process_all_rows img adj labels equiv y height next_label in
  next' > 0.
Proof.
  intros img adj labels equiv y height.
  revert y labels equiv.
  induction height as [|height' IH]; intros y labels equiv next_label Hpos.
  - simpl. exact Hpos.
  - simpl.
    destruct (y <? S height') eqn:Hlt.
    + destruct (process_row img adj labels equiv y 0 (width img) next_label) as [[labels' equiv'] next'] eqn:Hrow.
      pose proof (process_row_next_label_positive img adj labels equiv y 0 (width img) next_label Hpos) as H.
      rewrite Hrow in H.
      apply IH. exact H.
    + exact Hpos.
Qed.

(** ** 8.4 All Rows Processing Bounds *)

(** Helper: Empty height means no processing *)
Lemma process_all_rows_empty_height : forall img adj labels equiv y next_label,
  process_all_rows img adj labels equiv y 0 next_label = (labels, equiv, next_label).
Proof.
  intros. reflexivity.
Qed.

(** Helper: Process zero rows means no change *)
Lemma process_all_rows_zero_height : forall img adj labels equiv y next_label,
  process_all_rows img adj labels equiv y 0 next_label = (labels, equiv, next_label).
Proof.
  intros. reflexivity.
Qed.

(** Helper: Arithmetic for remaining rows *)
Lemma remaining_rows_arithmetic : forall height y,
  y < height ->
  S height - y = S (height - y).
Proof.
  intros. lia.
Qed.

(** Helper: Out of bounds means no processing *)
Lemma process_all_rows_out_of_bounds : forall img adj labels equiv y height next_label,
  y >= height ->
  process_all_rows img adj labels equiv y height next_label = (labels, equiv, next_label).
Proof.
  intros img adj labels equiv y height next_label Hbound.
  destruct height as [|h'].
  - (* Case height = 0 *)
    reflexivity.
  - (* Case height = S h'. Hbound is y >= S h' *)
    simpl.
    (* The goal is `(if y <? S h' then ... else ...) = ...` *)
    (* We prove which branch the `if` takes by destructing the condition. *)
    (* `eqn:E` saves the result of the condition in a new hypothesis `E`. *)
    destruct (y <? S h') eqn:E.
    + (* Case 1: Assume `y <? S h' = true`. This branch should be impossible. *)
      (* The hypothesis `E` is `y <? S h' = true`. Let's turn it into a proposition. *)
      apply Nat.ltb_lt in E.
      (* Now `E` is `y < S h'`. *)
      (* Our main hypothesis `Hbound` is `y >= S h'`. This contradicts `E`. *)
      (* We can show this contradiction formally. *)
      apply Nat.nlt_ge in Hbound.
      (* Now `Hbound` is `~ (y < S h')`. This directly contradicts `E`. *)
      contradiction.
    + (* Case 2: Assume `y <? S h' = false`. This is the case we expect. *)
      (* Since the condition is false, the `if` evaluates to the `else` branch. *)
      (* Coq simplifies the goal to: `(labels, equiv, next_label) = (labels, equiv, next_label)` *)
      reflexivity.
Qed.

(** ** 8.6 Foreground Pixel Label Assignment *)

(** Foreground pixels get positive labels after processing *)
Lemma process_pixel_foreground_gets_label : forall img adj labels equiv c next_label,
  get_pixel img c = true ->
  next_label > 0 ->
  let '(labels', _, _) := process_pixel img adj labels equiv c next_label in
  labels' c > 0.
Proof.
  intros img adj labels equiv c next_label Hfg Hpos.
  unfold process_pixel.
  rewrite Hfg.
  remember (if coord_x c =? 0 then 0 else 
            if adj (coord_x c - 1, coord_y c) c then labels (coord_x c - 1, coord_y c) else 0) as left.
  remember (if coord_y c =? 0 then 0 else
            if adj (coord_x c, coord_y c - 1) c then labels (coord_x c, coord_y c - 1) else 0) as up.
  destruct left as [|left_label]; destruct up as [|up_label]; simpl.
  - rewrite label_update_same. exact Hpos.
  - rewrite label_update_same. lia.
  - rewrite label_update_same. lia.
  - rewrite label_update_same. 
    unfold Nat.min.
    destruct (left_label <=? up_label); lia.
Qed.

(** ** 8.7 First Pass Label Positivity *)

(** First pass assigns positive labels *)
Lemma first_pass_labels_positive : forall img adj,
  let '(_, _, max_label) := first_pass img adj in
  max_label > 0.
Proof.
  intros img adj.
  unfold first_pass.
  assert (1 > 0) by lia.
  pose proof (process_all_rows_next_label_positive img adj empty_labeling empty_equiv 0 (height img) 1 H) as Hpos.
  destruct (process_all_rows img adj empty_labeling empty_equiv 0 (height img) 1) as [[? ?] max_label].
  exact Hpos.
Qed.

(** ** 8.8 Background Pixels Remain Unlabeled *)

(** Background pixels stay labeled as 0 *)
Lemma process_pixel_background_stays_zero : forall img adj labels equiv c next_label,
  get_pixel img c = false ->
  let '(labels', _, _) := process_pixel img adj labels equiv c next_label in
  labels' c = labels c.
Proof.
  intros img adj labels equiv c next_label Hbg.
  unfold process_pixel.
  rewrite Hbg.
  reflexivity.
Qed.

(** * Section 9: Arithmetic for All Rows Processing
    
    This section provides the arithmetic infrastructure needed to prove bounds
    on the all-rows processing function. We decompose the complex proof into
    manageable pieces by establishing key arithmetic properties. *)

(** ** 9.1 Match Expression Arithmetic *)

(** Subtraction with match on the subtrahend *)
Lemma match_sub_zero : forall n,
  match 0 with
  | 0 => S n
  | S m => n - m
  end = S n.
Proof.
  reflexivity.
Qed.

(** Subtraction with match on successor *)
Lemma match_sub_succ : forall n m,
  match S m with
  | 0 => S n
  | S m' => n - m'
  end = n - m.
Proof.
  reflexivity.
Qed.

(** General form of the match expression *)
Lemma match_sub_form : forall height y,
  match y with
  | 0 => S height
  | S y' => height - y'
  end = S height - y.
Proof.
  intros height y.
  destruct y as [|y'].
  - reflexivity.
  - reflexivity.
Qed.

(** ** 9.2 Height and Row Arithmetic *)

(** When y < S height, we have specific arithmetic properties *)
Lemma height_sub_arithmetic : forall height y,
  y < S height ->
  S height - y = S (height - y).
Proof.
  intros height y Hlt.
  lia.
Qed.

(** Subtraction by successor *)
Lemma sub_succ_sub : forall n m,
  m < n ->
  n - S m = n - m - 1.
Proof.
  intros n m Hlt.
  lia.
Qed.

(** Relationship between consecutive subtractions *)
Lemma consecutive_sub_relation : forall height y,
  S y <= height ->
  height - y = S (height - S y).
Proof.
  intros height y Hle.
  lia.
Qed.

(** ** 9.3 Multiplication and Subtraction Properties *)

(** Distributivity of multiplication over subtraction *)
Lemma mul_sub_distr_r : forall a b c,
  b >= c ->
  (b - c) * a = b * a - c * a.
Proof.
  intros a b c Hge.
  rewrite Nat.mul_comm.
  rewrite Nat.mul_comm with (n := b).
  rewrite Nat.mul_comm with (n := c).
  rewrite <- Nat.mul_sub_distr_l.
  reflexivity.
Qed.

(** Adding one to a product *)
Lemma succ_mul_expand : forall n m,
  S n * m = m + n * m.
Proof.
  intros n m.
  rewrite Nat.mul_succ_l.
  rewrite Nat.add_comm.
  reflexivity.
Qed.

(** Subtracting one from a product *)
Lemma pred_mul_contract : forall n m,
  n > 0 ->
  (n - 1) * m + m = n * m.
Proof.
  intros n m Hpos.
  destruct n as [|n'].
  - lia.
  - simpl. lia.
Qed.

(** ** 9.4 Row and Column Index Properties *)

(** When processing from column 0, we process exactly width pixels *)
Lemma process_from_zero : forall width,
  width - 0 = width.
Proof.
  intros width.
  apply Nat.sub_0_r.
Qed.

(** Remaining pixels after processing x columns *)
Lemma remaining_pixels : forall width x,
  x <= width ->
  width - x + x = width.
Proof.
  intros width x Hle.
  lia.
Qed.

(** Processing one more pixel *)
Lemma process_one_more : forall width x,
  x < width ->
  width - x = S (width - S x).
Proof.
  intros width x Hlt.
  lia.
Qed.

(** ** 9.5 Height Iteration Properties *)

(** Match expression evaluation for specific cases *)
Lemma match_height_zero : forall height,
  match 0 with
  | 0 => S height
  | S y' => height - y'
  end = S height.
Proof.
  reflexivity.
Qed.

(** Match expression for successor *)
Lemma match_height_succ : forall height y',
  match S y' with
  | 0 => S height
  | S y'' => height - y''
  end = height - y'.
Proof.
  reflexivity.
Qed.

(** Height arithmetic when iterating *)
Lemma height_iter_step : forall height y,
  y < height ->
  height - y = S (height - S y).
Proof.
  intros height y Hlt.
  lia.
Qed.

(** Total pixels in remaining rows *)
Lemma remaining_rows_pixels : forall width height y,
  y <= height ->
  (height - y) * width = height * width - y * width.
Proof.
  intros width height y Hle.
  rewrite mul_sub_distr_r.
  - reflexivity.
  - exact Hle.
Qed.

(** ** 9.6 Specific Patterns for All Rows Processing *)

(** Key relationship for consecutive row indices *)
Lemma consecutive_row_difference : forall height y,
  S (S y) <= height ->
  height - S (S y) = height - S y - 1.
Proof.
  intros height y Hle.
  lia.
Qed.

(** Specific case for height' - S y' when S (S y') <= height' *)
Lemma height_double_succ_relation : forall height' y' width,
  S (S y') <= height' ->
  (height' - S (S y')) * width + width = (height' - S y') * width.
Proof.
  intros height' y' width Hle.
  rewrite consecutive_row_difference by exact Hle.
  rewrite mul_sub_distr_r.
  - rewrite Nat.mul_1_l.
    assert (height' - S y' >= 1).
    { lia. }
    assert ((height' - S y') * width >= width).
    { destruct (height' - S y') as [|n].
      - lia.
      - simpl. lia. }
    lia.
  - lia.
Qed.

(** ** 9.7 Operational Lemmas for All Rows Processing *)

(** When y = 0, the match expression gives S height' *)
Lemma process_all_rows_from_zero : forall height' width,
  match 0 with
  | 0 => S height'
  | S y' => height' - y'
  end * width = S height' * width.
Proof.
  intros height' width.
  reflexivity.
Qed.

(** When y = S y', the match expression gives height' - y' *)
Lemma process_all_rows_from_succ : forall height' y' width,
  match S y' with
  | 0 => S height'
  | S y'' => height' - y''
  end * width = (height' - y') * width.
Proof.
  intros height' y' width.
  reflexivity.
Qed.

(** Processing exactly one row *)
Lemma process_single_row_bound : forall img adj labels equiv y next_label,
  let '(_, _, next') := process_row img adj labels equiv y 0 (width img) next_label in
  next' <= next_label + width img.
Proof.
  intros img adj labels equiv y next_label.
  pose proof (process_row_increment_bound img adj labels equiv y 0 (width img) next_label) as H.
  assert (0 <= width img) by lia.
  specialize (H H0).
  rewrite process_from_zero in H.
  exact H.
Qed.

(** ** 9.8 Compound Properties for Iteration *)

(** Match expression directly to multiplication *)
Lemma match_to_mult : forall height y width,
  y <= height ->
  match y with
  | 0 => S height
  | S y' => height - y'
  end * width = (S height - y) * width.
Proof.
  intros height y width Hle.
  rewrite <- match_sub_form.
  reflexivity.
Qed.

(** Combining single row bound with remaining rows *)
Lemma split_rows_bound : forall width height y,
  y < height ->
  width + (height - S y) * width = (height - y) * width.
Proof.
  intros width height y Hlt.
  assert (height - y = S (height - S y)) by (apply height_iter_step; exact Hlt).
  rewrite H.
  rewrite succ_mul_expand.
  reflexivity.
Qed.

(** Transitivity of bounds through row processing *)
Lemma bound_transitivity : forall base row_increment remaining_increment total,
  row_increment + remaining_increment <= total ->
  base + row_increment + remaining_increment <= base + total.
Proof.
  intros.
  lia.
Qed.

(** Decomposing bounds for the IH case *)
Lemma decompose_row_bound : forall width height y next_label next' next'',
  y < height ->
  next' <= next_label + width ->
  next'' <= next' + (height - S y) * width ->
  next'' <= next_label + (height - y) * width.
Proof.
  intros width height y next_label next' next'' Hlt H1 H2.
  assert (width + (height - S y) * width = (height - y) * width).
  { apply split_rows_bound. exact Hlt. }
  rewrite <- H in *.
  lia.
Qed.

(** Edge case when processing the last row *)
Lemma last_row_bound : forall width,
  1 * width = width.
Proof.
  intros. 
  apply Nat.mul_1_l.
Qed.

(** Relationship between height' and S height' bounds *)
Lemma height_succ_bound_relation : forall width height' y,
  y <= height' ->
  (S height' - y) * width = width + (height' - y) * width.
Proof.
  intros width height' y Hle.
  rewrite height_sub_arithmetic.
  - rewrite succ_mul_expand. reflexivity.
  - lia.
Qed.

(** Zero multiplication simplification *)
Lemma zero_mult_bound : forall width next_label,
  next_label + 0 * width = next_label.
Proof.
  intros.
  rewrite Nat.mul_0_l.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

(** When y equals height, we get 0 remaining rows *)
Lemma no_rows_when_equal : forall height,
  height - height = 0.
Proof.
  intros.
  apply Nat.sub_diag.
Qed.

(** Bound preservation through empty processing *)
Lemma empty_processing_bound : forall next_label,
  next_label <= next_label + 0.
Proof.
  intros.
  lia.
Qed.

(** ** 9.9 Decomposing the Main Bound *)

(** Case 1: Empty height *)
Lemma process_all_rows_bound_empty : forall img adj labels equiv y next_label,
  let '(_, _, next') := process_all_rows img adj labels equiv y 0 next_label in
  next' = next_label.
Proof.
  intros. reflexivity.
Qed.

(** Case 2: Out of bounds *)
Lemma process_all_rows_bound_out : forall img adj labels equiv h next_label,
  let '(_, _, next') := process_all_rows img adj labels equiv (S h) (S h) next_label in
  next' = next_label.
Proof.
  intros. simpl.
  assert (S h <? S h = false) by (apply Nat.ltb_irrefl).
  rewrite H. reflexivity.
Qed.

(** Case 3: Single row (y = height) *)
Lemma process_all_rows_bound_single : forall img adj labels equiv h next_label,
  let '(_, _, next') := process_all_rows img adj labels equiv h (S h) next_label in
  next' <= next_label + width img.
Proof.
  intros. simpl.
  assert (h <? S h = true) by (apply Nat.ltb_lt; lia).
  rewrite H.
  destruct (process_row img adj labels equiv h 0 (width img) next_label) as [[labels' equiv'] next'] eqn:Hrow.
  assert (S h >= h) by lia.
  rewrite (process_all_rows_out_of_bounds img adj labels' equiv' (S h) h next' H0).
  pose proof (process_single_row_bound img adj labels equiv h next_label) as Hbound.
  rewrite Hrow in Hbound.
  exact Hbound.
Qed.

(** Main theorem using the cases *)
Lemma process_all_rows_increment_bound : forall img adj labels equiv y height next_label,
  y <= height ->
  let '(_, _, next') := process_all_rows img adj labels equiv y height next_label in
  next' <= next_label + (height - y) * width img.
Proof.
  intros img adj labels equiv y height.
  generalize dependent y.
  generalize dependent labels.
  generalize dependent equiv.
  induction height as [|height' IH]; intros.
  - (* height = 0 *)
    pose proof (process_all_rows_bound_empty img adj labels equiv y next_label) as H0.
    destruct (process_all_rows img adj labels equiv y 0 next_label) as [[? ?] next'].
    rewrite H0.
    assert (0 - y = 0) by lia.
    rewrite H1. simpl. lia.
  - (* height = S height' *)
    simpl.
    destruct (y <? S height') eqn:Hlt.
    + (* y < S height' *)
      apply Nat.ltb_lt in Hlt.
      destruct (process_row img adj labels equiv y 0 (width img) next_label) as [[labels' equiv'] next'] eqn:Hrow.
      destruct (Nat.le_gt_cases (S y) height') as [Hle|Hgt].
      * (* S y <= height' *)
        specialize (IH equiv' labels' (S y) next' Hle).
        destruct (process_all_rows img adj labels' equiv' (S y) height' next') as [[? ?] next''].
        pose proof (process_single_row_bound img adj labels equiv y next_label) as Hb1.
        rewrite Hrow in Hb1.
        (* Case split on y *)
        destruct y as [|y'].
        -- (* y = 0 *)
           simpl. (* This evaluates the match to S height' *)
           (* Goal: next'' <= next_label + (width img + height' * width img) *)
           (* IH: next'' <= next' + (height' - 1) * width img *)
           (* Hb1: next' <= next_label + width img *)
           assert (width img + (height' - 1) * width img = height' * width img).
           { destruct height' as [|h'].
             - (* height' = 0, contradicts Hle: 1 <= 0 *)
               lia.
             - (* height' = S h' *)
               simpl.
               assert (h' - 0 = h') by apply Nat.sub_0_r.
               rewrite H0.
               reflexivity. }
           rewrite <- H0.
           lia.
-- (* y = S y' *)
           simpl. (* This evaluates the match to height' - y' *)
           assert (height' - y' = S (height' - S y')).
           { apply height_iter_step. lia. }
           rewrite H0.
           rewrite Nat.mul_succ_l.
           (* Goal: next'' <= next_label + (width img + (height' - S y') * width img) *)
           (* IH: next'' <= next' + (height' - S (S y')) * width img *)
           (* Need to relate height' - S (S y') to height' - S y' *)
           assert (height' - S (S y') = height' - S y' - 1).
           { lia. }
           rewrite H1 in IH.
           (* Now IH: next'' <= next' + ((height' - S y' - 1) * width img) *)
           (* We need to show that adding width img gives us what we want *)
           assert (width img + (height' - S y' - 1) * width img = (height' - S y') * width img).
           { assert (height' - S y' > 0).
             { lia. }
             destruct (height' - S y') as [|n] eqn:E.
             - lia.
             - simpl. rewrite Nat.sub_0_r. reflexivity. }
           rewrite <- H2.
           rewrite <- Nat.add_assoc.
           lia.
* (* S y > height', so y = height' *)
        assert (Heq: y = height') by lia.
        subst y.
        assert (Hge: S height' >= height') by lia.
        rewrite (process_all_rows_out_of_bounds img adj labels' equiv' (S height') height' next' Hge).
        (* Need to evaluate the match expression *)
        assert (Hmatch: (match height' with | 0 => S height' | S l0 => height' - l0 end) = 1).
        { destruct height' as [|l0].
          - (* height' = 0 *)
            simpl. reflexivity.
          - (* height' = S l0 *)
            simpl.
            assert (S l0 - l0 = 1).
            { clear. induction l0 as [|l0' IH].
              - reflexivity.
              - simpl. exact IH. }
            exact H0. }
        rewrite Hmatch.
        rewrite Nat.mul_1_l.
        pose proof (process_single_row_bound img adj labels equiv height' next_label) as Hb.
        rewrite Hrow in Hb.
        exact Hb.
+ (* y >= S height' *)
      apply Nat.ltb_nlt in Hlt.
      assert (y = S height') by lia.
      subst y.
      assert (height' - height' = 0) by apply Nat.sub_diag.
      rewrite H0. simpl. lia.
Qed.

(** ** 9.10 Completing Section 8's First Pass Bound *)

(** first_pass generates at most width * height labels *)
Lemma first_pass_label_bound : forall img adj,
  let '(_, _, max_label) := first_pass img adj in
  max_label <= 1 + width img * height img.
Proof.
  intros img adj.
  unfold first_pass.
  pose proof (process_all_rows_increment_bound img adj empty_labeling empty_equiv 0 (height img) 1) as H.
  assert (0 <= height img) by lia.
  specialize (H H0).
  destruct (process_all_rows img adj empty_labeling empty_equiv 0 (height img) 1) as [[? ?] max_label].
  assert (height img - 0 = height img) by lia.
  rewrite H1 in H.
  rewrite Nat.mul_comm.
  exact H.
Qed.

(** ** 9.11 Convenient Forms of the Main Bound *)

(** Specialized for processing from the beginning *)
Theorem process_all_rows_from_start : forall img adj labels equiv next_label,
  let '(_, _, next') := process_all_rows img adj labels equiv 0 (height img) next_label in
  next' <= next_label + height img * width img.
Proof.
  intros img adj labels equiv next_label.
  pose proof (process_all_rows_increment_bound img adj labels equiv 0 (height img) next_label) as H.
  assert (0 <= height img) by lia.
  specialize (H H0).
  assert (height img - 0 = height img) by lia.
  rewrite H1 in H.
  exact H.
Qed.

(** Computational form for exact pixel count *)
Theorem first_pass_bound_pixels : forall img adj,
  let '(_, _, max_label) := first_pass img adj in
  max_label <= 1 + (height img * width img).
Proof.
  intros img adj.
  unfold first_pass.
  apply process_all_rows_from_start.
Qed.

(** Bound in terms of total pixels *)
Definition total_pixels (img : bounded_image) : nat :=
  height img * width img.

Theorem first_pass_bound_total_pixels : forall img adj,
  let '(_, _, max_label) := first_pass img adj in
  max_label <= 1 + total_pixels img.
Proof.
  intros img adj.
  unfold total_pixels.
  apply first_pass_bound_pixels.
Qed.

(** Incremental bound - processing k rows adds at most k * width labels *)
Theorem process_rows_incremental : forall img adj labels equiv y k next_label,
  y + k <= height img ->
  let '(_, _, next') := process_all_rows img adj labels equiv y (y + k) next_label in
  next' <= next_label + k * width img.
Proof.
  intros img adj labels equiv y k next_label Hbound.
  pose proof (process_all_rows_increment_bound img adj labels equiv y (y + k) next_label) as H.
  assert (y <= y + k) by lia.
  specialize (H H0).
  assert ((y + k) - y = k) by lia.
  rewrite H1 in H.
  exact H.
Qed.

(** Useful for step-by-step reasoning *)
Corollary single_pixel_adds_at_most_one : forall img adj labels equiv c next_label,
  let '(_, _, next') := process_pixel img adj labels equiv c next_label in
  next' - next_label <= 1.
Proof.
  intros.
  pose proof (process_pixel_increment_bound img adj labels equiv c next_label) as H.
  destruct (process_pixel img adj labels equiv c next_label) as [[? ?] next'].
  lia.
Qed.

(** Row processing adds at most width labels *)
Corollary single_row_adds_at_most_width : forall img adj labels equiv y next_label,
  let '(_, _, next') := process_row img adj labels equiv y 0 (width img) next_label in
  next' - next_label <= width img.
Proof.
  intros.
  pose proof (process_single_row_bound img adj labels equiv y next_label) as H.
  destruct (process_row img adj labels equiv y 0 (width img) next_label) as [[? ?] next'].
  lia.
Qed.

(** * Section 10: Finite Image Properties
    
    This section establishes the finiteness properties of bounded images.
    We prove that bounded images have finitely many foreground pixels,
    finitely many possible adjacencies, and that connectivity is decidable. *)

(** ** 10.1 Coordinate Enumeration *)

(** Generate all coordinates within bounds *)
Fixpoint coords_up_to (width height : nat) : list coord :=
  match height with
  | 0 => []
  | S h' => coords_up_to width h' ++ 
            map (fun x => (x, h')) (seq 0 width)
  end.

(** coords_up_to generates exactly width * height coordinates *)
Lemma coords_up_to_length : forall width height,
  length (coords_up_to width height) = width * height.
Proof.
  intros width height.
  induction height as [|h' IH].
  - simpl. rewrite Nat.mul_0_r. reflexivity.
  - simpl.
    rewrite length_app.
    rewrite IH.
    rewrite length_map.
    rewrite length_seq.
    rewrite Nat.mul_succ_r.
    rewrite Nat.add_comm.
    reflexivity.
Qed.

(** Every coordinate in bounds appears in coords_up_to *)
Lemma coords_up_to_complete : forall width height x y,
  x < width -> y < height ->
  In (x, y) (coords_up_to width height).
Proof.
  intros width height x y Hx Hy.
  induction height as [|h' IH].
  - (* height = 0, contradicts y < 0 *)
    lia.
  - (* height = S h' *)
    simpl.
    apply in_or_app.
    destruct (Nat.lt_decidable y h') as [Hlt | Hge].
    + (* y < h' *)
      left. apply IH. exact Hlt.
    + (* y >= h', so y = h' since y < S h' *)
      right.
      assert (y = h') by lia.
      subst y.
      apply in_map_iff.
      exists x.
      split.
      * reflexivity.
      * apply in_seq.
        split; [lia | exact Hx].
Qed.

(** Every coordinate in coords_up_to is within bounds *)
Lemma coords_up_to_sound : forall width height c,
  In c (coords_up_to width height) ->
  coord_x c < width /\ coord_y c < height.
Proof.
  intros width height c H.
  induction height as [|h' IH].
  - simpl in H. contradiction.
  - simpl in H.
    apply in_app_or in H.
    destruct H as [H | H].
    + (* c is in coords_up_to width h' *)
      specialize (IH H).
      split.
      * exact (proj1 IH).
      * apply Nat.lt_lt_succ_r. exact (proj2 IH).
    + (* c is in map (fun x => (x, h')) (seq 0 width) *)
      apply in_map_iff in H.
      destruct H as [x [Heq Hin]].
      subst c. simpl.
      apply in_seq in Hin.
      split.
      * exact (proj2 Hin).
      * lia.
Qed.

(** ** 10.2 Bounded Image Coordinates *)

(** All coordinates of a bounded image *)
Definition image_coords (img : bounded_image) : list coord :=
  coords_up_to (width img) (height img).

(** image_coords contains exactly the in-bounds coordinates *)
Lemma image_coords_iff_in_bounds : forall img c,
  In c (image_coords img) <-> 
  coord_x c < width img /\ coord_y c < height img.
Proof.
  intros img c.
  unfold image_coords.
  split.
  - apply coords_up_to_sound.
  - intros [Hx Hy].
    destruct c as [x y]. simpl in *.
    apply coords_up_to_complete; assumption.
Qed.

(** Number of coordinates in a bounded image *)
Lemma image_coords_length : forall img,
  length (image_coords img) = width img * height img.
Proof.
  intros img.
  unfold image_coords.
  apply coords_up_to_length.
Qed.

(** ** 10.3 Foreground Pixels *)

(** Extract all foreground pixels from an image *)
Definition foreground_pixels (img : bounded_image) : list coord :=
  filter (fun c => get_pixel img c) (image_coords img).

(** Foreground pixels are a subset of all coordinates *)
Lemma foreground_pixels_subset : forall img c,
  In c (foreground_pixels img) -> In c (image_coords img).
Proof.
  intros img c H.
  unfold foreground_pixels in H.
  apply filter_In in H.
  exact (proj1 H).
Qed.

(** Foreground pixels have true pixel values *)
Lemma foreground_pixels_true : forall img c,
  In c (foreground_pixels img) -> get_pixel img c = true.
Proof.
  intros img c H.
  unfold foreground_pixels in H.
  apply filter_In in H.
  exact (proj2 H).
Qed.

(** A coordinate is in foreground_pixels iff it's in bounds and foreground *)
Lemma foreground_pixels_iff : forall img c,
  In c (foreground_pixels img) <-> 
  (coord_x c < width img /\ coord_y c < height img /\ get_pixel img c = true).
Proof.
  intros img c.
  unfold foreground_pixels.
  split.
  - intros H.
    apply filter_In in H.
    destruct H as [Hin Hpix].
    apply image_coords_iff_in_bounds in Hin.
    split; [exact (proj1 Hin) | split; [exact (proj2 Hin) | exact Hpix]].
  - intros [Hx [Hy Hpix]].
    apply filter_In.
    split.
    + apply image_coords_iff_in_bounds. split; assumption.
    + exact Hpix.
Qed.

(** The number of foreground pixels is bounded by total pixels *)
Lemma foreground_pixels_finite : forall img,
  length (foreground_pixels img) <= width img * height img.
Proof.
  intros img.
  unfold foreground_pixels.
  rewrite <- image_coords_length.
  (* We need to show: length (filter _ _) <= length _ *)
  assert (forall {A} (f : A -> bool) (l : list A),
    length (filter f l) <= length l).
  { intros A f l.
    induction l as [|a l' IH].
    - simpl. lia.
    - simpl. destruct (f a).
      + simpl. lia.
      + lia. }
  apply H.
Qed.

(** ** 10.4 Adjacency Finiteness *)

(** Cartesian product of two lists *)
Fixpoint cartesian_product {A B : Type} (l1 : list A) (l2 : list B) : list (A * B) :=
  match l1 with
  | [] => []
  | a :: l1' => map (fun b => (a, b)) l2 ++ cartesian_product l1' l2
  end.

(** All possible adjacencies in an image *)
Definition all_adjacencies (img : bounded_image) (adj : coord -> coord -> bool) : list (coord * coord) :=
  filter (fun p : coord * coord => let (c1, c2) := p in adj c1 c2)
         (cartesian_product (image_coords img) (image_coords img)).

(** Helper: If a and b are in lists, then (a,b) is in their cartesian product *)
Lemma in_cartesian_product : forall {A B : Type} (a : A) (b : B) (l1 : list A) (l2 : list B),
  In a l1 -> In b l2 -> In (a, b) (cartesian_product l1 l2).
Proof.
  intros A B a b l1 l2 H1 H2.
  induction l1 as [|x l1' IH].
  - simpl in H1. contradiction.
  - simpl in H1. destruct H1 as [H1 | H1].
    + (* a = x *)
      subst x. simpl.
      apply in_or_app. left.
      apply in_map. exact H2.
    + (* a in l1' *)
      simpl.
      apply in_or_app. right.
      apply IH. exact H1.
Qed.

(** Adjacency list contains all adjacent pairs *)
Lemma all_adjacencies_complete : forall img adj c1 c2,
  coord_x c1 < width img -> coord_y c1 < height img ->
  coord_x c2 < width img -> coord_y c2 < height img ->
  adj c1 c2 = true ->
  In (c1, c2) (all_adjacencies img adj).
Proof.
  intros img adj c1 c2 Hx1 Hy1 Hx2 Hy2 Hadj.
  unfold all_adjacencies.
  apply filter_In.
  split.
  - (* Need to show (c1, c2) is in cartesian product *)
    apply in_cartesian_product.
    + apply image_coords_iff_in_bounds. split; assumption.
    + apply image_coords_iff_in_bounds. split; assumption.
  - (* adj c1 c2 = true *)
    exact Hadj.
Qed.

(** Helper: If (a,b) is in cartesian product, then a is in l1 and b is in l2 *)
Lemma cartesian_product_in : forall {A B : Type} (a : A) (b : B) (l1 : list A) (l2 : list B),
  In (a, b) (cartesian_product l1 l2) -> In a l1 /\ In b l2.
Proof.
  intros A B a b l1 l2 H.
  induction l1 as [|x l1' IH].
  - simpl in H. contradiction.
  - simpl in H.
    apply in_app_or in H.
    destruct H as [H | H].
    + (* (a,b) in map (fun b => (x, b)) l2 *)
      apply in_map_iff in H.
      destruct H as [b' [Heq Hin]].
      injection Heq as Ha Hb.
      subst x b'.
      split.
      * simpl. left. reflexivity.
      * exact Hin.
    + (* (a,b) in cartesian_product l1' l2 *)
      apply IH in H.
      destruct H as [Ha Hb].
      split.
      * simpl. right. exact Ha.
      * exact Hb.
Qed.

(** Only in-bounds coordinates can be adjacent *)
Lemma all_adjacencies_sound : forall img adj p,
  In p (all_adjacencies img adj) ->
  let (c1, c2) := p in
  coord_x c1 < width img /\ coord_y c1 < height img /\
  coord_x c2 < width img /\ coord_y c2 < height img /\
  adj c1 c2 = true.
Proof.
  intros img adj p H.
  unfold all_adjacencies in H.
  apply filter_In in H.
  destruct H as [Hin Hadj].
  destruct p as [c1 c2]. simpl in Hadj.
  apply cartesian_product_in in Hin.
  destruct Hin as [H1 H2].
  apply image_coords_iff_in_bounds in H1.
  apply image_coords_iff_in_bounds in H2.
  split; [exact (proj1 H1) | split; [exact (proj2 H1) |
  split; [exact (proj1 H2) | split; [exact (proj2 H2) | exact Hadj]]]].
Qed.

(** Helper: Length of cartesian product *)
Lemma cartesian_product_length : forall {A B : Type} (l1 : list A) (l2 : list B),
  length (cartesian_product l1 l2) = length l1 * length l2.
Proof.
  intros A B l1 l2.
  induction l1 as [|a l1' IH].
  - simpl. reflexivity.
  - simpl. rewrite length_app.
    rewrite length_map.
    rewrite IH.
    simpl. reflexivity.
Qed.

(** The number of adjacencies is finite *)
Lemma all_adjacencies_finite : forall img adj,
  length (all_adjacencies img adj) <= (width img * height img) * (width img * height img).
Proof.
  intros img adj.
  unfold all_adjacencies.
  assert (length (filter (fun p : coord * coord => let (c1, c2) := p in adj c1 c2)
                        (cartesian_product (image_coords img) (image_coords img))) <= 
          length (cartesian_product (image_coords img) (image_coords img))).
  { generalize (cartesian_product (image_coords img) (image_coords img)).
    intros l.
    induction l as [|p l' IH].
    - simpl. lia.
    - simpl. destruct (let (c1, c2) := p in adj c1 c2).
      + simpl. lia.
      + lia. }
  rewrite cartesian_product_length in H.
  rewrite !image_coords_length in H.
  exact H.
Qed.

(** ** 10.5 Decidability of Connectivity *)

(** Check if there's a path between two coordinates using BFS *)
Fixpoint reachable_from (img : bounded_image) (adj : coord -> coord -> bool) 
                        (visited : list coord) (frontier : list coord) 
                        (target : coord) (fuel : nat) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
      if existsb (coord_eqb target) frontier then true
      else
        let neighbors c := 
          filter (fun c' => andb (get_pixel img c') 
                                (andb (adj c c') 
                                      (negb (existsb (coord_eqb c') visited))))
                 (image_coords img) in
        let new_frontier := 
          flat_map neighbors frontier in
        let new_visited := visited ++ frontier in
        match new_frontier with
        | [] => false
        | _ => reachable_from img adj new_visited new_frontier target fuel'
        end
  end.

(** Decide connectivity between two pixels *)
Definition connected_dec (img : bounded_image) (adj : coord -> coord -> bool) 
                        (c1 c2 : coord) : bool :=
  andb (get_pixel img c1)
       (andb (get_pixel img c2)
             (reachable_from img adj [] [c1] c2 (width img * height img))).

(** connected_dec returns false for background pixels *)
Lemma connected_dec_background : forall img adj c1 c2,
  get_pixel img c1 = false \/ get_pixel img c2 = false ->
  connected_dec img adj c1 c2 = false.
Proof.
  intros img adj c1 c2 H.
  unfold connected_dec.
  destruct H as [H | H].
  - rewrite H. simpl. reflexivity.
  - rewrite H. rewrite andb_false_r. reflexivity.
Qed.

(** If reachable_from finds target, then there's a path *)
Lemma reachable_from_sound : forall img adj visited frontier target fuel,
  reachable_from img adj visited frontier target fuel = true ->
  existsb (coord_eqb target) frontier = true \/
  exists c, In c frontier /\ 
            exists c', get_pixel img c' = true /\ 
                      adj c c' = true /\ 
                      negb (existsb (coord_eqb c') visited) = true.
Proof.
  intros img adj visited frontier target fuel.
  revert visited frontier.
  induction fuel as [|fuel' IH]; intros visited frontier H.
  - simpl in H. discriminate.
  - simpl in H.
    destruct (existsb (coord_eqb target) frontier) eqn:Htarget.
    + left. reflexivity.
    + right.
      remember (flat_map 
                 (fun c => filter 
                   (fun c' => andb (get_pixel img c') 
                                  (andb (adj c c') 
                                        (negb (existsb (coord_eqb c') visited))))
                   (image_coords img)) 
                 frontier) as new_frontier.
      destruct new_frontier as [|c' rest].
      * (* new_frontier = [] *)
        simpl in H. discriminate.
      * (* new_frontier = c' :: rest *)
        (* Since new_frontier is non-empty, some c in frontier has a neighbor *)
        assert (In c' (flat_map 
                        (fun c => filter 
                          (fun c' => andb (get_pixel img c') 
                                         (andb (adj c c') 
                                               (negb (existsb (coord_eqb c') visited))))
                          (image_coords img)) 
                        frontier)).
        { rewrite <- Heqnew_frontier. simpl. left. reflexivity. }
        apply in_flat_map in H0.
        destruct H0 as [c [Hc_in Hc'_in]].
        exists c. split. exact Hc_in.
        apply filter_In in Hc'_in.
        destruct Hc'_in as [_ Hfilter].
        rewrite !andb_true_iff in Hfilter.
        destruct Hfilter as [Hpixel [Hadj Hnot_visited]].
        exists c'. split; [exact Hpixel | split; [exact Hadj | exact Hnot_visited]].
Qed.

(** If we can reach from c1 to c2 in one step, they are connected *)
Lemma reachable_one_step_connected : forall img adj c1 c2,
  get_pixel img c1 = true ->
  get_pixel img c2 = true ->
  adj c1 c2 = true ->
  connected (bounded_to_simple img) adj c1 c2.
Proof.
  intros img adj c1 c2 H1 H2 Hadj.
  unfold bounded_to_simple.
  apply adjacent_implies_connected; assumption.
Qed.

(** All nodes in frontier are reachable from the start *)
Lemma reachable_from_frontier_connected : forall img adj visited frontier target fuel c_start c,
  (forall a b, adj a b = adj b a) ->
  get_pixel img c_start = true ->
  (forall c', In c' frontier -> connected (bounded_to_simple img) adj c_start c') ->
  In c frontier ->
  reachable_from img adj visited frontier target fuel = true ->
  connected (bounded_to_simple img) adj c_start c.
Proof.
  intros img adj visited frontier target fuel c_start c adj_sym Hstart Hfront Hin Hreach.
  apply Hfront. exact Hin.
Qed.

(** If target is in frontier, we found it *)
Lemma reachable_from_found : forall img adj visited frontier target fuel,
  fuel > 0 ->
  existsb (coord_eqb target) frontier = true ->
  reachable_from img adj visited frontier target fuel = true.
Proof.
  intros img adj visited frontier target [|fuel'] Hfuel H.
  - simpl in Hfuel. lia.
  - simpl. rewrite H. reflexivity.
Qed.

(** Elements produced by flat_map filter are adjacent to elements in frontier *)
Lemma flat_map_filter_adjacent : forall img (adj : coord -> coord -> bool) visited frontier c',
  In c' (flat_map 
          (fun c => filter 
            (fun c' => andb (get_pixel img c') 
                           (andb (adj c c') 
                                 (negb (existsb (coord_eqb c') visited))))
            (image_coords img)) 
          frontier) ->
  exists c, In c frontier /\ adj c c' = true /\ get_pixel img c' = true.
Proof.
  intros img adj visited frontier c' H.
  apply in_flat_map in H.
  destruct H as [c [Hc_in Hc'_filter]].
  exists c. split. exact Hc_in.
  apply filter_In in Hc'_filter.
  destruct Hc'_filter as [_ Hprop].
  rewrite !andb_true_iff in Hprop.
  destruct Hprop as [Hpix [Hadj _]].
  split; assumption.
Qed.

(** If existsb returns true, there's an element satisfying the predicate *)
Lemma existsb_coord_eqb : forall target l,
  existsb (coord_eqb target) l = true ->
  In target l.
Proof.
  intros target l H.
  apply existsb_exists in H.
  destruct H as [c [Hin Heq]].
  apply coord_eqb_true_iff in Heq.
  subst c. exact Hin.
Qed.

(** One step of adjacency preserves connectivity *)
Lemma connected_step_preserves : forall img adj c_start c c',
  (forall a b, adj a b = adj b a) ->
  connected (bounded_to_simple img) adj c_start c ->
  get_pixel img c' = true ->
  adj c c' = true ->
  connected (bounded_to_simple img) adj c_start c'.
Proof.
  intros img adj c_start c c' adj_sym Hconn Hpix Hadj.
  unfold bounded_to_simple in *.
  apply connected_step with c; assumption.
Qed.

(** If all elements in a list are connected to start, and we extend by adjacency, 
    new elements are also connected *)
Lemma frontier_expansion_connected : forall img adj c_start frontier,
  (forall a b, adj a b = adj b a) ->
  (forall c, In c frontier -> connected (bounded_to_simple img) adj c_start c) ->
  forall c', In c' (flat_map 
                     (fun c => filter 
                       (fun c' => andb (get_pixel img c') 
                                      (andb (adj c c') 
                                            (negb (existsb (coord_eqb c') []))))
                       (image_coords img)) 
                     frontier) ->
  connected (bounded_to_simple img) adj c_start c'.
Proof.
  intros img adj c_start frontier adj_sym Hfront c' H.
  apply flat_map_filter_adjacent in H.
  destruct H as [c [Hc_in [Hadj Hpix]]].
  apply connected_step_preserves with c.
  - exact adj_sym.
  - apply Hfront. exact Hc_in.
  - exact Hpix.
  - exact Hadj.
Qed.

(** Key invariant: frontier contains only foreground pixels *)
Lemma reachable_from_frontier_foreground : forall img adj visited frontier target fuel,
  (forall c, In c frontier -> get_pixel img c = true) ->
  reachable_from img adj visited frontier target fuel = true ->
  get_pixel img target = true.
Proof.
  intros img adj visited frontier target fuel.
  revert visited frontier target.
  induction fuel as [|fuel' IH]; intros visited frontier target Hfront H.
  - simpl in H. discriminate.
  - simpl in H.
    destruct (existsb (coord_eqb target) frontier) eqn:Htarget.
    + (* target in frontier *)
      apply existsb_coord_eqb in Htarget.
      apply Hfront. exact Htarget.
    + (* recurse on expanded frontier *)
      match type of H with
      | context[match ?expanded with | [] => _ | _ => _ end] =>
        destruct expanded as [|c' rest] eqn:Hexpanded
      end.
      * simpl in H. discriminate.
      * apply IH with (visited ++ frontier) (c' :: rest).
        -- intros c Hin.
           rewrite <- Hexpanded in Hin.
           apply in_flat_map in Hin.
           destruct Hin as [c0 [_ Hfilter]].
           apply filter_In in Hfilter.
           destruct Hfilter as [_ Hprop].
           rewrite andb_true_iff in Hprop.
           exact (proj1 Hprop).
        -- exact H.
Qed.

(** More general frontier expansion that works with any visited list *)
Lemma frontier_expansion_connected_general : forall img adj c_start frontier visited,
  (forall a b, adj a b = adj b a) ->
  (forall c, In c frontier -> connected (bounded_to_simple img) adj c_start c) ->
  forall c', In c' (flat_map 
                     (fun c => filter 
                       (fun c' => andb (get_pixel img c') 
                                      (andb (adj c c') 
                                            (negb (existsb (coord_eqb c') visited))))
                       (image_coords img)) 
                     frontier) ->
  connected (bounded_to_simple img) adj c_start c'.
Proof.
  intros img adj c_start frontier visited adj_sym Hfront c' H.
  apply flat_map_filter_adjacent in H.
  destruct H as [c [Hc_in [Hadj Hpix]]].
  apply connected_step_preserves with c.
  - exact adj_sym.
  - apply Hfront. exact Hc_in.
  - exact Hpix.
  - exact Hadj.
Qed.

(** Core invariant: all elements in frontier are connected to start *)
Lemma reachable_from_invariant : forall img adj visited frontier target fuel c_start,
  (forall a b, adj a b = adj b a) ->
  get_pixel img c_start = true ->
  (forall c, In c frontier -> connected (bounded_to_simple img) adj c_start c) ->
  reachable_from img adj visited frontier target fuel = true ->
  connected (bounded_to_simple img) adj c_start target.
Proof.
  intros img adj visited frontier target fuel.
  revert visited frontier target.
  induction fuel as [|fuel' IH]; intros visited frontier target c_start adj_sym Hstart Hinv H.
  - simpl in H. discriminate.
  - simpl in H.
    destruct (existsb (coord_eqb target) frontier) eqn:Htarget.
    + (* target in frontier - use invariant *)
      apply existsb_coord_eqb in Htarget.
      apply Hinv. exact Htarget.
    + (* recurse with expanded frontier *)
      match type of H with
      | context[match ?expanded with | [] => _ | _ => _ end] =>
        destruct expanded as [|c' rest] eqn:Hexpanded
      end.
      * simpl in H. discriminate.
      * (* Apply IH with new invariant *)
        eapply IH.
        -- exact adj_sym.
        -- exact Hstart.
        -- (* Prove new invariant *)
           intros c Hin.
           assert (In c (flat_map 
                         (fun c => filter 
                           (fun c' => andb (get_pixel img c') 
                                          (andb (adj c c') 
                                                (negb (existsb (coord_eqb c') visited))))
                           (image_coords img)) 
                         frontier)).
           { rewrite Hexpanded. exact Hin. }
           apply frontier_expansion_connected_general with frontier visited.
           ++ exact adj_sym.
           ++ exact Hinv.
           ++ exact H0.
        -- exact H.
Qed.

(** If c_start is foreground and reachable_from succeeds, target is connected to c_start *)
Lemma reachable_from_implies_connected : forall img adj c_start target fuel,
  (forall a b, adj a b = adj b a) ->
  get_pixel img c_start = true ->
  reachable_from img adj [] [c_start] target fuel = true ->
  connected (bounded_to_simple img) adj c_start target.
Proof.
  intros img adj c_start target fuel adj_sym Hstart H.
  apply reachable_from_invariant with [] [c_start] fuel.
  - exact adj_sym.
  - exact Hstart.
  - intros c Hin.
    simpl in Hin. destruct Hin.
    + subst c. apply connected_refl. unfold bounded_to_simple. exact Hstart.
    + contradiction.
  - exact H.
Qed.

(** connected_dec correctly decides connectivity - soundness direction *)
Theorem connected_dec_sound : forall img adj c1 c2,
  (forall a b, adj a b = adj b a) ->
  connected_dec img adj c1 c2 = true ->
  connected (bounded_to_simple img) adj c1 c2.
Proof.
  intros img adj c1 c2 adj_sym H.
  unfold connected_dec in H.
  rewrite !andb_true_iff in H.
  destruct H as [Hc1 [Hc2 Hreach]].
  apply reachable_from_implies_connected with (width img * height img).
  - exact adj_sym.
  - exact Hc1.
  - exact Hreach.
Qed.

(** * Section 11: BFS Correctness and Completeness
    
    This section proves that our BFS-based reachability algorithm correctly
    decides connectivity. We establish that BFS systematically explores all
    reachable nodes within bounded steps. *)

(** ** 11.1 BFS State and Invariants *)

(** BFS maintains visited nodes and a frontier *)
Record bfs_state : Type := mkBFSState {
  visited : list coord;
  frontier : list coord
}.

(** A node is explored if it's in visited or frontier *)
Definition explored (s : bfs_state) (c : coord) : bool :=
  orb (existsb (coord_eqb c) (visited s))
      (existsb (coord_eqb c) (frontier s)).

(** BFS invariant: all frontier nodes are connected to start *)
Definition bfs_invariant (img : bounded_image) (adj : coord -> coord -> bool) 
                        (start : coord) (s : bfs_state) : Prop :=
  (forall c, In c (frontier s) -> 
    get_pixel img c = true /\ 
    connected (bounded_to_simple img) adj start c) /\
  (forall c, In c (visited s) -> 
    get_pixel img c = true /\ 
    connected (bounded_to_simple img) adj start c).

(** Initial state satisfies invariant *)
Lemma bfs_initial_invariant : forall img adj start,
  get_pixel img start = true ->
  bfs_invariant img adj start (mkBFSState [] [start]).
Proof.
  intros img adj start Hstart.
  unfold bfs_invariant. simpl.
  split.
  - intros c H. destruct H as [H | H].
    + subst c. split.
      * exact Hstart.
      * apply connected_refl. unfold bounded_to_simple. exact Hstart.
    + contradiction.
  - intros c H. contradiction.
Qed.

(** ** 11.2 BFS Expansion Properties *)

(** Neighbors of a node that haven't been explored *)
Definition unexplored_neighbors (img : bounded_image) (adj : coord -> coord -> bool)
                               (s : bfs_state) (c : coord) : list coord :=
  filter (fun c' => andb (get_pixel img c')
                        (andb (adj c c')
                              (negb (explored s c'))))
         (image_coords img).

(** One step of BFS expansion *)
Definition bfs_step (img : bounded_image) (adj : coord -> coord -> bool)
                   (s : bfs_state) : bfs_state :=
  match frontier s with
  | [] => s  (* No more nodes to explore *)
  | _ => mkBFSState 
           (visited s ++ frontier s)
           (flat_map (unexplored_neighbors img adj s) (frontier s))
  end.

(** Helper: unexplored_neighbors produces foreground pixels *)
Lemma unexplored_neighbors_foreground : forall img adj s c c',
  In c' (unexplored_neighbors img adj s c) ->
  get_pixel img c' = true.
Proof.
  intros img adj s c c' H.
  unfold unexplored_neighbors in H.
  apply filter_In in H.
  destruct H as [_ Hprop].
  rewrite !andb_true_iff in Hprop.
  destruct Hprop as [Hpix _].
  exact Hpix.
Qed.

(** Helper: unexplored_neighbors are adjacent to source *)
Lemma unexplored_neighbors_adjacent : forall img adj s c c',
  In c' (unexplored_neighbors img adj s c) ->
  adj c c' = true.
Proof.
  intros img adj s c c' H.
  unfold unexplored_neighbors in H.
  apply filter_In in H.
  destruct H as [_ Hprop].
  rewrite !andb_true_iff in Hprop.
  destruct Hprop as [_ [Hadj _]].
  exact Hadj.
Qed.

(** Helper: new frontier nodes are connected via frontier nodes *)
Lemma new_frontier_connected : forall img adj start s c',
  (forall a b, adj a b = adj b a) ->
  bfs_invariant img adj start s ->
  In c' (flat_map (unexplored_neighbors img adj s) (frontier s)) ->
  connected (bounded_to_simple img) adj start c'.
Proof.
  intros img adj start s c' adj_sym Hinv H.
  apply in_flat_map in H.
  destruct H as [c [Hc_front Hc'_unexplored]].
  destruct Hinv as [Hfront_inv _].
  assert (Hc_prop := Hfront_inv c Hc_front).
  destruct Hc_prop as [_ Hc_conn].
  assert (Hc'_pix := unexplored_neighbors_foreground img adj s c c' Hc'_unexplored).
  assert (Hc'_adj := unexplored_neighbors_adjacent img adj s c c' Hc'_unexplored).
  unfold bounded_to_simple.
  apply connected_step with c.
  - exact Hc_conn.
  - exact Hc'_pix.
  - exact Hc'_adj.
Qed.

(** Helper: extended visited maintains invariant *)
Lemma extended_visited_invariant : forall img adj start s c,
  bfs_invariant img adj start s ->
  In c (visited s ++ frontier s) ->
  get_pixel img c = true /\ connected (bounded_to_simple img) adj start c.
Proof.
  intros img adj start s c Hinv H.
  destruct Hinv as [Hfront_inv Hvisit_inv].
  apply in_app_or in H.
  destruct H as [H | H].
  - apply Hvisit_inv. exact H.
  - apply Hfront_inv. exact H.
Qed.

(** BFS step preserves the invariant *)
Lemma bfs_step_preserves_invariant : forall img adj start s,
  (forall a b, adj a b = adj b a) ->
  bfs_invariant img adj start s ->
  bfs_invariant img adj start (bfs_step img adj s).
Proof.
  intros img adj start s adj_sym Hinv.
  unfold bfs_step.
  destruct (frontier s) as [|c cs] eqn:Hfront.
  - (* Empty frontier - no change *)
    exact Hinv.
  - (* Non-empty frontier *)
    unfold bfs_invariant. simpl. split.
    + (* New frontier maintains invariant *)
      intros c' H.
      split.
      * (* c' is foreground *)
        simpl in H.
        apply in_app_or in H.
        destruct H as [H | H].
        -- apply unexplored_neighbors_foreground with adj s c.
           exact H.
        -- apply in_flat_map in H.
           destruct H as [c0 [_ Hc'_in]].
           apply unexplored_neighbors_foreground with adj s c0.
           exact Hc'_in.
      * (* c' is connected to start *)
        apply new_frontier_connected with s.
        -- exact adj_sym.
        -- exact Hinv.
        -- simpl in H.
           assert (frontier s = c :: cs) by exact Hfront.
           rewrite H0.
           simpl.
           exact H.
    + (* Extended visited maintains invariant *)
      intros c0 H.
      apply extended_visited_invariant with s.
      * exact Hinv.
      * assert (frontier s = c :: cs) by exact Hfront.
        rewrite H0.
        exact H.
Qed.

(** ** 11.3 BFS Progress Properties *)

(** If a node is unexplored, it's not in visited or frontier *)
Lemma unexplored_not_in_state : forall s c,
  explored s c = false ->
  ~ In c (visited s) /\ ~ In c (frontier s).
Proof.
  intros s c H.
  unfold explored in H.
  rewrite orb_false_iff in H.
  destruct H as [Hvisit Hfront].
  split.
  - intro Hin.
    assert (existsb (coord_eqb c) (visited s) = true).
    { apply existsb_exists. exists c. split.
      - exact Hin.
      - apply coord_eqb_refl. }
    rewrite H in Hvisit. discriminate.
  - intro Hin.
    assert (existsb (coord_eqb c) (frontier s) = true).
    { apply existsb_exists. exists c. split.
      - exact Hin.
      - apply coord_eqb_refl. }
    rewrite H in Hfront. discriminate.
Qed. 

(** New frontier nodes were unexplored *)
Lemma new_frontier_unexplored : forall img adj s c,
  In c (flat_map (unexplored_neighbors img adj s) (frontier s)) ->
  explored s c = false.
Proof.
  intros img adj s c H.
  apply in_flat_map in H.
  destruct H as [c' [_ Hc_unexplored]].
  unfold unexplored_neighbors in Hc_unexplored.
  apply filter_In in Hc_unexplored.
  destruct Hc_unexplored as [_ Hprop].
  rewrite !andb_true_iff in Hprop.
  destruct Hprop as [_ [_ Hnot_explored]].
  apply negb_true_iff in Hnot_explored.
  exact Hnot_explored.
Qed.

(** Helper: Length of visited after BFS step *)
Lemma bfs_step_visited_length : forall img adj s,
  frontier s <> [] ->
  length (visited (bfs_step img adj s)) = length (visited s) + length (frontier s).
Proof.
  intros img adj s Hnonempty.
  unfold bfs_step.
  destruct (frontier s) as [|c cs] eqn:Hfront.
  - contradiction.
  - simpl.
    apply length_app.
Qed.

(** Helper: Total nodes in BFS state *)
Lemma bfs_total_nodes : forall img adj s,
  frontier s <> [] ->
  length (frontier (bfs_step img adj s)) + length (visited (bfs_step img adj s)) =
  length (frontier (bfs_step img adj s)) + length (visited s) + length (frontier s).
Proof.
  intros img adj s Hnonempty.
  rewrite bfs_step_visited_length.
  - rewrite Nat.add_assoc. reflexivity.
  - exact Hnonempty.
Qed.

(** BFS explores all nodes or frontier becomes empty *)
Lemma bfs_step_decreases_unexplored : forall img adj s,
  frontier s <> [] ->
  length (frontier (bfs_step img adj s)) + length (visited (bfs_step img adj s)) >=
  length (frontier s) + length (visited s).
Proof.
  intros img adj s Hnonempty.
  rewrite bfs_total_nodes by exact Hnonempty.
  (* Now: length (frontier (bfs_step img adj s)) + length (visited s) + length (frontier s) >=
          length (frontier s) + length (visited s) *)
  rewrite Nat.add_comm with (n := length (frontier s)).
  (* Now: length (frontier s) + length (visited s) + length (frontier (bfs_step img adj s)) >=
          length (frontier s) + length (visited s) *)
  rewrite <- Nat.add_assoc.
  (* Now: length (frontier (bfs_step img adj s)) + (length (visited s) + length (frontier s)) >=
          length (visited s) + length (frontier s) *)
  (* This holds because we're adding a non-negative number to the RHS *)
  assert (0 <= length (frontier (bfs_step img adj s))) by apply Nat.le_0_l.
  lia.
Qed.

(** ** 11.4 BFS Termination *)

(** Helper: unexplored_neighbors produces in-bounds coordinates *)
Lemma unexplored_neighbors_in_bounds : forall img adj s c c',
  In c' (unexplored_neighbors img adj s c) ->
  In c' (image_coords img).
Proof.
  intros img adj s c c' H.
  unfold unexplored_neighbors in H.
  apply filter_In in H.
  destruct H as [Hin _].
  exact Hin.
Qed.

(** New frontier nodes are in bounds *)
Lemma bfs_step_frontier_in_bounds : forall img adj s c,
  In c (frontier (bfs_step img adj s)) ->
  In c (image_coords img).
Proof.
  intros img adj s c H.
  unfold bfs_step in H.
  destruct (frontier s) as [|c0 cs] eqn:Hfront.
  - (* frontier s = [] *)
    rewrite Hfront in H.
    simpl in H.
    (* H : In c [] *)
    inversion H.
  - simpl in H.
    apply in_app_or in H.
    destruct H as [H | H].
    + (* In c (unexplored_neighbors img adj s c0) *)
      apply unexplored_neighbors_in_bounds with adj s c0.
      exact H.
    + (* In c (flat_map (unexplored_neighbors img adj s) cs) *)
      apply in_flat_map in H.
      destruct H as [c' [_ Hc_unexplored]].
      apply unexplored_neighbors_in_bounds with adj s c'.
      exact Hc_unexplored.
Qed.

(** Helper: If BFS invariant holds, frontier contains in-bounds coordinates *)
Lemma bfs_invariant_frontier_in_bounds : forall img adj start s c,
  bfs_invariant img adj start s ->
  In c (frontier s) ->
  In c (image_coords img).
Proof.
  intros img adj start s c Hinv Hin.
  destruct Hinv as [Hfront_inv _].
  assert (Hc := Hfront_inv c Hin).
  destruct Hc as [Hpix _].
  apply image_coords_iff_in_bounds.
  unfold get_pixel in Hpix.
  destruct (in_bounds img c) eqn:Hbound.
  - unfold in_bounds in Hbound.
    rewrite !andb_true_iff in Hbound.
    destruct Hbound as [Hx Hy].
    apply Nat.ltb_lt in Hx, Hy.
    split; assumption.
  - discriminate.
Qed.

(** Helper: If BFS invariant holds, visited contains in-bounds coordinates *)
Lemma bfs_invariant_visited_in_bounds : forall img adj start s c,
  bfs_invariant img adj start s ->
  In c (visited s) ->
  In c (image_coords img).
Proof.
  intros img adj start s c Hinv Hin.
  destruct Hinv as [_ Hvisit_inv].
  assert (Hc := Hvisit_inv c Hin).
  destruct Hc as [Hpix _].
  apply image_coords_iff_in_bounds.
  unfold get_pixel in Hpix.
  destruct (in_bounds img c) eqn:Hbound.
  - unfold in_bounds in Hbound.
    rewrite !andb_true_iff in Hbound.
    destruct Hbound as [Hx Hy].
    apply Nat.ltb_lt in Hx, Hy.
    split; assumption.
  - discriminate.
Qed.

(** Helper: In initial BFS state, visited and frontier are disjoint *)
Lemma bfs_initial_disjoint : forall start,
  forall c, ~ (In c ([] : list coord) /\ In c [start]).
Proof.
  intros start c [Hvisit _].
  exact Hvisit.
Qed.

(** Helper: unexplored_neighbors excludes explored nodes *)
Lemma unexplored_neighbors_not_explored : forall img adj s c c',
  In c' (unexplored_neighbors img adj s c) ->
  explored s c' = false.
Proof.
  intros img adj s c c' H.
  unfold unexplored_neighbors in H.
  apply filter_In in H.
  destruct H as [_ Hprop].
  rewrite !andb_true_iff in Hprop.
  destruct Hprop as [_ [_ Hnot_explored]].
  apply negb_true_iff in Hnot_explored.
  exact Hnot_explored.
Qed.

(** Helper: BFS state maintains disjoint visited and frontier *)
Definition bfs_disjoint (s : bfs_state) : Prop :=
  forall c, ~ (In c (visited s) /\ In c (frontier s)).

(** Initial BFS state has disjoint visited and frontier *)
Lemma bfs_initial_state_disjoint : forall start,
  bfs_disjoint (mkBFSState [] [start]).
Proof.
  intros start.
  unfold bfs_disjoint. simpl.
  intros c [Hvisit _].
  exact Hvisit.
Qed.

(** BFS step preserves disjoint property *)
Lemma bfs_step_preserves_disjoint : forall img adj s,
  bfs_disjoint s ->
  bfs_disjoint (bfs_step img adj s).
Proof.
  intros img adj s Hdisj.
  unfold bfs_step.
  destruct (frontier s) as [|c cs] eqn:Hfront.
  - (* Empty frontier - no change *)
    exact Hdisj.
  - (* Non-empty frontier *)
    unfold bfs_disjoint. simpl.
    intros c' [Hvisit' Hfront'].
    (* c' in new visited = visited s ++ (c :: cs) *)
    apply in_app_or in Hvisit'.
    destruct Hvisit' as [Hvisit' | Hvisit'].
    + (* c' in old visited *)
      (* c' in new frontier = unexplored_neighbors ... ++ flat_map ... *)
      apply in_app_or in Hfront'.
      destruct Hfront' as [Hfront' | Hfront'].
      * (* c' in unexplored_neighbors img adj s c *)
        assert (explored s c' = false).
        { apply unexplored_neighbors_not_explored with img adj c.
          exact Hfront'. }
        unfold explored in H.
        rewrite orb_false_iff in H.
        destruct H as [Hvisit_false _].
        assert (existsb (coord_eqb c') (visited s) = true).
        { apply existsb_exists. exists c'. split.
          - exact Hvisit'.
          - apply coord_eqb_refl. }
        rewrite H in Hvisit_false. discriminate.
      * (* c' in flat_map (unexplored_neighbors img adj s) cs *)
        apply in_flat_map in Hfront'.
        destruct Hfront' as [c0 [_ Hc'_unexplored]].
        assert (explored s c' = false).
        { apply unexplored_neighbors_not_explored with img adj c0.
          exact Hc'_unexplored. }
        unfold explored in H.
        rewrite orb_false_iff in H.
        destruct H as [Hvisit_false _].
        assert (existsb (coord_eqb c') (visited s) = true).
        { apply existsb_exists. exists c'. split.
          - exact Hvisit'.
          - apply coord_eqb_refl. }
        rewrite H in Hvisit_false. discriminate.
    + (* c' in old frontier = c :: cs *)
      rewrite <- Hfront in Hvisit'.
      (* c' in new frontier *)
      apply in_app_or in Hfront'.
      destruct Hfront' as [Hfront' | Hfront'].
      * (* c' in unexplored_neighbors img adj s c *)
        assert (explored s c' = false).
        { apply unexplored_neighbors_not_explored with img adj c.
          exact Hfront'. }
        unfold explored in H.
        rewrite orb_false_iff in H.
        destruct H as [_ Hfront_false].
        assert (existsb (coord_eqb c') (frontier s) = true).
        { apply existsb_exists. exists c'. split.
          - exact Hvisit'.
          - apply coord_eqb_refl. }
        rewrite H in Hfront_false. discriminate.
      * (* c' in flat_map (unexplored_neighbors img adj s) cs *)
        apply in_flat_map in Hfront'.
        destruct Hfront' as [c0 [_ Hc'_unexplored]].
        assert (explored s c' = false).
        { apply unexplored_neighbors_not_explored with img adj c0.
          exact Hc'_unexplored. }
        unfold explored in H.
        rewrite orb_false_iff in H.
        destruct H as [_ Hfront_false].
        assert (existsb (coord_eqb c') (frontier s) = true).
        { apply existsb_exists. exists c'. split.
          - exact Hvisit'.
          - apply coord_eqb_refl. }
        rewrite H in Hfront_false. discriminate.
Qed.

(** Helper: All nodes in BFS state are in bounds *)
Lemma bfs_state_all_in_bounds : forall img adj start s,
  (forall a b, adj a b = adj b a) ->
  bfs_invariant img adj start s ->
  (forall c, In c (visited s) -> In c (image_coords img)) /\
  (forall c, In c (frontier s) -> In c (image_coords img)).
Proof.
  intros img adj start s adj_sym Hinv.
  split.
  - intros c Hin.
    apply (bfs_invariant_visited_in_bounds img adj start s c Hinv Hin).
  - intros c Hin.
    apply (bfs_invariant_frontier_in_bounds img adj start s c Hinv Hin).
Qed.

(** Helper: A list of in-bounds coordinates has bounded length *)
Lemma in_bounds_list_length : forall img l,
  (forall c, In c l -> In c (image_coords img)) ->
  NoDup l ->
  length l <= width img * height img.
Proof.
  intros img l Hall_in HNoDup.
  assert (Hsubset: incl l (image_coords img)).
  { unfold incl. exact Hall_in. }
  assert (length l <= length (image_coords img)).
  { apply NoDup_incl_length.
    - exact HNoDup.
    - exact Hsubset. }
  rewrite image_coords_length in H.
  exact H.
Qed.

(** Helper: Initial BFS state has NoDup frontier *)
Lemma bfs_initial_nodup_frontier : forall start,
  NoDup ([start] : list coord).
Proof.
  intros start.
  apply NoDup_cons.
  - intro H. exact H.
  - apply NoDup_nil.
Qed.

(** Helper: Initial BFS state has NoDup visited *)
Lemma bfs_initial_nodup_visited :
  NoDup ([] : list coord).
Proof.
  apply NoDup_nil.
Qed.

(** Helper: BFS state maintains NoDup property *)
Definition bfs_nodup (s : bfs_state) : Prop :=
  NoDup (visited s) /\ NoDup (frontier s).

(** Initial BFS state has NoDup *)
Lemma bfs_initial_nodup : forall start,
  bfs_nodup (mkBFSState [] [start]).
Proof.
  intros start.
  unfold bfs_nodup. simpl.
  split.
  - apply bfs_initial_nodup_visited.
  - apply bfs_initial_nodup_frontier.
Qed.

(** Helper: NoDup preserved when appending disjoint lists *)
Lemma NoDup_app_disjoint : forall {A : Type} (l1 l2 : list A),
  NoDup l1 ->
  NoDup l2 ->
  (forall x, In x l1 -> ~ In x l2) ->
  NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 H1 H2 Hdisj.
  induction l1 as [|a l1' IH].
  - simpl. exact H2.
  - simpl. apply NoDup_cons.
    + intro H.
      apply in_app_or in H.
      destruct H as [H | H].
      * inversion H1. subst. contradiction.
      * apply (Hdisj a).
        -- simpl. left. reflexivity.
        -- exact H.
    + apply IH.
      * inversion H1. exact H4.
      * intros x Hin.
        apply Hdisj.
        simpl. right. exact Hin.
Qed.

(** Helper: seq produces distinct elements *)
Lemma seq_NoDup : forall start len,
  NoDup (seq start len).
Proof.
  intros start len.
  generalize dependent start.
  induction len as [|len' IH]; intros start.
  - simpl. apply NoDup_nil.
  - simpl. apply NoDup_cons.
    + intro H. apply in_seq in H.
      destruct H as [Hle Hlt].
      lia.
    + apply IH.
Qed.

(** Helper: map with injective function preserves NoDup *)
Lemma map_NoDup_inj : forall {A B : Type} (f : A -> B) (l : list A),
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup l ->
  NoDup (map f l).
Proof.
  intros A B f l Hinj HNoDup.
  induction HNoDup as [|a l' Hnot_in HNoDup' IH].
  - simpl. apply NoDup_nil.
  - simpl. apply NoDup_cons.
    + intro H. apply in_map_iff in H.
      destruct H as [x [Heq Hin]].
      (* f a = f x and x ∈ l', so by injectivity a = x *)
      assert (a = x).
      { apply Hinj.
        - left. reflexivity.
        - right. exact Hin.
        - symmetry. exact Heq. }
      subst x.
      contradiction.
    + apply IH.
      intros x y Hx Hy.
      apply Hinj.
      * right. exact Hx.
      * right. exact Hy.
Qed.

(** Helper: Pairing with fixed second component is injective *)
Lemma pair_fixed_second_inj : forall {A B : Type} (b : B) (l : list A),
  forall x y, In x l -> In y l -> (x, b) = (y, b) -> x = y.
Proof.
  intros A B b l x y _ _ H.
  assert (x = fst (x, b)) by reflexivity.
  assert (y = fst (y, b)) by reflexivity.
  rewrite H0, H1.
  rewrite H.
  reflexivity.
Qed.

(** Helper: coords_up_to produces NoDup list *)
Lemma coords_up_to_NoDup : forall width height,
  NoDup (coords_up_to width height).
Proof.
  intros width height.
  induction height as [|h' IH].
  - simpl. apply NoDup_nil.
  - simpl. apply NoDup_app_disjoint.
    + exact IH.
    + (* NoDup (map (fun x => (x, h')) (seq 0 width)) *)
      apply map_NoDup_inj.
      * apply pair_fixed_second_inj.
      * apply seq_NoDup.
    + (* Disjointness: different y-coordinates *)
      intros c Hin1 Hin2.
      destruct c as [x y].
      apply coords_up_to_sound in Hin1.
      apply in_map_iff in Hin2.
      destruct Hin2 as [x' [Heq Hin_seq]].
      (* Heq : (x', h') = (x, y) *)
      inversion Heq. subst x' y.
      destruct Hin1 as [_ Hy_bound].
      (* h' < h', contradiction *)
      apply (Nat.lt_irrefl h' Hy_bound).
Qed.

(** image_coords produces NoDup list *)
Lemma image_coords_NoDup : forall img,
  NoDup (image_coords img).
Proof.
  intros img.
  unfold image_coords.
  apply coords_up_to_NoDup.
Qed.

(** Helper: filter preserves NoDup *)
Lemma filter_NoDup : forall {A : Type} (f : A -> bool) (l : list A),
  NoDup l -> NoDup (filter f l).
Proof.
  intros A f l HNoDup.
  induction HNoDup as [|a l' Hnot_in HNoDup' IH].
  - simpl. apply NoDup_nil.
  - simpl. destruct (f a) eqn:Hfa.
    + apply NoDup_cons.
      * intro H. apply filter_In in H.
        destruct H as [Hin _].
        contradiction.
      * exact IH.
    + exact IH.
Qed.

(** unexplored_neighbors produces NoDup list *)
Lemma unexplored_neighbors_NoDup : forall img adj s c,
  NoDup (unexplored_neighbors img adj s c).
Proof.
  intros img adj s c.
  unfold unexplored_neighbors.
  apply filter_NoDup.
  apply image_coords_NoDup.
Qed.

(** Helper: flat_map preserves NoDup when results are disjoint *)
Lemma flat_map_NoDup_disjoint : forall {A B : Type} (f : A -> list B) (l : list A),
  NoDup l ->
  (forall x, In x l -> NoDup (f x)) ->
  (forall x y, In x l -> In y l -> x <> y -> 
    (forall b, In b (f x) -> ~ In b (f y))) ->
  NoDup (flat_map f l).
Proof.
  intros A B f l HNoDup Hf_NoDup Hdisjoint.
  induction HNoDup as [|a l' Hnot_in HNoDup' IH].
  - simpl. apply NoDup_nil.
  - simpl. apply NoDup_app_disjoint.
    + apply Hf_NoDup. left. reflexivity.
    + apply IH.
      * intros x Hin. apply Hf_NoDup. right. exact Hin.
      * intros x y Hinx Hiny Hneq.
        apply Hdisjoint.
        -- right. exact Hinx.
        -- right. exact Hiny.
        -- exact Hneq.
    + intros b Hb_in_fa Hb_in_flat.
      apply in_flat_map in Hb_in_flat.
      destruct Hb_in_flat as [x [Hx_in Hb_in_fx]].
      assert (Hneq: a <> x).
      { intro Heq. subst x. contradiction. }
      assert (H := Hdisjoint a x).
      specialize (H (or_introl eq_refl)).
      specialize (H (or_intror Hx_in)).
      specialize (H Hneq).
      specialize (H b).
      specialize (H Hb_in_fa).
      contradiction.
Qed.

Fixpoint remove_dups {A : Type} (eqb : A -> A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | a :: l' => 
      if existsb (eqb a) l' then remove_dups eqb l'
      else a :: remove_dups eqb l'
  end.

Lemma remove_dups_subset : forall {A : Type} (eqb : A -> A -> bool) (l : list A) x,
  In x (remove_dups eqb l) -> In x l.
Proof.
  intros A eqb l.
  induction l as [|a l' IH]; intros x H.
  - simpl in H. contradiction.
  - simpl in H. destruct (existsb (eqb a) l') eqn:E.
    + right. apply IH. exact H.
    + destruct H as [H | H].
      * left. exact H.
      * right. apply IH. exact H.
Qed.

Lemma remove_dups_NoDup : forall {A : Type} (eqb : A -> A -> bool) (l : list A),
  (forall x y, eqb x y = true <-> x = y) ->
  NoDup (remove_dups eqb l).
Proof.
  intros A eqb l Heqb_iff.
  induction l as [|a l' IH].
  - simpl. apply NoDup_nil.
  - simpl. destruct (existsb (eqb a) l') eqn:Hexists.
    + exact IH.
    + apply NoDup_cons.
      * intro H.
        assert (In a l').
        { apply remove_dups_subset in H. exact H. }
        assert (existsb (eqb a) l' = true).
        { apply existsb_exists. exists a. split.
          - exact H0.
          - apply Heqb_iff. reflexivity. }
        rewrite H1 in Hexists. discriminate.
      * exact IH.
Qed.

(** For BFS termination, we don't need NoDup - we just need progress *)
Lemma bfs_makes_progress : forall img adj s,
  frontier s <> [] ->
  length (visited (bfs_step img adj s)) > length (visited s).
Proof.
  intros img adj s Hnonempty.
  unfold bfs_step.
  destruct (frontier s) as [|c cs] eqn:Hfront.
  - contradiction.
  - simpl.
    rewrite length_app.
    assert (length (c :: cs) > 0).
    { simpl. lia. }
    lia.
Qed.

(** BFS eventually exhausts the frontier or finds the target *)
Lemma bfs_progress_or_done : forall img adj s target,
  frontier s <> [] ->
  reachable_from img adj (visited s) (frontier s) target 1 = true \/
  frontier (bfs_step img adj s) = [] \/
  length (visited (bfs_step img adj s)) > length (visited s).
Proof.
  intros img adj s target Hnonempty.
  unfold reachable_from at 1.
  simpl.
  destruct (existsb (coord_eqb target) (frontier s)) eqn:Htarget.
  - (* Target found in frontier *)
    left. reflexivity.
  - (* Target not in frontier *)
    right.
    unfold bfs_step.
    destruct (frontier s) as [|c cs] eqn:Hfront.
    + contradiction.
    + (* frontier = c :: cs *)
      simpl.
      remember (flat_map (unexplored_neighbors img adj s) (c :: cs)) as new_frontier.
      destruct new_frontier as [|c' rest] eqn:Hnew.
      * (* New frontier is empty *)
        left.
        (* Goal: unexplored_neighbors img adj s c ++ flat_map (unexplored_neighbors img adj s) cs = [] *)
        (* We have: Heqnew_frontier : [] = flat_map (unexplored_neighbors img adj s) (c :: cs) *)
        (* Note that simpl on flat_map (f) (c :: cs) gives f c ++ flat_map f cs *)
        simpl in Heqnew_frontier.
        symmetry.
        exact Heqnew_frontier.
      * (* New frontier is non-empty, visited grows *)
        right.
        rewrite length_app.
        rewrite <- Hfront.
        assert (length (frontier s) > 0).
        { rewrite Hfront. simpl. lia. }
        lia.
Qed.

Definition bfs_step_dedup (img : bounded_image) (adj : coord -> coord -> bool)
                         (s : bfs_state) : bfs_state :=
  match frontier s with
  | [] => s
  | _ => mkBFSState 
           (visited s ++ frontier s)
           (remove_dups coord_eqb 
             (flat_map (unexplored_neighbors img adj s) (frontier s)))
  end.

Lemma bfs_step_dedup_preserves_nodup : forall img adj s,
  bfs_nodup s ->
  bfs_disjoint s ->
  bfs_nodup (bfs_step_dedup img adj s).
Proof.
  intros img adj s Hnodup Hdisj.
  unfold bfs_step_dedup.
  destruct (frontier s) as [|c cs] eqn:Hfront.
  - exact Hnodup.
  - unfold bfs_nodup in *.
    destruct Hnodup as [Hvis_nodup Hfront_nodup].
    split.
    + apply NoDup_app_disjoint.
      * exact Hvis_nodup.
      * rewrite Hfront in Hfront_nodup. exact Hfront_nodup.
      * intros x Hin_vis Hin_front.
        apply (Hdisj x).
        split.
        -- exact Hin_vis.
        -- rewrite Hfront. exact Hin_front.
    + apply remove_dups_NoDup.
      intros x y.
      apply coord_eqb_true_iff.
Qed.
            
