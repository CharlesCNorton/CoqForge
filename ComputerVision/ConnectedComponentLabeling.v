(** * Connected Component Labeling in Coq

    This formalization develops a verified implementation of connected component
    labeling (CCL), a fundamental algorithm in computer vision and image processing.
    
    ** Overview
    
    Connected component labeling assigns unique labels to connected regions of 
    foreground pixels in a binary image. Two pixels belong to the same component
    if and only if there exists a path of foreground pixels connecting them,
    where adjacency is defined by either 4-connectivity or 8-connectivity.
    
    ** Goals of this formalization:
    
    1. Provide a formal specification of what it means for pixels to be connected
    2. Define correct labeling as an equivalence relation on foreground pixels
    3. Implement and verify classical CCL algorithms (two-pass, union-find)
    4. Prove key properties:
       - Correctness: pixels have same label iff they are connected
       - Uniqueness: any two correct labelings are equivalent up to relabeling
       - Termination: algorithms complete in finite time
       - Efficiency bounds: relating runtime to image dimensions
    
    ** Structure:
    
    - Basic definitions: coordinates, images, adjacency relations
    - Connectivity specification: paths and reachability
    - Labeling specification: when is a labeling correct?
    - Algorithm implementations with correctness proofs
    - Applications and extensions
    
    ** Why formalize this?
    
    CCL is ubiquitous in vision systems, yet implementations often contain subtle
    bugs, especially at image boundaries or with complex pixel patterns. A formal
    verification provides confidence for safety-critical applications and serves
    as a foundation for verifying more complex vision algorithms.
*)

(** * Imports and Setup *)

Require Import Coq.Init.Prelude.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Lia.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Logic.
Require Import Coq.Init.Notations.

Open Scope nat_scope.

(** * Basic Types *)

(** ** Coordinates
    
    We represent pixel coordinates as pairs of natural numbers (x, y).
    The origin (0, 0) is at the top-left corner, with x increasing rightward
    and y increasing downward, following standard image processing conventions.
*)
Definition coord : Type := prod nat nat.

(** Accessor functions for coordinates *)
Definition fst_coord (c : coord) : nat :=
  match c with
  | pair x y => x
  end.

Definition snd_coord (c : coord) : nat :=
  match c with
  | pair x y => y
  end.

(** ** Images
    
    We begin with a simple unbounded image representation as a function
    from coordinates to booleans. Later we'll add bounded images with
    explicit dimensions for more realistic modeling.
    
    Convention: true represents foreground (object) pixels, 
                false represents background pixels
*)
Definition simple_image : Type := forall (c : coord), bool.

(** The empty image contains no foreground pixels *)
Definition empty_image : simple_image := fun _ => false.

(** ** Labelings
    
    A labeling assigns a natural number label to each coordinate.
    We use 0 to represent "unlabeled" or background pixels.
    Connected foreground pixels should receive the same positive label.
*)
Definition labeling : Type := forall (c : coord), nat.

(** The empty labeling assigns 0 to all pixels *)
Definition empty_labeling : labeling := fun _ => O.

(** * Adjacency Relations *)

(** Helper function: absolute difference between natural numbers *)
Definition abs_diff (a b : nat) : nat :=
  match Nat.leb a b with
  | true => Nat.sub b a
  | false => Nat.sub a b
  end.

(** ** 4-connectivity adjacency
    
    Two pixels are 4-adjacent if they share an edge, i.e., they differ
    by exactly 1 in either x or y coordinate (but not both).
    
    This gives each pixel up to 4 neighbors:
    - (x-1, y) left
    - (x+1, y) right  
    - (x, y+1) down
    - (x, y-1) up
*)
Definition adjacent_4 (c1 c2 : coord) : bool :=
  let x1 := fst_coord c1 in
  let y1 := snd_coord c1 in
  let x2 := fst_coord c2 in
  let y2 := snd_coord c2 in
  match Nat.eqb x1 x2 with
  | true => Nat.eqb (abs_diff y1 y2) (S O)  (* same x, differ by 1 in y *)
  | false => andb (Nat.eqb y1 y2) (Nat.eqb (abs_diff x1 x2) (S O))  (* same y, differ by 1 in x *)
  end.

(** ** Basic tests for 4-adjacency *)

Example test_adj4_horiz : adjacent_4 (pair O O) (pair (S O) O) = true := eq_refl.
Example test_adj4_vert : adjacent_4 (pair O O) (pair O (S O)) = true := eq_refl.
Example test_adj4_diag : adjacent_4 (pair O O) (pair (S O) (S O)) = false := eq_refl.

(** ** 8-connectivity adjacency
    
    Two pixels are 8-adjacent if they share an edge or corner, i.e., they differ
    by at most 1 in both x and y coordinates (but not identical).
    
    This gives each pixel up to 8 neighbors, including diagonals.
*)
Definition adjacent_8 (c1 c2 : coord) : bool :=
  let x1 := fst_coord c1 in
  let y1 := snd_coord c1 in
  let x2 := fst_coord c2 in
  let y2 := snd_coord c2 in
  let dx := abs_diff x1 x2 in
  let dy := abs_diff y1 y2 in
  andb (andb (Nat.leb dx (S O)) (Nat.leb dy (S O))) 
       (negb (andb (Nat.eqb dx O) (Nat.eqb dy O))).

(** Tests for 8-connectivity *)
Example test_adj8_horiz : adjacent_8 (pair O O) (pair (S O) O) = true := eq_refl.
Example test_adj8_diag : adjacent_8 (pair O O) (pair (S O) (S O)) = true := eq_refl.
Example test_adj8_self : adjacent_8 (pair O O) (pair O O) = false := eq_refl.
Example test_adj8_far : adjacent_8 (pair O O) (pair (S (S O)) O) = false := eq_refl.

(** * Paths and Connectivity *)

(** ** Paths
    
    A path in an image is a sequence of coordinates where consecutive
    coordinates are adjacent (according to the chosen connectivity).
    We represent paths as lists of coordinates.
*)

(** Check if a list of coordinates forms a valid path with given adjacency *)
Fixpoint is_path (adj : coord -> coord -> bool) (p : list coord) : bool :=
  match p with
  | [] => true
  | [_] => true
  | c1 :: (c2 :: rest) as tail => andb (adj c1 c2) (is_path adj tail)
  end.

(** A path is valid in an image if all coordinates are foreground pixels *)
Fixpoint path_in_image (img : simple_image) (p : list coord) : bool :=
  match p with
  | [] => true
  | c :: rest => andb (img c) (path_in_image img rest)
  end.

(** A valid path combines both requirements *)
Definition valid_path (img : simple_image) (adj : coord -> coord -> bool) 
                     (p : list coord) : bool :=
  andb (is_path adj p) (path_in_image img p).

(** Test path validity *)
Definition test_img : simple_image := fun c =>
  match c with
  | pair O O => true
  | pair (S O) O => true
  | pair O (S O) => true
  | _ => false
  end.

Example test_valid_path : 
  valid_path test_img adjacent_4 [pair O O; pair (S O) O] = true := eq_refl.

Example test_invalid_path : 
  valid_path test_img adjacent_4 [pair O O; pair (S O) (S O)] = false := eq_refl.

(** ** Connectivity
    
    Two pixels are connected if there exists a valid path between them.
    We define this inductively to avoid issues with unbounded search.
*)

Inductive connected (img : simple_image) (adj : coord -> coord -> bool) 
                   : coord -> coord -> Prop :=
  | connected_refl : forall c, img c = true -> connected img adj c c
  | connected_step : forall c1 c2 c3, 
      connected img adj c1 c2 -> 
      img c3 = true -> 
      adj c2 c3 = true -> 
      connected img adj c1 c3.

(** Connectivity is an equivalence relation on foreground pixels *)
Definition connected_symmetric img adj := 
  forall c1 c2, connected img adj c1 c2 -> connected img adj c2 c1.

Definition connected_transitive img adj := 
  forall c1 c2 c3, connected img adj c1 c2 -> connected img adj c2 c3 -> 
                   connected img adj c1 c3.

(** Test that proof mode works with -noinit flag fixed by Prelude import *)
Example proof_mode_test : O = O.
Proof.
  reflexivity.
Qed.

(** Helper: absolute difference is symmetric *)
Lemma abs_diff_sym : forall a b, abs_diff a b = abs_diff b a.
Proof.
  intros a b.
  unfold abs_diff.
  destruct (Nat.leb a b) eqn:Hab; destruct (Nat.leb b a) eqn:Hba.
  - (* a <= b and b <= a means a = b *)
    apply Nat.leb_le in Hab.
    apply Nat.leb_le in Hba.
    assert (a = b) by lia.
    subst. reflexivity.
  - (* a <= b and not b <= a *)
    reflexivity.
  - (* not a <= b and b <= a *)
    reflexivity.
  - (* not a <= b and not b <= a - impossible *)
    apply Nat.leb_nle in Hab.
    apply Nat.leb_nle in Hba.
    lia.
Qed.

(** Adjacency is symmetric *)
Lemma adjacent_4_sym : forall c1 c2, 
  adjacent_4 c1 c2 = adjacent_4 c2 c1.
Proof.
  intros c1 c2.
  unfold adjacent_4.
  destruct c1 as [x1 y1].
  destruct c2 as [x2 y2].
  simpl.
  rewrite Nat.eqb_sym.
  rewrite (Nat.eqb_sym y1 y2).
  rewrite abs_diff_sym.
  rewrite (abs_diff_sym x1 x2).
  destruct (Nat.eqb x2 x1); destruct (Nat.eqb y2 y1); reflexivity.
Qed.

(** Connected pixels must be foreground *)
Lemma connected_implies_foreground : forall img adj c1 c2,
  connected img adj c1 c2 -> img c1 = true /\ img c2 = true.
Proof.
  intros img adj c1 c2 H.
  induction H.
  - split; assumption.
  - split.
    + apply IHconnected.
    + assumption.
Qed.

(** Build connectivity backwards *)
Lemma connected_extend_left : forall img adj c1 c2 c3,
  img c1 = true ->
  adj c1 c2 = true ->
  connected img adj c2 c3 ->
  connected img adj c1 c3.
Proof.
  intros img adj c1 c2 c3 H_img1 H_adj H_conn.
  induction H_conn.
  - (* Base case: c2 = c and connected img adj c c *)
    apply connected_step with c1.
    + apply connected_refl. exact H_img1.
    + exact H.
    + exact H_adj.
  - (* Step case: c2 connected to c0, c0 connected to c3 *)
    apply connected_step with c2.
    + apply IHH_conn. exact H_adj.
    + exact H.
    + exact H0.
Qed.

(** Connectivity is symmetric *)
Lemma connected_sym : forall img adj c1 c2,
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

(** Connectivity is transitive *)
Lemma connected_trans : forall img adj c1 c2 c3,
  connected img adj c1 c2 -> connected img adj c2 c3 -> connected img adj c1 c3.
Proof.
  intros img adj c1 c2 c3 H12 H23.
  induction H23.
  - exact H12.
  - apply connected_step with c2.
    + apply IHconnected. exact H12.
    + exact H.
    + exact H0.
Qed.

(** * Correct Labeling Specification *)

(** A labeling respects connectivity if connected pixels have the same label *)
Definition respects_connectivity (img : simple_image) (adj : coord -> coord -> bool) 
                                (l : labeling) : Prop :=
  forall c1 c2, img c1 = true -> img c2 = true ->
                connected img adj c1 c2 -> l c1 = l c2.

(** A labeling separates components if pixels with same label are connected *)
Definition separates_components (img : simple_image) (adj : coord -> coord -> bool)
                               (l : labeling) : Prop :=
  forall c1 c2, img c1 = true -> img c2 = true ->
                l c1 = l c2 -> l c1 <> O -> connected img adj c1 c2.

(** Background pixels get label 0 *)
Definition labels_background (img : simple_image) (l : labeling) : Prop :=
  forall c, img c = false -> l c = O.

(** A correct labeling satisfies all three properties *)
Definition correct_labeling (img : simple_image) (adj : coord -> coord -> bool)
                           (l : labeling) : Prop :=
  labels_background img l /\
  respects_connectivity img adj l /\
  separates_components img adj l.

(** * Properties of Correct Labelings *)

(** Connectivity is reflexive on foreground pixels *)
Lemma connected_refl_fg : forall img adj c,
  img c = true -> connected img adj c c.
Proof.
  intros img adj c H.
  apply connected_refl. exact H.
Qed.

(** Connectivity is symmetric for foreground pixels *)
Lemma connected_sym_fg : forall img adj c1 c2,
  (forall a b, adj a b = adj b a) ->
  img c1 = true -> img c2 = true ->
  connected img adj c1 c2 -> connected img adj c2 c1.
Proof.
  intros img adj c1 c2 adj_sym H1 H2 H.
  apply connected_sym.
  - exact adj_sym.
  - exact H.
Qed.

(** Connectivity is transitive for foreground pixels *)
Lemma connected_trans_fg : forall img adj c1 c2 c3,
  img c1 = true -> img c2 = true -> img c3 = true ->
  connected img adj c1 c2 -> connected img adj c2 c3 -> 
  connected img adj c1 c3.
Proof.
  intros img adj c1 c2 c3 H1 H2 H3 H12 H23.
  apply connected_trans with c2.
  - exact H12.
  - exact H23.
Qed.

(** If two foreground pixels have the same non-zero label in a correct labeling,
    they must be connected *)
Lemma same_label_implies_connected : forall img adj l c1 c2,
  correct_labeling img adj l ->
  img c1 = true -> img c2 = true ->
  l c1 = l c2 -> l c1 <> O ->
  connected img adj c1 c2.
Proof.
  intros img adj l c1 c2 [Hbg [Hresp Hsep]] H1 H2 Heq Hneq.
  apply Hsep.
  - exact H1.
  - exact H2.
  - exact Heq.
  - exact Hneq.
Qed.

(** * Bounded Images *)

(** An image with explicit dimensions *)
Record bounded_image : Type := mkBoundedImage {
  width : nat;
  height : nat;
  pixels : coord -> bool
}.

(** Check if a coordinate is within bounds *)
Definition in_bounds (img : bounded_image) (c : coord) : bool :=
  let (x, y) := c in
  andb (Nat.ltb x (width img)) (Nat.ltb y (height img)).

(** Safe pixel access that returns false for out-of-bounds *)
Definition get_pixel (img : bounded_image) (c : coord) : bool :=
  if in_bounds img c then pixels img c else false.
