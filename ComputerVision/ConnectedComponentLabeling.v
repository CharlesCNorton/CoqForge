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

(** * Fundamental Properties of Adjacency and Connectivity *)

(** Absolute difference is symmetric *)
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

(** Count foreground pixels in a row *)
Fixpoint count_row (img : bounded_image) (y : nat) (x : nat) : nat :=
  match x with
  | O => O
  | S x' => (if get_pixel img (pair x' y) then S O else O) + count_row img y x'
  end.

(** Count all foreground pixels in bounded image *)
Fixpoint count_foreground (img : bounded_image) (y : nat) : nat :=
  match y with
  | O => O
  | S y' => count_row img y' (width img) + count_foreground img y'
  end.

(** * Two-Pass Connected Component Labeling Algorithm *)

(** Label equivalence table - tracks which labels should be merged *)
Definition equiv_table := nat -> nat -> bool.

(** Empty equivalence table *)
Definition empty_equiv : equiv_table := fun _ _ => false.

(** Add an equivalence *)
Definition add_equiv (e : equiv_table) (l1 l2 : nat) : equiv_table :=
  fun a b => orb (e a b) (orb (andb (Nat.eqb a l1) (Nat.eqb b l2))
                              (andb (Nat.eqb a l2) (Nat.eqb b l1))).

(** Find minimum equivalent label *)
Fixpoint find_min_equiv (e : equiv_table) (l : nat) (fuel : nat) : nat :=
  match fuel with
  | O => l
  | S fuel' => 
    let scan := fix scan_labels n :=
      match n with
      | O => l
      | S n' => if e l n' then
                  Nat.min n' (scan_labels n')
                else scan_labels n'
      end
    in Nat.min l (scan l)
  end.

(** Coordinate equality *)
Definition coord_eq (c1 c2 : coord) : bool :=
  match c1, c2 with
  | pair x1 y1, pair x2 y2 => andb (Nat.eqb x1 x2) (Nat.eqb y1 y2)
  end.

(** Process a single row left-to-right *)
Fixpoint first_pass_row (img : bounded_image) (adj : coord -> coord -> bool)
                        (prev_labels : coord -> nat) (equiv : equiv_table)
                        (y : nat) (x : nat) (fuel : nat) (next_label : nat) 
                        : (coord -> nat) * equiv_table * nat :=
  match fuel with
  | O => (prev_labels, equiv, next_label)
  | S fuel' =>
    if Nat.ltb x (width img) then
      let c := pair x y in
      if get_pixel img c then
        (* Check left and up neighbors *)
        let left := if x =? O then O else 
                    if adj (pair (pred x) y) c then prev_labels (pair (pred x) y) else O in
        let up := if y =? O then O else
                  if adj (pair x (pred y)) c then prev_labels (pair x (pred y)) else O in
        match left, up with
        | O, O => (* No labeled neighbors - new label *)
          let new_labels := fun c' => if coord_eq c c' then next_label else prev_labels c' in
          first_pass_row img adj new_labels equiv y (S x) fuel' (S next_label)
        | _, _ => (* Use minimum of existing labels *)
          let label := match left, up with
                       | O, u => u
                       | l, O => l
                       | l, u => Nat.min l u
                       end in
          let new_labels := fun c' => if coord_eq c c' then label else prev_labels c' in
          let new_equiv := match left, up with
                           | O, _ => equiv
                           | _, O => equiv
                           | l, u => if Nat.eqb l u then equiv else add_equiv equiv l u
                           end in
          first_pass_row img adj new_labels new_equiv y (S x) fuel' next_label
        end
      else
        first_pass_row img adj prev_labels equiv y (S x) fuel' next_label
    else
      (prev_labels, equiv, next_label)
  end.

(** Process a row starting from x=0 *)
Definition process_row (img : bounded_image) (adj : coord -> coord -> bool)
                      (prev_labels : coord -> nat) (equiv : equiv_table)
                      (y : nat) (next_label : nat) 
                      : (coord -> nat) * equiv_table * nat :=
  first_pass_row img adj prev_labels equiv y O (width img) next_label.

(** Process all rows from top to bottom *)
Fixpoint first_pass_rows (img : bounded_image) (adj : coord -> coord -> bool)
                         (labels : coord -> nat) (equiv : equiv_table)
                         (y : nat) (fuel : nat) (next_label : nat)
                         : (coord -> nat) * equiv_table * nat :=
  match fuel with
  | O => (labels, equiv, next_label)
  | S fuel' =>
    if Nat.ltb y (height img) then
      let '(labels', equiv', next') := process_row img adj labels equiv y next_label in
      first_pass_rows img adj labels' equiv' (S y) fuel' next'
    else
      (labels, equiv, next_label)
  end.

(** Complete first pass *)
Definition first_pass (img : bounded_image) (adj : coord -> coord -> bool) 
                     : (coord -> nat) * equiv_table * nat :=
  first_pass_rows img adj empty_labeling empty_equiv O (height img) (S O).

(** Second pass: resolve equivalences *)
Definition second_pass (labels : coord -> nat) (equiv : equiv_table) (max_label : nat) : coord -> nat :=
  fun c => 
    let l := labels c in
    if Nat.eqb l O then O
    else find_min_equiv equiv l max_label.

(** Complete two-pass algorithm *)
Definition two_pass_ccl (img : bounded_image) (adj : coord -> coord -> bool) : labeling :=
  let '(labels, equiv, max_label) := first_pass img adj in
  second_pass labels equiv max_label.

(** * Example: Testing the Algorithm *)

(** Create a simple test image *)
Definition test_image : bounded_image :=
  mkBoundedImage 3 3 (fun c =>
    match c with
    | pair O O => true      (* X.. *)
    | pair (S O) O => true   (* XX. *)
    | pair O (S O) => true   (* X.. *)
    | pair (S (S O)) (S O) => true  (* ..X *)
    | pair (S (S O)) (S (S O)) => true (* ..X *)
    | _ => false
    end).

(** Apply CCL algorithm *)
Definition test_labels := two_pass_ccl test_image adjacent_4.

(** Verify results *)
Compute test_labels (pair O O).
Compute test_labels (pair (S O) O).
Compute test_labels (pair O (S O)).

(** Adding an equivalence preserves existing equivalences *)
Lemma add_equiv_preserves : forall e l1 l2 a b,
  e a b = true -> add_equiv e l1 l2 a b = true.
Proof.
  intros e l1 l2 a b H.
  unfold add_equiv.
  rewrite H. reflexivity.
Qed.

(** Add creates the intended equivalence *)
Lemma add_equiv_creates : forall e l1 l2,
  add_equiv e l1 l2 l1 l2 = true.
Proof.
  intros e l1 l2.
  unfold add_equiv.
  rewrite Nat.eqb_refl.
  rewrite Nat.eqb_refl.
  simpl.
  rewrite orb_true_r.
  reflexivity.
Qed.

(** Equivalence tables should include reflexivity *)
Definition equiv_refl (e : equiv_table) : Prop :=
  forall l, e l l = true.

(** If equiv table is reflexive, add_equiv preserves it *)
Lemma add_equiv_preserves_refl : forall e l1 l2,
  equiv_refl e ->
  equiv_refl (add_equiv e l1 l2).
Proof.
  intros e l1 l2 Hrefl.
  unfold equiv_refl in *.
  intros l.
  unfold add_equiv.
  rewrite Hrefl.
  reflexivity.
Qed.

(** Understand find_min_equiv behavior *)
Example find_min_test : find_min_equiv empty_equiv 5 0 = 5.
Proof.
  compute.
  reflexivity.
Qed.

(** Basic property of coord_eq *)
Lemma coord_eq_refl : forall c,
  coord_eq c c = true.
Proof.
  intros c.
  destruct c as [x y].
  unfold coord_eq.
  rewrite Nat.eqb_refl.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(** coord_eq is symmetric *)
Lemma coord_eq_sym : forall c1 c2,
  coord_eq c1 c2 = coord_eq c2 c1.
Proof.
  intros c1 c2.
  destruct c1 as [x1 y1].
  destruct c2 as [x2 y2].
  unfold coord_eq.
  rewrite Nat.eqb_sym.
  rewrite (Nat.eqb_sym y1 y2).
  reflexivity.
Qed.

(** coord_eq decides equality *)
Lemma coord_eq_true_iff : forall c1 c2,
  coord_eq c1 c2 = true <-> c1 = c2.
Proof.
  intros c1 c2.
  split.
  - intros H.
    destruct c1 as [x1 y1], c2 as [x2 y2].
    unfold coord_eq in H.
    apply andb_prop in H. destruct H as [Hx Hy].
    apply Nat.eqb_eq in Hx. apply Nat.eqb_eq in Hy.
    subst. reflexivity.
  - intros H. subst. apply coord_eq_refl.
Qed.

(** Labeling update preserves values for different coordinates *)
Lemma label_update_preserves : forall (prev_labels : labeling) (c c' : coord) (label : nat),
  c <> c' ->
  (if coord_eq c c' then label else prev_labels c') = prev_labels c'.
Proof.
  intros prev_labels c c' label Hneq.
  destruct (coord_eq c c') eqn:Heq.
  - apply coord_eq_true_iff in Heq. contradiction.
  - reflexivity.
Qed.

(** Pairs are equal iff components are equal *)
Lemma pair_eq_iff : forall (x1 y1 x2 y2 : nat),
  pair x1 y1 = pair x2 y2 <-> x1 = x2 /\ y1 = y2.
Proof.
  intros x1 y1 x2 y2.
  split.
  - intros H. 
    injection H as H1 H2.
    split; assumption.
  - intros [H1 H2].
    subst. reflexivity.
Qed.

(** Pairs with different first components are not equal *)
Lemma pair_neq_fst : forall (x1 x2 y : nat),
  x1 <> x2 -> pair x1 y <> pair x2 y.
Proof.
  intros x1 x2 y Hneq Heq.
  apply pair_eq_iff in Heq.
  destruct Heq as [Hx _].
  contradiction.
Qed.

(** Applying updated labeling to different coordinate *)
Lemma updated_labeling_at_different : forall x y x' y' (prev_labels : labeling) (label : nat),
  pair x y <> pair x' y' ->
  (fun c' : coord =>
    if let (x2, y2) := c' in (x =? x2) && (y =? y2)
    then label
    else prev_labels c') (pair x' y') = prev_labels (pair x' y').
Proof.
  intros x y x' y' prev_labels label Hneq.
  simpl.
  destruct (x =? x') eqn:Hx; destruct (y =? y') eqn:Hy.
  - apply Nat.eqb_eq in Hx. apply Nat.eqb_eq in Hy.
    subst. exfalso. apply Hneq. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.  
  - simpl. reflexivity.
Qed.

(** * Intermediate Theorems: Combining Basic Lemmas *)

(** ** Connectivity as an Equivalence Relation *)

(** First, let's verify we have the equivalence properties individually *)
Theorem connectivity_equiv_refl : forall img adj c,
  (forall a b, adj a b = adj b a) ->
  img c = true ->
  connected img adj c c.
Proof.
  intros img adj c adj_sym H.
  apply connected_refl. exact H.
Qed.

Theorem connectivity_equiv_sym : forall img adj c1 c2,
  (forall a b, adj a b = adj b a) ->
  connected img adj c1 c2 ->
  connected img adj c2 c1.
Proof.
  intros img adj c1 c2 adj_sym H.
  apply connected_sym; assumption.
Qed.

Theorem connectivity_equiv_trans : forall img adj c1 c2 c3,
  connected img adj c1 c2 ->
  connected img adj c2 c3 ->
  connected img adj c1 c3.
Proof.
  intros img adj c1 c2 c3 H12 H23.
  apply connected_trans with c2; assumption.
Qed.


Theorem connectivity_is_equivalence : forall img adj,
  (forall a b, adj a b = adj b a) ->
  (forall c, img c = true -> connected img adj c c) /\
  (forall c1 c2, connected img adj c1 c2 -> connected img adj c2 c1) /\
  (forall c1 c2 c3, connected img adj c1 c2 -> connected img adj c2 c3 -> connected img adj c1 c3).
Proof.
  intros img adj adj_sym.
  split; [| split].
  - intros c H. apply connected_refl. exact H.
  - intros c1 c2 H. apply connected_sym; assumption.
  - intros c1 c2 c3 H12 H23. apply connected_trans with c2; assumption.
Qed.

(** ** Labels partition foreground pixels into connected components *)

Theorem label_partition : forall img adj l,
  (forall a b, adj a b = adj b a) ->
  correct_labeling img adj l ->
  (forall c, img c = true -> l c <> O) ->  (* Add this assumption *)
  forall c1 c2, img c1 = true -> img c2 = true ->
    (l c1 = l c2 /\ l c1 <> O) <-> connected img adj c1 c2.
Proof.
  intros img adj l adj_sym [Hbg [Hresp Hsep]] Hfg_nonzero c1 c2 H1 H2.
  split.
  - intros [Heq Hneq]. apply Hsep; assumption.
  - intros Hconn. 
    assert (l c1 = l c2) by (apply Hresp; assumption).
    split; [exact H | apply Hfg_nonzero; exact H1].
Qed.

(** ** Adjacent foreground pixels are connected *)

Theorem adjacent_implies_connected : forall img adj c1 c2,
  img c1 = true -> img c2 = true -> adj c1 c2 = true ->
  connected img adj c1 c2.
Proof.
  intros img adj c1 c2 H1 H2 Hadj.
  apply connected_step with c1.
  - apply connected_refl. exact H1.
  - exact H2.
  - exact Hadj.
Qed.

(** And with symmetric adjacency, the connection is bidirectional *)
Theorem adjacent_implies_bidirectional_connection : forall img adj c1 c2,
  (forall a b, adj a b = adj b a) ->
  img c1 = true -> img c2 = true -> adj c1 c2 = true ->
  connected img adj c1 c2 /\ connected img adj c2 c1.
Proof.
  intros img adj c1 c2 adj_sym H1 H2 Hadj.
  split.
  - apply adjacent_implies_connected; assumption.
  - apply adjacent_implies_connected.
    + exact H2.
    + exact H1.
    + rewrite adj_sym. exact Hadj.
Qed.

(** ** Every valid path induces connectivity between endpoints *)

Theorem valid_path_implies_connected : forall img adj path c1 cn,
  valid_path img adj path = true ->
  head path = Some c1 ->
  last path cn = cn ->  (* last returns default if empty *)
  path <> [] ->  (* path must be non-empty *)
  connected img adj c1 cn.
Proof.
  intros img adj path.
  induction path as [|c path' IH].
  - (* Empty path *)
    intros c1 cn Hvalid Hhead Hlast Hneq.
    contradiction.
  - intros c1 cn Hvalid Hhead Hlast Hneq.
    simpl in Hhead. injection Hhead as Heq. subst c.
    destruct path' as [|c' path''].
    + (* Single element *)
      simpl in Hlast. subst cn.
      apply connected_refl.
      unfold valid_path in Hvalid.
      simpl in Hvalid.
      unfold path_in_image in Hvalid.
      simpl in Hvalid.
      apply andb_prop in Hvalid. destruct Hvalid as [H _].
      exact H.
    + (* Multiple elements *)
      unfold valid_path in Hvalid.
      simpl in Hvalid.
      apply andb_prop in Hvalid. destruct Hvalid as [Hpath Himg].
      simpl in Hpath.
      apply andb_prop in Hpath. destruct Hpath as [Hadj Hpath'].
      unfold path_in_image in Himg.
      simpl in Himg.
      apply andb_prop in Himg. destruct Himg as [Hc1 Himg'].
      (* Extract img c' = true from Himg' *)
      assert (Hc': img c' = true).
      { unfold path_in_image in Himg'.
        simpl in Himg'.
        apply andb_prop in Himg'. destruct Himg' as [H _].
        exact H. }
      assert (Hlast': last (c' :: path'') cn = cn).
      { exact Hlast. }
      apply connected_trans with c'.
      * apply adjacent_implies_connected; assumption.
      * apply IH.
        -- unfold valid_path.
           apply andb_true_intro. split.
           ++ exact Hpath'.
           ++ exact Himg'.
        -- reflexivity.
        -- exact Hlast'.
        -- discriminate.
Qed.

(** ** Bounded images can be viewed as simple images *)

Definition bounded_to_simple (img : bounded_image) : simple_image :=
  fun c => get_pixel img c.

Theorem bounded_connectivity_preserved : forall bimg adj c1 c2,
  connected (bounded_to_simple bimg) adj c1 c2 <->
  connected (fun c => get_pixel bimg c) adj c1 c2.
Proof.
  intros bimg adj c1 c2.
  unfold bounded_to_simple.
  reflexivity.
Qed.

(** Connectivity in bounded images respects bounds *)
Theorem bounded_connected_in_bounds : forall bimg adj c1 c2,
  connected (bounded_to_simple bimg) adj c1 c2 ->
  in_bounds bimg c1 = true /\ in_bounds bimg c2 = true.
Proof.
  intros bimg adj c1 c2 H.
  apply connected_implies_foreground in H.
  destruct H as [H1 H2].
  unfold bounded_to_simple in H1, H2.
  unfold get_pixel in H1, H2.
  split.
  - destruct (in_bounds bimg c1) eqn:E1.
    + reflexivity.
    + discriminate.
  - destruct (in_bounds bimg c2) eqn:E2.
    + reflexivity.
    + discriminate.
Qed.

(** ** The Component Collapse Theorem *)
(** When switching from 4-adjacency to 8-adjacency, components can only merge, never split *)

Theorem component_collapse : forall c1 c2,
  adjacent_4 c1 c2 = true -> adjacent_8 c1 c2 = true.
Proof.
  intros [x1 y1] [x2 y2] H4.
  unfold adjacent_4 in H4.
  unfold adjacent_8.
  simpl in *.
  destruct (x1 =? x2) eqn:Heqx.
  - (* Same x coordinate *)
    apply Nat.eqb_eq in Heqx. subst x2.
    assert (abs_diff x1 x1 = 0).
    { unfold abs_diff. rewrite Nat.leb_refl. lia. }
    rewrite H.
    simpl.
    assert (abs_diff y1 y2 = 1).
    { destruct (Nat.eqb (abs_diff y1 y2) 1) eqn:E.
      - apply Nat.eqb_eq in E. exact E.
      - simpl in H4. congruence. }
    rewrite H0.
    simpl.
    reflexivity.
  - (* Different x, must have same y *)
    apply andb_prop in H4. destruct H4 as [Heqy H1].
    apply Nat.eqb_eq in Heqy. subst y2.
    assert (abs_diff y1 y1 = 0).
    { unfold abs_diff. rewrite Nat.leb_refl. lia. }
    rewrite H.
    assert (abs_diff x1 x2 = 1).
    { apply Nat.eqb_eq in H1. exact H1. }
    rewrite H0.
    simpl.
    apply Nat.eqb_neq in Heqx.
    destruct (Nat.eq_dec x1 x2); [contradiction|].
    simpl. reflexivity.
Qed.

(** This implies connectivity can only increase *)
Theorem connectivity_monotone : forall img c1 c2,
  connected img adjacent_4 c1 c2 ->
  connected img adjacent_8 c1 c2.
Proof.
  intros img c1 c2 H.
  induction H.
  - apply connected_refl. assumption.
  - apply connected_step with c2.
    + exact IHconnected.
    + exact H0.
    + apply component_collapse. exact H1.
Qed.

(** ** Components are Maximal Connected Sets *)
(** A component defined by a correct labeling is maximal: 
    no foreground pixel outside the component can be added while preserving connectivity *)

Theorem component_maximality : forall img adj l label,
  (forall a b, adj a b = adj b a) ->
  correct_labeling img adj l ->
  (forall c, img c = true -> l c <> 0) ->
  label <> 0 ->
  forall c_out c_in,
    img c_out = true ->
    img c_in = true ->
    l c_in = label ->
    l c_out <> label ->
    ~ connected img adj c_out c_in.
Proof.
  intros img adj l label adj_sym [Hbg [Hresp Hsep]] Hfg_nonzero Hlabel_nonzero.
  intros c_out c_in Hout_fg Hin_fg Hin_label Hout_diff Hconn.
  (* If they're connected, they must have the same label *)
  assert (l c_out = l c_in).
  { apply Hresp; assumption. }
  (* But we know they have different labels *)
  congruence.
Qed.

(** Corollary: Components partition the foreground pixels *)
Theorem component_partition : forall img adj l,
  (forall a b, adj a b = adj b a) ->
  correct_labeling img adj l ->
  (forall c, img c = true -> l c <> 0) ->
  forall c1 c2,
    img c1 = true ->
    img c2 = true ->
    (l c1 = l c2) \/ ~ connected img adj c1 c2.
Proof.
  intros img adj l adj_sym Hcorrect Hfg_nonzero c1 c2 H1 H2.
  destruct (Nat.eq_dec (l c1) (l c2)).
  - left. assumption.
  - right. intros Hconn.
    destruct Hcorrect as [Hbg [Hresp Hsep]].
    assert (l c1 = l c2) by (apply Hresp; assumption).
    contradiction.
Qed.

(** ** The Label Count Theorem *)
(** The number of distinct non-zero labels in a correct labeling 
    equals the number of connected components *)

(** First, define what it means for two foreground pixels to be in different components *)
Definition in_different_components (img : simple_image) (adj : coord -> coord -> bool) (c1 c2 : coord) : Prop :=
  img c1 = true /\ img c2 = true /\ ~ connected img adj c1 c2.

(** A label is "used" if some foreground pixel has that label *)
Definition label_used (img : simple_image) (l : labeling) (label : nat) : Prop :=
  exists c, img c = true /\ l c = label.

(** The minimum label theorem: you can't correctly label n components with fewer than n labels *)
Theorem minimum_labels_needed : forall img adj l c1 c2,
  (forall a b, adj a b = adj b a) ->
  correct_labeling img adj l ->
  (forall c, img c = true -> l c <> 0) ->
  in_different_components img adj c1 c2 ->
  l c1 <> l c2.
Proof.
  intros img adj l c1 c2 adj_sym [Hbg [Hresp Hsep]] Hfg_nonzero [H1 [H2 Hnconn]].
  intros Heq.
  assert (l c1 <> 0) by (apply Hfg_nonzero; assumption).
  assert (connected img adj c1 c2) by (apply Hsep; assumption).
  contradiction.
Qed.

(** Each component gets exactly one label *)
Theorem one_label_per_component : forall img adj l label1 label2,
  (forall a b, adj a b = adj b a) ->
  correct_labeling img adj l ->
  (forall c, img c = true -> l c <> 0) ->
  label1 <> 0 ->
  label2 <> 0 ->
  label_used img l label1 ->
  label_used img l label2 ->
  (exists c1 c2, l c1 = label1 /\ l c2 = label2 /\ connected img adj c1 c2) ->
  label1 = label2.
Proof.
  intros img adj l label1 label2 adj_sym [Hbg [Hresp Hsep]] Hfg_nonzero.
  intros Hl1_nonzero Hl2_nonzero [c1 [H1c1 Hl1]] [c2 [H2c2 Hl2]] [c1' [c2' [Heq1 [Heq2 Hconn]]]].
  (* c1' and c2' are connected and have labels label1 and label2 respectively *)
  (* By correctness, they must have the same label *)
  assert (Hfg: img c1' = true /\ img c2' = true).
  { apply connected_implies_foreground with adj. exact Hconn. }
  destruct Hfg as [Hc1'_fg Hc2'_fg].
  assert (l c1' = l c2').
  { apply Hresp; assumption. }
  (* But l c1' = label1 and l c2' = label2 *)
  congruence.
Qed.

(** ** The Component Boundary Theorem *)
(** A pixel is on the boundary of its component if it has an adjacent pixel
    that is either background or in a different component *)

Definition on_component_boundary (img : simple_image) (adj : coord -> coord -> bool) 
                                 (l : labeling) (c : coord) : Prop :=
  img c = true /\ 
  exists c', adj c c' = true /\ 
             (img c' = false \/ (img c' = true /\ l c <> l c')).

(** Boundary pixels connect different components *)
Theorem boundary_bridges_components : forall img adj l c c1 c2,
  (forall a b, adj a b = adj b a) ->
  correct_labeling img adj l ->
  (forall c, img c = true -> l c <> 0) ->
  on_component_boundary img adj l c ->
  adj c c1 = true -> adj c c2 = true ->
  img c1 = true -> img c2 = true ->
  l c = l c1 -> l c <> l c2 ->
  ~ connected img adj c1 c2.
Proof.
  intros img adj l c c1 c2 adj_sym [Hbg [Hresp Hsep]] Hfg_nonzero.
  intros [Hc_fg [c' [Hadj_c' Hc']]] Hadj1 Hadj2 H1 H2 Heq1 Hneq2 Hconn.
  (* If c1 and c2 were connected, they'd have the same label *)
  assert (l c1 = l c2) by (apply Hresp; assumption).
  (* But c has the same label as c1 and different from c2 *)
  congruence.
Qed.

(** Interior pixels have all neighbors in the same component *)
Definition interior_pixel (img : simple_image) (adj : coord -> coord -> bool)
                         (l : labeling) (c : coord) : Prop :=
  img c = true /\
  forall c', adj c c' = true -> img c' = true /\ l c = l c'.

(** Check if a pixel is interior - decidable version *)
Definition is_interior_pixel (img : simple_image) (adj : coord -> coord -> bool)
                            (l : labeling) (c : coord) (neighbors : list coord) : bool :=
  andb (img c) 
       (forallb (fun c' => implb (adj c c') 
                                 (andb (img c') (Nat.eqb (l c) (l c')))) 
                neighbors).

(** A simpler boundary characterization that's decidable *)
Definition has_boundary_neighbor (img : simple_image) (adj : coord -> coord -> bool)
                                (l : labeling) (c : coord) (neighbors : list coord) : bool :=
  existsb (fun c' => andb (adj c c') 
                         (orb (negb (img c'))
                              (andb (img c') (negb (Nat.eqb (l c) (l c'))))))
          neighbors.

(** A simpler theorem about boundary existence *)
Theorem boundary_exists_if_different_labels : forall img adj l c1 c2,
  img c1 = true ->
  img c2 = true ->
  adj c1 c2 = true ->
  l c1 <> l c2 ->
  on_component_boundary img adj l c1.
Proof.
  intros img adj l c1 c2 H1 H2 Hadj Hneq.
  unfold on_component_boundary.
  split; [assumption|].
  exists c2.
  split; [assumption|].
  right.
  split; assumption.
Qed.

(** A pixel with a background neighbor is on the boundary *)
Theorem background_neighbor_is_boundary : forall img adj l c c',
  img c = true ->
  adj c c' = true ->
  img c' = false ->
  on_component_boundary img adj l c.
Proof.
  intros img adj l c c' Hc Hadj Hc'.
  unfold on_component_boundary.
  split; [assumption|].
  exists c'.
  split; [assumption|].
  left. assumption.
Qed.

(** Components are separated by boundaries or background *)
Theorem component_separation : forall img adj l c1 c2,
  (forall a b, adj a b = adj b a) ->
  correct_labeling img adj l ->
  (forall c, img c = true -> l c <> 0) ->
  img c1 = true ->
  img c2 = true ->
  l c1 <> l c2 ->
  ~ adj c1 c2 = true.
Proof.
  intros img adj l c1 c2 adj_sym [Hbg [Hresp Hsep]] Hfg_nonzero H1 H2 Hneq Hadj.
  (* If they were adjacent, we could connect them *)
  assert (connected img adj c1 c2).
  { apply adjacent_implies_connected; assumption. }
  (* But then they'd have the same label *)
  assert (l c1 = l c2).
  { apply Hresp; assumption. }
  contradiction.
Qed.

Example test_label_00 : test_labels (pair 0 0) = 1.
Proof. compute. reflexivity. Qed.

Example test_label_10 : test_labels (pair 1 0) = 1.
Proof. compute. reflexivity. Qed.

Example test_label_01 : test_labels (pair 0 1) = 1.
Proof. compute. reflexivity. Qed.

Example test_label_21 : test_labels (pair 2 1) = 2.
Proof. compute. reflexivity. Qed.

Example test_label_22 : test_labels (pair 2 2) = 2.
Proof. compute. reflexivity. Qed.

(* Now verify the components *)
Example test_component_1 : 
  test_labels (pair 0 0) = test_labels (pair 1 0) /\
  test_labels (pair 1 0) = test_labels (pair 0 1).
Proof. compute. split; reflexivity. Qed.

Example test_component_2 :
  test_labels (pair 2 1) = test_labels (pair 2 2).
Proof. compute. reflexivity. Qed.

Example test_different_components :
  test_labels (pair 0 0) <> test_labels (pair 2 1).
Proof. compute. discriminate. Qed.

(** Empty labeling assigns 0 everywhere *)
Lemma empty_labeling_zero : forall c,
  empty_labeling c = 0.
Proof.
  intro c. reflexivity.
Qed.

(** The labeling function only changes at specific coordinates *)
Lemma label_update_spec : forall (labels : labeling) (c c' : coord) (label : nat),
  (fun c'' : coord => if coord_eq c c'' then label else labels c'') c' =
  if coord_eq c c' then label else labels c'.
Proof.
  intros. reflexivity.
Qed.

(** Label update at different coordinates preserves the value *)
Lemma label_update_neq : forall (labels : labeling) (c c' : coord) (label : nat),
  c <> c' ->
  (fun c'' : coord => if coord_eq c c'' then label else labels c'') c' = labels c'.
Proof.
  intros labels c c' label Hneq.
  simpl.
  destruct (coord_eq c c') eqn:Heq.
  - apply coord_eq_true_iff in Heq. contradiction.
  - reflexivity.
Qed.

(** Coordinates with different y values are not equal *)
Lemma coord_neq_diff_y : forall x1 y1 x2 y2,
  y1 <> y2 ->
  (pair x1 y1 : coord) <> (pair x2 y2 : coord).
Proof.
  intros x1 y1 x2 y2 Hy Heq.
  apply pair_eq_iff in Heq.
  destruct Heq as [_ Heq_y].
  contradiction.
Qed.

(** coord_eq returns false for coordinates with different y values *)
Lemma coord_eq_diff_y : forall x1 y1 x2 y2,
  y1 <> y2 ->
  coord_eq (pair x1 y1) (pair x2 y2) = false.
Proof.
  intros x1 y1 x2 y2 Hy.
  unfold coord_eq.
  destruct (x1 =? x2) eqn:Hx; destruct (y1 =? y2) eqn:Heqy; simpl.
  - apply Nat.eqb_eq in Heqy. contradiction.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** Label update on one row doesn't affect other rows *)
Lemma label_update_diff_row : forall (labels : labeling) (x y x' y' : nat) (label : nat),
  y <> y' ->
  (fun c => if coord_eq (pair x y) c then label else labels c) (pair x' y') = labels (pair x' y').
Proof.
  intros labels x y x' y' label Hy.
  apply label_update_neq.
  apply coord_neq_diff_y.
  exact Hy.
Qed.

(** The specific label update pattern used in first_pass_row *)
Lemma first_pass_update_diff_row : forall (labels : labeling) (x y x' y' : nat) (label : nat),
  y <> y' ->
  (fun c' : coord => 
    match c' with 
    | pair x2 y2 => if (x =? x2) && (y =? y2) then label else labels c'
    end) (pair x' y') = 
  labels (pair x' y').
Proof.
  intros labels x y x' y' label Hy.
  simpl.
  destruct (x =? x') eqn:Hx; destruct (y =? y') eqn:Heqy; simpl.
  - apply Nat.eqb_eq in Heqy. contradiction.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** first_pass_row with fuel 0 returns inputs unchanged *)
Lemma first_pass_row_fuel_0 : 
  forall img adj labels equiv y x next_label,
  first_pass_row img adj labels equiv y x 0 next_label = (labels, equiv, next_label).
Proof.
  intros. simpl. reflexivity.
Qed.

(** first_pass_row with x >= width returns inputs unchanged *)
Lemma first_pass_row_out_of_bounds :
  forall img adj labels equiv y x fuel next_label,
  x >= width img ->
  first_pass_row img adj labels equiv y x (S fuel) next_label = (labels, equiv, next_label).
Proof.
  intros img adj labels equiv y x fuel next_label Hwidth.
  simpl.
  assert (x <? width img = false).
  { apply Nat.ltb_ge. exact Hwidth. }
  rewrite H.
  reflexivity.
Qed.

(** first_pass_row on background pixel recurses without changing labels *)
Lemma first_pass_row_background_pixel :
  forall img adj labels equiv y x fuel next_label,
  x < width img ->
  get_pixel img (pair x y) = false ->
  first_pass_row img adj labels equiv y x (S fuel) next_label =
  first_pass_row img adj labels equiv y (S x) fuel next_label.
Proof.
  intros img adj labels equiv y x fuel next_label Hlt Hpixel.
  simpl.
  rewrite (proj2 (Nat.ltb_lt _ _) Hlt).
  rewrite Hpixel.
  reflexivity.
Qed.

(** The new_labels function in first_pass_row only differs at the current pixel *)
Lemma first_pass_row_update_current_only :
  forall (labels : labeling) (x y : nat) (label : nat) (x' y' : nat),
  pair x y <> pair x' y' ->
  (fun c' : coord => match c' with
                     | pair x2 y2 => if (x =? x2) && (y =? y2) then label else labels c'
                     end) (pair x' y') = labels (pair x' y').
Proof.
  intros labels x y label x' y' Hneq.
  simpl.
  destruct (x =? x') eqn:Hx; destruct (y =? y') eqn:Hy; simpl.
  - apply Nat.eqb_eq in Hx. apply Nat.eqb_eq in Hy.
    subst. contradiction Hneq. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** Extract labels from first_pass_row result *)
Lemma first_pass_row_labels_component :
  forall img adj labels equiv y x fuel next_label,
  let result := first_pass_row img adj labels equiv y x fuel next_label in
  let '(labels', _, _) := result in
  labels' = fst (fst result).
Proof.
  intros.
  destruct result as [[labels' equiv'] next'].
  simpl. reflexivity.
Qed.

(** first_pass_row preserves labels on different rows - explicit version *)
Lemma first_pass_row_preserves_diff_row :
  forall fuel img adj labels equiv y x next_label y' x',
  y' <> y ->
  let result := first_pass_row img adj labels equiv y x fuel next_label in
  let '(labels', _, _) := result in
  labels' (pair x' y') = labels (pair x' y').
Proof.
  induction fuel as [|fuel IH]; intros img adj labels equiv y x next_label y' x' Hy.
  - simpl. reflexivity.
  - simpl.
    destruct (x <? width img) eqn:Hlt; [|reflexivity].
    destruct (get_pixel img (pair x y)) eqn:Hpixel.
    + (* Foreground pixel *)
      assert (Hy_sym: y <> y') by (intros H; apply Hy; symmetry; exact H).
      destruct (x =? 0) eqn:Hx0;
      destruct (adj (pair (pred x) y) (pair x y)) eqn:Hadj_left;
      destruct (y =? 0) eqn:Hy0;
      destruct (adj (pair x (pred y)) (pair x y)) eqn:Hadj_up;
      try destruct (labels (pair (pred x) y)) eqn:Hleft;
      try destruct (labels (pair x (pred y))) eqn:Hup;
      (* Apply IH to the recursive call *)
      match goal with
      | |- context[first_pass_row img adj ?new_labels ?new_equiv y (S x) fuel ?new_next] =>
        specialize (IH img adj new_labels new_equiv y (S x) new_next y' x' Hy);
        remember (first_pass_row img adj new_labels new_equiv y (S x) fuel new_next) as rec_result;
        destruct rec_result as [[rec_labels rec_equiv] rec_next];
        simpl in IH; simpl;
        rewrite IH;
        apply first_pass_update_diff_row; exact Hy_sym
      end.
    + (* Background pixel *)
      apply IH. exact Hy.
Qed.

(** first_pass_row preserves labels on different rows - cleaner version *)
Lemma first_pass_row_preserves_diff_row_v2 :
  forall fuel img adj labels equiv y x next_label labels' equiv' next' y' x',
  y' <> y ->
  first_pass_row img adj labels equiv y x fuel next_label = (labels', equiv', next') ->
  labels' (pair x' y') = labels (pair x' y').
Proof.
  intros fuel img adj labels equiv y x next_label labels' equiv' next' y' x' Hy Heq.
  generalize (first_pass_row_preserves_diff_row fuel img adj labels equiv y x next_label y' x' Hy).
  rewrite Heq.
  simpl.
  intros H. exact H.
Qed.

(** first_pass_rows preserves labels on future rows *)
Lemma first_pass_rows_preserves_future_rows :
  forall fuel img adj labels equiv y next_label y' x',
  y' >= y + fuel ->
  let result := first_pass_rows img adj labels equiv y fuel next_label in
  let '(labels', _, _) := result in
  labels' (pair x' y') = labels (pair x' y').
Proof.
  induction fuel as [|fuel IH]; intros img adj labels equiv y next_label y' x' Hfuture.
  - simpl. reflexivity.
  - simpl.
    destruct (y <? height img) eqn:Hlt; [|reflexivity].
    assert (Hdiff: y' <> y) by lia.
    unfold process_row.
    destruct (first_pass_row img adj labels equiv y 0 (width img) next_label) as [[row_labels row_equiv] row_next] eqn:Hrow.
    assert (Hpreserve: row_labels (pair x' y') = labels (pair x' y')).
    { apply (first_pass_row_preserves_diff_row_v2 (width img) img adj labels equiv y 0 next_label row_labels row_equiv row_next y' x' Hdiff Hrow). }
    specialize (IH img adj row_labels row_equiv (S y) row_next y' x').
    assert (y' >= S y + fuel) by lia.
    specialize (IH H).
    destruct (first_pass_rows img adj row_labels row_equiv (S y) fuel row_next) as [[rec_labels rec_equiv] rec_next] eqn:Hrec.
    simpl in IH. simpl.
    rewrite IH. exact Hpreserve.
Qed.

(** empty_labeling assigns 0 to all pixels *)
Lemma empty_labeling_all_zero : forall c,
  empty_labeling c = 0.
Proof.
  intro c. reflexivity.
Qed.

(** The label update in first_pass_row only changes one pixel *)
Lemma first_pass_label_update_at : forall (labels : labeling) (x y : nat) (label : nat) (x' y' : nat),
  (fun c' : coord => 
    match c' with 
    | pair x2 y2 => if (x =? x2) && (y =? y2) then label else labels c'
    end) (pair x' y') =
  if coord_eq (pair x y) (pair x' y') then label else labels (pair x' y').
Proof.
  intros labels x y label x' y'.
  unfold coord_eq.
  simpl.
  reflexivity.
Qed.

(** If a pixel is background, any label update at a different coordinate preserves its zero label *)
Lemma background_label_update_preserves_zero : forall (img : bounded_image) (labels : labeling) x y label c,
  get_pixel img c = false ->
  labels c = 0 ->
  coord_eq (pair x y) c = false ->
  (fun c' : coord => 
    match c' with 
    | pair x2 y2 => if (x =? x2) && (y =? y2) then label else labels c'
    end) c = 0.
Proof.
  intros img labels x y label c Hbg Hzero Hneq.
  destruct c as [xc yc].
  simpl.
  destruct (x =? xc) eqn:Hx; destruct (y =? yc) eqn:Hy; simpl.
  - (* x = xc and y = yc, but coord_eq says they're different - contradiction *)
    unfold coord_eq in Hneq.
    rewrite Hx in Hneq. rewrite Hy in Hneq.
    simpl in Hneq. discriminate.
  - exact Hzero.
  - exact Hzero.
  - exact Hzero.
Qed.

(** The update function assigns the new label at the target coordinate *)
Lemma label_update_at_target : forall (labels : labeling) x y label,
  (fun c' : coord => 
    match c' with 
    | pair x2 y2 => if (x =? x2) && (y =? y2) then label else labels c'
    end) (pair x y) = label.
Proof.
  intros labels x y label.
  simpl.
  rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(** Label updates in first_pass_row preserve zero for background pixels *)
Lemma foreground_update_preserves_background_zero : forall (img : bounded_image) (labels : labeling) x y label,
  (forall c, get_pixel img c = false -> labels c = 0) ->
  get_pixel img (pair x y) = true ->
  forall c, get_pixel img c = false ->
    (fun c' : coord => 
      match c' with 
      | pair x2 y2 => if (x =? x2) && (y =? y2) then label else labels c'
      end) c = 0.
Proof.
  intros img labels x y label Hinv Hfg c Hbg.
  destruct c as [xc yc].
  simpl.
  destruct (x =? xc) eqn:Hx; destruct (y =? yc) eqn:Hy; simpl.
  - (* x = xc and y = yc *)
    apply Nat.eqb_eq in Hx. apply Nat.eqb_eq in Hy.
    subst. rewrite Hbg in Hfg. discriminate.
  - apply Hinv. exact Hbg.
  - apply Hinv. exact Hbg.
  - apply Hinv. exact Hbg.
Qed.

(** The exact pattern match form used in first_pass_row *)
Lemma first_pass_update_pattern : forall (labels : labeling) x y (label : nat) c,
  match c with 
  | pair x2 y2 => if (x =? x2) && (y =? y2) then label else labels c
  end =
  (fun c' : coord => 
    match c' with 
    | pair x2 y2 => if (x =? x2) && (y =? y2) then label else labels c'
    end) c.
Proof.
  intros labels x y label c.
  destruct c as [xc yc].
  reflexivity.
Qed.

(** If we're updating at a foreground pixel, background pixels stay 0 *)
Lemma update_at_foreground_preserves_background : forall img labels x y label c,
  get_pixel img (pair x y) = true ->
  get_pixel img c = false ->
  (forall c', get_pixel img c' = false -> labels c' = 0) ->
  match c with 
  | pair x2 y2 => if (x =? x2) && (y =? y2) then label else labels c
  end = 0.
Proof.
  intros img labels x y label c Hfg Hbg Hinv.
  destruct c as [xc yc].
  destruct (x =? xc) eqn:Hx; destruct (y =? yc) eqn:Hy; simpl.
  - (* x = xc and y = yc, so c = (x,y) *)
    apply Nat.eqb_eq in Hx. apply Nat.eqb_eq in Hy.
    subst. rewrite Hfg in Hbg. discriminate.
  - apply Hinv. exact Hbg.
  - apply Hinv. exact Hbg.
  - apply Hinv. exact Hbg.
Qed.

(** Helper that matches the exact pattern in first_pass_row *)
Lemma update_preserves_background_exact : forall img labels x y label c,
  get_pixel img (pair x y) = true ->
  get_pixel img c = false ->
  (forall c', get_pixel img c' = false -> labels c' = 0) ->
  (if let (x2, y2) := c in (x =? x2) && (y =? y2) then label else labels c) = 0.
Proof.
  intros img labels x y label c Hfg Hbg Hinv.
  destruct c as [xc yc].
  destruct (x =? xc) eqn:Hx; destruct (y =? yc) eqn:Hy; simpl.
  - (* x = xc and y = yc, so c = (x,y) *)
    apply Nat.eqb_eq in Hx. apply Nat.eqb_eq in Hy.
    subst. rewrite Hfg in Hbg. discriminate.
  - apply Hinv. exact Hbg.
  - apply Hinv. exact Hbg.
  - apply Hinv. exact Hbg.
Qed.

(** first_pass_row preserves zero labels for background pixels - fixed version *)
Lemma first_pass_row_preserves_background_zero_v2 :
  forall fuel img adj labels equiv y x next_label,
  (forall c, get_pixel img c = false -> labels c = 0) ->
  let '(labels', _, _) := first_pass_row img adj labels equiv y x fuel next_label in
  forall c, get_pixel img c = false -> labels' c = 0.
Proof.
  induction fuel as [|fuel IH]; intros img adj labels equiv y x next_label Hinv.
  - simpl. exact Hinv.
  - simpl.
    destruct (x <? width img) eqn:Hwidth; [|exact Hinv].
    destruct (get_pixel img (pair x y)) eqn:Hpixel.
    + (* Foreground pixel case *)
      destruct (x =? 0) eqn:Hx0;
      destruct (y =? 0) eqn:Hy0;
      try destruct (adj (pair (pred x) y) (pair x y)) eqn:Hadj_left;
      try destruct (adj (pair x (pred y)) (pair x y)) eqn:Hadj_up;
      try destruct (labels (pair (pred x) y)) eqn:Hleft;
      try destruct (labels (pair x (pred y))) eqn:Hup;
      apply IH;
      intros c' Hbg';
      apply update_preserves_background_exact with img;
      assumption.
    + (* Background pixel - just recurse *)
      apply IH. exact Hinv.
Qed.

(** first_pass_rows preserves zero labels for background pixels *)
Lemma first_pass_rows_preserves_background_zero :
  forall fuel img adj labels equiv y next_label,
  (forall c, get_pixel img c = false -> labels c = 0) ->
  let '(labels', _, _) := first_pass_rows img adj labels equiv y fuel next_label in
  forall c, get_pixel img c = false -> labels' c = 0.
Proof.
  induction fuel as [|fuel IH]; intros img adj labels equiv y next_label Hinv.
  - simpl. exact Hinv.
  - simpl.
    destruct (y <? height img) eqn:Hheight; [|exact Hinv].
    unfold process_row.
    destruct (first_pass_row img adj labels equiv y 0 (width img) next_label) as [[row_labels row_equiv] row_next] eqn:Hrow.
    apply IH.
    intros c Hbg.
    generalize (first_pass_row_preserves_background_zero_v2 (width img) img adj labels equiv y 0 next_label Hinv).
    rewrite Hrow. simpl.
    intro H. apply H. exact Hbg.
Qed.

(** first_pass assigns 0 to background pixels *)
Lemma first_pass_labels_background :
  forall img adj,
  let '(labels, _, _) := first_pass img adj in
  forall c, get_pixel img c = false -> labels c = 0.
Proof.
  intros img adj.
  unfold first_pass.
  remember (first_pass_rows img adj empty_labeling empty_equiv 0 (height img) 1) as result.
  destruct result as [[labels equiv] next].
  intros c Hbg.
  generalize (first_pass_rows_preserves_background_zero (height img) img adj empty_labeling empty_equiv 0 1).
  rewrite <- Heqresult. simpl.
  intro H.
  apply H.
  - intros c' _. apply empty_labeling_all_zero.
  - exact Hbg.
Qed.

(** If a pixel at (x,y) is foreground, first_pass_row will give it a non-zero label *)
Lemma first_pass_row_labels_current_pixel :
  forall img adj labels equiv y x next_label,
  x < width img ->
  get_pixel img (pair x y) = true ->
  next_label > 0 ->
  let '(labels', _, _) := first_pass_row img adj labels equiv y x 1 next_label in
  labels' (pair x y) > 0.
Proof.
  intros img adj labels equiv y x next_label Hwidth Hfg Hpos.
  simpl.
  rewrite (proj2 (Nat.ltb_lt _ _) Hwidth).
  rewrite Hfg.
  destruct (x =? 0) eqn:Hx0;
  destruct (y =? 0) eqn:Hy0;
  try destruct (adj (pair (pred x) y) (pair x y)) eqn:Hadj_left;
  try destruct (adj (pair x (pred y)) (pair x y)) eqn:Hadj_up;
  try destruct (labels (pair (pred x) y)) eqn:Hleft;
  try destruct (labels (pair x (pred y))) eqn:Hup;
  simpl; rewrite Nat.eqb_refl; rewrite Nat.eqb_refl; simpl;
  try lia;
  try (apply Nat.lt_0_succ);
  try (apply Nat.min_glb_lt_iff; split; lia).
Qed.

(** next_label is always positive in first_pass_row *)
Lemma first_pass_row_next_label_positive :
  forall fuel img adj labels equiv y x next_label,
  next_label > 0 ->
  let '(_, _, next') := first_pass_row img adj labels equiv y x fuel next_label in
  next' > 0.
Proof.
  induction fuel as [|fuel IH]; intros img adj labels equiv y x next_label Hpos.
  - simpl. exact Hpos.
  - simpl.
    destruct (x <? width img) eqn:Hwidth; [|exact Hpos].
    destruct (get_pixel img (pair x y)) eqn:Hpixel.
    + (* Foreground pixel *)
      destruct (x =? 0) eqn:Hx0;
      destruct (y =? 0) eqn:Hy0;
      try destruct (adj (pair (pred x) y) (pair x y)) eqn:Hadj_left;
      try destruct (adj (pair x (pred y)) (pair x y)) eqn:Hadj_up;
      try destruct (labels (pair (pred x) y)) eqn:Hleft;
      try destruct (labels (pair x (pred y))) eqn:Hup;
      apply IH; lia.
    + (* Background pixel *)
      apply IH. exact Hpos.
Qed.

(** Simplified: first_pass_row never decreases next_label in one step *)
Lemma first_pass_row_single_step_monotone :
  forall img adj labels equiv y x next_label,
  let '(_, _, next') := first_pass_row img adj labels equiv y x 1 next_label in
  next' >= next_label.
Proof.
  intros img adj labels equiv y x next_label.
  simpl.
  destruct (x <? width img) eqn:Hwidth; [|lia].
  destruct (get_pixel img (pair x y)) eqn:Hpixel; [|simpl; lia].
  (* Foreground pixel *)
  destruct (x =? 0) eqn:Hx0;
  destruct (y =? 0) eqn:Hy0;
  try destruct (adj (pair (pred x) y) (pair x y)) eqn:Hadj_left;
  try destruct (adj (pair x (pred y)) (pair x y)) eqn:Hadj_up;
  try destruct (labels (pair (pred x) y));
  try destruct (labels (pair x (pred y)));
  simpl; lia.
Qed.

(** Helper 1: Out of bounds case *)
Lemma first_pass_row_out_of_bounds_monotone :
  forall img adj labels equiv y x fuel next_label,
  x >= width img ->
  first_pass_row img adj labels equiv y x (S fuel) next_label = (labels, equiv, next_label).
Proof.
  intros img adj labels equiv y x fuel next_label Hbound.
  simpl.
  assert (x <? width img = false) by (apply Nat.ltb_ge; exact Hbound).
  rewrite H.
  reflexivity.
Qed.

(** Helper 2: Background pixel case *)
Lemma first_pass_row_background_monotone :
  forall img adj labels equiv y x fuel next_label,
  x < width img ->
  get_pixel img (pair x y) = false ->
  first_pass_row img adj labels equiv y x (S fuel) next_label =
  first_pass_row img adj labels equiv y (S x) fuel next_label.
Proof.
  intros img adj labels equiv y x fuel next_label Hlt Hbg.
  simpl.
  rewrite (proj2 (Nat.ltb_lt _ _) Hlt).
  rewrite Hbg.
  reflexivity.
Qed.

(** Helper 3: When x = 0 and y = 0, we always get a new label *)
Lemma first_pass_row_origin_new_label :
  forall img adj labels equiv fuel next_label,
  0 < width img ->
  get_pixel img (pair 0 0) = true ->
  first_pass_row img adj labels equiv 0 0 (S fuel) next_label =
  first_pass_row img adj 
    (fun c' => match c' with 
               | pair x2 y2 => if (0 =? x2) && (0 =? y2) then next_label else labels c'
               end)
    equiv 0 1 fuel (S next_label).
Proof.
  intros img adj labels equiv fuel next_label Hwidth Hfg.
  simpl.
  rewrite (proj2 (Nat.ltb_lt _ _) Hwidth).
  rewrite Hfg.
  f_equal.
  apply functional_extensionality.
  intros [x y].
  reflexivity.
Qed.
