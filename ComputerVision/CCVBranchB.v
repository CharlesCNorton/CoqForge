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

Require Import Coq.Init.Prelude.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Open Scope nat_scope.

(** * Section 1: Foundations - Basic Types and Definitions
    
    This section establishes the fundamental types for image processing:
    coordinates, images, labelings, and basic utility functions. *)

(** ** Coordinate System *)

Definition coord : Type := nat * nat.

Definition coord_x (c : coord) : nat := fst c.
Definition coord_y (c : coord) : nat := snd c.

Definition coord_eqb (c1 c2 : coord) : bool :=
  match c1, c2 with
  | (x1, y1), (x2, y2) => andb (Nat.eqb x1 x2) (Nat.eqb y1 y2)
  end.

(** ** Images *)

Record image : Type := mkImage {
  width : nat;
  height : nat;
  pixels : coord -> bool
}.

Definition in_bounds (img : image) (c : coord) : bool :=
  andb (Nat.ltb (coord_x c) (width img)) 
       (Nat.ltb (coord_y c) (height img)).

Definition get_pixel (img : image) (c : coord) : bool :=
  if in_bounds img c then pixels img c else false.

(** ** Labelings *)

Definition labeling : Type := coord -> nat.

Definition empty_labeling : labeling := fun _ => 0.

(** ** Adjacency Relations *)

Definition abs_diff (a b : nat) : nat :=
  if a <=? b then b - a else a - b.

Definition adjacent_4 (c1 c2 : coord) : bool :=
  let dx := abs_diff (coord_x c1) (coord_x c2) in
  let dy := abs_diff (coord_y c1) (coord_y c2) in
  andb (Nat.eqb (dx + dy) 1) (orb (Nat.eqb dx 0) (Nat.eqb dy 0)).

Definition adjacent_8 (c1 c2 : coord) : bool :=
  let dx := abs_diff (coord_x c1) (coord_x c2) in
  let dy := abs_diff (coord_y c1) (coord_y c2) in
  andb (andb (Nat.leb dx 1) (Nat.leb dy 1)) 
       (negb (andb (Nat.eqb dx 0) (Nat.eqb dy 0))).

(** ** Scan Order *)

(** Raster scan order: row-by-row from top to bottom, 
    left-to-right within each row *)
Definition raster_lt (c1 c2 : coord) : bool :=
  orb (Nat.ltb (coord_y c1) (coord_y c2))
      (andb (Nat.eqb (coord_y c1) (coord_y c2))
            (Nat.ltb (coord_x c1) (coord_x c2))).

(** ** Prior Neighbors for Different Connectivities *)

Definition prior_neighbors_4 (c : coord) : list coord :=
  let x := coord_x c in
  let y := coord_y c in
  (if 0 <? x then [(x - 1, y)] else []) ++     (* left *)
  (if 0 <? y then [(x, y - 1)] else []).       (* up *)

Definition prior_neighbors_8 (c : coord) : list coord :=
  let x := coord_x c in
  let y := coord_y c in
  (if andb (0 <? x) (0 <? y) then [(x - 1, y - 1)] else []) ++  (* up-left *)
  (if 0 <? y then [(x, y - 1)] else []) ++                      (* up *)
  (if andb (x <? x + 1) (0 <? y) then [(x + 1, y - 1)] else []) ++ (* up-right *)
  (if 0 <? x then [(x - 1, y)] else []).                        (* left *)

(** ** Basic Properties *)

Lemma coord_eqb_refl : forall c,
  coord_eqb c c = true.
Proof.
  intros [x y]. unfold coord_eqb. 
  rewrite !Nat.eqb_refl. reflexivity.
Qed.

Lemma coord_eqb_sym : forall c1 c2,
  coord_eqb c1 c2 = coord_eqb c2 c1.
Proof.
  intros [x1 y1] [x2 y2]. unfold coord_eqb.
  rewrite (Nat.eqb_sym x1 x2), (Nat.eqb_sym y1 y2). 
  reflexivity.
Qed.

Lemma coord_eqb_true_iff : forall c1 c2,
  coord_eqb c1 c2 = true <-> c1 = c2.
Proof.
  intros [x1 y1] [x2 y2]. unfold coord_eqb.
  rewrite andb_true_iff, !Nat.eqb_eq.
  split.
  - intros [Hx Hy]. f_equal; assumption.
  - intros H. injection H. intros Hy Hx. split; assumption.
Qed.

Lemma abs_diff_sym : forall a b,
  abs_diff a b = abs_diff b a.
Proof.
  intros a b. unfold abs_diff.
  destruct (a <=? b) eqn:Hab; destruct (b <=? a) eqn:Hba.
  - apply Nat.leb_le in Hab, Hba. 
    assert (a = b) by lia. subst. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Nat.leb_nle in Hab, Hba. lia.
Qed.

Lemma abs_diff_zero : forall a,
  abs_diff a a = 0.
Proof.
  intros a. unfold abs_diff.
  rewrite Nat.leb_refl, Nat.sub_diag. reflexivity.
Qed.

Lemma adjacent_4_sym : forall c1 c2,
  adjacent_4 c1 c2 = adjacent_4 c2 c1.
Proof.
  intros c1 c2. unfold adjacent_4.
  rewrite (abs_diff_sym (coord_x c1) (coord_x c2)).
  rewrite (abs_diff_sym (coord_y c1) (coord_y c2)).
  reflexivity.
Qed.

Lemma adjacent_8_sym : forall c1 c2,
  adjacent_8 c1 c2 = adjacent_8 c2 c1.
Proof.
  intros c1 c2. unfold adjacent_8.
  rewrite (abs_diff_sym (coord_x c1) (coord_x c2)).
  rewrite (abs_diff_sym (coord_y c1) (coord_y c2)).
  reflexivity.
Qed.

Lemma adjacent_4_irrefl : forall c,
  adjacent_4 c c = false.
Proof.
  intros c. unfold adjacent_4.
  rewrite !abs_diff_zero, Nat.add_0_r, !Nat.eqb_refl.
  reflexivity.
Qed.

Lemma adjacent_8_irrefl : forall c,
  adjacent_8 c c = false.
Proof.
  intros c. unfold adjacent_8.
  rewrite !abs_diff_zero.
  simpl.
  reflexivity.
Qed.

Lemma get_pixel_out_of_bounds : forall img c,
  in_bounds img c = false -> get_pixel img c = false.
Proof.
  intros img c H. unfold get_pixel. rewrite H. reflexivity.
Qed.

Lemma raster_lt_trans : forall c1 c2 c3,
  raster_lt c1 c2 = true ->
  raster_lt c2 c3 = true ->
  raster_lt c1 c3 = true.
Proof.
  intros [x1 y1] [x2 y2] [x3 y3] H12 H23.
  unfold raster_lt, coord_x, coord_y in *.
  simpl in *.
  apply orb_prop in H12, H23.
  destruct H12 as [Hy12 | Hxy12], H23 as [Hy23 | Hxy23].
  - (* y1 < y2 and y2 < y3 *)
    apply Nat.ltb_lt in Hy12, Hy23.
    assert (y1 <? y3 = true) by (apply Nat.ltb_lt; lia).
    rewrite H. reflexivity.
  - (* y1 < y2 and y2 = y3 with x2 < x3 *)
    apply andb_prop in Hxy23. destruct Hxy23 as [Hy23 Hx23].
    apply Nat.eqb_eq in Hy23. apply Nat.ltb_lt in Hy12. subst y3.
    assert (y1 <? y2 = true) by (apply Nat.ltb_lt; assumption).
    rewrite H. reflexivity.
  - (* y1 = y2 with x1 < x2 and y2 < y3 *)
    apply andb_prop in Hxy12. destruct Hxy12 as [Hy12 Hx12].
    apply Nat.eqb_eq in Hy12. apply Nat.ltb_lt in Hy23. subst y2.
    assert (y1 <? y3 = true) by (apply Nat.ltb_lt; assumption).
    rewrite H. reflexivity.
  - (* y1 = y2 with x1 < x2 and y2 = y3 with x2 < x3 *)
    apply andb_prop in Hxy12, Hxy23.
    destruct Hxy12 as [Hy12 Hx12], Hxy23 as [Hy23 Hx23].
    apply Nat.eqb_eq in Hy12, Hy23.
    apply Nat.ltb_lt in Hx12, Hx23.
    subst y2 y3.
    rewrite Nat.eqb_refl. simpl.
    assert (x1 <? x3 = true) by (apply Nat.ltb_lt; lia).
    rewrite H.
    rewrite orb_true_r. reflexivity.
Qed.

Lemma raster_lt_irrefl : forall c,
  raster_lt c c = false.
Proof.
  intros [x y]. unfold raster_lt, coord_x, coord_y.
  rewrite Nat.ltb_irrefl, Nat.eqb_refl.
  simpl. apply Nat.ltb_irrefl.
Qed.

(** ** Properties of Prior Neighbors *)

Lemma prior_neighbors_4_before : forall c c',
  In c' (prior_neighbors_4 c) ->
  raster_lt c' c = true.
Proof.
  intros [x y] [x' y'] H.
  unfold prior_neighbors_4, coord_x, coord_y in H.
  simpl in H.
  apply in_app_iff in H. destruct H as [H | H].
  - (* left neighbor *)
    case_eq (0 <? x); intro Hx.
    + (* 0 < x is true *)
      rewrite Hx in H.
      simpl in H. destruct H as [H | H]; [|contradiction].
      injection H as Hx' Hy'. subst x' y'.
      unfold raster_lt, coord_x, coord_y. simpl.
      rewrite Nat.ltb_irrefl, Nat.eqb_refl. simpl.
      apply Nat.ltb_lt. apply Nat.ltb_lt in Hx. lia.
    + (* 0 < x is false *)
      rewrite Hx in H. simpl in H. contradiction.
  - (* up neighbor *)
    case_eq (0 <? y); intro Hy.
    + (* 0 < y is true *)
      rewrite Hy in H.
      simpl in H. destruct H as [H | H]; [|contradiction].
      injection H as Hx' Hy'. subst x' y'.
      unfold raster_lt, coord_x, coord_y. simpl.
      assert (Hlt: y - 1 <? y = true).
      { apply Nat.ltb_lt. apply Nat.ltb_lt in Hy. lia. }
      rewrite Hlt. reflexivity.
    + (* 0 < y is false *)
      rewrite Hy in H. simpl in H. contradiction.
Qed.

Lemma prior_neighbors_8_before : forall c c',
  In c' (prior_neighbors_8 c) ->
  raster_lt c' c = true.
Proof.
  intros [x y] [x' y'] H.
  unfold prior_neighbors_8, coord_x, coord_y in H.
  simpl in H.
  repeat (apply in_app_iff in H; destruct H as [H | H]).
  - (* up-left neighbor *)
    case_eq (andb (0 <? x) (0 <? y)); intro Hxy.
    + (* x > 0 and y > 0 *)
      rewrite Hxy in H. simpl in H.
      destruct H as [H | H]; [|contradiction].
      injection H as Hx' Hy'. subst x' y'.
      unfold raster_lt, coord_x, coord_y. simpl.
      (* y - 1 < y, so we're in an earlier row *)
      assert (Hlt: y - 1 <? y = true).
      { apply Nat.ltb_lt. 
        apply andb_prop in Hxy. destruct Hxy as [_ Hy].
        apply Nat.ltb_lt in Hy. lia. }
      rewrite Hlt. reflexivity.
    + (* not (x > 0 and y > 0) *)
      rewrite Hxy in H. simpl in H. contradiction.
  - (* up neighbor *)
    case_eq (0 <? y); intro Hy.
    + (* y > 0 *)
      rewrite Hy in H. simpl in H.
      destruct H as [H | H]; [|contradiction].
      injection H as Hx' Hy'. subst x' y'.
      unfold raster_lt, coord_x, coord_y. simpl.
      assert (Hlt: y - 1 <? y = true).
      { apply Nat.ltb_lt. apply Nat.ltb_lt in Hy. lia. }
      rewrite Hlt. reflexivity.
    + (* y = 0 *)
      rewrite Hy in H. simpl in H. contradiction.
  - (* up-right neighbor *)
    case_eq (andb (x <? x + 1) (0 <? y)); intro Hxy.
    + (* always true when y > 0 *)
      rewrite Hxy in H. simpl in H.
      destruct H as [H | H]; [|contradiction].
      injection H as Hx' Hy'. subst x' y'.
      unfold raster_lt, coord_x, coord_y. simpl.
      (* y - 1 < y, so we're in an earlier row *)
      assert (Hlt: y - 1 <? y = true).
      { apply Nat.ltb_lt.
        apply andb_prop in Hxy. destruct Hxy as [_ Hy].
        apply Nat.ltb_lt in Hy. lia. }
      rewrite Hlt. reflexivity.
    + (* not possible if y > 0 *)
      rewrite Hxy in H. simpl in H. contradiction.
  - (* left neighbor *)
    case_eq (0 <? x); intro Hx.
    + (* x > 0 *)
      rewrite Hx in H. simpl in H.
      destruct H as [H | H]; [|contradiction].
      injection H as Hx' Hy'. subst x' y'.
      unfold raster_lt, coord_x, coord_y. simpl.
      (* Same row, earlier column *)
      rewrite Nat.ltb_irrefl, Nat.eqb_refl. simpl.
      apply Nat.ltb_lt. apply Nat.ltb_lt in Hx. lia.
    + (* x = 0 *)
      rewrite Hx in H. simpl in H. contradiction.
Qed.

(** ** Neighbor Checking *)

Definition check_prior_neighbors_4 (img : image) (c : coord) : list coord :=
  filter (fun c' => andb (get_pixel img c') (adjacent_4 c' c)) 
         (prior_neighbors_4 c).

Definition check_prior_neighbors_8 (img : image) (c : coord) : list coord :=
  filter (fun c' => andb (get_pixel img c') (adjacent_8 c' c)) 
         (prior_neighbors_8 c).

Lemma check_prior_neighbors_4_adjacent : forall img c c',
  In c' (check_prior_neighbors_4 img c) ->
  adjacent_4 c' c = true /\ get_pixel img c' = true.
Proof.
  intros img c c' H.
  unfold check_prior_neighbors_4 in H.
  apply filter_In in H. destruct H as [_ H].
  apply andb_prop in H. destruct H as [H1 H2].
  split; assumption.
Qed.

Lemma check_prior_neighbors_8_adjacent : forall img c c',
  In c' (check_prior_neighbors_8 img c) ->
  adjacent_8 c' c = true /\ get_pixel img c' = true.
Proof.
  intros img c c' H.
  unfold check_prior_neighbors_8 in H.
  apply filter_In in H. destruct H as [_ H].
  apply andb_prop in H. destruct H as [H1 H2].
  split; assumption.
Qed.

(** ** Coordinate Generation *)

Fixpoint seq_coords_row (x_start width y : nat) : list coord :=
  match width with
  | 0 => []
  | S w' => (x_start, y) :: seq_coords_row (S x_start) w' y
  end.

Fixpoint seq_coords (w h : nat) : list coord :=
  match h with
  | 0 => []
  | S h' => seq_coords w h' ++ seq_coords_row 0 w h'
  end.

Definition all_coords (img : image) : list coord :=
  seq_coords (width img) (height img).

Lemma seq_coords_row_in : forall x y x_start width,
  In (x, y) (seq_coords_row x_start width y) <->
  x_start <= x < x_start + width.
Proof.
  intros x y x_start width.
  generalize dependent x_start.
  induction width; intros x_start.
  - simpl. split; intros H.
    + contradiction.
    + lia.
  - simpl. split; intros H.
    + destruct H as [H | H].
      * injection H as Hx. subst. lia.
      * apply IHwidth in H. lia.
    + destruct (Nat.eq_dec x x_start).
      * subst. left. reflexivity.
      * right. apply IHwidth. lia.
Qed.

Lemma seq_coords_row_y : forall x y x_start width y_row,
  In (x, y) (seq_coords_row x_start width y_row) ->
  y = y_row.
Proof.
  intros x y x_start width y_row H.
  generalize dependent x_start.
  induction width; intros x_start H.
  - simpl in H. contradiction.
  - simpl in H. destruct H as [H | H].
    + injection H. intros H0 H1. symmetry. assumption.
    + apply IHwidth in H. assumption.
Qed.

Lemma seq_coords_in : forall x y w h,
  In (x, y) (seq_coords w h) <->
  x < w /\ y < h.
Proof.
  intros x y w h.
  induction h.
  - simpl. split; intros H.
    + contradiction.
    + lia.
  - simpl. rewrite in_app_iff. split; intros H.
    + destruct H as [H | H].
      * apply IHh in H. lia.
      * assert (Hy: y = h) by (apply seq_coords_row_y in H; assumption).
        subst y.
        apply seq_coords_row_in in H. lia.
    + destruct H as [Hx Hy].
      destruct (Nat.lt_decidable y h).
      * left. apply IHh. split; assumption.
      * right. 
        assert (y = h) by lia. subst y.
        apply seq_coords_row_in. lia.
Qed.

Lemma all_coords_complete : forall img c,
  in_bounds img c = true -> In c (all_coords img).
Proof.
  intros img [x y] H.
  unfold all_coords, in_bounds, coord_x, coord_y in *.
  apply andb_prop in H. destruct H as [Hx Hy].
  apply Nat.ltb_lt in Hx, Hy.
  apply seq_coords_in. split; assumption.
Qed.

Lemma all_coords_sound : forall img c,
  In c (all_coords img) -> in_bounds img c = true.
Proof.
  intros img [x y] H.
  unfold all_coords in H.
  apply seq_coords_in in H. destruct H as [Hx Hy].
  unfold in_bounds, coord_x, coord_y.
  apply andb_true_intro. split.
  - apply Nat.ltb_lt. assumption.
  - apply Nat.ltb_lt. assumption.
Qed.

Lemma adjacent_4_manhattan : forall c1 c2,
  adjacent_4 c1 c2 = true <-> 
  abs_diff (coord_x c1) (coord_x c2) + 
  abs_diff (coord_y c1) (coord_y c2) = 1.
Proof.
  intros [x1 y1] [x2 y2].
  unfold adjacent_4, coord_x, coord_y.
  split.
  - intro H.
    apply andb_prop in H. destruct H as [H1 H2].
    apply Nat.eqb_eq in H1. assumption.
  - intro H.
    simpl in H. (* This simplifies fst/snd in H *)
    simpl. (* Simplify fst and snd in goal *)
    apply andb_true_intro. split.
    + apply Nat.eqb_eq. assumption.
    + (* Need to show that one of dx or dy is 0 *)
      destruct (abs_diff x1 x2) eqn:Edx, (abs_diff y1 y2) eqn:Edy.
      * (* dx = 0, dy = 0 *)
        simpl. reflexivity.
      * (* dx = 0, dy = S n *)
        simpl. reflexivity.
      * (* dx = S n, dy = 0 *)
        simpl. reflexivity.
      * (* dx = S n, dy = S n0 *)
        (* This case is impossible: S n + S n0 >= 2 but H says the sum is 1 *)
        exfalso. simpl in H. lia.
Qed.

Lemma prior_neighbors_4_adjacent : forall c c',
  In c' (prior_neighbors_4 c) -> adjacent_4 c' c = true.
Proof.
  intros [x y] [x' y'] H.
  unfold prior_neighbors_4, coord_x, coord_y in H.
  simpl in H.
  apply in_app_iff in H. destruct H as [H | H].
  - (* left neighbor *)
    case_eq (0 <? x); intro Hx.
    + rewrite Hx in H. simpl in H.
      destruct H as [H | H]; [|contradiction].
      injection H as Hx' Hy'. subst x' y'.
      unfold adjacent_4, coord_x, coord_y. simpl.
      rewrite abs_diff_zero.
      assert (H1: abs_diff (x - 1) x = 1).
      { unfold abs_diff. 
        apply Nat.ltb_lt in Hx.
        assert (H0: x - 1 <=? x = true) by (apply Nat.leb_le; lia).
        rewrite H0. lia. }
      rewrite H1. simpl.
      reflexivity.
    + rewrite Hx in H. simpl in H. contradiction.
  - (* up neighbor *)
    case_eq (0 <? y); intro Hy.
    + rewrite Hy in H. simpl in H.
      destruct H as [H | H]; [|contradiction].
      injection H as Hx' Hy'. subst x' y'.
      unfold adjacent_4, coord_x, coord_y. simpl.
      rewrite abs_diff_zero.
      assert (H1: abs_diff (y - 1) y = 1).
      { rewrite abs_diff_sym. unfold abs_diff.
        apply Nat.ltb_lt in Hy.
        assert (H0: y <=? y - 1 = false) by (apply Nat.leb_nle; lia).
        rewrite H0. lia. }
      rewrite H1. simpl.
      reflexivity.
    + rewrite Hy in H. simpl in H. contradiction.
Qed.

Lemma prior_neighbors_8_adjacent : forall c c',
  In c' (prior_neighbors_8 c) -> adjacent_8 c' c = true.
Proof.
  intros [x y] [x' y'] H.
  unfold prior_neighbors_8, coord_x, coord_y in H.
  simpl in H.
  repeat (apply in_app_iff in H; destruct H as [H | H]).
  - (* up-left neighbor *)
    case_eq (andb (0 <? x) (0 <? y)); intro Hxy.
    + rewrite Hxy in H. simpl in H.
      destruct H as [H | H]; [|contradiction].
      injection H as Hx' Hy'. subst x' y'.
      unfold adjacent_8, coord_x, coord_y. simpl.
      apply andb_prop in Hxy. destruct Hxy as [Hx Hy].
      apply Nat.ltb_lt in Hx, Hy.
      assert (H1: abs_diff (x - 1) x = 1).
      { unfold abs_diff. 
        assert (H0: x - 1 <=? x = true) by (apply Nat.leb_le; lia).
        rewrite H0. lia. }
      assert (H2: abs_diff (y - 1) y = 1).
      { unfold abs_diff.
        assert (H0: y - 1 <=? y = true) by (apply Nat.leb_le; lia).
        rewrite H0. lia. }
      rewrite H1, H2. simpl. reflexivity.
    + rewrite Hxy in H. simpl in H. contradiction.
  - (* up neighbor *)
    case_eq (0 <? y); intro Hy.
    + rewrite Hy in H. simpl in H.
      destruct H as [H | H]; [|contradiction].
      injection H as Hx' Hy'. subst x' y'.
      unfold adjacent_8, coord_x, coord_y. simpl.
      rewrite abs_diff_zero.
      apply Nat.ltb_lt in Hy.
      assert (H1: abs_diff (y - 1) y = 1).
      { unfold abs_diff.
        assert (H0: y - 1 <=? y = true) by (apply Nat.leb_le; lia).
        rewrite H0. lia. }
      rewrite H1. simpl. reflexivity.
    + rewrite Hy in H. simpl in H. contradiction.
  - (* up-right neighbor *)
    case_eq (andb (x <? x + 1) (0 <? y)); intro Hxy.
    + rewrite Hxy in H. simpl in H.
      destruct H as [H | H]; [|contradiction].
      injection H as Hx' Hy'. subst x' y'.
      unfold adjacent_8, coord_x, coord_y. simpl.
      apply andb_prop in Hxy. destruct Hxy as [_ Hy].
      apply Nat.ltb_lt in Hy.
      assert (H1: abs_diff (x + 1) x = 1).
      { unfold abs_diff.
        assert (H0: x + 1 <=? x = false) by (apply Nat.leb_nle; lia).
        rewrite H0. lia. }
      assert (H2: abs_diff (y - 1) y = 1).
      { unfold abs_diff.
        assert (H0: y - 1 <=? y = true) by (apply Nat.leb_le; lia).
        rewrite H0. lia. }
      rewrite H1, H2. simpl. reflexivity.
    + rewrite Hxy in H. simpl in H. contradiction.
  - (* left neighbor *)
    case_eq (0 <? x); intro Hx.
    + rewrite Hx in H. simpl in H.
      destruct H as [H | H]; [|contradiction].
      injection H as Hx' Hy'. subst x' y'.
      unfold adjacent_8, coord_x, coord_y. simpl.
      rewrite abs_diff_zero.
      apply Nat.ltb_lt in Hx.
      assert (H1: abs_diff (x - 1) x = 1).
      { unfold abs_diff.
        assert (H0: x - 1 <=? x = true) by (apply Nat.leb_le; lia).
        rewrite H0. lia. }
      rewrite H1. simpl. reflexivity.
    + rewrite Hx in H. simpl in H. contradiction.
Qed.

(** 4-adjacency implies 8-adjacency *)
Lemma adjacent_4_implies_8 : forall c1 c2,
  adjacent_4 c1 c2 = true -> adjacent_8 c1 c2 = true.
Proof.
  intros c1 c2 H.
  unfold adjacent_4, adjacent_8 in *.
  apply andb_prop in H. destruct H as [Hsum Hor].
  apply Nat.eqb_eq in Hsum.
  (* From 4-adjacency: dx + dy = 1 and (dx = 0 or dy = 0) *)
  (* This means either dx = 0, dy = 1 or dx = 1, dy = 0 *)
  apply orb_prop in Hor.
  apply andb_true_intro. split.
  - (* Show dx <= 1 and dy <= 1 *)
    apply andb_true_intro.
    destruct Hor as [Hdx | Hdy].
    + (* dx = 0 *)
      apply Nat.eqb_eq in Hdx. rewrite Hdx in *.
      rewrite Nat.add_0_l in Hsum. rewrite Hsum.
      split; simpl; reflexivity.
    + (* dy = 0 *)
      apply Nat.eqb_eq in Hdy. rewrite Hdy in *.
      rewrite Nat.add_0_r in Hsum. rewrite Hsum.
      split; simpl; reflexivity.
  - (* Show not (dx = 0 and dy = 0) *)
    apply negb_true_iff.
    apply andb_false_iff.
    destruct Hor as [Hdx | Hdy].
    + (* dx = 0, so dy = 1 *)
      apply Nat.eqb_eq in Hdx. rewrite Hdx in *.
      rewrite Nat.add_0_l in Hsum.
      right. apply Nat.eqb_neq. rewrite Hsum. discriminate.
    + (* dy = 0, so dx = 1 *)
      apply Nat.eqb_eq in Hdy. rewrite Hdy in *.
      rewrite Nat.add_0_r in Hsum.
      left. apply Nat.eqb_neq. rewrite Hsum. discriminate.
Qed.

(** Prior neighbors are bounded *)
Lemma prior_neighbors_4_length : forall c,
  length (prior_neighbors_4 c) <= 2.
Proof.
  intros [x y]. unfold prior_neighbors_4, coord_x, coord_y.
  simpl.
  destruct (0 <? x); destruct (0 <? y); simpl; lia.
Qed.

(** ** Examples and Tests *)

Example test_adjacent_4 : 
  adjacent_4 (0, 0) (0, 1) = true /\
  adjacent_4 (0, 0) (1, 0) = true /\
  adjacent_4 (0, 0) (1, 1) = false /\
  adjacent_4 (2, 3) (3, 3) = true.
Proof.
  repeat split; reflexivity.
Qed.

Example test_adjacent_8 :
  adjacent_8 (0, 0) (0, 1) = true /\
  adjacent_8 (0, 0) (1, 0) = true /\
  adjacent_8 (0, 0) (1, 1) = true /\
  adjacent_8 (0, 0) (2, 2) = false.
Proof.
  repeat split; reflexivity.
Qed.

Example test_prior_neighbors_4 :
  prior_neighbors_4 (2, 3) = [(1, 3); (2, 2)].
Proof.
  reflexivity.
Qed.

Example test_prior_neighbors_8 :
  prior_neighbors_8 (2, 3) = [(1, 2); (2, 2); (3, 2); (1, 3)].
Proof.
  reflexivity.
Qed.

(** ** More Examples and Tests *)

(** Examples showing adjacency edge cases *)
Example test_adjacent_4_edge_cases :
  adjacent_4 (0, 0) (0, 0) = false /\  (* not reflexive *)
  adjacent_4 (5, 3) (7, 3) = false /\  (* distance 2 *)
  adjacent_4 (1, 1) (2, 2) = false /\  (* diagonal *)
  adjacent_4 (10, 5) (10, 6) = true /\ (* vertical *)
  adjacent_4 (3, 8) (2, 8) = true.     (* horizontal *)
Proof.
  repeat split; reflexivity.
Qed.

(** Examples showing 8-adjacency includes diagonals *)
Example test_adjacent_8_diagonals :
  adjacent_8 (5, 5) (4, 4) = true /\  (* up-left *)
  adjacent_8 (5, 5) (6, 4) = true /\  (* up-right *)
  adjacent_8 (5, 5) (4, 6) = true /\  (* down-left *)
  adjacent_8 (5, 5) (6, 6) = true.    (* down-right *)
Proof.
  repeat split; reflexivity.
Qed.

(** Examples of raster scan order *)
Example test_raster_lt_ordering :
  raster_lt (0, 0) (1, 0) = true /\   (* same row, left to right *)
  raster_lt (5, 0) (0, 1) = true /\   (* earlier row comes first *)
  raster_lt (2, 3) (2, 3) = false /\  (* not reflexive *)
  raster_lt (3, 2) (1, 3) = true /\   (* row matters more than column *)
  raster_lt (9, 1) (0, 2) = true.     (* even if column is much larger *)
Proof.
  repeat split; reflexivity.
Qed.

(** Examples showing prior neighbors for 4-connectivity *)
Example test_prior_neighbors_4_cases :
  prior_neighbors_4 (0, 0) = [] /\              (* top-left corner *)
  prior_neighbors_4 (3, 0) = [(2, 0)] /\        (* top edge *)
  prior_neighbors_4 (0, 5) = [(0, 4)] /\        (* left edge *)
  prior_neighbors_4 (3, 5) = [(2, 5); (3, 4)].  (* interior *)
Proof.
  repeat split; reflexivity.
Qed.

(** Examples showing prior neighbors for 8-connectivity *)
Example test_prior_neighbors_8_cases :
  prior_neighbors_8 (0, 0) = [] /\                              (* corner *)
  prior_neighbors_8 (1, 0) = [(0, 0)] /\                        (* top edge *)
  prior_neighbors_8 (0, 1) = [(0, 0); (1, 0)] /\               (* left edge *)
  prior_neighbors_8 (1, 1) = [(0, 0); (1, 0); (2, 0); (0, 1)]. (* all 4 *)
Proof.
  repeat split; reflexivity.
Qed.

(** Example showing how check_prior_neighbors filters *)
Definition sample_image : image :=
  mkImage 3 3 (fun c =>
    match c with
    | (0, 0) => true   (* * . . *)
    | (2, 0) => true   (* . . * *)
    | (1, 1) => true   (* . * . *)
    | (0, 2) => true   (* * . . *)
    | (1, 2) => true   (* * * . *)
    | _ => false
    end).

Example test_check_prior_neighbors_4 :
  check_prior_neighbors_4 sample_image (1, 1) = [] /\           (* no adjacent foreground *)
  check_prior_neighbors_4 sample_image (1, 2) = [(0, 2); (1, 1)] /\ (* left and up both on *)
  check_prior_neighbors_4 sample_image (2, 0) = [] /\           (* isolated pixel *)
  check_prior_neighbors_4 sample_image (2, 2) = [(1, 2)].       (* only left is on *)
Proof.
  repeat split; reflexivity.
Qed.

(** Example showing bounds checking *)
Example test_in_bounds :
  let img := mkImage 5 3 (fun _ => true) in
  in_bounds img (0, 0) = true /\
  in_bounds img (4, 2) = true /\   (* max valid coordinate *)
  in_bounds img (5, 2) = false /\  (* x out of bounds *)
  in_bounds img (4, 3) = false /\  (* y out of bounds *)
  in_bounds img (5, 3) = false.    (* both out of bounds *)
Proof.
  repeat split; reflexivity.
Qed.

(** Example showing get_pixel with bounds *)
Example test_get_pixel_bounds :
  let img := mkImage 2 2 (fun c => Nat.eqb (coord_x c + coord_y c) 1) in
  (* Image pattern: . * *)
  (*                * . *)
  get_pixel img (0, 0) = false /\
  get_pixel img (1, 0) = true /\
  get_pixel img (0, 1) = true /\
  get_pixel img (1, 1) = false /\
  get_pixel img (2, 0) = false /\  (* out of bounds returns false *)
  get_pixel img (0, 2) = false.    (* out of bounds returns false *)
Proof.
  repeat split; reflexivity.
Qed.

(** Example showing coordinate generation *)
Example test_seq_coords_small :
  seq_coords 2 2 = [(0, 0); (1, 0); (0, 1); (1, 1)].
Proof.
  reflexivity.
Qed.

Example test_seq_coords_row_single :
  seq_coords_row 3 2 5 = [(3, 5); (4, 5)].  (* 2 pixels starting at x=3, y=5 *)
Proof.
  reflexivity.
Qed.

(** Example showing relationship between prior neighbors and adjacency *)
Example test_prior_neighbors_are_adjacent :
  forall neighbor, In neighbor (prior_neighbors_4 (5, 7)) -> 
    adjacent_4 neighbor (5, 7) = true /\
    raster_lt neighbor (5, 7) = true.
Proof.
  intros neighbor H.
  simpl in H.
  (* H : neighbor = (4, 7) \/ neighbor = (5, 6) \/ False *)
  destruct H as [H | H].
  - (* neighbor = (4, 7) *)
    rewrite <- H. split; reflexivity.
  - destruct H as [H | H].
    + (* neighbor = (5, 6) *)
      rewrite <- H. split; reflexivity.
    + (* False *)
      contradiction.
Qed.

(** Example demonstrating manhattan distance for 4-adjacency *)
Example test_manhattan_distance :
  abs_diff 3 5 = 2 /\
  abs_diff 7 4 = 3 /\
  abs_diff 10 10 = 0 /\
  (abs_diff 3 4 + abs_diff 7 7 = 1) /\  (* This gives 4-adjacency *)
  (abs_diff 3 5 + abs_diff 7 8 = 3).    (* This doesn't *)
Proof.
  repeat split; reflexivity.
Qed.
