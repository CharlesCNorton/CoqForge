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

Definition prior_neighbors_8 (img : image) (c : coord) : list coord :=
  let x := coord_x c in
  let y := coord_y c in
  (if andb (0 <? x) (0 <? y) then [(x - 1, y - 1)] else []) ++  (* up-left *)
  (if 0 <? y then [(x, y - 1)] else []) ++                      (* up *)
  (if andb (x + 1 <? width img) (0 <? y) then [(x + 1, y - 1)] else []) ++ (* up-right *)
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

Lemma prior_neighbors_8_before : forall img c c',
  In c' (prior_neighbors_8 img c) ->
  raster_lt c' c = true.
Proof.
  intros img [x y] [x' y'] H.
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
    case_eq (andb (x + 1 <? width img) (0 <? y)); intro Hxy.
    + (* x + 1 < width and y > 0 *)
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
    + (* not (x + 1 < width and y > 0) *)
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
         (prior_neighbors_8 img c).

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

Lemma prior_neighbors_8_adjacent : forall img c c',
  In c' (prior_neighbors_8 img c) -> adjacent_8 c' c = true.
Proof.
  intros img [x y] [x' y'] H.
  unfold prior_neighbors_8, coord_x, coord_y in H.
  simpl in H.
  repeat (apply in_app_iff in H; destruct H as [H | H]).
  - (* up-left neighbor *)
    destruct (andb (0 <? x) (0 <? y)) eqn:Hxy.
    + (* condition is true *)
      simpl in H.
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
    + (* condition is false *)
      simpl in H. contradiction.
  - (* up neighbor *)
    destruct (0 <? y) eqn:Hy.
    + simpl in H.
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
    + simpl in H. contradiction.
  - (* up-right neighbor *)
    destruct (andb (x + 1 <? width img) (0 <? y)) eqn:Hxy.
    + simpl in H.
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
    + simpl in H. contradiction.
  - (* left neighbor *)
    destruct (0 <? x) eqn:Hx.
    + simpl in H.
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
    + simpl in H. contradiction.
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

Lemma prior_neighbors_4_NoDup : forall c,
  NoDup (prior_neighbors_4 c).
Proof.
  intros [x y].
  unfold prior_neighbors_4, coord_x, coord_y.
  simpl.
  destruct (0 <? x) eqn:Hx; destruct (0 <? y) eqn:Hy.
  - (* x > 0, y > 0: both neighbors exist *)
    apply NoDup_cons.
    + (* (x-1, y) not in [(x, y-1)] *)
      intro H. simpl in H. destruct H as [H | H].
      * (* (x-1, y) = (x, y-1) *)
        injection H as Hx_eq Hy_eq.
        (* x-1 = x is impossible *)
        apply Nat.ltb_lt in Hx. lia.
      * contradiction.
    + apply NoDup_cons.
      * intro H. contradiction.
      * apply NoDup_nil.
  - (* x > 0, y = 0: only left neighbor *)
    apply NoDup_cons.
    + intro H. contradiction.
    + apply NoDup_nil.
  - (* x = 0, y > 0: only up neighbor *)
    apply NoDup_cons.
    + intro H. contradiction.
    + apply NoDup_nil.
  - (* x = 0, y = 0: no neighbors *)
    apply NoDup_nil.
Qed.

(** Helper: If 4-adjacent, one of four relative positions *)
Lemma adjacent_4_cases : forall x y x' y',
  adjacent_4 (x', y') (x, y) = true ->
  (x' = x - 1 /\ y' = y) \/    (* left *)
  (x' = x + 1 /\ y' = y) \/    (* right *)
  (x' = x /\ y' = y - 1) \/    (* up *)
  (x' = x /\ y' = y + 1).      (* down *)
Proof.
  intros x y x' y' Hadj.
  apply adjacent_4_manhattan in Hadj.
  simpl in Hadj.
  (* Manhattan distance 1 means exactly one of dx, dy is 1, other is 0 *)
  destruct (abs_diff x' x) eqn:Edx, (abs_diff y' y) eqn:Edy;
  try (simpl in Hadj; lia).
  - (* dx = 0, dy = S n *)
    simpl in Hadj. assert (n = 0) by lia. subst n.
    unfold abs_diff in Edx, Edy.
    destruct (x' <=? x) eqn:Ex', (y' <=? y) eqn:Ey'.
    + apply Nat.leb_le in Ex', Ey'.
      assert (x = x') by lia.
      assert (y - y' = 1) by lia.
      right. right. left. split; lia.
    + apply Nat.leb_le in Ex'. apply Nat.leb_nle in Ey'.
      assert (x = x') by lia.
      assert (y' - y = 1) by lia.
      right. right. right. split; lia.
    + apply Nat.leb_nle in Ex'. apply Nat.leb_le in Ey'.
      lia.
    + apply Nat.leb_nle in Ex', Ey'. lia.
  - (* dx = S n, dy = 0 *)
    simpl in Hadj. assert (n = 0) by lia. subst n.
    unfold abs_diff in Edx, Edy.
    destruct (x' <=? x) eqn:Ex', (y' <=? y) eqn:Ey'.
    + apply Nat.leb_le in Ex', Ey'.
      assert (y = y') by lia.
      assert (x - x' = 1) by lia.
      left. split; lia.
    + apply Nat.leb_le in Ex'. apply Nat.leb_nle in Ey'.
      assert (y = y') by lia. lia.
    + apply Nat.leb_nle in Ex'. apply Nat.leb_le in Ey'.
      assert (y = y') by lia.
      assert (x' - x = 1) by lia.
      right. left. split; lia.
    + apply Nat.leb_nle in Ex', Ey'.
      assert (y = y') by lia. lia.
Qed.

(** Helper: Raster order constrains relative positions *)
Lemma raster_lt_position : forall x y x' y',
  raster_lt (x', y') (x, y) = true ->
  y' < y \/ (y' = y /\ x' < x).
Proof.
  intros x y x' y' H.
  unfold raster_lt, coord_x, coord_y in H.
  simpl in H.
  apply orb_prop in H.
  destruct H as [Hy | Hxy].
  - left. apply Nat.ltb_lt in Hy. assumption.
  - right. apply andb_prop in Hxy.
    destruct Hxy as [Hy Hx].
    apply Nat.eqb_eq in Hy.
    apply Nat.ltb_lt in Hx.
    split; assumption.
Qed.

(** Helper: Combining adjacency with raster order limits to 2 cases *)
Lemma adjacent_4_before_cases : forall x y x' y',
  adjacent_4 (x', y') (x, y) = true ->
  raster_lt (x', y') (x, y) = true ->
  (x' = x - 1 /\ y' = y /\ x > 0) \/    (* left *)
  (x' = x /\ y' = y - 1 /\ y > 0).      (* up *)
Proof.
  intros x y x' y' Hadj Hbefore.
  apply adjacent_4_cases in Hadj.
  apply raster_lt_position in Hbefore.
  destruct Hadj as [H | [H | [H | H]]].
  - (* left: x' = x - 1, y' = y *)
    destruct H as [Hx' Hy']. subst.
    destruct Hbefore as [Hy_lt | [Hy_eq Hx_lt]].
    + lia.  (* y < y is impossible *)
    + left. split; [reflexivity | split; [reflexivity | lia]].
  - (* right: x' = x + 1, y' = y *)
    destruct H as [Hx' Hy']. subst.
    destruct Hbefore as [Hy_lt | [Hy_eq Hx_lt]].
    + lia.  (* y < y is impossible *)
    + lia.  (* x + 1 < x is impossible *)
  - (* up: x' = x, y' = y - 1 *)
    destruct H as [Hx' Hy']. subst.
    destruct Hbefore as [Hy_lt | [Hy_eq Hx_lt]].
    + right. split; [reflexivity | split; [reflexivity | lia]].
    + lia.  (* y - 1 = y is impossible when y > 0 *)
  - (* down: x' = x, y' = y + 1 *)
    destruct H as [Hx' Hy']. subst.
    destruct Hbefore as [Hy_lt | [Hy_eq Hx_lt]].
    + lia.  (* y + 1 < y is impossible *)
    + lia.  (* y + 1 = y is impossible *)
Qed.

Lemma prior_neighbors_4_complete : forall c c',
  adjacent_4 c' c = true ->
  raster_lt c' c = true ->
  In c' (prior_neighbors_4 c).
Proof.
  intros [x y] [x' y'] Hadj Hbefore.
  apply adjacent_4_before_cases in Hadj; [|assumption].
  unfold prior_neighbors_4, coord_x, coord_y. simpl.
  destruct Hadj as [[Hx' [Hy' Hx_pos]] | [Hx' [Hy' Hy_pos]]].
  - (* left: x' = x - 1, y' = y *)
    subst x' y'.
    assert (0 <? x = true) by (apply Nat.ltb_lt; assumption).
    rewrite H. simpl. left. reflexivity.
  - (* up: x' = x, y' = y - 1 *)
    subst x' y'.
    assert (0 <? y = true) by (apply Nat.ltb_lt; assumption).
    destruct (0 <? x) eqn:Hx.
    + (* x > 0: list is [(x-1,y); (x,y-1)] *)
      rewrite H. simpl. right. left. reflexivity.
    + (* x = 0: list is [(x,y-1)] *)
      rewrite H. simpl. left. reflexivity.
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
  let img := mkImage 10 10 (fun _ => true) in  (* dummy image large enough *)
  prior_neighbors_8 img (2, 3) = [(1, 2); (2, 2); (3, 2); (1, 3)].
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
  let img := mkImage 10 10 (fun _ => true) in  (* dummy image *)
  prior_neighbors_8 img (0, 0) = [] /\                              (* corner *)
  prior_neighbors_8 img (1, 0) = [(0, 0)] /\                        (* top edge *)
  prior_neighbors_8 img (0, 1) = [(0, 0); (1, 0)] /\               (* left edge *)
  prior_neighbors_8 img (1, 1) = [(0, 0); (1, 0); (2, 0); (0, 1)]. (* all 4 *)
Proof.
  repeat split; reflexivity.
Qed. (* all 4 *)

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


(** Example showing a corner case *)
Example test_prior_neighbors_corner :
  let img := mkImage 10 10 (fun _ => true) in  (* dummy image *)
  (* At (0,0), no prior neighbors exist *)
  prior_neighbors_4 (0, 0) = [] /\
  prior_neighbors_8 img (0, 0) = [] /\
  (* At (1,0), only left neighbor *)
  prior_neighbors_4 (1, 0) = [(0, 0)] /\
  prior_neighbors_8 img (1, 0) = [(0, 0)] /\
  (* At (0,1), only up neighbor for 4, but two for 8 *)
  prior_neighbors_4 (0, 1) = [(0, 0)] /\
  prior_neighbors_8 img (0, 1) = [(0, 0); (1, 0)].
Proof.
  repeat split; reflexivity.
Qed.


(** Example demonstrating the relationship between adjacency and prior neighbors *)
Example test_adjacency_prior_relationship :
  forall x y,
    x > 0 -> y > 0 ->
    (* For interior pixels, prior_neighbors_4 has exactly 2 elements *)
    length (prior_neighbors_4 (x, y)) = 2 /\
    (* And they are exactly the left and up neighbors *)
    prior_neighbors_4 (x, y) = [(x-1, y); (x, y-1)].
Proof.
  intros x y Hx Hy.
  unfold prior_neighbors_4, coord_x, coord_y.
  simpl.
  assert (0 <? x = true) by (apply Nat.ltb_lt; assumption).
  assert (0 <? y = true) by (apply Nat.ltb_lt; assumption).
  rewrite H, H0.
  simpl. split; reflexivity.
Qed.

(** Example showing prior_neighbors respects image bounds implicitly *)
Example test_prior_with_small_image :
  let img := mkImage 3 3 (fun c => true) in  (* 3x3 image *)
  let c := (1, 1) in  (* center pixel *)
  (* All prior neighbors are in bounds *)
  forall n, In n (prior_neighbors_4 c) -> in_bounds img n = true.
Proof.
  simpl. intros n H.
  destruct H as [H | [H | H]].
  - rewrite <- H. reflexivity.
  - rewrite <- H. reflexivity.
  - contradiction.
Qed.

(** Example combining everything: checking actual adjacencies *)
Example test_complete_prior_check :
  let img := sample_image in  (* from earlier *)
  let c := (1, 2) in
  (* prior_neighbors_4 finds all candidates *)
  prior_neighbors_4 c = [(0, 2); (1, 1)] /\
  (* check filters to only adjacent foreground *)
  check_prior_neighbors_4 img c = [(0, 2); (1, 1)] /\
  (* These are all the 4-adjacent prior foreground pixels *)
  forall c', get_pixel img c' = true ->
             adjacent_4 c' c = true ->
             raster_lt c' c = true ->
             In c' (check_prior_neighbors_4 img c).
Proof.
  split; [reflexivity | split; [reflexivity |]].
  intros c' Hpix Hadj Hbefore.
  unfold check_prior_neighbors_4.
  apply filter_In. split.
  - apply prior_neighbors_4_complete; assumption.
  - rewrite Hpix, Hadj. reflexivity.
Qed.

(** Examples showing completeness: all valid prior neighbors are found *)
Example test_prior_neighbors_4_complete_concrete :
  (* At position (3,2), the prior 4-neighbors are (2,2) and (3,1) *)
  let c := (3, 2) in
  (* Check that these are indeed in prior_neighbors_4 *)
  In (2, 2) (prior_neighbors_4 c) /\
  In (3, 1) (prior_neighbors_4 c) /\
  (* And these are the only ones *)
  length (prior_neighbors_4 c) = 2.
Proof.
  simpl. split.
  - (* In (2, 2) [(2, 2); (3, 1)] *)
    left. reflexivity.
  - split.
    + (* In (3, 1) [(2, 2); (3, 1)] *)
      right. left. reflexivity.
    + (* length = 2 *)
      reflexivity.
Qed.

(** Example showing completeness captures exactly the right neighbors *)
Example test_4_adjacency_completeness :
  let c := (5, 7) in
  (* Manual check: the only 4-adjacent coords before (5,7) are: *)
  let left := (4, 7) in   (* left neighbor *)
  let up := (5, 6) in     (* up neighbor *)
  (* These are 4-adjacent and before c *)
  (adjacent_4 left c = true /\ raster_lt left c = true) /\
  (adjacent_4 up c = true /\ raster_lt up c = true) /\
  (* And they're in prior_neighbors_4 *)
  prior_neighbors_4 c = [left; up].
Proof.
  simpl. repeat split; reflexivity.
Qed.

(** Alternative: Example showing prior_neighbors_4 finds all valid neighbors *)
Example test_prior_neighbors_finds_all :
  let c := (2, 3) in
  (* Every element in prior_neighbors_4 is 4-adjacent and before c *)
  (forall n, In n (prior_neighbors_4 c) -> 
             adjacent_4 n c = true /\ raster_lt n c = true) /\
  (* Specific check for this position *)
  prior_neighbors_4 c = [(1, 3); (2, 2)].
Proof.
  split.
  - intros n H. simpl in H.
    destruct H as [H | [H | H]].
    + rewrite <- H. simpl. split; reflexivity.
    + rewrite <- H. simpl. split; reflexivity.
    + contradiction.
  - reflexivity.
Qed.

(** Example showing 8-connectivity at image boundary *)
Example test_prior_neighbors_8_boundary :
  let img := mkImage 3 3 (fun _ => true) in
  (* At (2, 1), we're at the right edge *)
  prior_neighbors_8 img (2, 1) = [(1, 0); (2, 0); (1, 1)] /\
  (* Note: (3, 0) is NOT included because x+1 would be out of bounds *)
  (* At (2, 2), bottom-right corner *)
  prior_neighbors_8 img (2, 2) = [(1, 1); (2, 1); (1, 2)].
Proof.
  repeat split; reflexivity.
Qed.

(** Example showing how check_prior_neighbors_8 filters *)
Example test_check_prior_neighbors_8 :
  let img := sample_image in  (* 3x3 image with specific pattern *)
  check_prior_neighbors_8 img (1, 1) = [(0, 0); (2, 0)] /\  (* up-left and up-right *)
  check_prior_neighbors_8 img (1, 2) = [(1, 1); (0, 2)] /\  (* up and left *)
  check_prior_neighbors_8 img (2, 1) = [(2, 0); (1, 1)] /\  (* up and left *)
  check_prior_neighbors_8 img (2, 2) = [(1, 1); (1, 2)].    (* up and left *)
Proof.
  repeat split; reflexivity.
Qed.

(** * Section 2: Union-Find Data Structure
    
    A persistent union-find (disjoint-set) data structure for managing
    label equivalences during connected component labeling. *)

(** ** Core Union-Find *)

Definition uf := nat -> nat.

Definition uf_init : uf := fun x => x.

Definition uf_find (u : uf) (x : nat) : nat := u x.

Definition uf_union (u : uf) (x y : nat) : uf :=
  let px := uf_find u x in
  let py := uf_find u y in
  fun z => if Nat.eqb px (uf_find u z) then py else uf_find u z.

Definition uf_same_set (u : uf) (x y : nat) : bool :=
  Nat.eqb (uf_find u x) (uf_find u y).

(** ** Basic Properties *)

Lemma uf_find_init : forall x,
  uf_find uf_init x = x.
Proof.
  reflexivity.
Qed.

Lemma uf_union_connects : forall u x y,
  let u' := uf_union u x y in
  uf_find u' x = uf_find u' y.
Proof.
  intros u x y.
  unfold uf_union, uf_find.
  simpl.
  (* uf_find u' x = u' x = if (u x =? u x) then u y else u x *)
  rewrite Nat.eqb_refl.
  (* Now we have: u y = u' y *)
  (* u' y = if (u x =? u y) then u y else u y *)
  (* Both branches are u y, so this equals u y *)
  destruct (u x =? u y); reflexivity.
Qed.

Lemma uf_same_set_refl : forall u x,
  uf_same_set u x x = true.
Proof.
  intros u x. unfold uf_same_set.
  apply Nat.eqb_refl.
Qed.

Lemma uf_same_set_sym : forall u x y,
  uf_same_set u x y = uf_same_set u y x.
Proof.
  intros u x y. unfold uf_same_set.
  apply Nat.eqb_sym.
Qed.

Lemma uf_same_set_after_union : forall u x y z,
  uf_same_set u x z = true ->
  uf_same_set (uf_union u x y) y z = true.
Proof.
  intros u x y z H.
  unfold uf_same_set, uf_union, uf_find in *.
  apply Nat.eqb_eq in H.
  simpl.
  (* Need to show: (if u x =? u y then u y else u y) =? (if u x =? u z then u y else u z) = true *)
  (* First simplify the left side *)
  assert (Hy: (if u x =? u y then u y else u y) = u y).
  { destruct (u x =? u y); reflexivity. }
  rewrite Hy.
  (* Now use H: u x = u z *)
  rewrite H.
  rewrite Nat.eqb_refl.
  (* Now we have: u y =? u y = true *)
  apply Nat.eqb_refl.
Qed.

(** ** Integration with CCL *)

(** Build union-find from list of equivalent label pairs *)
Fixpoint uf_from_equiv_list (pairs : list (nat * nat)) : uf :=
  match pairs with
  | [] => uf_init
  | (x, y) :: rest => uf_union (uf_from_equiv_list rest) x y
  end.

(** Apply union-find to resolve a labeling *)
Definition resolve_labels (u : uf) (l : labeling) : labeling :=
  fun c => uf_find u (l c).

(** Check if a label is a representative (root) *)
Definition is_representative (u : uf) (x : nat) : bool :=
  Nat.eqb (uf_find u x) x.

(** Get representative for a label, but preserve 0 (background) *)
Definition get_representative (u : uf) (label : nat) : nat :=
  if Nat.eqb label 0 then 0 else uf_find u label.

(** ** Properties for CCL *)

(** Well-formed union-find preserves 0 as background *)
Definition uf_well_formed (u : uf) : Prop :=
  uf_find u 0 = 0.

(** Initial union-find is well-formed *)
Lemma uf_init_well_formed : uf_well_formed uf_init.
Proof.
  unfold uf_well_formed, uf_init, uf_find.
  reflexivity.
Qed.

Lemma resolve_labels_background : forall u l c,
  uf_find u 0 = 0 ->
  l c = 0 -> 
  resolve_labels u l c = 0.
Proof.
  intros u l c H0 H.
  unfold resolve_labels.
  rewrite H.
  exact H0.
Qed.

Lemma resolve_labels_same_set : forall u l c1 c2,
  l c1 <> 0 ->
  l c2 <> 0 ->
  uf_same_set u (l c1) (l c2) = true ->
  resolve_labels u l c1 = resolve_labels u l c2.
Proof.
  intros u l c1 c2 H1 H2 H.
  unfold resolve_labels, uf_same_set in *.
  apply Nat.eqb_eq in H.
  exact H.
Qed.

Lemma uf_union_preserves_zero : forall u x y,
  uf_find u 0 = 0 ->
  (forall n, n <> 0 -> u n <> 0) ->
  x <> 0 ->
  y <> 0 ->
  uf_find (uf_union u x y) 0 = uf_find u 0.
Proof.
  intros u x y H0 Hinv Hx Hy.
  unfold uf_union, uf_find.
  simpl.
  destruct (u x =? u 0) eqn:E.
  - apply Nat.eqb_eq in E.
    exfalso.
    apply (Hinv x Hx).
    rewrite E.
    exact H0.
  - reflexivity.
Qed.

(** ** Equivalence Classes *)

(** Get all elements in the same equivalence class up to max_label *)
Definition equiv_class_members (u : uf) (x : nat) (max_label : nat) : list nat :=
  filter (fun y => uf_same_set u x y) (seq 1 max_label).

(** Count number of distinct representatives from 1 to max_label *)
Definition count_components (u : uf) (max_label : nat) : nat :=
  length (filter (fun x => is_representative u x) (seq 1 max_label)).

(** ** Correctness Properties *)

Theorem uf_equivalence : forall u,
  (forall x, uf_same_set u x x = true) /\
  (forall x y, uf_same_set u x y = uf_same_set u y x) /\
  (forall x y z, uf_same_set u x y = true -> 
                 uf_same_set u y z = true -> 
                 uf_same_set u x z = true).
Proof.
  intro u.
  split; [|split].
  - apply uf_same_set_refl.
  - apply uf_same_set_sym.
  - intros x y z H1 H2.
    unfold uf_same_set in *.
    apply Nat.eqb_eq in H1, H2.
    apply Nat.eqb_eq.
    congruence.
Qed.

(** Union-find maintains partition property *)
Lemma uf_partition : forall u x y,
  uf_same_set u x y = true \/ uf_same_set u x y = false.
Proof.
  intros u x y.
  destruct (uf_same_set u x y); [left | right]; reflexivity.
Qed.

(** ** Building Equivalences During First Pass *)

(** Record equivalence between adjacent pixels *)
Definition record_adjacency (u : uf) (label1 label2 : nat) : uf :=
  if andb (negb (Nat.eqb label1 0)) (negb (Nat.eqb label2 0)) then
    if Nat.eqb label1 label2 then u else uf_union u label1 label2
  else u.

Lemma record_adjacency_connects : forall u l1 l2,
  l1 <> 0 ->
  l2 <> 0 ->
  l1 <> l2 ->
  uf_same_set (record_adjacency u l1 l2) l1 l2 = true.
Proof.
  intros u l1 l2 H1 H2 H3.
  unfold record_adjacency.
  assert (E1: negb (l1 =? 0) = true) by (apply negb_true_iff; apply Nat.eqb_neq; assumption).
  assert (E2: negb (l2 =? 0) = true) by (apply negb_true_iff; apply Nat.eqb_neq; assumption).
  rewrite E1, E2. simpl.
  assert (E3: l1 =? l2 = false) by (apply Nat.eqb_neq; assumption).
  rewrite E3.
  unfold uf_same_set.
  apply Nat.eqb_eq.
  apply uf_union_connects.
Qed.

(** ** Label Compaction *)

(** Map from old labels to compacted labels (1, 2, 3, ...) *)
Definition build_label_map (u : uf) (max_label : nat) : nat -> nat :=
  let representatives := filter (fun x => is_representative u x) (seq 1 max_label) in
  let fix assign_compact (reps : list nat) (next : nat) (label : nat) : nat :=
    match reps with
    | [] => 0
    | r :: rest =>
        if Nat.eqb (uf_find u label) r then next
        else assign_compact rest (S next) label
    end
  in fun label => 
    if Nat.eqb label 0 then 0 
    else assign_compact representatives 1 label.

(** Apply label map to get final compacted labeling *)
Definition compact_labels (u : uf) (l : labeling) (max_label : nat) : labeling :=
  let label_map := build_label_map u max_label in
  fun c => label_map (l c).

(** ** Properties of Compaction *)

Lemma build_label_map_zero : forall u max_label,
  build_label_map u max_label 0 = 0.
Proof.
  intros u max_label.
  unfold build_label_map.
  reflexivity.
Qed.

Lemma compact_labels_background : forall u l max_label c,
  l c = 0 -> compact_labels u l max_label c = 0.
Proof.
  intros u l max_label c H.
  unfold compact_labels.
  rewrite H.
  apply build_label_map_zero.
Qed.

(** ** Examples and Tests *)

Example test_uf_basic :
  let u0 := uf_init in
  let u1 := uf_union u0 1 2 in
  let u2 := uf_union u1 3 4 in
  let u3 := uf_union u2 2 3 in
  (* Now 1,2,3,4 are all in the same set *)
  uf_same_set u3 1 4 = true /\
  uf_same_set u3 1 5 = false /\
  uf_find u3 0 = 0. (* 0 unchanged *)
Proof.
  simpl. repeat split; reflexivity.
Qed.

Example test_record_adjacency :
  let u0 := uf_init in
  let u1 := record_adjacency u0 1 2 in
  let u2 := record_adjacency u1 0 3 in  (* ignored: has 0 *)
  let u3 := record_adjacency u2 2 2 in  (* ignored: same label *)
  let u4 := record_adjacency u3 2 3 in
  uf_same_set u4 1 3 = true /\
  uf_find u4 0 = 0.
Proof.
  simpl. repeat split; reflexivity.
Qed.

Example test_resolve_labels :
  let l := fun c => match c with
                    | (0, 0) => 1
                    | (1, 0) => 2
                    | (0, 1) => 3
                    | _ => 0
                    end in
  let u := uf_from_equiv_list [(1, 2); (2, 3)] in
  let l' := resolve_labels u l in
  (* All three pixels now have the same label *)
  l' (0, 0) = l' (1, 0) /\
  l' (1, 0) = l' (0, 1) /\
  l' (1, 1) = 0. (* background stays 0 *)
Proof.
  simpl. repeat split; reflexivity.
Qed.

Example test_label_compaction :
  let u := uf_from_equiv_list [(2, 5); (7, 9)] in
  (* Representatives are: 0, 1, 3, 4, 5, 6, 8, 9 *)
  (* But we only count positive labels, so: 1, 3, 4, 5, 6, 8, 9 *)
  (* After union: 1, 3, 4, 5, 6, 8, 9 with 2->5 and 7->9 *)
  (* So representatives are: 1, 3, 4, 5, 6, 8, 9 *)
  let map := build_label_map u 10 in
  map 0 = 0 /\    (* background *)
  map 1 = 1 /\    (* first component *)
  map 2 = 4 /\    (* same as 5 *)
  map 3 = 2 /\    (* second component *)  
  map 4 = 3 /\    (* third component *)
  map 5 = 4 /\    (* fourth component (merged with 2) *)
  map 6 = 5.      (* fifth component *)
Proof.
  simpl. repeat split; reflexivity.
Qed.

(** Alternative test focusing on sequential compaction *)
Example test_sequential_compaction :
  let u := uf_from_equiv_list [(10, 20); (30, 40); (20, 30)] in
  (* Groups: {10,20,30,40} plus singletons 1-9,11-19,21-29,31-39,41-50 *)
  let map := build_label_map u 50 in
  (* All elements in the merged group get the same compacted label *)
  (map 10 = map 20) /\
  (map 20 = map 30) /\
  (map 30 = map 40) /\
  (* Background stays 0 *)
  (map 0 = 0).
Proof.
  simpl. repeat split; reflexivity.
Qed.

(** ** Integration Examples: Combining Image Processing with Union-Find *)

(** Example: Processing a small image strip to show how adjacencies create equivalences *)
Example adjacency_to_equivalence :
  let img := mkImage 4 1 (fun c => negb (Nat.eqb (coord_x c) 2)) in
  (* Image: * * . * *)
  (* Labels would be: 1 2 0 3 *)
  let labels := fun c => match c with
                         | (0, 0) => 1
                         | (1, 0) => 2
                         | (2, 0) => 0
                         | (3, 0) => 3
                         | _ => 0
                         end in
  (* Check prior neighbors at each position *)
  let neighbors_at_1 := check_prior_neighbors_4 img (1, 0) in
  let neighbors_at_3 := check_prior_neighbors_4 img (3, 0) in
  (* Build equivalences from adjacencies *)
  let u := record_adjacency uf_init 1 2 in  (* pixels 0 and 1 are adjacent *)
  let resolved := resolve_labels u labels in
  (* After resolution, pixels 0 and 1 have same label *)
  neighbors_at_1 = [(0, 0)] /\
  neighbors_at_3 = [] /\  (* gap at position 2 *)
  resolved (0, 0) = resolved (1, 0) /\
  resolved (3, 0) = 3.  (* stays separate *)
Proof.
  simpl. repeat split; reflexivity.
Qed.

(** Example: Complete pipeline on a 2x2 image *)
Example complete_pipeline_2x2 :
  let img := mkImage 2 2 (fun c => negb (coord_eqb c (1, 1))) in
  (* Image: * * *)
  (*        * . *)
  (* Initial labels (simulating first pass): *)
  let initial_labels := fun c => match c with
                                 | (0, 0) => 1
                                 | (1, 0) => 2  
                                 | (0, 1) => 3
                                 | (1, 1) => 0
                                 | _ => 0
                                 end in
  (* Adjacencies found during scan: *)
  (* - (1,0) has prior neighbor (0,0): labels 2 and 1 are equivalent *)
  (* - (0,1) has prior neighbor (0,0): labels 3 and 1 are equivalent *)
  let u := uf_from_equiv_list [(2, 1); (3, 1)] in
  let resolved := resolve_labels u initial_labels in
  let final := compact_labels u initial_labels 3 in
  (* All three foreground pixels end up with the same label *)
  (resolved (0, 0) = resolved (1, 0)) /\
  (resolved (1, 0) = resolved (0, 1)) /\
  (resolved (1, 1) = 0) /\
  (* After compaction, they get label 1 *)
  (final (0, 0) = 1) /\
  (final (1, 0) = 1) /\
  (final (0, 1) = 1) /\
  (final (1, 1) = 0).
Proof.
  simpl. repeat split; reflexivity.
Qed.

(** Example: 8-connectivity creating more complex equivalences *)
Example eight_connectivity_equivalence :
  let img := mkImage 3 2 (fun _ => true) in
  (* Image: * * * *)
  (*        * * * *)
  (* With 8-connectivity, pixel (1,1) connects to all prior pixels *)
  let prior := prior_neighbors_8 img (1, 1) in
  let adjacent := check_prior_neighbors_8 img (1, 1) in
  (* If these had labels 1,2,3,4 respectively: *)
  let labels := fun c => match c with
                         | (0, 0) => 1
                         | (1, 0) => 2
                         | (2, 0) => 3
                         | (0, 1) => 4
                         | _ => 0
                         end in
  (* All would need to be marked equivalent *)
  let u := uf_from_equiv_list [(2, 1); (3, 2); (4, 1)] in
  let resolved := resolve_labels u labels in
  (* Verify the prior neighbors *)
  prior = [(0, 0); (1, 0); (2, 0); (0, 1)] /\
  adjacent = [(0, 0); (1, 0); (2, 0); (0, 1)] /\
  (* All get the same label after resolution *)
  (resolved (0, 0) = resolved (1, 0)) /\
  (resolved (1, 0) = resolved (2, 0)) /\
  (resolved (2, 0) = resolved (0, 1)).
Proof.
  simpl. repeat split; reflexivity.
Qed.

(** Example: Demonstrating why we need union-find *)
Example why_union_find_needed :
  let img := mkImage 4 1 (fun _ => true) in
  (* Image: * * * * *)
  (* Processing left to right: *)
  (* Position 0: gets label 1 *)
  (* Position 1: sees 0, gets label 1 *)  
  (* Position 2: sees 1, gets label 1 *)
  (* Position 3: sees 2, gets label 1 *)
  (* BUT what if we had assigned differently? *)
  let labels_alt := fun c => match coord_x c with
                             | 0 => 1
                             | 1 => 1
                             | 2 => 2  (* new label *)
                             | 3 => 2
                             | _ => 0
                             end in
  (* We'd need to record that labels 1 and 2 are equivalent *)
  let u := record_adjacency uf_init 1 2 in
  let resolved := resolve_labels u labels_alt in
  (* After resolution, all pixels have the same label *)
  (resolved (0, 0) = resolved (3, 0)).
Proof.
  simpl. reflexivity.
Qed.

(** Example: Gap detection *)
Example gap_prevents_merger :
  let img := mkImage 5 1 (fun c => negb (Nat.eqb (coord_x c) 2)) in
  (* Image: * * . * * *)
  let labels := fun c => match coord_x c with
                         | 0 => 1
                         | 1 => 1
                         | 2 => 0
                         | 3 => 2
                         | 4 => 2
                         | _ => 0
                         end in
  (* No adjacency across the gap *)
  let neighbors_at_3 := check_prior_neighbors_4 img (3, 0) in
  (* So no equivalence between labels 1 and 2 *)
  let u := uf_init in  (* no unions needed *)
  let resolved := resolve_labels u labels in
  neighbors_at_3 = [] /\
  (resolved (0, 0) = 1) /\
  (resolved (3, 0) = 2) /\
  (resolved (0, 0) <> resolved (3, 0)).
Proof.
  simpl. repeat split; discriminate.
Qed.

(** * Section 3: Abstract Component Specification
    
    This section defines what it means for a labeling to be correct,
    independent of any algorithm. We characterize connected components
    as equivalence classes and specify the properties any valid CCL
    solution must satisfy. *)

(** ** Connected Components as Equivalence Classes *)

(** Two pixels are connected if they can be linked by a chain of adjacent foreground pixels *)
Inductive connected (img : image) (adj : coord -> coord -> bool) : coord -> coord -> Prop :=
  | connected_refl : forall c,
      get_pixel img c = true -> connected img adj c c
  | connected_step : forall c1 c2 c3,
      connected img adj c1 c2 ->
      get_pixel img c3 = true ->
      adj c2 c3 = true ->
      connected img adj c1 c3.

(** Connected pixels are foreground *)
Lemma connected_foreground : forall img adj c1 c2,
  connected img adj c1 c2 ->
  get_pixel img c1 = true /\ get_pixel img c2 = true.
Proof.
  intros img adj c1 c2 H.
  induction H.
  - split; assumption.
  - split.
    + apply IHconnected.
    + assumption.
Qed.

(** Adjacent foreground pixels are connected *)
Lemma adjacent_connected : forall img adj c1 c2,
  get_pixel img c1 = true ->
  get_pixel img c2 = true ->
  adj c1 c2 = true ->
  connected img adj c1 c2.
Proof.
  intros img adj c1 c2 H1 H2 Hadj.
  apply connected_step with c1.
  - apply connected_refl. assumption.
  - assumption.
  - assumption.
Qed.


(** Connectivity is transitive *)
Lemma connected_trans : forall img adj c1 c2 c3,
  connected img adj c1 c2 ->
  connected img adj c2 c3 ->
  connected img adj c1 c3.
Proof.
  intros img adj c1 c2 c3 H12 H23.
  induction H23.
  - assumption.
  - apply connected_step with c2.
    + apply IHconnected. assumption.
    + assumption.
    + assumption.
Qed.

(** Connectivity is symmetric when adjacency is symmetric *)
Lemma connected_sym : forall img adj c1 c2,
  (forall a b, adj a b = adj b a) ->
  connected img adj c1 c2 -> connected img adj c2 c1.
Proof.
  intros img adj c1 c2 Hadj_sym Hconn.
  induction Hconn.
  - apply connected_refl. assumption.
  - (* We have: c1 → c2 → c3
       We want: c3 → c1
       By IH: c2 → c1
       So we need: c3 → c2 → c1 *)
    assert (Hc2: get_pixel img c2 = true).
    { apply (connected_foreground img adj c1 c2 Hconn). }
    (* First show c3 → c2 *)
    assert (Hc3c2: connected img adj c3 c2).
    { apply adjacent_connected.
      - assumption.
      - assumption.
      - rewrite Hadj_sym. assumption. }
    (* Then use transitivity *)
    apply connected_trans with c2.
    + assumption.
    + assumption.
Qed.
  
(** ** Correct Labeling Specification *)

(** A labeling is correct if it satisfies these properties: *)
Record correct_labeling (img : image) (adj : coord -> coord -> bool) (l : labeling) : Prop := {
  (* 1. Background pixels get label 0 *)
  label_background : forall c, get_pixel img c = false -> l c = 0;
  
  (* 2. Foreground pixels get positive labels *)
  label_foreground : forall c, get_pixel img c = true -> l c > 0;
  
  (* 3. Connected pixels get the same label *)
  label_connected : forall c1 c2, connected img adj c1 c2 -> l c1 = l c2;
  
  (* 4. Same positive label implies connected *)
  label_same_implies_connected : forall c1 c2, 
    l c1 = l c2 -> l c1 > 0 -> connected img adj c1 c2
}.

(** ** Properties of Correct Labelings *)

(** Labels partition the foreground pixels *)
Theorem labeling_partitions : forall img adj l,
  (forall a b, adj a b = adj b a) ->
  correct_labeling img adj l ->
  forall c1 c2, get_pixel img c1 = true -> get_pixel img c2 = true ->
    (l c1 = l c2 <-> connected img adj c1 c2).
Proof.
  intros img adj l Hadj_sym Hcorrect c1 c2 Hc1 Hc2.
  destruct Hcorrect as [Hbg Hfg Hconn Hsame].
  split.
  - intros Heq.
    assert (l c1 > 0) by (apply Hfg; assumption).
    apply Hsame; assumption.
  - intros Hconnected.
    apply Hconn. assumption.
Qed.

(** Components are equivalence classes *)
Theorem components_are_equivalence_classes : forall img adj l,
  (forall a b, adj a b = adj b a) ->
  correct_labeling img adj l ->
  (* Reflexive *)
  (forall c, get_pixel img c = true -> connected img adj c c) /\
  (* Symmetric *)
  (forall c1 c2, connected img adj c1 c2 -> connected img adj c2 c1) /\
  (* Transitive *)
  (forall c1 c2 c3, connected img adj c1 c2 -> connected img adj c2 c3 -> 
                    connected img adj c1 c3).
Proof.
  intros img adj l Hadj_sym Hcorrect.
  split; [|split].
  - intros c Hc. apply connected_refl. assumption.
  - intros c1 c2 H. apply connected_sym; assumption.
  - apply connected_trans.
Qed.

(** ** Component Properties *)

(** A component is the set of all pixels with a given label *)
Definition component (img : image) (l : labeling) (label : nat) : coord -> Prop :=
  fun c => get_pixel img c = true /\ l c = label.

(** Components are maximal connected sets *)
Lemma component_maximal : forall img adj l label,
  (forall a b, adj a b = adj b a) ->
  correct_labeling img adj l ->
  label > 0 ->
  forall c c', component img l label c ->
               get_pixel img c' = true ->
               connected img adj c c' ->
               component img l label c'.
Proof.
  intros img adj l label Hadj_sym Hcorrect Hlabel c c' [Hc Hlc] Hc' Hconn.
  unfold component.
  split.
  - assumption.
  - rewrite <- Hlc. 
    apply (label_connected img adj l Hcorrect).
    apply connected_sym.
    + assumption.
    + assumption.
Qed.


(** Different components are disjoint *)
Lemma components_disjoint : forall img adj l label1 label2,
  (forall a b, adj a b = adj b a) ->
  correct_labeling img adj l ->
  label1 <> label2 ->
  forall c, ~ (component img l label1 c /\ component img l label2 c).
Proof.
  intros img adj l label1 label2 Hadj_sym Hcorrect Hdiff c [H1 H2].
  unfold component in *.
  destruct H1 as [_ Hl1], H2 as [_ Hl2].
  rewrite Hl1 in Hl2.
  apply Hdiff. assumption.
Qed.

(** ** Existence and Uniqueness *)

(** Any two correct labelings induce the same partition *)
Theorem correct_labelings_equivalent : forall img adj l1 l2,
  (forall a b, adj a b = adj b a) ->
  correct_labeling img adj l1 ->
  correct_labeling img adj l2 ->
  forall c1 c2, get_pixel img c1 = true -> get_pixel img c2 = true ->
    (l1 c1 = l1 c2 <-> l2 c1 = l2 c2).
Proof.
  intros img adj l1 l2 Hadj_sym Hcorr1 Hcorr2 c1 c2 Hc1 Hc2.
  rewrite (labeling_partitions img adj l1 Hadj_sym Hcorr1 c1 c2 Hc1 Hc2).
  rewrite (labeling_partitions img adj l2 Hadj_sym Hcorr2 c1 c2 Hc1 Hc2).
  reflexivity.
Qed.

(** ** Label Properties *)

(** The set of labels used in a correct labeling *)
Definition labels_used (img : image) (l : labeling) : nat -> Prop :=
  fun label => exists c, get_pixel img c = true /\ l c = label.

(** Every positive label corresponds to a non-empty component *)
Lemma label_has_pixels : forall img adj l label,
  correct_labeling img adj l ->
  label > 0 ->
  labels_used img l label ->
  exists c, component img l label c.
Proof.
  intros img adj l label Hcorrect Hpos Hused.
  unfold labels_used in Hused.
  destruct Hused as [c [Hc Hlabel]].
  exists c.
  unfold component.
  split; assumption.
Qed.

(** Zero is never used for foreground *)
Lemma zero_only_background : forall img adj l,
  correct_labeling img adj l ->
  ~ labels_used img l 0.
Proof.
  intros img adj l Hcorrect Hused.
  unfold labels_used in Hused.
  destruct Hused as [c [Hc H0]].
  destruct Hcorrect as [_ Hfg _ _].
  assert (l c > 0) by (apply Hfg; assumption).
  rewrite H0 in H. inversion H.
Qed.

(** ** Component Count *)

(** The number of components is the number of distinct positive labels *)
Definition num_components (img : image) (l : labeling) (bound : nat) : nat :=
  length (filter (fun label => 
    match label with 
    | 0 => false 
    | S _ => existsb (fun c => andb (get_pixel img c) (Nat.eqb (l c) label)) 
                     (all_coords img)
    end) (seq 0 (S bound))).

Lemma existsb_label_exists : forall img l label coords,
  label > 0 ->
  existsb (fun c => andb (get_pixel img c) (Nat.eqb (l c) label)) coords = true ->
  exists c, In c coords /\ get_pixel img c = true /\ l c = label.
Proof.
  intros img l label coords Hpos Hexists.
  apply existsb_exists in Hexists.
  destruct Hexists as [c [Hin Hc]].
  apply andb_prop in Hc.
  destruct Hc as [Hget Heq].
  apply Nat.eqb_eq in Heq.
  exists c. split; [|split]; assumption.
Qed.

Lemma different_labels_different_pixels : forall img adj l c1 c2,
  correct_labeling img adj l ->
  get_pixel img c1 = true ->
  get_pixel img c2 = true ->
  l c1 > 0 ->
  l c2 > 0 ->
  l c1 <> l c2 ->
  c1 <> c2.
Proof.
  intros img adj l c1 c2 Hcorrect Hc1 Hc2 Hpos1 Hpos2 Hdiff_label.
  intro Heq_coord.
  subst c2.
  contradiction.
Qed.

Lemma used_label_has_pixel : forall img l label max_label,
  In label (filter (fun label => 
    match label with 
    | 0 => false 
    | S _ => existsb (fun c => andb (get_pixel img c) (Nat.eqb (l c) label)) 
                     (all_coords img)
    end) (seq 0 (S max_label))) ->
  exists c, In c (all_coords img) /\ get_pixel img c = true /\ l c = label.
Proof.
  intros img l label max_label Hin.
  apply filter_In in Hin.
  destruct Hin as [_ Hfilter].
  destruct label.
  - discriminate.
  - apply (existsb_label_exists img l (S label) (all_coords img)).
    + lia.
    + assumption.
Qed.

Lemma label_to_pixel_injection : forall img adj l max_label,
  correct_labeling img adj l ->
  (forall c, l c <= max_label) ->
  forall label1 label2,
  In label1 (filter (fun label => 
    match label with 
    | 0 => false 
    | S _ => existsb (fun c => andb (get_pixel img c) (Nat.eqb (l c) label)) 
                     (all_coords img)
    end) (seq 0 (S max_label))) ->
  In label2 (filter (fun label => 
    match label with 
    | 0 => false 
    | S _ => existsb (fun c => andb (get_pixel img c) (Nat.eqb (l c) label)) 
                     (all_coords img)
    end) (seq 0 (S max_label))) ->
  label1 <> label2 ->
  (exists c1, In c1 (all_coords img) /\ get_pixel img c1 = true /\ l c1 = label1) ->
  (exists c2, In c2 (all_coords img) /\ get_pixel img c2 = true /\ l c2 = label2) ->
  exists c1 c2, c1 <> c2 /\ 
                In c1 (filter (fun c => get_pixel img c) (all_coords img)) /\
                In c2 (filter (fun c => get_pixel img c) (all_coords img)) /\
                l c1 = label1 /\ l c2 = label2.
Proof.
  intros img adj l max_label Hcorrect Hbound label1 label2 Hin1 Hin2 Hdiff [c1 [Hc1_in [Hc1_fg Hc1_l]]] [c2 [Hc2_in [Hc2_fg Hc2_l]]].
  exists c1, c2.
  split.
  - intro Heq. subst c2. rewrite Hc1_l in Hc2_l. subst label2. contradiction.
  - split; [|split; [|split]].
    + apply filter_In. split; assumption.
    + apply filter_In. split; assumption.
    + assumption.
    + assumption.
Qed.

Lemma seq_NoDup : forall start len,
  NoDup (seq start len).
Proof.
  intros start len.
  generalize dependent start.
  induction len; intros start.
  - simpl. apply NoDup_nil.
  - simpl. apply NoDup_cons.
    + intro H. apply in_seq in H. lia.
    + apply IHlen.
Qed.

Lemma filter_NoDup : forall {A : Type} (f : A -> bool) (l : list A),
  NoDup l -> NoDup (filter f l).
Proof.
  intros A f l HNoDup.
  induction HNoDup.
  - simpl. apply NoDup_nil.
  - simpl. destruct (f x) eqn:Hfx.
    + apply NoDup_cons.
      * intro Hin. apply filter_In in Hin. destruct Hin as [Hin _]. contradiction.
      * assumption.
    + assumption.
Qed.

Lemma label_witness_exists : forall img l used_labels label,
  label > 0 ->
  In label used_labels ->
  used_labels = filter (fun label => 
    match label with 
    | 0 => false 
    | S _ => existsb (fun c => andb (get_pixel img c) (Nat.eqb (l c) label)) 
                     (all_coords img)
    end) (seq 0 (S (length used_labels))) ->
  exists c, In c (filter (fun c => get_pixel img c) (all_coords img)) /\ l c = label.
Proof.
  intros img l used_labels label Hpos Hin Heq.
  rewrite Heq in Hin.
  apply filter_In in Hin.
  destruct Hin as [_ Hfilter].
  destruct label.
  - lia.
  - apply existsb_exists in Hfilter.
    destruct Hfilter as [c [Hc_in Hc_prop]].
    apply andb_prop in Hc_prop.
    destruct Hc_prop as [Hget Heq_label].
    apply Nat.eqb_eq in Heq_label.
    exists c. split.
    + apply filter_In. split; assumption.
    + assumption.
Qed.

Lemma component_count_bound : forall img adj l max_label,
  correct_labeling img adj l ->
  (forall c, l c <= max_label) ->
  num_components img l max_label <= 
  length (filter (fun c => get_pixel img c) (all_coords img)).
Proof.
  intros img adj l max_label Hcorrect Hbound.
  unfold num_components.
  
  set (used_labels := filter (fun label => 
    match label with 
    | 0 => false 
    | S _ => existsb (fun c => andb (get_pixel img c) (Nat.eqb (l c) label)) 
                     (all_coords img)
    end) (seq 0 (S max_label))).
  
  set (foreground_pixels := filter (fun c => get_pixel img c) (all_coords img)).
  
  (* For each used label, we can find a pixel with that label *)
  assert (Hmap: forall label, In label used_labels -> 
                exists c, In c foreground_pixels /\ l c = label).
  { intros label Hin.
    apply (used_label_has_pixel img l label max_label) in Hin.
    destruct Hin as [c [Hc_all [Hc_fg Hc_label]]].
    exists c. split.
    - unfold foreground_pixels. apply filter_In. split; assumption.
    - assumption. }
  
  (* Key: the image of l restricted to foreground_pixels contains used_labels *)
  assert (Himage: forall label, In label used_labels -> 
                  In label (map l foreground_pixels)).
  { intros label Hin.
    destruct (Hmap label Hin) as [c [Hc_in Hc_label]].
    apply in_map_iff. exists c. split; assumption. }
  
  (* Length of used_labels <= length of (map l foreground_pixels) *)
  assert (Hlen: length used_labels <= length (map l foreground_pixels)).
  { apply NoDup_incl_length.
    - apply filter_NoDup. apply seq_NoDup.
    - unfold incl. assumption. }
  
  (* Length of map = length of original list *)
  rewrite length_map in Hlen.
  exact Hlen.
Qed.

(** ** Concrete Examples of Connectivity and Labeling *)

(** Example: Simple horizontal line *)
Example horizontal_line_connected :
  let img := mkImage 4 1 (fun _ => true) in
  connected img adjacent_4 (0, 0) (3, 0).
Proof.
  apply connected_step with (2, 0).
  - apply connected_step with (1, 0).
    + apply connected_step with (0, 0).
      * apply connected_refl. reflexivity.
      * reflexivity.
      * reflexivity.
    + reflexivity.
    + reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** Example: Disconnected pixels *)
Example disconnected_diagonal :
  let img := mkImage 3 3 (fun c => orb (coord_eqb c (0, 0)) (coord_eqb c (2, 2))) in
  (* Image: * . . *)
  (*        . . . *)
  (*        . . * *)
  ~ connected img adjacent_4 (0, 0) (2, 2).
Proof.
  intro H.
  assert (Hfg: forall c, get_pixel (mkImage 3 3 (fun c => orb (coord_eqb c (0, 0)) (coord_eqb c (2, 2)))) c = true -> 
                        c = (0, 0) \/ c = (2, 2)).
  { intros [x y] Hpix.
    unfold get_pixel in Hpix.
    destruct (in_bounds _ _) eqn:E.
    - simpl in Hpix.
      apply orb_prop in Hpix.
      destruct Hpix as [H1 | H2].
      + unfold coord_eqb in H1.
        apply andb_prop in H1. destruct H1 as [Hx Hy].
        apply Nat.eqb_eq in Hx, Hy.
        left. subst. reflexivity.
      + unfold coord_eqb in H2.
        apply andb_prop in H2. destruct H2 as [Hx Hy].
        apply Nat.eqb_eq in Hx, Hy.
        right. subst. reflexivity.
    - discriminate. }
  
  remember (0, 0) as start.
  remember (2, 2) as target.
  revert Heqstart Heqtarget.
  induction H; intros.
  - subst. discriminate.
  - subst.
    assert (c2 = (0, 0) \/ c2 = (2, 2)).
    { apply connected_foreground in H. apply Hfg. apply H. }
    assert ((2, 2) = (0, 0) \/ (2, 2) = (2, 2)) by (apply Hfg; assumption).
    destruct H2; [discriminate|].
    destruct H1; subst.
    + unfold adjacent_4, coord_x, coord_y, abs_diff in H0.
      simpl in H0. discriminate.
    + eapply IHconnected; reflexivity.
Qed.
