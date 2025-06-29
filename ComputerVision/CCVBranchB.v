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
  simpl.
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
  
  (* Show that any path from (0,0) to (2,2) is impossible *)
  assert (H0: forall c1 c2, connected (mkImage 3 3 (fun c => orb (coord_eqb c (0, 0)) (coord_eqb c (2, 2)))) adjacent_4 c1 c2 ->
                        c1 = (0, 0) -> c2 = (2, 2) -> False).
  { intros c1 c2 Hpath.
    induction Hpath; intros.
    - subst. discriminate.
    - subst c1 c3.
      assert (Hc2: c2 = (0, 0) \/ c2 = (2, 2)).
      { apply connected_foreground in Hpath. apply Hfg. apply Hpath. }
      destruct Hc2; subst c2.
      + unfold adjacent_4, coord_x, coord_y, abs_diff in H1. simpl in H1. discriminate.
      + eapply IHHpath; reflexivity. }
  
  eapply H0; [exact H | reflexivity | reflexivity].
Qed.

(** * Section 4: Single-Pass Algorithm
    
    This section implements the single-pass connected component labeling
    algorithm using union-find to track label equivalences. *)

(** ** Algorithm State *)

Record ccl_state : Type := mkCCLState {
  labels : labeling;
  equiv : uf;
  next_label : nat
}.

Definition initial_state : ccl_state :=
  mkCCLState empty_labeling uf_init 1.

(** ** Core Algorithm *)

Definition process_pixel (img : image) (adj : coord -> coord -> bool) 
                        (check_neighbors : image -> coord -> list coord)
                        (s : ccl_state) (c : coord) : ccl_state :=
  if get_pixel img c then
    let neighbors := check_neighbors img c in
    let neighbor_labels := map (labels s) neighbors in
    let positive_labels := filter (fun l => negb (Nat.eqb l 0)) neighbor_labels in
    match positive_labels with
    | [] => 
        mkCCLState 
          (fun c' => if coord_eqb c c' then next_label s else labels s c')
          (equiv s)
          (S (next_label s))
    | l :: rest =>
        let min_label := fold_left Nat.min rest l in
        let new_equiv := fold_left (fun u l' => record_adjacency u min_label l') 
                                   positive_labels (equiv s) in
        mkCCLState
          (fun c' => if coord_eqb c c' then min_label else labels s c')
          new_equiv
          (next_label s)
    end
  else
    s.

Definition ccl_pass (img : image) (adj : coord -> coord -> bool)
                    (check_neighbors : image -> coord -> list coord) : ccl_state :=
  fold_left (process_pixel img adj check_neighbors) (all_coords img) initial_state.

Definition ccl_algorithm (img : image) (adj : coord -> coord -> bool)
                        (check_neighbors : image -> coord -> list coord) : labeling :=
  let final_state := ccl_pass img adj check_neighbors in
  let max_label := next_label final_state - 1 in
  compact_labels (equiv final_state) (resolve_labels (equiv final_state) (labels final_state)) max_label.

Definition ccl_4 (img : image) : labeling :=
  ccl_algorithm img adjacent_4 check_prior_neighbors_4.

Definition ccl_8 (img : image) : labeling :=
  ccl_algorithm img adjacent_8 check_prior_neighbors_8.

(** ** Algorithm Properties *)

Definition state_labels_pixels (img : image) (s : ccl_state) : Prop :=
  forall c, labels s c > 0 -> get_pixel img c = true.

Definition state_labels_background (img : image) (s : ccl_state) : Prop :=
  forall c, get_pixel img c = false -> labels s c = 0.

Definition processed_before_in (img : image) (c : coord) : list coord :=
  filter (fun c' => raster_lt c' c) (all_coords img).

Definition partial_correct (img : image) (adj : coord -> coord -> bool) 
                          (s : ccl_state) (processed : list coord) : Prop :=
  (forall c, In c processed -> get_pixel img c = false -> labels s c = 0) /\
  (forall c, In c processed -> get_pixel img c = true -> labels s c > 0) /\
  (forall c1 c2, In c1 processed -> In c2 processed ->
                 get_pixel img c1 = true -> get_pixel img c2 = true ->
                 adj c1 c2 = true ->
                 uf_same_set (equiv s) (labels s c1) (labels s c2) = true) /\
  (forall c, ~ In c processed -> labels s c = 0).

(** ** Helper Lemmas *)

Lemma filter_positive_labels : forall labels,
  forall l, In l (filter (fun l => negb (Nat.eqb l 0)) labels) -> l > 0.
Proof.
  intros labels l H.
  apply filter_In in H.
  destruct H as [_ Hpos].
  apply negb_true_iff in Hpos.
  apply Nat.eqb_neq in Hpos.
  lia.
Qed.

Lemma fold_min_positive : forall l n,
  n > 0 ->
  (forall x, In x l -> x > 0) ->
  fold_left Nat.min l n > 0.
Proof.
  intros l n Hn Hall.
  generalize dependent n.
  induction l; intros n Hn.
  - simpl. assumption.
  - simpl. apply IHl.
    + intros x Hx. apply Hall. right. assumption.
    + assert (a > 0) by (apply Hall; left; reflexivity).
      destruct n, a; try lia.
Qed.

(** ** Basic Properties *)

Lemma process_pixel_background_unchanged : forall img adj check_neighbors s c,
  get_pixel img c = false ->
  process_pixel img adj check_neighbors s c = s.
Proof.
  intros img adj check_neighbors s c H.
  unfold process_pixel. rewrite H. reflexivity.
Qed.

Lemma process_pixel_preserves_other : forall img adj check_neighbors s c c',
  c <> c' ->
  labels (process_pixel img adj check_neighbors s c) c' = labels s c'.
Proof.
  intros img adj check_neighbors s c c' Hneq.
  unfold process_pixel.
  destruct (get_pixel img c) eqn:Hpix.
  - destruct (check_neighbors img c) eqn:Hneighbors.
    + simpl.
      assert (coord_eqb c c' = false).
      { apply Bool.not_true_iff_false. intro H.
        apply coord_eqb_true_iff in H. contradiction. }
      rewrite H. reflexivity.
    + destruct (filter _ _); simpl.
      * assert (coord_eqb c c' = false).
        { apply Bool.not_true_iff_false. intro H.
          apply coord_eqb_true_iff in H. contradiction. }
        rewrite H. reflexivity.
      * assert (coord_eqb c c' = false).
        { apply Bool.not_true_iff_false. intro H.
          apply coord_eqb_true_iff in H. contradiction. }
        rewrite H. reflexivity.
  - reflexivity.
Qed.

Lemma process_pixel_next_label_increases : forall img adj check_neighbors s c,
  next_label s <= next_label (process_pixel img adj check_neighbors s c).
Proof.
  intros img adj check_neighbors s c.
  unfold process_pixel.
  destruct (get_pixel img c).
  - destruct (check_neighbors img c).
    + simpl. lia.
    + destruct (filter _ _); simpl; lia.
  - lia.
Qed.

Lemma process_pixel_labels_current : forall img adj check_neighbors s c,
  next_label s > 0 ->
  get_pixel img c = true ->
  labels (process_pixel img adj check_neighbors s c) c > 0.
Proof.
  intros img adj check_neighbors s c Hnext Hpix.
  unfold process_pixel. rewrite Hpix.
  destruct (check_neighbors img c) eqn:Hneighbors.
  - simpl. rewrite coord_eqb_refl. assumption.
  - destruct (filter _ _) eqn:Hfilter; simpl.
    + rewrite coord_eqb_refl. assumption.
    + rewrite coord_eqb_refl.
      apply fold_min_positive.
      * apply filter_positive_labels with (labels := map (labels s) (c0 :: l)).
        rewrite Hfilter. left. reflexivity.
      * intros x Hx.
        apply filter_positive_labels with (labels := map (labels s) (c0 :: l)).
        rewrite Hfilter. right. assumption.
Qed.

Lemma process_pixel_preserves_background : forall img adj check_neighbors s c,
  state_labels_background img s ->
  state_labels_background img (process_pixel img adj check_neighbors s c).
Proof.
  intros img adj check_neighbors s c Hinv.
  unfold state_labels_background in *.
  intros c' Hbg.
  destruct (coord_eqb c c') eqn:Heq.
  - apply coord_eqb_true_iff in Heq. subst c'.
    rewrite process_pixel_background_unchanged.
    + apply Hinv. assumption.
    + assumption.
  - rewrite process_pixel_preserves_other.
    + apply Hinv. assumption.
    + intro H. subst. rewrite coord_eqb_refl in Heq. discriminate.
Qed.

Lemma uf_union_preserves_others : forall u x y l1 l2,
  uf_same_set u l1 l2 = true ->
  uf_same_set (uf_union u x y) l1 l2 = true.
Proof.
  intros u x y l1 l2 H.
  unfold uf_same_set, uf_union, uf_find in *.
  apply Nat.eqb_eq in H.
  apply Nat.eqb_eq.
  destruct (u x =? u l1) eqn:E1; destruct (u x =? u l2) eqn:E2.
  - reflexivity.
  - exfalso.
    apply Nat.eqb_eq in E1.
    apply Nat.eqb_neq in E2.
    congruence.
  - exfalso.
    apply Nat.eqb_neq in E1.
    apply Nat.eqb_eq in E2.
    congruence.
  - assumption.
Qed.

Lemma process_pixel_preserves_equiv : forall img adj check_neighbors s c l1 l2,
  uf_same_set (equiv s) l1 l2 = true ->
  uf_same_set (equiv (process_pixel img adj check_neighbors s c)) l1 l2 = true.
Proof.
  intros img adj check_neighbors s c l1 l2 H.
  unfold process_pixel.
  destruct (get_pixel img c); [|assumption].
  destruct (check_neighbors img c).
  - simpl. assumption.
  - destruct (filter _ _) as [|n l0]; simpl.
    + assumption.
    + remember (fold_left Nat.min l0 n) as min_label.
      assert (Hgen: forall labels u,
        uf_same_set u l1 l2 = true ->
        uf_same_set 
          (fold_left (fun u' l' => record_adjacency u' min_label l') labels u) 
          l1 l2 = true).
      { intros labels0 u0 H0.
        generalize dependent u0.
        induction labels0 as [|x xs IH]; intros u0 H0.
        - simpl. assumption.
        - simpl. apply IH.
          unfold record_adjacency.
          destruct (negb (min_label =? 0) && negb (x =? 0)) eqn:E.
          + destruct (min_label =? x).
            * assumption.
            * apply uf_union_preserves_others. assumption.
          + assumption. }
      apply (Hgen (n :: l0) (equiv s) H).
Qed.

(** ** Invariant Preservation *)

Lemma fold_left_preserves : forall {A B : Type} (f : B -> A -> B) (P : B -> Prop) (l : list A) (b : B),
  P b ->
  (forall b' a, P b' -> In a l -> P (f b' a)) ->
  P (fold_left f l b).
Proof.
  intros A B f P l.
  induction l as [|a l' IH]; intros b Hb Hf.
  - simpl. assumption.
  - simpl. apply IH.
    + apply Hf; [assumption | left; reflexivity].
    + intros b' a' Hb' Ha'.
      apply Hf; [assumption | right; assumption].
Qed.

Lemma ccl_pass_labels_background : forall img adj check_neighbors,
  state_labels_background img (ccl_pass img adj check_neighbors).
Proof.
  intros img adj check_neighbors.
  unfold ccl_pass.
  apply fold_left_preserves.
  - unfold state_labels_background, initial_state, empty_labeling. 
    intros c H. reflexivity.
  - intros s c Hs Hc.
    apply process_pixel_preserves_background. assumption.
Qed.

(** ** Algorithm Examples *)

Example test_single_pixel :
  let img := mkImage 1 1 (fun _ => true) in
  let result := ccl_4 img in
  result (0, 0) = 1.
Proof.
  reflexivity.
Qed.

Example test_two_pixels_adjacent :
  let img := mkImage 2 1 (fun _ => true) in
  let result := ccl_4 img in
  result (0, 0) = result (1, 0).
Proof.
  reflexivity.
Qed.

Example test_two_pixels_gap :
  let img := mkImage 3 1 (fun c => negb (coord_eqb c (1, 0))) in
  let result := ccl_4 img in
  result (0, 0) <> result (2, 0).
Proof.
  simpl. discriminate.
Qed.

Example test_L_shape :
  let img := mkImage 3 3 (fun c => 
    orb (coord_eqb c (0, 0)) (orb (coord_eqb c (0, 1)) (coord_eqb c (1, 1)))) in
  let result := ccl_4 img in
  (result (0, 0) = result (0, 1)) /\
  (result (0, 1) = result (1, 1)).
Proof.
  split; reflexivity.
Qed.

(** ** Example: Verifying Algorithm on a Minimal Image *)

Example minimal_ccl_verification :
  let img := mkImage 2 1 (fun _ => true) in
  (* Image pattern: * * *)
  let result := ccl_4 img in
  (* Both pixels should have the same label since they're adjacent *)
  result (0, 0) = result (1, 0) /\
  result (0, 0) > 0.
Proof.
  compute.
  split; reflexivity.
Qed.

(** ** Example: L-shaped Component *)

Example L_shape_verification :
  let img := mkImage 3 3 (fun c =>
    orb (orb (coord_eqb c (0, 0)) (coord_eqb c (0, 1)))
        (orb (coord_eqb c (0, 2)) (coord_eqb c (1, 2)))) in
  (* Image pattern: * . . *)
  (*                * . . *)
  (*                * * . *)
  let result := ccl_4 img in
  (* All four pixels form one connected component *)
  result (0, 0) = result (0, 1).
Proof.
  unfold ccl_4, ccl_algorithm.
  simpl.
  compute.
  reflexivity.
Qed.

(** ** Example: Diagonal Components - 4 vs 8 Connectivity *)

Example diagonal_connectivity_difference :
  let img := mkImage 3 3 (fun c =>
    orb (andb (Nat.eqb (coord_x c) (coord_y c)) (Nat.leb (coord_x c) 1))
        (andb (Nat.eqb (coord_x c) (2 - coord_y c)) (Nat.leb 1 (coord_x c)))) in
  (* Image pattern: * . * *)
  (*                . * . *)
  (*                * . . *)
  (* Two diagonal lines that meet at (1,1) *)
  let result4 := ccl_4 img in
  let result8 := ccl_8 img in
  (* With 4-connectivity, they're separate components *)
  result4 (0, 0) <> result4 (2, 0).
Proof.
  compute.
  discriminate.
Qed.

(** ** Example: Multiple Connected Components *)

Example multiple_components :
  let img := mkImage 5 3 (fun c =>
    orb (andb (Nat.leb (coord_x c) 1) (Nat.eqb (coord_y c) 0))
        (orb (andb (Nat.leb 3 (coord_x c)) (Nat.eqb (coord_y c) 1))
             (coord_eqb c (2, 2)))) in
  (* Image pattern: * * . . . *)
  (*                . . . * * *)
  (*                . . * . . *)
  let result := ccl_4 img in
  (* Three separate components *)
  (result (0, 0) = result (1, 0)) /\  (* Component 1 *)
  (result (3, 1) = result (4, 1)) /\  (* Component 2 *)
  (result (2, 2) > 0) /\              (* Component 3 *)
  (result (0, 0) <> result (3, 1)) /\
  (result (0, 0) <> result (2, 2)) /\
  (result (3, 1) <> result (2, 2)).
Proof.
  compute.
  split. reflexivity.
  split. reflexivity.
  split. apply Nat.lt_0_succ.
  split. discriminate.
  split. discriminate.
  discriminate.
Qed.

(** * Section 5: Algorithm Correctness Properties
    
    This section proves that our single-pass algorithm correctly identifies
    connected components by establishing key invariants about paths, 
    equivalences, and label assignments. *)

(** ** Raster Order Properties *)

Lemma raster_lt_total : forall c1 c2,
  c1 <> c2 -> raster_lt c1 c2 = true \/ raster_lt c2 c1 = true.
Proof.
  intros [x1 y1] [x2 y2] Hneq.
  unfold raster_lt.
  simpl.
  destruct (y1 <? y2) eqn:E1.
  - left. reflexivity.
  - destruct (y2 <? y1) eqn:E2.
    + right. reflexivity.
    + apply Nat.ltb_nlt in E1.
      apply Nat.ltb_nlt in E2.
      assert (y1 = y2) by lia. subst y2.
      assert (x1 <> x2).
      { intro Heq. subst x2. apply Hneq. reflexivity. }
      destruct (x1 <? x2) eqn:E3.
      * left. rewrite Nat.eqb_refl. simpl. 
        reflexivity.  (* Just reflexivity - goal is already true = true *)
      * right. rewrite Nat.eqb_refl. simpl.
        apply Nat.ltb_nlt in E3.
        assert (x2 < x1) by lia.
        apply Nat.ltb_lt in H0. assumption.
Qed.

(** ** Partial Correctness Invariant *)

(** The key invariant: after processing pixels up to c, the state correctly
    captures prior-neighbor equivalences among processed pixels *)
Definition strong_partial_correct (img : image) (adj : coord -> coord -> bool) 
                                 (s : ccl_state) (processed : list coord) : Prop :=
  (* Basic labeling properties *)
  (forall c, In c processed -> get_pixel img c = false -> labels s c = 0) /\
  (forall c, In c processed -> get_pixel img c = true -> labels s c > 0) /\
  (forall c, ~ In c processed -> labels s c = 0) /\
  (* Prior-neighbor equivalence property *)
  (forall c1 c2, In c1 processed -> In c2 processed ->
                 get_pixel img c1 = true -> get_pixel img c2 = true ->
                 adj c1 c2 = true -> raster_lt c1 c2 = true ->
                 uf_same_set (equiv s) (labels s c1) (labels s c2) = true).


(** Helper: processed pixels form a prefix in raster order *)
Definition raster_prefix (processed : list coord) : Prop :=
  forall c1 c2, In c1 processed -> raster_lt c2 c1 = true -> In c2 processed.

(** ** Helper Lemmas for process_pixel_maintains_invariant *)

(** The next_label is always positive throughout the algorithm *)
Lemma initial_state_next_label_positive : 
  next_label initial_state > 0.
Proof.
  unfold initial_state. simpl. 
  apply Nat.lt_0_succ.
Qed.

(** process_pixel preserves next_label positivity *)
Lemma process_pixel_next_label_positive : forall img adj check_neighbors s c,
  next_label s > 0 ->
  next_label (process_pixel img adj check_neighbors s c) > 0.
Proof.
  intros img adj check_neighbors s c Hpos.
  unfold process_pixel.
  destruct (get_pixel img c).
  - destruct (check_neighbors img c).
    + simpl. lia.
    + destruct (filter _ _).
      * simpl. lia.
      * simpl. assumption.
  - assumption.
Qed.

(** Labels only change at the processed pixel *)
Lemma process_pixel_labels_unchanged : forall img adj check_neighbors s c c',
  c <> c' ->
  labels (process_pixel img adj check_neighbors s c) c' = labels s c'.
Proof.
  intros img adj check_neighbors s c c' Hneq.
  unfold process_pixel.
  destruct (get_pixel img c); [|reflexivity].
  destruct (check_neighbors img c).
  - simpl. 
    assert (coord_eqb c c' = false).
    { apply Bool.not_true_iff_false. intro H. 
      apply coord_eqb_true_iff in H. contradiction. }
    rewrite H. reflexivity.
  - destruct (filter _ _); simpl.
    + assert (coord_eqb c c' = false).
      { apply Bool.not_true_iff_false. intro H. 
        apply coord_eqb_true_iff in H. contradiction. }
      rewrite H. reflexivity.
    + assert (coord_eqb c c' = false).
      { apply Bool.not_true_iff_false. intro H. 
        apply coord_eqb_true_iff in H. contradiction. }
      rewrite H. reflexivity.
Qed.

(** Background pixels stay unlabeled after processing *)
Lemma process_pixel_preserves_background_label : forall img adj check_neighbors s c c',
  get_pixel img c' = false ->
  labels (process_pixel img adj check_neighbors s c) c' = 0 ->
  labels s c' = 0.
Proof.
  intros img adj check_neighbors s c c' Hbg Hlabel.
  destruct (coord_eqb c c') eqn:Heq.
  - (* c = c' *)
    apply coord_eqb_true_iff in Heq. subst c'.
    unfold process_pixel in Hlabel.
    rewrite Hbg in Hlabel.
    assumption.
  - (* c ≠ c' *)
    rewrite (process_pixel_labels_unchanged img adj check_neighbors s c c') in Hlabel.
    + assumption.
    + intro H. subst c'. rewrite coord_eqb_refl in Heq. discriminate.
Qed.

(** fold_left with record_adjacency preserves existing equivalences *)
Lemma fold_record_adjacency_preserves : forall labels min_label u l1 l2,
  uf_same_set u l1 l2 = true ->
  uf_same_set 
    (fold_left (fun u' l' => record_adjacency u' min_label l') labels u) 
    l1 l2 = true.
Proof.
  intros labels min_label u l1 l2 H.
  generalize dependent u.
  induction labels as [|x xs IH]; intros u H.
  - simpl. assumption.
  - simpl. apply IH.
    unfold record_adjacency.
    destruct (negb (min_label =? 0) && negb (x =? 0)) eqn:E.
    + destruct (min_label =? x).
      * assumption.
      * apply uf_union_preserves_others. assumption.
    + assumption.
Qed.

Lemma fold_record_adjacency_creates : forall labels min_label u,
  min_label > 0 ->
  (forall l, In l labels -> l > 0) ->
  forall l, In l labels ->
    uf_same_set 
      (fold_left (fun u' l' => record_adjacency u' min_label l') labels u)
      min_label l = true.
Proof.
  intros labels min_label.
  induction labels as [|x xs IH]; intros u Hmin_pos Hall_pos l Hin.
  - (* labels = [] *)
    simpl in Hin. contradiction.
  - (* labels = x :: xs *)
    simpl in Hin. destruct Hin as [Heq | Hin'].
    + (* l = x *)
      subst l. simpl.
      assert (Hx_pos: x > 0) by (apply Hall_pos; left; reflexivity).
      assert (Hafter_x: uf_same_set (record_adjacency u min_label x) min_label x = true).
      { unfold record_adjacency.
        assert (negb (min_label =? 0) = true) by (apply negb_true_iff; apply Nat.eqb_neq; lia).
        assert (negb (x =? 0) = true) by (apply negb_true_iff; apply Nat.eqb_neq; lia).
        rewrite H, H0. simpl.
        destruct (min_label =? x) eqn:E.
        - apply Nat.eqb_eq in E. subst x.
          apply uf_same_set_refl.
        - unfold uf_same_set.
          apply Nat.eqb_eq.
          apply uf_union_connects. }
      apply (fold_record_adjacency_preserves xs min_label _ min_label x).
      assumption.
    + (* l ∈ xs *)
      simpl.
      (* Apply IH with the updated union-find structure *)
      apply (IH (record_adjacency u min_label x)).
      * assumption.
      * intros l' Hl'. apply Hall_pos. right. assumption.
      * assumption.
Qed.

Lemma process_pixel_equiv_neighbors : forall img adj check_neighbors s c c1 c2,
  get_pixel img c = true ->
  In c1 (check_neighbors img c) ->
  In c2 (check_neighbors img c) ->
  labels s c1 > 0 ->
  labels s c2 > 0 ->
  uf_same_set (equiv (process_pixel img adj check_neighbors s c)) 
              (labels s c1) (labels s c2) = true.
Proof.
  intros img adj check_neighbors s c c1 c2 Hpix Hin1 Hin2 Hpos1 Hpos2.
  unfold process_pixel.
  rewrite Hpix.
  destruct (check_neighbors img c) as [|n ns] eqn:Hneighbors.
  - (* check_neighbors img c = [] *)
    simpl in Hin1. contradiction.
  - (* check_neighbors img c = n :: ns *)
    remember (filter (fun l => negb (l =? 0)) (map (labels s) (n :: ns))) as positive_labels.
    destruct positive_labels as [|l ls] eqn:Hpos_labels.
    + (* No positive labels - contradiction *)
      assert (In (labels s c1) (filter (fun l => negb (l =? 0)) (map (labels s) (n :: ns)))).
      { apply filter_In. split.
        - apply in_map. assumption.
        - apply negb_true_iff. apply Nat.eqb_neq. lia. }
      rewrite <- Heqpositive_labels in H. simpl in H. contradiction.
    + (* positive_labels = l :: ls *)
      simpl.
      remember (fold_left Nat.min ls l) as min_label.
      (* Key insight: both labels s c1 and labels s c2 are in positive_labels *)
      assert (Hin_pos1: In (labels s c1) (l :: ls)).
      { rewrite Heqpositive_labels.
        apply filter_In. split.
        - apply in_map. assumption.
        - apply negb_true_iff. apply Nat.eqb_neq. lia. }
      assert (Hin_pos2: In (labels s c2) (l :: ls)).
      { rewrite Heqpositive_labels.
        apply filter_In. split.
        - apply in_map. assumption.
        - apply negb_true_iff. apply Nat.eqb_neq. lia. }
      (* l is positive since it's in the filtered list *)
      assert (Hl_pos: l > 0).
      { assert (In l (l :: ls)) by (left; reflexivity).
        rewrite Heqpositive_labels in H.
        apply filter_In in H. destruct H as [_ H].
        apply negb_true_iff in H. apply Nat.eqb_neq in H. lia. }
      (* After folding, both are equivalent to min_label *)
      assert (H1: uf_same_set 
                    (fold_left (fun u' l' => record_adjacency u' min_label l') (l :: ls) (equiv s))
                    min_label (labels s c1) = true).
      { apply fold_record_adjacency_creates.
        - subst min_label. apply fold_min_positive.
          + assumption.
          + intros x Hx. 
            assert (In x (l :: ls)) by (right; assumption).
            rewrite Heqpositive_labels in H.
            apply filter_In in H. destruct H as [_ H].
            apply negb_true_iff in H. apply Nat.eqb_neq in H. lia.
        - intros l' Hl'. 
          assert (In l' (l :: ls)) by assumption.
          rewrite Heqpositive_labels in H.
          apply filter_In in H. destruct H as [_ H].
          apply negb_true_iff in H. apply Nat.eqb_neq in H. lia.
        - assumption. }
      assert (H2: uf_same_set 
                    (fold_left (fun u' l' => record_adjacency u' min_label l') (l :: ls) (equiv s))
                    min_label (labels s c2) = true).
      { apply fold_record_adjacency_creates.
        - subst min_label. apply fold_min_positive.
          + assumption.
          + intros x Hx. 
            assert (In x (l :: ls)) by (right; assumption).
            rewrite Heqpositive_labels in H.
            apply filter_In in H. destruct H as [_ H].
            apply negb_true_iff in H. apply Nat.eqb_neq in H. lia.
        - intros l' Hl'. 
          assert (In l' (l :: ls)) by assumption.
          rewrite Heqpositive_labels in H.
          apply filter_In in H. destruct H as [_ H].
          apply negb_true_iff in H. apply Nat.eqb_neq in H. lia.
        - assumption. }
(* By transitivity through min_label *)
      unfold uf_same_set in *.
      apply Nat.eqb_eq in H1, H2.
      apply Nat.eqb_eq.
      (* H1 and H2 use fold_left on (l :: ls), but goal has it unfolded *)
      simpl in H1, H2.
      rewrite <- H1, <- H2.
      reflexivity.
Qed.

(** The current pixel gets assigned a valid label *)
Lemma process_pixel_labels_current_pixel : forall img adj check_neighbors s c,
  get_pixel img c = true ->
  next_label s > 0 ->
  let s' := process_pixel img adj check_neighbors s c in
  labels s' c > 0 /\
  (forall c', In c' (check_neighbors img c) -> 
    labels s c' > 0 -> 
    uf_same_set (equiv s') (labels s' c) (labels s c') = true).
Proof.
  intros img adj check_neighbors s c Hpix Hnext.
  unfold process_pixel.
  rewrite Hpix.
  destruct (check_neighbors img c) as [|n ns] eqn:Hneighbors.
  - (* No neighbors - gets fresh label *)
    simpl. split.
    + rewrite coord_eqb_refl. assumption.
    + intros c' Hin. simpl in Hin. contradiction.
  - (* Has neighbors *)
    remember (filter (fun l => negb (l =? 0)) (map (labels s) (n :: ns))) as positive_labels.
    destruct positive_labels as [|l ls] eqn:Hpos_labels.
    + (* No positive labels - gets fresh label *)
      simpl. split.
      * rewrite coord_eqb_refl. assumption.
      * intros c' Hin Hpos.
        assert (In (labels s c') (map (labels s) (n :: ns))).
        { apply in_map. assumption. }
        assert (In (labels s c') (filter (fun l => negb (l =? 0)) (map (labels s) (n :: ns)))).
        { apply filter_In. split.
          - assumption.
          - apply negb_true_iff. apply Nat.eqb_neq. lia. }
        rewrite <- Heqpositive_labels in H0. simpl in H0. contradiction.
    + (* positive_labels = l :: ls - gets min label *)
      simpl. 
      remember (fold_left Nat.min ls l) as min_label.
      split.
      * rewrite coord_eqb_refl.
        subst min_label. apply fold_min_positive.
        -- assert (In l (l :: ls)) by (left; reflexivity).
           rewrite Heqpositive_labels in H.
           apply filter_positive_labels in H. assumption.
        -- intros x Hx.
           assert (In x (l :: ls)) by (right; assumption).
           rewrite Heqpositive_labels in H.
           apply filter_positive_labels in H. assumption.
      * intros c' Hin Hpos.
        assert (In (labels s c') (l :: ls)).
        { rewrite Heqpositive_labels.
          apply filter_In. split.
          - apply in_map. assumption.
          - apply negb_true_iff. apply Nat.eqb_neq. lia. }
        rewrite coord_eqb_refl.
        (* The key is that fold_left starts from (equiv s) and processes l :: ls *)
        unfold uf_same_set.
        apply Nat.eqb_eq.
        subst min_label.
        (* After folding, min_label and labels s c' are in same set *)
        assert (Hmin_pos: fold_left Nat.min ls l > 0).
        { apply fold_min_positive.
          - assert (In l (l :: ls)) by (left; reflexivity).
            rewrite Heqpositive_labels in H0.
            apply filter_positive_labels in H0. assumption.
          - intros x Hx.
            assert (In x (l :: ls)) by (right; assumption).
            rewrite Heqpositive_labels in H0.
            apply filter_positive_labels in H0. assumption. }
        assert (Hall_pos: forall x, In x (l :: ls) -> x > 0).
        { intros x Hx.
          assert (In x (l :: ls)) by assumption.
          rewrite Heqpositive_labels in H0.
          apply filter_positive_labels in H0. assumption. }
        change (uf_find 
                 (fold_left (fun u' l' => record_adjacency u' (fold_left Nat.min ls l) l') 
                           (l :: ls) (equiv s))
                 (fold_left Nat.min ls l) =
               uf_find 
                 (fold_left (fun u' l' => record_adjacency u' (fold_left Nat.min ls l) l') 
                           (l :: ls) (equiv s))
                 (labels s c')).
assert (uf_same_set 
                 (fold_left (fun u' l' => record_adjacency u' (fold_left Nat.min ls l) l') 
                           (l :: ls) (equiv s))
                 (fold_left Nat.min ls l)
                 (labels s c') = true).
        { apply (fold_record_adjacency_creates (l :: ls) (fold_left Nat.min ls l) (equiv s) Hmin_pos Hall_pos (labels s c') H). }
        unfold uf_same_set in H0.
        apply Nat.eqb_eq in H0.
        exact H0.
Qed.

(** * Missing Union-Find Infrastructure Lemmas *)

(** 1. Characterization of when union creates new equivalences *)
Lemma uf_union_creates_equiv_characterization : forall u l1 l2 x y,
  uf_same_set u l1 l2 = false ->
  uf_same_set (uf_union u x y) l1 l2 = true ->
  (uf_find u l1 = uf_find u x \/ uf_find u l1 = uf_find u y) /\
  (uf_find u l2 = uf_find u x \/ uf_find u l2 = uf_find u y).
Proof.
  intros u l1 l2 x y Hbefore Hafter.
  unfold uf_same_set in *.
  apply Nat.eqb_neq in Hbefore.
  apply Nat.eqb_eq in Hafter.
  unfold uf_union, uf_find in Hafter.
  
  (* Analyze how uf_union affected l1 and l2 *)
  remember (uf_find u x =? uf_find u l1) as b1.
  remember (uf_find u x =? uf_find u l2) as b2.
  destruct b1 eqn:Eb1; destruct b2 eqn:Eb2.
  
  - (* Case 1: Both l1 and l2 were in x's class *)
    symmetry in Heqb1, Heqb2.
    apply Nat.eqb_eq in Heqb1, Heqb2.
    (* This means uf_find u l1 = uf_find u x = uf_find u l2 *)
    rewrite <- Heqb1, <- Heqb2 in Hbefore.
    contradiction.
- (* Case 2: l1 in x's class, l2 not *)
    symmetry in Heqb1, Heqb2.
    apply Nat.eqb_eq in Heqb1.
    apply Nat.eqb_neq in Heqb2.
    (* After union: l1 maps to y, l2 stays unchanged *)
    unfold uf_find in Heqb1, Heqb2.
    rewrite Heqb1 in Hafter.
    rewrite Nat.eqb_refl in Hafter.
    assert (Hneq: u l1 <> u l2).
    { rewrite <- Heqb1. exact Heqb2. }
    assert (H: (u l1 =? u l2) = false).
    { apply Nat.eqb_neq. exact Hneq. }
    rewrite H in Hafter.
    (* Now Hafter : u y = u l2 *)
    split.
    + left. unfold uf_find. symmetry. exact Heqb1.
    + right. unfold uf_find. symmetry. exact Hafter.
- (* Case 3: l2 in x's class, l1 not *)
    symmetry in Heqb1, Heqb2.
    apply Nat.eqb_neq in Heqb1.
    apply Nat.eqb_eq in Heqb2.
    (* After union: l2 maps to y, l1 stays unchanged *)
    unfold uf_find in Heqb1, Heqb2.
    rewrite Heqb2 in Hafter.
    assert (Hneq: u l1 <> u l2).
    { intro Heq. apply Heqb1. rewrite Heq. exact Heqb2. }
    assert (Hneq': u l2 <> u l1).
    { intro Heq. apply Hneq. symmetry. exact Heq. }
    assert (H: (u l2 =? u l1) = false).
    { apply Nat.eqb_neq. exact Hneq'. }
    rewrite H in Hafter.
    rewrite Nat.eqb_refl in Hafter.
    (* Now Hafter : u l1 = u y *)
    split.
    + right. unfold uf_find. exact Hafter.
    + left. unfold uf_find. symmetry. exact Heqb2.
- (* Case 4: Neither in x's class *)
    symmetry in Heqb1, Heqb2.
    apply Nat.eqb_neq in Heqb1, Heqb2.
    (* After union: both stay unchanged *)
    unfold uf_find in Heqb1, Heqb2.
    assert (H1: u x =? u l1 = false).
    { apply Nat.eqb_neq. exact Heqb1. }
    assert (H2: u x =? u l2 = false).
    { apply Nat.eqb_neq. exact Heqb2. }
    rewrite H1, H2 in Hafter.
    (* So Hafter : u l1 = u l2, contradicting Hbefore *)
    unfold uf_find in Hbefore.
    contradiction.
Qed.

(** 2. Union preserves non-equivalence for unrelated labels *)
Lemma uf_union_preserves_non_equiv : forall u l1 l2 x y,
  uf_same_set u l1 l2 = false ->
  uf_find u l1 <> uf_find u x ->
  uf_find u l1 <> uf_find u y ->
  uf_find u l2 <> uf_find u x ->
  uf_find u l2 <> uf_find u y ->
  uf_same_set (uf_union u x y) l1 l2 = false.
Proof.
  intros u l1 l2 x y Hbefore Hl1x Hl1y Hl2x Hl2y.
  unfold uf_same_set in *.
  apply Nat.eqb_neq in Hbefore.
  apply Nat.eqb_neq.
  unfold uf_union, uf_find in *.
  
  (* Since l1 is not in x's class, it remains unchanged *)
  assert (H1: (u x =? u l1) = false).
  { apply Nat.eqb_neq. intro H. symmetry in H. contradiction. }
  rewrite H1.
  
  (* Since l2 is not in x's class, it remains unchanged *)
  assert (H2: (u x =? u l2) = false).
  { apply Nat.eqb_neq. intro H. symmetry in H. contradiction. }
  rewrite H2.
  
  (* Both sides are just u l1 and u l2, which are different by Hbefore *)
  exact Hbefore.
Qed.

(** 3. Complete characterization of when record_adjacency creates new equivalences *)
Lemma record_adjacency_creates_equiv_iff : forall u x y l1 l2,
  uf_same_set u l1 l2 = false ->
  (uf_same_set (record_adjacency u x y) l1 l2 = true <->
   x <> 0 /\ y <> 0 /\ x <> y /\ 
   ((uf_find u l1 = uf_find u x \/ uf_find u l1 = uf_find u y) /\
    (uf_find u l2 = uf_find u x \/ uf_find u l2 = uf_find u y))).
Proof.
  intros u x y l1 l2 Hbefore.
  unfold record_adjacency.
  split.
  
  - (* Forward direction *)
    intro Hafter.
    destruct (negb (x =? 0) && negb (y =? 0)) eqn:Hnonzero.
    + (* Both x and y are non-zero *)
      apply andb_prop in Hnonzero.
      destruct Hnonzero as [Hx Hy].
      apply negb_true_iff in Hx, Hy.
      apply Nat.eqb_neq in Hx, Hy.
      destruct (x =? y) eqn:Hxy.
      * (* x = y *)
        apply Nat.eqb_eq in Hxy.
        subst y.
        (* record_adjacency didn't change u, so same_set should still be false *)
        rewrite Hbefore in Hafter.
        discriminate.
      * (* x ≠ y *)
        apply Nat.eqb_neq in Hxy.
        split; [exact Hx|].
        split; [exact Hy|].
        split; [exact Hxy|].
        (* Now apply uf_union_creates_equiv_characterization *)
        apply (uf_union_creates_equiv_characterization u l1 l2 x y Hbefore Hafter).
    + (* At least one of x or y is zero *)
      (* record_adjacency didn't change u, so same_set should still be false *)
      rewrite Hbefore in Hafter.
      discriminate.
- (* Backward direction *)
    intros [Hx [Hy [Hxy Hequiv]]].
    assert (Hnonzero: negb (x =? 0) && negb (y =? 0) = true).
    { apply andb_true_intro. split.
      - apply negb_true_iff. apply Nat.eqb_neq. exact Hx.
      - apply negb_true_iff. apply Nat.eqb_neq. exact Hy. }
    rewrite Hnonzero.
    assert (Hxy': (x =? y) = false).
    { apply Nat.eqb_neq. exact Hxy. }
    rewrite Hxy'.
    (* Now we need to show uf_same_set (uf_union u x y) l1 l2 = true *)
    unfold uf_same_set, uf_union, uf_find.
    apply Nat.eqb_eq.
    destruct Hequiv as [[Hl1x | Hl1y] [Hl2x | Hl2y]].
+ (* l1 in x's class, l2 in x's class *)
      unfold uf_find in Hl1x, Hl2x.
      assert (H1: u x =? u l1 = true).
      { apply Nat.eqb_eq. symmetry. exact Hl1x. }
      assert (H2: u x =? u l2 = true).
      { apply Nat.eqb_eq. symmetry. exact Hl2x. }
      rewrite H1, H2.
      reflexivity.
+ (* l1 in x's class, l2 in y's class *)
      unfold uf_find in Hl1x, Hl2y.
      assert (H1: u x =? u l1 = true).
      { apply Nat.eqb_eq. symmetry. exact Hl1x. }
      rewrite H1.
      assert (H2: u x =? u l2 = false).
      { apply Nat.eqb_neq. intro H.
        (* If u x = u l2, then u l1 = u x = u l2, contradicting Hbefore *)
        unfold uf_same_set in Hbefore.
        apply Nat.eqb_neq in Hbefore.
        apply Hbefore.
        unfold uf_find.
        rewrite Hl1x, H.
        reflexivity. }
      rewrite H2.
      symmetry. exact Hl2y.
+ (* l1 in y's class, l2 in x's class *)
      unfold uf_find in Hl1y, Hl2x.
      assert (H1: u x =? u l1 = false).
      { apply Nat.eqb_neq. intro H. 
        (* If u x = u l1, then since u l1 = u y, we'd have u x = u y *)
        assert (Hxy_eq: u x = u y).
        { rewrite H. exact Hl1y. }
        (* This means x and y are already in same class, but then l1 and l2 would be too *)
        unfold uf_same_set in Hbefore.
        apply Nat.eqb_neq in Hbefore.
        apply Hbefore.
        unfold uf_find.
        rewrite Hl1y, <- Hxy_eq, <- Hl2x.
        reflexivity. }
      rewrite H1.
      assert (H2: u x =? u l2 = true).
      { apply Nat.eqb_eq. symmetry. exact Hl2x. }
      rewrite H2.
      exact Hl1y.
+ (* l1 in y's class, l2 in y's class *)
      unfold uf_find in Hl1y, Hl2y.
      assert (H1: u x =? u l1 = false).
      { apply Nat.eqb_neq. intro H. 
        (* If u x = u l1 and u l1 = u y, then u x = u y *)
        assert (Hxy_eq: u x = u y).
        { rewrite H. exact Hl1y. }
        (* But then l1 and l2 would already be equivalent *)
        unfold uf_same_set in Hbefore.
        apply Nat.eqb_neq in Hbefore.
        apply Hbefore.
        unfold uf_find.
        rewrite Hl1y, Hl2y.
        reflexivity. }
      assert (H2: u x =? u l2 = false).
      { apply Nat.eqb_neq. intro H. 
        (* Similar reasoning *)
        assert (Hxy_eq: u x = u y).
        { rewrite H. exact Hl2y. }
        unfold uf_same_set in Hbefore.
        apply Nat.eqb_neq in Hbefore.
        apply Hbefore.
        unfold uf_find.
        rewrite Hl1y, Hl2y.
        reflexivity. }
      rewrite H1, H2.
      rewrite Hl1y, Hl2y.
      reflexivity.
Qed.

(** 4. Direct computation of find after union *)
Lemma uf_find_after_union : forall u x y z,
  uf_find (uf_union u x y) z = 
  if uf_find u x =? uf_find u z then uf_find u y else uf_find u z.
Proof.
  intros u x y z.
  unfold uf_union, uf_find.
  reflexivity.
Qed.

(** 5. process_pixel maintains background labels *)
Lemma process_pixel_maintains_background_labels : 
  forall img adj check_neighbors s c processed,
  state_labels_background img s -> 
  forall c', In c' processed -> 
  get_pixel img c' = false -> 
  labels (process_pixel img adj check_neighbors s c) c' = 0.
Proof.
  intros img adj check_neighbors s c processed Hbg c' Hc'_in Hc'_bg.
  destruct (coord_eqb c c') eqn:Heq.
  - (* c = c' *)
    apply coord_eqb_true_iff in Heq. subst c'.
    rewrite process_pixel_background_unchanged.
    + apply Hbg. assumption.
    + assumption.
  - (* c ≠ c' *)
    rewrite process_pixel_preserves_other.
    + apply Hbg. assumption.
    + intro H. subst c'. rewrite coord_eqb_refl in Heq. discriminate.
Qed.

(** 6. process_pixel maintains foreground labels *)
Lemma process_pixel_maintains_foreground_labels :
  forall img adj check_neighbors s c processed,
  ~ In c processed ->
  (forall c', In c' processed -> get_pixel img c' = true -> labels s c' > 0) ->
  forall c', In c' processed -> 
  get_pixel img c' = true -> 
  labels (process_pixel img adj check_neighbors s c) c' > 0.
Proof.
  intros img adj check_neighbors s c processed Hnotin Hfg c' Hc'_in Hc'_fg.
  rewrite process_pixel_preserves_other.
  - apply Hfg; assumption.
  - intro H. subst c'. contradiction.
Qed.

(** 7. process_pixel maintains unprocessed pixels unlabeled *)
Lemma process_pixel_maintains_unprocessed :
  forall img adj check_neighbors s c processed,
  (forall c', ~ In c' processed -> labels s c' = 0) ->
  forall c', ~ In c' (c :: processed) -> 
  labels (process_pixel img adj check_neighbors s c) c' = 0.
Proof.
  intros img adj check_neighbors s c processed Hunproc c' Hc'_notin.
  assert (c' <> c).
  { intro H. subst c'. apply Hc'_notin. left. reflexivity. }
  rewrite process_pixel_preserves_other; auto.
  apply Hunproc.
  intro Hc'_in. apply Hc'_notin. right. assumption.
Qed.

(** The key theorem: processing a pixel maintains strong partial correctness *)
Theorem process_pixel_maintains_invariant : 
  forall img adj check_neighbors s c processed,
  (* Assumptions about the adjacency relation *)
  (forall a b, adj a b = adj b a) ->
  (* Assumptions about check_neighbors *)
  (forall c', In c' (check_neighbors img c) -> 
    get_pixel img c' = true /\ adj c' c = true /\ raster_lt c' c = true) ->
  (forall c1 c2, get_pixel img c1 = true -> get_pixel img c2 = true ->
    adj c1 c2 = true -> raster_lt c1 c2 = true -> 
    c2 = c -> In c1 (check_neighbors img c)) ->
  (* Current state satisfies invariant *)
  strong_partial_correct img adj s processed ->
  raster_prefix processed ->
  ~ In c processed ->
  (forall c', In c' processed -> raster_lt c' c = true) ->
  next_label s > 0 ->
  (* Then the new state maintains invariant *)
  strong_partial_correct img adj (process_pixel img adj check_neighbors s c) (c :: processed).
Proof.
  intros img adj check_neighbors s c processed Hadj_sym Hcheck_sound Hcheck_complete 
         Hinv Hprefix Hnotin Hbefore Hnext.
  
  set (s' := process_pixel img adj check_neighbors s c).
  unfold strong_partial_correct in *.
  destruct Hinv as [Hbg [Hfg [Hunproc Hprior]]].
  split; [|split; [|split]].
  
  (** Part 1: Background pixels stay labeled 0 **)
  - intros c' [Hc'_eq | Hc'_in] Hc'_bg.
    + (* c' = c *)
      subst c'. unfold s'.
      rewrite process_pixel_background_unchanged; auto.
    + (* c' ∈ processed *)
      unfold s'.
      rewrite process_pixel_labels_unchanged.
      * apply Hbg; assumption.
      * intro Heq. subst c'. contradiction.

  (** Part 2: Foreground pixels get positive labels **)
  - intros c' [Hc'_eq | Hc'_in] Hc'_fg.
    + (* c' = c *)
      subst c'. unfold s'.
      apply process_pixel_labels_current; assumption.
    + (* c' ∈ processed *)
      unfold s'.
      rewrite process_pixel_labels_unchanged.
      * apply Hfg; assumption.
      * intro Heq. subst c'. contradiction.

  (** Part 3: Unprocessed pixels stay unlabeled **)
  - intros c' Hc'_notin.
    assert (c' <> c).
    { intro Heq. subst c'. apply Hc'_notin. left. reflexivity. }
    unfold s'.
    rewrite process_pixel_labels_unchanged; auto.
    apply Hunproc.
    intro Hc'_in. apply Hc'_notin. right. assumption.

(** Part 4: Prior-neighbor equivalence **)
  - intros c1 c2 Hc1_in Hc2_in Hc1_fg Hc2_fg Hadj Hc1_before_c2.
    
    (* Case analysis on which pixels are c *)
    destruct Hc1_in as [Hc1_eq | Hc1_old]; destruct Hc2_in as [Hc2_eq | Hc2_old].
    
    + (* Both c1 = c and c2 = c - impossible since c1 ≠ c2 *)
      subst c1 c2. exfalso.
      rewrite raster_lt_irrefl in Hc1_before_c2. discriminate.
    
    + (* c1 = c, c2 ∈ processed - impossible since c comes after all processed *)
      subst c1. exfalso.
      assert (raster_lt c2 c = true) by (apply Hbefore; assumption).
      (* We have both raster_lt c2 c and raster_lt c c2, which is impossible *)
      assert (raster_lt c c = true).
      { apply (raster_lt_trans c c2 c); assumption. }
      rewrite raster_lt_irrefl in H0. discriminate.
    
+ (* c1 ∈ processed, c2 = c - this is the key case *)
      subst c2.
      (* c1 is a prior neighbor of c *)
      assert (In c1 (check_neighbors img c)).
      { apply (Hcheck_complete c1 c Hc1_fg Hc2_fg Hadj Hc1_before_c2).
        reflexivity. }
      
      unfold s'.
      (* Labels of c1 unchanged *)
      assert (Hlabel_c1: labels s' c1 = labels s c1).
      { apply process_pixel_labels_unchanged. intro; subst. contradiction. }
      
(* After processing, c's label is equivalent to c1's label *)
      assert (Hpos_c1: labels s c1 > 0).
      { apply Hfg; assumption. }
      assert (Hlemma := process_pixel_labels_current_pixel img adj check_neighbors s c Hc2_fg Hnext).
      destruct Hlemma as [_ Hequiv].
      
fold s'.
      rewrite Hlabel_c1.
      rewrite uf_same_set_sym.
      apply Hequiv; assumption.
    
+ (* c1, c2 ∈ processed - both labels unchanged *)
      unfold s'.
      assert (labels s' c1 = labels s c1).
      { apply process_pixel_labels_unchanged. intro; subst. contradiction. }
      assert (labels s' c2 = labels s c2).
      { apply process_pixel_labels_unchanged. intro; subst. contradiction. }
      
      fold s'.
      rewrite H, H0.
      
      (* Equivalence preserved by process_pixel *)
      apply process_pixel_preserves_equiv.
      apply Hprior; assumption.
Qed.
