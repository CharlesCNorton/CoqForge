(*
  CoqChess.v
  
  Chess formalization with machine-checked correctness proofs.
  Uses Fin.t 8 for coordinates, Prop specifications, boolean execution.
*)

(* ========================================================================= *)
(* IMPORTS                                                                   *)
(* ========================================================================= *)

Require Import Coq.Init.Prelude.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Decidable.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.Vector.
Local Notation vec := Vector.t.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.NArith.
Require Import Coq.micromega.Lia.

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Import ListNotations.
Require Import Coq.Init.Nat.

Require Import Coq.Bool.Bool.
Require Import Coq.Bool.BoolEq.
Require Import Coq.Bool.Sumbool.

Require Import Coq.ssr.ssreflect.
Require Import Coq.ssr.ssrfun.
Require Import Coq.ssr.ssrbool.

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Set Program Mode.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z_scope.
Open Scope bool_scope.

(* ========================================================================= *)
(* GLOBAL NOTATIONS                                                         *)
(* ========================================================================= *)

Notation "'F8'" := (Fin.t 8) (at level 0).

(* Fin constructor aliases to avoid qualification *)
Module Export FinNotations.
  Notation F1 := Fin.F1.
  Notation FS := Fin.FS.
End FinNotations.

Reserved Notation "b [ p ]" (at level 9, no associativity).
Reserved Notation "b [ p := x ]" (at level 9, no associativity).

(* ========================================================================= *)
(* COORDINATES                                                               *)
(* ========================================================================= *)

Definition Rank : Type := F8.
Definition File : Type := F8.

Record Position : Type := mkPos {
  pos_rank : Rank;
  pos_file : File
}.

Definition position_eqb (p1 p2 : Position) : bool :=
  Fin.eqb (pos_rank p1) (pos_rank p2) && Fin.eqb (pos_file p1) (pos_file p2).

Lemma position_eqb_spec p1 p2 : reflect (p1 = p2) (position_eqb p1 p2).
Proof.
  case H: (position_eqb p1 p2); constructor.
  - unfold position_eqb in H.
    apply andb_prop in H. destruct H as [Hr Hf].
    apply Fin.eqb_eq in Hr. apply Fin.eqb_eq in Hf.
    destruct p1, p2; simpl in *; subst; reflexivity.
  - intro Heq. subst p2.
    unfold position_eqb in H.
    assert (Hr: Fin.eqb (pos_rank p1) (pos_rank p1) = true).
    { apply Fin.eqb_eq. reflexivity. }
    assert (Hf: Fin.eqb (pos_file p1) (pos_file p1) = true).
    { apply Fin.eqb_eq. reflexivity. }
    rewrite Hr in H. rewrite Hf in H. discriminate.
Qed.

Definition Position_dec : forall p q : Position, {p = q} + {p <> q}.
Proof. 
  intros p q; destruct (position_eqb_spec p q); [left|right]; auto. 
Defined.

Fixpoint enum_fin (n : nat) : list (Fin.t n) :=
  match n with
  | O => []
  | S n' => Fin.F1 :: map Fin.FS (enum_fin n')
  end.

Lemma NoDup_map {A B : Type} (f : A -> B) (l : list A) :
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup l -> NoDup (map f l).
Proof.
  intros Hinj Hnd. induction Hnd; simpl; constructor.
  - intro Hmap. apply in_map_iff in Hmap as [y [Hy Hin]].
    symmetry in Hy.
    pose proof (Hinj x y (or_introl eq_refl) (or_intror Hin) Hy).
    subst. contradiction.
  - apply IHHnd. intros x0 y0 Hx Hy. apply Hinj; right; auto.
Qed.

Lemma enum_fin_NoDup n : NoDup (enum_fin n).
Proof.
  induction n as [|n IH]; simpl; constructor.
  - intro Hin. apply in_map_iff in Hin as [x [Hx _]]. inversion Hx.
  - apply NoDup_map.
    + intros x y _ _ Heq.
      dependent destruction Heq. reflexivity.
    + exact IH.
Qed.

Lemma enum_fin_complete n (i : Fin.t n) : In i (enum_fin n).
Proof.
  revert i; induction n as [|n IH]; intros i.
  - dependent destruction i.
  - dependent destruction i; simpl; auto. right. apply in_map, IH.
Qed.

Definition fins8 : list F8 := enum_fin 8.

Definition all_positions : list Position :=
  flat_map (fun r => map (fun f => mkPos r f) fins8) fins8.

Lemma mkPos_injective (r : Rank) (f1 f2 : File) :
  mkPos r f1 = mkPos r f2 -> f1 = f2.
Proof. intro H; inversion H; reflexivity. Qed.

Lemma NoDup_app {A : Type} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> In x l2 -> False) -> NoDup (l1 ++ l2).
Proof.
  intros H1 H2 Hdisj.
  induction H1 as [|h t Hh Ht IH]; simpl; auto.
  constructor.
  - intro Hin. apply in_app_or in Hin as [Hin1 | Hin2].
    + contradiction.
    + apply (Hdisj h); auto. left. reflexivity.
  - apply IH. intros x0 Hx0 Hy0. apply (Hdisj x0); auto. right. auto.
Qed.

Lemma NoDup_flat_map_disjoint {A B : Type} (f : A -> list B) (l : list A) :
  NoDup l ->
  (forall x, In x l -> NoDup (f x)) ->
  (forall x y, In x l -> In y l -> x <> y -> 
    forall b, ~ (In b (f x) /\ In b (f y))) ->
  NoDup (flat_map f l).
Proof.
  intros Hnd Hnd_each Hdisj.
  induction l.
  - simpl. constructor.
  - simpl. apply NoDup_app.
    + inversion Hnd. subst. apply Hnd_each. left. reflexivity.
    + inversion Hnd. subst. apply IHl; auto.
      * intros. apply Hnd_each. right. exact H.
      * intros x y Hx Hy Hneq. apply Hdisj; auto. right. auto. right. auto.
    + intros b Hb1 Hb2.
      apply in_flat_map in Hb2.
      destruct Hb2 as [y [Hy Hby]].
      inversion Hnd. subst.
      assert (~ (In b (f a) /\ In b (f y))).
      { apply Hdisj. left. reflexivity. right. exact Hy. intro. subst. contradiction. }
      destruct H. split; auto.
Qed.

Lemma all_positions_NoDup : NoDup all_positions.
Proof.
  unfold all_positions.
  apply NoDup_flat_map_disjoint.
  - apply enum_fin_NoDup.
  - intros r _. apply NoDup_map.
    + intros f1 f2 _ _ Heq. apply mkPos_injective with (r := r). exact Heq.
    + apply enum_fin_NoDup.
  - intros r1 r2 Hr1 Hr2 Hneq p [Hp1 Hp2].
    apply in_map_iff in Hp1 as [f1 [Heq1 _]].
    apply in_map_iff in Hp2 as [f2 [Heq2 _]].
    subst p. inversion Heq2 as [Hrf]. subst r2. exact (Hneq eq_refl).
Qed.

Lemma all_positions_complete : forall p, In p all_positions.
Proof.
  intros [r f]. unfold all_positions.
  apply in_flat_map. exists r. split; [apply enum_fin_complete|].
  apply in_map. apply enum_fin_complete.
Qed.

Definition rankZ (p: Position) : Z :=
  Z.of_nat (proj1_sig (Fin.to_nat (pos_rank p))).

Definition fileZ (p: Position) : Z :=
  Z.of_nat (proj1_sig (Fin.to_nat (pos_file p))).

Definition within8 (z: Z) : bool := (0 <=? z) && (z <? 8).

Lemma within8_true_iff z : within8 z = true <-> (0 <= z < 8)%Z.
Proof.
  unfold within8. rewrite andb_true_iff.
  rewrite Z.leb_le. rewrite Z.ltb_lt. tauto.
Qed.

Lemma rankZ_bounds p : (0 <= rankZ p < 8)%Z.
Proof.
  unfold rankZ. destruct (Fin.to_nat (pos_rank p)) as [n Hn]. simpl. lia.
Qed.

Lemma fileZ_bounds p : (0 <= fileZ p < 8)%Z.
Proof.
  unfold fileZ. destruct (Fin.to_nat (pos_file p)) as [n Hn]. simpl. lia.
Qed.

Lemma Z_to_nat_lt_8 z : (0 <= z < 8)%Z -> (Z.to_nat z < 8)%nat.
Proof.
  intros [Hz0 Hz8].
  rewrite <- (Z2Nat.id z Hz0) in Hz8.
  change 8 with (Z.of_nat 8) in Hz8.
  apply Nat2Z.inj_lt in Hz8. simpl in Hz8. exact Hz8.
Qed.

Definition offset (p : Position) (dr df : Z) : option Position :=
  let r' := rankZ p + dr in
  let f' := fileZ p + df in
  if (0 <=? r') && (r' <? 8) && (0 <=? f') && (f' <? 8) then
    let nr := Z.to_nat r' in
    let nf := Z.to_nat f' in
    match lt_dec nr 8, lt_dec nf 8 with
    | left Hr, left Hf => Some (mkPos (Fin.of_nat_lt Hr) (Fin.of_nat_lt Hf))
    | _, _ => None
    end
  else None.

Lemma offset_to_nat (p p' : Position) dr df :
  offset p dr df = Some p' ->
  proj1_sig (Fin.to_nat (pos_rank p')) = Z.to_nat (rankZ p + dr) /\
  proj1_sig (Fin.to_nat (pos_file p')) = Z.to_nat (fileZ p + df).
Proof.
  unfold offset. 
  set (r' := rankZ p + dr). set (f' := fileZ p + df).
  destruct ((0 <=? r') && (r' <? 8) && (0 <=? f') && (f' <? 8)) eqn:Eb; [|discriminate].
  set (nr := Z.to_nat r'). set (nf := Z.to_nat f').
  destruct (lt_dec nr 8) as [Hr|Hr]; [|discriminate].
  destruct (lt_dec nf 8) as [Hf|Hf]; [|discriminate].
  intro H. inversion H. clear H. subst p'.
  split; rewrite Fin.to_nat_of_nat; reflexivity.
Qed.

Lemma andb4_true (a b c d : bool) :
  a && b && c && d = true -> 
  a = true /\ b = true /\ c = true /\ d = true.
Proof.
  intro H.
  apply andb_prop in H as [H1 H2].
  apply andb_prop in H1 as [H3 H4].
  apply andb_prop in H3 as [Ha Hb].
  exact (conj Ha (conj Hb (conj H4 H2))).
Qed.

Lemma offset_guards_true p dr df p' :
  offset p dr df = Some p' ->
  within8 (rankZ p + dr) = true /\ within8 (fileZ p + df) = true.
Proof.
  unfold offset. intros Hok.
  set (r' := rankZ p + dr). set (f' := fileZ p + df).
  case_eq ((0 <=? r') && (r' <? 8) && (0 <=? f') && (f' <? 8)); 
    intro Hg; rewrite Hg in Hok; [|discriminate].
  apply andb4_true in Hg as [Hr1 [Hr2 [Hf1 Hf2]]].
  split; unfold within8; apply andb_true_iff; split; assumption.
Qed.

Lemma within8_true_bounds z : within8 z = true -> (0 <= z < 8)%Z.
Proof. intro Hz; apply within8_true_iff in Hz; exact Hz. Qed.

Lemma within8_rankZ p : within8 (rankZ p) = true.
Proof.
  unfold within8. apply andb_true_iff. split.
  - apply Z.leb_le. apply rankZ_bounds.
  - apply Z.ltb_lt. apply rankZ_bounds.
Qed.

Lemma within8_fileZ p : within8 (fileZ p) = true.
Proof.
  unfold within8. apply andb_true_iff. split.
  - apply Z.leb_le. apply fileZ_bounds.
  - apply Z.ltb_lt. apply fileZ_bounds.
Qed.

Lemma within8_bounds_nonneg z : within8 z = true -> 0 <= z.
Proof.
  intro H. apply within8_true_bounds in H. lia.
Qed.

Lemma offset_rankZ_eq p p' dr df :
  offset p dr df = Some p' ->
  proj1_sig (Fin.to_nat (pos_rank p')) = Z.to_nat (rankZ p + dr).
Proof.
  intro H. pose proof H as H'.
  apply offset_to_nat in H' as [Hr _]. exact Hr.
Qed.

Lemma offset_fileZ_eq p p' dr df :
  offset p dr df = Some p' ->
  proj1_sig (Fin.to_nat (pos_file p')) = Z.to_nat (fileZ p + df).
Proof.
  intro H. pose proof H as H'.
  apply offset_to_nat in H' as [_ Hf]. exact Hf.
Qed.

Lemma offset_guard_backward p dr df :
  within8 (rankZ p + dr) = true ->
  within8 (fileZ p + df) = true ->
  (0 <=? rankZ p) && (rankZ p <? 8) && (0 <=? fileZ p) && (fileZ p <? 8) = true.
Proof.
  intros _ _.
  repeat (apply andb_true_intro; split).
  - apply Z.leb_le. apply rankZ_bounds.
  - apply Z.ltb_lt. apply rankZ_bounds.
  - apply Z.leb_le. apply fileZ_bounds.
  - apply Z.ltb_lt. apply fileZ_bounds.
Qed.

Lemma Z_to_nat_rankZ_lt_8 p : (Z.to_nat (rankZ p) < 8)%nat.
Proof.
  apply Z_to_nat_lt_8. apply rankZ_bounds.
Qed.

Lemma Z_to_nat_fileZ_lt_8 p : (Z.to_nat (fileZ p) < 8)%nat.
Proof.
  apply Z_to_nat_lt_8. apply fileZ_bounds.
Qed.

Lemma offset_rankZ_roundtrip p p' dr df :
  offset p dr df = Some p' ->
  Z.of_nat (Z.to_nat (rankZ p + dr)) = rankZ p + dr.
Proof.
  intro H.
  assert (Hguards: within8 (rankZ p + dr) = true /\ within8 (fileZ p + df) = true).
  { apply offset_guards_true with (p' := p'). exact H. }
  destruct Hguards as [Hrg _].
  apply Z2Nat.id.
  apply within8_bounds_nonneg. exact Hrg.
Qed.

Lemma offset_fileZ_roundtrip p p' dr df :
  offset p dr df = Some p' ->
  Z.of_nat (Z.to_nat (fileZ p + df)) = fileZ p + df.
Proof.
  intro H.
  assert (Hguards: within8 (rankZ p + dr) = true /\ within8 (fileZ p + df) = true).
  { apply offset_guards_true with (p' := p'). exact H. }
  destruct Hguards as [_ Hfg].
  apply Z2Nat.id.
  apply within8_bounds_nonneg. exact Hfg.
Qed.

Lemma offset_rankZ_recover p p' dr df :
  offset p dr df = Some p' ->
  rankZ p' = rankZ p + dr.
Proof.
  intro Hok.
  unfold rankZ.
  pose proof Hok as Hok'.
  apply offset_to_nat in Hok' as [Hr _].
  rewrite Hr.
  assert (Hroundtrip: Z.of_nat (Z.to_nat (rankZ p + dr)) = rankZ p + dr).
  { apply offset_rankZ_roundtrip with (p' := p') (df := df). exact Hok. }
  exact Hroundtrip.
Qed.

Lemma offset_fileZ_recover p p' dr df :
  offset p dr df = Some p' ->
  fileZ p' = fileZ p + df.
Proof.
  intro Hok.
  unfold fileZ.
  pose proof Hok as Hok'.
  apply offset_to_nat in Hok' as [_ Hf].
  rewrite Hf.
  assert (Hroundtrip: Z.of_nat (Z.to_nat (fileZ p + df)) = fileZ p + df).
  { apply offset_fileZ_roundtrip with (p' := p') (dr := dr). exact Hok. }
  exact Hroundtrip.
Qed.

Theorem offset_preserves_board_validity (p p' : Position) (dr df : Z) :
  offset p dr df = Some p' ->
  rankZ p' = rankZ p + dr /\
  fileZ p' = fileZ p + df /\
  (0 <= rankZ p' < 8) /\
  (0 <= fileZ p' < 8).
Proof.
  intro H.
  split; [|split; [|split]].
  - apply offset_rankZ_recover with (df := df). exact H.
  - apply offset_fileZ_recover with (dr := dr). exact H.
  - apply rankZ_bounds.
  - apply fileZ_bounds.
Qed.

Lemma offset_reverse (p p' : Position) (dr df : Z) :
  offset p dr df = Some p' ->
  offset p' (-dr) (-df) = Some p.
Proof.
  intro H. pose proof H as Hcopy.
  apply offset_rankZ_recover with (df := df) in H as Hr.
  apply offset_fileZ_recover with (dr := dr) in H as Hf.
  unfold offset in Hcopy.
  case_eq ((0 <=? rankZ p + dr) && (rankZ p + dr <? 8) && (0 <=? fileZ p + df) && (fileZ p + df <? 8));
    intro Hcond; rewrite Hcond in Hcopy; [|discriminate].
  destruct (lt_dec (Z.to_nat (rankZ p + dr)) 8) as [HrOk|]; [|discriminate].
  destruct (lt_dec (Z.to_nat (fileZ p + df)) 8) as [HfOk|]; [|discriminate].
  inversion Hcopy. clear Hcopy. subst p'.
  unfold offset.
  simpl. unfold rankZ, fileZ. simpl.
  rewrite !Fin.to_nat_of_nat. simpl.
  assert (Hr_nat: Z.of_nat (Z.to_nat (rankZ p + dr)) = rankZ p + dr).
  { apply Z2Nat.id. apply andb4_true in Hcond as [Ha [Hb _]].
    apply Z.leb_le in Ha. apply Z.ltb_lt in Hb. lia. }
  assert (Hf_nat: Z.of_nat (Z.to_nat (fileZ p + df)) = fileZ p + df).
  { apply Z2Nat.id. apply andb4_true in Hcond as [_ [_ [Hc Hd]]].
    apply Z.leb_le in Hc. apply Z.ltb_lt in Hd. lia. }
  rewrite Hr_nat. rewrite Hf_nat.
  replace (rankZ p + dr + -dr) with (rankZ p) by ring.
  replace (fileZ p + df + -df) with (fileZ p) by ring.
  assert (Hg: (0 <=? rankZ p) && (rankZ p <? 8) && (0 <=? fileZ p) && (fileZ p <? 8) = true).
  { apply andb_true_intro. split. apply andb_true_intro. split. apply andb_true_intro. split.
    apply Z.leb_le; apply rankZ_bounds.
    apply Z.ltb_lt; apply rankZ_bounds.
    apply Z.leb_le; apply fileZ_bounds.
    apply Z.ltb_lt; apply fileZ_bounds. }
  rewrite Hg.
  destruct (lt_dec (Z.to_nat (rankZ p)) 8) as [Hr'|];
    [|exfalso; apply n; apply Z_to_nat_rankZ_lt_8].
  destruct (lt_dec (Z.to_nat (fileZ p)) 8) as [Hf'|];
    [|exfalso; apply n; apply Z_to_nat_fileZ_lt_8].
  f_equal.
  destruct p as [pr pf].
  assert (HrEq: Fin.of_nat_lt Hr' = pr).
  { apply Fin.to_nat_inj. rewrite Fin.to_nat_of_nat.
    unfold rankZ. simpl.
    destruct (Fin.to_nat pr) as [x Hx]. simpl.
    rewrite Nat2Z.id. reflexivity. }
  assert (HfEq: Fin.of_nat_lt Hf' = pf).
  { apply Fin.to_nat_inj. rewrite Fin.to_nat_of_nat.
    unfold fileZ. simpl.
    destruct (Fin.to_nat pf) as [y Hy]. simpl.
    rewrite Nat2Z.id. reflexivity. }
  rewrite HrEq. rewrite HfEq. simpl. reflexivity.
Qed.

Theorem knight_move_symmetric (p p' : Position) :
  (offset p 2 1 = Some p' \/ offset p 2 (-1) = Some p' \/
   offset p (-2) 1 = Some p' \/ offset p (-2) (-1) = Some p' \/
   offset p 1 2 = Some p' \/ offset p 1 (-2) = Some p' \/
   offset p (-1) 2 = Some p' \/ offset p (-1) (-2) = Some p') ->
  (offset p' (-2) (-1) = Some p \/ offset p' (-2) 1 = Some p \/
   offset p' 2 (-1) = Some p \/ offset p' 2 1 = Some p \/
   offset p' (-1) (-2) = Some p \/ offset p' (-1) 2 = Some p \/
   offset p' 1 (-2) = Some p \/ offset p' 1 2 = Some p).
Proof.
  intro H.
  destruct H as [H1|[H2|[H3|[H4|[H5|[H6|[H7|H8]]]]]]].
  - left. apply offset_reverse with (dr := 2) (df := 1). exact H1.
  - right. left. apply offset_reverse with (dr := 2) (df := -1). exact H2.
  - right. right. left. apply offset_reverse with (dr := -2) (df := 1). exact H3.
  - right. right. right. left. apply offset_reverse with (dr := -2) (df := -1). exact H4.
  - right. right. right. right. left. apply offset_reverse with (dr := 1) (df := 2). exact H5.
  - right. right. right. right. right. left. apply offset_reverse with (dr := 1) (df := -2). exact H6.
  - right. right. right. right. right. right. left. apply offset_reverse with (dr := -1) (df := 2). exact H7.
  - right. right. right. right. right. right. right. apply offset_reverse with (dr := -1) (df := -2). exact H8.
Qed.

Theorem offset_invertible (p p' : Position) (dr df : Z) :
  offset p dr df = Some p' -> offset p' (-dr) (-df) = Some p.
Proof.
  apply offset_reverse.
Qed.

(* ========================================================================= *)
(* BASIC TYPES                                                               *)
(* ========================================================================= *)

Inductive Color : Type := White | Black.

Definition opposite_color (c : Color) : Color :=
  match c with White => Black | Black => White end.

Lemma opposite_color_involutive : forall c, opposite_color (opposite_color c) = c.
Proof.
  destruct c; reflexivity.
Qed.

Lemma opposite_color_neq : forall c, opposite_color c <> c.
Proof.
  destruct c; discriminate.
Qed.

Definition color_eqb (c1 c2 : Color) : bool :=
  match c1 with
  | White => match c2 with White => true | Black => false end
  | Black => match c2 with White => false | Black => true end
  end.

Lemma color_eqb_spec : forall c1 c2 : Color, reflect (c1 = c2) (color_eqb c1 c2).
Proof.
  intros c1 c2.
  destruct c1, c2; simpl; constructor; try congruence.
Qed.

Lemma color_eqb_refl c : color_eqb c c = true.
Proof.
  destruct c; reflexivity.
Qed.

Definition Color_dec : forall c1 c2 : Color, {c1 = c2} + {c1 <> c2}.
Proof.
  decide equality.
Defined.

Lemma color_eqb_sym : forall c1 c2, color_eqb c1 c2 = color_eqb c2 c1.
Proof.
  destruct c1, c2; reflexivity.
Qed.

Lemma color_eqb_trans : forall c1 c2 c3,
  color_eqb c1 c2 = true -> color_eqb c2 c3 = true -> color_eqb c1 c3 = true.
Proof.
  intros c1 c2 c3 H12 H23.
  destruct (color_eqb_spec c1 c2); try discriminate.
  destruct (color_eqb_spec c2 c3); try discriminate.
  subst. apply color_eqb_refl.
Qed.

Inductive PieceType : Type := Pawn | Knight | Bishop | Rook | Queen | King.

Definition ptype_eqb (p1 p2 : PieceType) : bool :=
  match p1 with
  | Pawn => match p2 with Pawn => true | _ => false end
  | Knight => match p2 with Knight => true | _ => false end
  | Bishop => match p2 with Bishop => true | _ => false end
  | Rook => match p2 with Rook => true | _ => false end
  | Queen => match p2 with Queen => true | _ => false end
  | King => match p2 with King => true | _ => false end
  end.

Lemma ptype_eqb_spec p1 p2 : reflect (p1 = p2) (ptype_eqb p1 p2).
Proof.
  destruct p1, p2; simpl; constructor; congruence.
Qed.

Lemma ptype_eqb_refl p : ptype_eqb p p = true.
Proof.
  destruct p; reflexivity.
Qed.

Definition PieceType_dec : forall p1 p2 : PieceType, {p1 = p2} + {p1 <> p2}.
Proof.
  decide equality.
Defined.

Lemma ptype_eqb_sym : forall p1 p2, ptype_eqb p1 p2 = ptype_eqb p2 p1.
Proof.
  destruct p1, p2; reflexivity.
Qed.

Lemma ptype_eqb_trans : forall p1 p2 p3,
  ptype_eqb p1 p2 = true -> ptype_eqb p2 p3 = true -> ptype_eqb p1 p3 = true.
Proof.
  intros p1 p2 p3 H12 H23.
  destruct (ptype_eqb_spec p1 p2); try discriminate.
  destruct (ptype_eqb_spec p2 p3); try discriminate.
  subst. apply ptype_eqb_refl.
Qed.

Record Piece : Type := mkPiece {
  piece_color : Color;
  piece_type : PieceType
}.

Definition piece_eqb (p1 p2 : Piece) : bool :=
  color_eqb (piece_color p1) (piece_color p2) && 
  ptype_eqb (piece_type p1) (piece_type p2).

Lemma piece_eqb_spec p1 p2 : reflect (p1 = p2) (piece_eqb p1 p2).
Proof.
  case H: (piece_eqb p1 p2); constructor.
  - unfold piece_eqb in H. apply andb_prop in H. destruct H as [Hc Ht].
    destruct (color_eqb_spec (piece_color p1) (piece_color p2)); try discriminate.
    destruct (ptype_eqb_spec (piece_type p1) (piece_type p2)); try discriminate.
    destruct p1, p2; simpl in *; subst; reflexivity.
  - intro Heq. subst. unfold piece_eqb in H.
    rewrite color_eqb_refl in H. rewrite ptype_eqb_refl in H.
    discriminate.
Qed.

Lemma piece_eqb_refl p : piece_eqb p p = true.
Proof.
  unfold piece_eqb. rewrite color_eqb_refl. rewrite ptype_eqb_refl. reflexivity.
Qed.

Definition Piece_dec : forall p1 p2 : Piece, {p1 = p2} + {p1 <> p2}.
Proof.
  intros p1 p2.
  destruct p1 as [c1 t1], p2 as [c2 t2].
  destruct (Color_dec c1 c2), (PieceType_dec t1 t2); subst.
  - left; reflexivity.
  - right; intro H; inversion H; contradiction.
  - right; intro H; inversion H; contradiction.
  - right; intro H; inversion H; contradiction.
Defined.

(* Common piece constructors *)
Definition white_pawn := mkPiece White Pawn.
Definition white_knight := mkPiece White Knight.
Definition white_bishop := mkPiece White Bishop.
Definition white_rook := mkPiece White Rook.
Definition white_queen := mkPiece White Queen.
Definition white_king := mkPiece White King.

Definition black_pawn := mkPiece Black Pawn.
Definition black_knight := mkPiece Black Knight.
Definition black_bishop := mkPiece Black Bishop.
Definition black_rook := mkPiece Black Rook.
Definition black_queen := mkPiece Black Queen.
Definition black_king := mkPiece Black King.

Lemma piece_eta : forall p, p = mkPiece (piece_color p) (piece_type p).
Proof.
  destruct p; reflexivity.
Qed.

Inductive CastleSide : Type := KingSide | QueenSide.

Definition castle_side_eqb (s1 s2 : CastleSide) : bool :=
  match s1 with
  | KingSide => match s2 with KingSide => true | QueenSide => false end
  | QueenSide => match s2 with KingSide => false | QueenSide => true end
  end.

Lemma castle_side_eqb_spec s1 s2 : reflect (s1 = s2) (castle_side_eqb s1 s2).
Proof.
  destruct s1, s2; simpl; constructor; congruence.
Qed.

Definition CastleSide_dec : forall s1 s2 : CastleSide, {s1 = s2} + {s1 <> s2}.
Proof.
  decide equality.
Defined.

Inductive Move : Type :=
  | MNormal : Position -> Position -> option PieceType -> Move
  | MCastle : CastleSide -> Move.

Definition move_eqb (m1 m2 : Move) : bool :=
  match m1 with
  | MNormal s1 d1 p1 =>
      match m2 with
      | MNormal s2 d2 p2 =>
          position_eqb s1 s2 && position_eqb d1 d2 &&
          match p1 with
          | None => match p2 with None => true | Some _ => false end
          | Some t1 => match p2 with None => false | Some t2 => ptype_eqb t1 t2 end
          end
      | MCastle _ => false
      end
  | MCastle s1 =>
      match m2 with
      | MNormal _ _ _ => false
      | MCastle s2 => castle_side_eqb s1 s2
      end
  end.

Lemma move_eqb_spec m1 m2 : reflect (m1 = m2) (move_eqb m1 m2).
Proof.
  destruct m1; destruct m2; simpl.
  - case H: (position_eqb p p1 && position_eqb p0 p2 && _); constructor.
    + apply andb_prop in H. destruct H as [H1 H2].
      apply andb_prop in H1. destruct H1 as [Hs Hd].
      destruct (position_eqb_spec p p1); try discriminate.
      destruct (position_eqb_spec p0 p2); try discriminate.
      subst. f_equal.
      destruct o as [pt1|], o0 as [pt2|]; try discriminate; auto.
      simpl in H2. destruct (ptype_eqb_spec pt1 pt2); try discriminate.
      subst. reflexivity.
    + intro Heq. injection Heq. intros. subst.
      unfold move_eqb in H. simpl in H.
      destruct (position_eqb_spec p1 p1); simpl in H; try congruence.
      destruct (position_eqb_spec p2 p2); simpl in H; try congruence.
      destruct o0 as [pt|]; simpl in H; try congruence.
      rewrite ptype_eqb_refl in H. congruence.
  - constructor. congruence.
  - constructor. congruence.
  - destruct (castle_side_eqb_spec c c0); constructor; congruence.
Qed.

Lemma move_eqb_refl m : move_eqb m m = true.
Proof.
  destruct m; simpl.
  - destruct (position_eqb_spec p p); simpl; try congruence.
    destruct (position_eqb_spec p0 p0); simpl; try congruence.
    simpl. destruct o as [pt|]; simpl; auto. apply ptype_eqb_refl.
  - destruct c; reflexivity.
Qed.

Definition Move_dec : forall m1 m2 : Move, {m1 = m2} + {m1 <> m2}.
Proof.
  intros m1 m2.
  destruct m1, m2.
  - destruct (Position_dec p p1), (Position_dec p0 p2); subst.
    + destruct o as [pt1|], o0 as [pt2|].
      * destruct (PieceType_dec pt1 pt2); subst.
        -- left; reflexivity.
        -- right; intro H; inversion H; contradiction.
      * right; intro H; inversion H.
      * right; intro H; inversion H.
      * left; reflexivity.
    + right; intro H; inversion H; contradiction.
    + right; intro H; inversion H; contradiction.
    + right; intro H; inversion H; contradiction.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - destruct (CastleSide_dec c c0); subst.
    + left; reflexivity.
    + right; intro H; inversion H; contradiction.
Defined.

(* Move destructors *)
Definition move_from (m : Move) : option Position :=
  match m with
  | MNormal from _ _ => Some from
  | MCastle _ => None
  end.

Definition move_to (m : Move) : option Position :=
  match m with
  | MNormal _ to _ => Some to
  | MCastle _ => None
  end.

Definition move_promotion (m : Move) : option PieceType :=
  match m with
  | MNormal _ _ promo => promo
  | MCastle _ => None
  end.

(* Move predicates *)
Definition is_normal_move (m : Move) : bool :=
  match m with MNormal _ _ _ => true | _ => false end.

Definition is_castle_move (m : Move) : bool :=
  match m with MCastle _ => true | _ => false end.

Definition is_promotion (m : Move) : bool :=
  match m with MNormal _ _ (Some _) => true | _ => false end.

(* Boolean predicate lemmas *)
Lemma color_eqb_true_iff : forall c1 c2, 
  color_eqb c1 c2 = true <-> c1 = c2.
Proof.
  intros c1 c2. split.
  - intro H. destruct (color_eqb_spec c1 c2); auto. discriminate.
  - intro H. subst. apply color_eqb_refl.
Qed.

Lemma color_eqb_false_iff : forall c1 c2,
  color_eqb c1 c2 = false <-> c1 <> c2.
Proof.
  intros c1 c2. split.
  - intro H. destruct (color_eqb_spec c1 c2). discriminate. auto.
  - intro H. destruct (color_eqb_spec c1 c2). contradiction. auto.
Qed.

Lemma ptype_eqb_true_iff : forall t1 t2,
  ptype_eqb t1 t2 = true <-> t1 = t2.
Proof.
  intros t1 t2. split.
  - intro H. destruct (ptype_eqb_spec t1 t2); auto. discriminate.
  - intro H. subst. apply ptype_eqb_refl.
Qed.

Lemma ptype_eqb_false_iff : forall t1 t2,
  ptype_eqb t1 t2 = false <-> t1 <> t2.
Proof.
  intros t1 t2. split.
  - intro H. destruct (ptype_eqb_spec t1 t2). discriminate. auto.
  - intro H. destruct (ptype_eqb_spec t1 t2). contradiction. auto.
Qed.

(* Exhaustiveness lemmas *)
Lemma Color_cases : forall (c : Color), c = White \/ c = Black.
Proof.
  destruct c; [left | right]; reflexivity.
Qed.

Lemma PieceType_cases : forall (t : PieceType),
  t = Pawn \/ t = Knight \/ t = Bishop \/ t = Rook \/ t = Queen \/ t = King.
Proof.
  destruct t; [left | right; left | right; right; left | 
               right; right; right; left | right; right; right; right; left |
               right; right; right; right; right]; reflexivity.
Qed.

Lemma CastleSide_cases : forall (s : CastleSide), s = KingSide \/ s = QueenSide.
Proof.
  destruct s; [left | right]; reflexivity.
Qed.

(* Promotion validity *)
Definition is_valid_promotion (pt : PieceType) : bool :=
  match pt with
  | Queen => true
  | Rook => true
  | Bishop => true
  | Knight => true
  | Pawn => false
  | King => false
  end.

Lemma is_valid_promotion_spec : forall pt,
  is_valid_promotion pt = true <-> 
  (pt = Queen \/ pt = Rook \/ pt = Bishop \/ pt = Knight).
Proof.
  intro pt. unfold is_valid_promotion. split.
  - destruct pt; intro H; try discriminate.
    + right; right; right; reflexivity.
    + right; right; left; reflexivity.
    + right; left; reflexivity.
    + left; reflexivity.
  - intros [H | [H | [H | H]]]; subst; reflexivity.
Qed.

(* ========================================================================= *)
(* BOARD IMPLEMENTATION                                                      *)
(* ========================================================================= *)

Definition Board := Position -> option Piece.

Definition board_empty : Board := fun _ => None.

Definition board_get (b : Board) (p : Position) : option Piece := b p.

Definition board_set (b : Board) (p : Position) (x : option Piece) : Board :=
  fun q => if Position_dec q p then x else b q.

Notation "b [ p ]" := (board_get b p).
Notation "b [ p := x ]" := (board_set b p x).

Lemma board_ext : forall b1 b2, 
  (forall p, b1[p] = b2[p]) -> b1 = b2.
Proof.
  intros b1 b2 H.
  apply functional_extensionality. exact H.
Qed.

Lemma board_set_same : forall b p x y,
  (b[p := x])[p := y] = b[p := y].
Proof.
  intros b p x y.
  apply board_ext. intro q.
  unfold board_get, board_set.
  destruct (Position_dec q p); reflexivity.
Qed.

Lemma board_set_comm : forall b p q x y,
  p <> q -> (b[p := x])[q := y] = (b[q := y])[p := x].
Proof.
  intros b p q x y Hneq.
  apply board_ext. intro r.
  unfold board_get, board_set.
  destruct (Position_dec r q), (Position_dec r p); subst; try reflexivity.
  contradiction.
Qed.

Lemma board_get_set_same : forall b p x,
  (b[p := x])[p] = x.
Proof.
  intros b p x.
  unfold board_get, board_set.
  destruct (Position_dec p p); [reflexivity | congruence].
Qed.

Lemma board_get_set_diff : forall b p q x,
  p <> q -> (b[p := x])[q] = b[q].
Proof.
  intros b p q x Hneq.
  unfold board_get, board_set.
  destruct (Position_dec q p).
  - subst. contradiction.
  - reflexivity.
Qed.

Lemma board_set_id b p :
  b[p := b[p]] = b.
Proof.
  apply board_ext. intro q.
  unfold board_get, board_set.
  destruct (Position_dec q p); subst; reflexivity.
Qed.

Lemma board_empty_get p :
  board_empty[p] = None.
Proof.
  reflexivity.
Qed.

Lemma board_set_empty_none b p :
  b[p := None] = b <-> b[p] = None.
Proof.
  split.
  - intro H. rewrite <- H. apply board_get_set_same.
  - intro H. apply board_ext. intro q.
    destruct (Position_dec q p).
    + subst. rewrite board_get_set_same. symmetry. exact H.
    + rewrite board_get_set_diff; auto.
Qed.

Definition occupied (b : Board) (p : Position) : bool :=
  match b[p] with
  | Some _ => true
  | None => false
  end.

Definition occupied_by (b : Board) (p : Position) (c : Color) : bool :=
  match b[p] with
  | Some piece => color_eqb (piece_color piece) c
  | None => false
  end.

Definition occupied_by_type (b : Board) (p : Position) (t : PieceType) : bool :=
  match b[p] with
  | Some piece => ptype_eqb (piece_type piece) t
  | None => false
  end.

Definition occupied_by_piece (b : Board) (p : Position) (pc : Piece) : bool :=
  match b[p] with
  | Some piece => piece_eqb piece pc
  | None => false
  end.

Lemma occupied_iff_some b p :
  occupied b p = true <-> exists pc, b[p] = Some pc.
Proof.
  unfold occupied. destruct (b[p]) eqn:H.
  - split. intro. exists p0. reflexivity.
    intro. reflexivity.
  - split. intro. discriminate.
    intros [pc Hpc]. congruence.
Qed.

Lemma not_occupied_iff_none b p :
  occupied b p = false <-> b[p] = None.
Proof.
  unfold occupied. destruct (b[p]) eqn:H.
  - split; intro; discriminate.
  - split; intro; reflexivity.
Qed.

Lemma occupied_by_iff : forall b p c,
  occupied_by b p c = true <-> exists pc, b[p] = Some pc /\ piece_color pc = c.
Proof.
  intros b p c.
  unfold occupied_by. destruct (b[p]) eqn:H.
  - split.
    + intro Hc. destruct (color_eqb_spec (piece_color p0) c); try discriminate.
      exists p0. split; congruence.
    + intros [pc [Hpc HcEq]]. injection Hpc. intro HEq. subst p0.
      rewrite <- HcEq. apply color_eqb_refl.
  - split.
    + intro. discriminate.
    + intros [pc [Hpc _]]. congruence.
Qed.

Definition square_empty (b : Board) (p : Position) : Prop :=
  b[p] = None.

Definition square_has_piece (b : Board) (p : Position) (pc : Piece) : Prop :=
  b[p] = Some pc.

Definition square_has_color (b : Board) (p : Position) (c : Color) : Prop :=
  exists pc, b[p] = Some pc /\ piece_color pc = c.

Definition square_has_type (b : Board) (p : Position) (t : PieceType) : Prop :=
  exists pc, b[p] = Some pc /\ piece_type pc = t.

Definition board_remove (b : Board) (p : Position) : Board :=
  b[p := None].

Definition board_move (b : Board) (src dst : Position) : Board :=
  (b[src := None])[dst := b[src]].

Lemma board_move_empty b src dst :
  b[src] = None -> 
  board_move b src dst = (b[src := None])[dst := None].
Proof.
  intro H. unfold board_move. rewrite H.
  reflexivity.
Qed.

Lemma board_move_occupied b src dst pc :
  b[src] = Some pc -> 
  src <> dst ->
  (board_move b src dst)[dst] = Some pc /\
  (board_move b src dst)[src] = None.
Proof.
  intros H Hneq.
  unfold board_move. split.
  - rewrite board_get_set_same. exact H.
  - rewrite board_get_set_diff; auto.
    rewrite board_get_set_same. reflexivity.
Qed.

Lemma board_move_other b src dst q :
  q <> src -> q <> dst ->
  (board_move b src dst)[q] = b[q].
Proof.
  intros Hs Hd.
  unfold board_move.
  rewrite board_get_set_diff; auto.
  rewrite board_get_set_diff; auto.
Qed.

Definition count_pieces_of_type (b : Board) (c : Color) (t : PieceType) : nat :=
  List.length (List.filter (fun p => occupied_by_piece b p (mkPiece c t)) all_positions).

Definition count_kings (b : Board) (c : Color) : nat :=
  count_pieces_of_type b c King.

Lemma count_kings_empty c :
  count_kings board_empty c = 0%nat.
Proof.
  unfold count_kings, count_pieces_of_type.
  assert (H: List.filter (fun p => occupied_by_piece board_empty p (mkPiece c King)) all_positions = []).
  { induction all_positions as [|h t IH]; simpl.
    - reflexivity.
    - unfold occupied_by_piece, board_empty, board_get. simpl.
      exact IH. }
  rewrite H. reflexivity.
Qed.

Definition find_king (b : Board) (c : Color) : option Position :=
  find (fun p => occupied_by_piece b p (mkPiece c King)) all_positions.

Lemma find_king_correct b c p :
  find_king b c = Some p ->
  b[p] = Some (mkPiece c King).
Proof.
  unfold find_king.
  intro H.
  apply find_some in H as [_ H].
  unfold occupied_by_piece in H.
  destruct (b[p]) eqn:Hp; try discriminate.
  destruct (piece_eqb_spec p0 (mkPiece c King)); congruence.
Qed.

(* ========================================================================= *)
(* BOARD WELL-FORMEDNESS                                                    *)
(* ========================================================================= *)

(* Kings must be at least 2 squares apart (cannot be adjacent) *)
Definition kings_not_adjacent (b : Board) : Prop :=
  forall pw pb,
    b[pw] = Some white_king ->
    b[pb] = Some black_king ->
    let dr := Z.abs (rankZ pw - rankZ pb) in
    let df := Z.abs (fileZ pw - fileZ pb) in
    Z.max dr df >= 2.

(* Exactly one king per color *)
Definition exactly_one_king (b : Board) (c : Color) : Prop :=
  count_kings b c = 1%nat.

(* Main board well-formedness predicate *)
Definition WFBoard (b : Board) : Prop :=
  exactly_one_king b White /\
  exactly_one_king b Black /\
  kings_not_adjacent b.

(* ========================================================================= *)
(* GAME STATE                                                                *)
(* ========================================================================= *)

(* Direction helper *)
Definition forwardZ (c : Color) : Z :=
  match c with White => 1 | Black => -1 end.

Record CastlingRights : Type := mkCastlingRights {
  white_king_side : bool;
  white_queen_side : bool;
  black_king_side : bool;
  black_queen_side : bool
}.

Definition no_castling : CastlingRights :=
  mkCastlingRights false false false false.

Record GameState : Type := mkGameState {
  board : Board;
  turn : Color;
  castling : CastlingRights;
  en_passant : option Position;  (* Target square for en passant capture *)
  halfmove : nat;                (* Halfmove clock for 50-move rule *)
  fullmove : nat                 (* Fullmove number *)
}.

(* Helper definitions for castling positions - using Fin constructors *)
(* e1 = rank 0, file 4 *)
Definition white_king_start := mkPos F1 (FS (FS (FS (FS F1)))).
(* h1 = rank 0, file 7 *)  
Definition white_rook_king_side := mkPos F1 (FS (FS (FS (FS (FS (FS (FS F1))))))).
(* a1 = rank 0, file 0 *)
Definition white_rook_queen_side := mkPos F1 F1.

(* e8 = rank 7, file 4 *)
Definition black_king_start := mkPos (FS (FS (FS (FS (FS (FS (FS F1))))))) (FS (FS (FS (FS F1)))).
(* h8 = rank 7, file 7 *)
Definition black_rook_king_side := mkPos (FS (FS (FS (FS (FS (FS (FS F1))))))) (FS (FS (FS (FS (FS (FS (FS F1))))))).
(* a8 = rank 7, file 0 *)
Definition black_rook_queen_side := mkPos (FS (FS (FS (FS (FS (FS (FS F1))))))) F1.

(* Castling rights coherence: if you have castling rights, the king and rook must be in position *)
Definition castling_coherent (st : GameState) : Prop :=
  (white_king_side (castling st) = true -> 
    board st white_king_start = Some white_king /\
    board st white_rook_king_side = Some white_rook) /\
  (white_queen_side (castling st) = true ->
    board st white_king_start = Some white_king /\
    board st white_rook_queen_side = Some white_rook) /\
  (black_king_side (castling st) = true ->
    board st black_king_start = Some black_king /\
    board st black_rook_king_side = Some black_rook) /\
  (black_queen_side (castling st) = true ->
    board st black_king_start = Some black_king /\
    board st black_rook_queen_side = Some black_rook).

(* Rank of the EP target for the side to move *)
Definition ep_target_rank (side_to_move : Color) : Z :=
  match side_to_move with
  | White => 5  (* 0-based: rank 5; Black just two-stepped from 6 to 4 *)
  | Black => 2  (* 0-based: rank 2; White just two-stepped from 1 to 3 *)
  end.

(* En passant coherence: target square must be on the correct rank and empty *)
Definition en_passant_coherent (st : GameState) : Prop :=
  match en_passant st with
  | None => True
  | Some pos =>
      (* Target square is empty *)
      board st pos = None /\
      (* Target is on the correct rank for the side to move *)
      rankZ pos = ep_target_rank (turn st)
  end.

(* Complete game state well-formedness *)
Definition WFState (st : GameState) : Prop :=
  WFBoard (board st) /\
  castling_coherent st /\
  en_passant_coherent st.

(* ========================================================================= *)
(* ATTACK PREDICATES                                                        *)
(* ========================================================================= *)

(* Pawn attacks diagonally forward *)
Definition pawn_attacks_spec (b : Board) (from to : Position) (c : Color) : Prop :=
  b[from] = Some (mkPiece c Pawn) /\
  let dr := if color_eqb c White then 1 else -1 in
  (offset from dr 1 = Some to \/ offset from dr (-1) = Some to).

(* Knight attacks in L-shape *)
Definition knight_attacks_spec (b : Board) (from to : Position) (c : Color) : Prop :=
  b[from] = Some (mkPiece c Knight) /\
  (offset from 2 1 = Some to \/ offset from 2 (-1) = Some to \/
   offset from (-2) 1 = Some to \/ offset from (-2) (-1) = Some to \/
   offset from 1 2 = Some to \/ offset from 1 (-2) = Some to \/
   offset from (-1) 2 = Some to \/ offset from (-1) (-2) = Some to).

(* Helper: clear path between positions along a direction *)
Fixpoint clear_path_n (b : Board) (from : Position) (dr df : Z) (n : nat) : Prop :=
  match n with
  | O => True
  | S n' =>
      match offset from dr df with
      | None => True
      | Some p => b[p] = None /\ clear_path_n b p dr df n'
      end
  end.

(* Line attacks reach target with clear path *)
Definition line_attacks_spec (b : Board) (from to : Position) (dr df : Z) : Prop :=
  exists (n : nat), (n > 0)%nat /\
  offset from (Z.of_nat n * dr) (Z.of_nat n * df) = Some to /\
  clear_path_n b from dr df (Nat.pred n).

(* Bishop attacks diagonally *)
Definition bishop_attacks_spec (b : Board) (from to : Position) (c : Color) : Prop :=
  b[from] = Some (mkPiece c Bishop) /\
  (line_attacks_spec b from to 1 1 \/ line_attacks_spec b from to 1 (-1) \/
   line_attacks_spec b from to (-1) 1 \/ line_attacks_spec b from to (-1) (-1)).

(* Rook attacks horizontally and vertically *)
Definition rook_attacks_spec (b : Board) (from to : Position) (c : Color) : Prop :=
  b[from] = Some (mkPiece c Rook) /\
  (line_attacks_spec b from to 1 0 \/ line_attacks_spec b from to (-1) 0 \/
   line_attacks_spec b from to 0 1 \/ line_attacks_spec b from to 0 (-1)).

(* Queen attacks like both bishop and rook *)
Definition queen_attacks_spec (b : Board) (from to : Position) (c : Color) : Prop :=
  b[from] = Some (mkPiece c Queen) /\
  (line_attacks_spec b from to 1 1 \/ line_attacks_spec b from to 1 (-1) \/
   line_attacks_spec b from to (-1) 1 \/ line_attacks_spec b from to (-1) (-1) \/
   line_attacks_spec b from to 1 0 \/ line_attacks_spec b from to (-1) 0 \/
   line_attacks_spec b from to 0 1 \/ line_attacks_spec b from to 0 (-1)).

(* King attacks one square in any direction *)
Definition king_attacks_spec (b : Board) (from to : Position) (c : Color) : Prop :=
  b[from] = Some (mkPiece c King) /\
  (offset from 1 0 = Some to \/ offset from (-1) 0 = Some to \/
   offset from 0 1 = Some to \/ offset from 0 (-1) = Some to \/
   offset from 1 1 = Some to \/ offset from 1 (-1) = Some to \/
   offset from (-1) 1 = Some to \/ offset from (-1) (-1) = Some to).

(* Main attack predicate: position 'from' attacks position 'to' *)
Definition attacks_spec (b : Board) (from to : Position) : Prop :=
  match b[from] with
  | None => False
  | Some pc =>
      let c := piece_color pc in
      match piece_type pc with
      | Pawn => pawn_attacks_spec b from to c
      | Knight => knight_attacks_spec b from to c
      | Bishop => bishop_attacks_spec b from to c
      | Rook => rook_attacks_spec b from to c
      | Queen => queen_attacks_spec b from to c
      | King => king_attacks_spec b from to c
      end
  end.

(* ========================================================================= *)
(* BOOLEAN ATTACK IMPLEMENTATION                                            *)
(* ========================================================================= *)

(* Handy offset lists *)
Definition knight_offsets : list (Z * Z) :=
  [(2,1); (2,-1); (-2,1); (-2,-1); (1,2); (1,-2); (-1,2); (-1,-2)]%Z.

Definition king_offsets : list (Z * Z) :=
  [(1,0); (-1,0); (0,1); (0,-1); (1,1); (1,-1); (-1,1); (-1,-1)]%Z.

(* First blocker along a ray (purely executable) *)
Fixpoint first_piece_on_ray (b : Board) (s : Position) (dr df : Z) (fuel : nat) : option Position :=
  match fuel with
  | O => None
  | S k =>
      match offset s dr df with
      | None => None
      | Some s1 =>
          match b[s1] with
          | Some _ => Some s1
          | None => first_piece_on_ray b s1 dr df k
          end
      end
  end.

(* Boolean attack check: is position t attacked by color c? *)
Definition attacks_b (b : Board) (c : Color) (t : Position) : bool :=
  (* Check for pawn attacks *)
  let pawn_dr := if color_eqb c White then -1 else 1 in
  let pawn_left := offset t pawn_dr (-1) in
  let pawn_right := offset t pawn_dr 1 in
  let pawn_hit :=
    existsb (fun so =>
      match so with
      | Some s =>
          match b[s] with
          | Some pc => color_eqb (piece_color pc) c && ptype_eqb (piece_type pc) Pawn
          | None => false
          end
      | None => false
      end) (pawn_left :: pawn_right :: nil) in
  
  (* Check for knight attacks *)
  let knight_hit :=
    existsb (fun od =>
      let dr := fst od in
      let df := snd od in
      match offset t (-dr) (-df) with
      | Some s =>
          match b[s] with
          | Some pc => color_eqb (piece_color pc) c && ptype_eqb (piece_type pc) Knight
          | None => false
          end
      | None => false
      end) knight_offsets in
  
  (* Check for king attacks *)
  let king_hit :=
    existsb (fun od =>
      let dr := fst od in
      let df := snd od in
      match offset t (-dr) (-df) with
      | Some s =>
          match b[s] with
          | Some pc => color_eqb (piece_color pc) c && ptype_eqb (piece_type pc) King
          | None => false
          end
      | None => false
      end) king_offsets in
  
  (* Check for rook/queen attacks on ranks and files *)
  let rook_dirs := [(1,0); (-1,0); (0,1); (0,-1)]%Z in
  let rook_like :=
    existsb (fun od =>
      let dr := fst od in
      let df := snd od in
      match first_piece_on_ray b t (-dr) (-df) 7 with
      | Some s =>
          match b[s] with
          | Some pc => 
              color_eqb (piece_color pc) c &&
              (ptype_eqb (piece_type pc) Rook || ptype_eqb (piece_type pc) Queen)
          | None => false
          end
      | None => false
      end) rook_dirs in
  
  (* Check for bishop/queen attacks on diagonals *)
  let bishop_dirs := [(1,1); (1,-1); (-1,1); (-1,-1)]%Z in
  let bishop_like :=
    existsb (fun od =>
      let dr := fst od in
      let df := snd od in
      match first_piece_on_ray b t (-dr) (-df) 7 with
      | Some s =>
          match b[s] with
          | Some pc =>
              color_eqb (piece_color pc) c &&
              (ptype_eqb (piece_type pc) Bishop || ptype_eqb (piece_type pc) Queen)
          | None => false
          end
      | None => false
      end) bishop_dirs in
  
  pawn_hit || knight_hit || king_hit || rook_like || bishop_like.

(* ========================================================================= *)
(* CHECK PREDICATES                                                         *)
(* ========================================================================= *)

(* Specification: king of color c is in check *)
Definition in_check_spec (b : Board) (c : Color) : Prop :=
  exists kpos, 
    b[kpos] = Some (mkPiece c King) /\
    exists from, attacks_spec b from kpos /\
    exists pc, b[from] = Some pc /\ piece_color pc = opposite_color c.

(* Boolean check: is king of color c in check? *)
Definition in_check_b (b : Board) (c : Color) : bool :=
  match find_king b c with
  | None => false  (* No king found - shouldn't happen in well-formed board *)
  | Some kpos => attacks_b b (opposite_color c) kpos
  end.

(* Helper lemma: if pawn attacks succeed in attacks_b, then attacks_spec holds *)
Lemma pawn_attacks_b_true_spec : forall b c t,
  (let pawn_dr := if color_eqb c White then -1 else 1 in
   let pawn_left := offset t pawn_dr (-1) in
   let pawn_right := offset t pawn_dr 1 in
   existsb (fun so =>
     match so with
     | Some s =>
         match b[s] with
         | Some pc => color_eqb (piece_color pc) c && ptype_eqb (piece_type pc) Pawn
         | None => false
         end
     | None => false
     end) (pawn_left :: pawn_right :: nil)) = true ->
  exists from, attacks_spec b from t /\ 
               exists pc, b[from] = Some pc /\ piece_color pc = c.
Proof.
  intros b c t H.
  simpl in H.
  apply orb_true_iff in H.
  destruct H as [Hleft | Hright].
  - destruct (offset t (if color_eqb c White then -1 else 1) (-1)) eqn:Eoff; simpl in Hleft.
    + destruct (b[p]) eqn:Ebp; try discriminate.
      destruct p0 as [pc_col pc_typ].
      simpl in Hleft.
      destruct (andb_prop _ _ Hleft) as [Hcol Htyp].
      apply color_eqb_true_iff in Hcol.
      apply ptype_eqb_true_iff in Htyp.
      subst pc_col pc_typ.
      exists p.
      split.
      * unfold attacks_spec.
        rewrite Ebp. simpl.
        unfold pawn_attacks_spec.
        split; [exact Ebp|].
        destruct c; simpl in Eoff |- *.
        -- left.
           replace 1 with (- (-1)) by lia.
           replace 1 with (- (-1)) by lia.
           apply offset_reverse. exact Eoff.
        -- left.
           assert (offset p (-1) 1 = Some t).
           { apply offset_reverse with (dr := 1) (df := (-1)). exact Eoff. }
           exact H.
      * exists (mkPiece c Pawn). split; [exact Ebp | reflexivity].
    + discriminate.
  - simpl in Hright.
    destruct (offset t (if color_eqb c White then -1 else 1) 1) eqn:Eoff; simpl in Hright.
    + destruct (b[p]) eqn:Ebp; try discriminate.
      destruct p0 as [pc_col pc_typ].
      simpl in Hright.
      assert (color_eqb pc_col c = true /\ ptype_eqb pc_typ Pawn = true).
      { rewrite orb_false_r in Hright. apply andb_prop. exact Hright. }
      destruct H as [Hcol Htyp].
      apply color_eqb_true_iff in Hcol.
      apply ptype_eqb_true_iff in Htyp.
      subst pc_col pc_typ.
      exists p.
      split.
      * unfold attacks_spec.
        rewrite Ebp. simpl.
        unfold pawn_attacks_spec.
        split; [exact Ebp|].
        destruct c; simpl in Eoff |- *.
        -- right.
           assert (offset p 1 (-1) = Some t).
           { apply offset_reverse with (dr := (-1)) (df := 1). exact Eoff. }
           exact H.
        -- right.
           assert (offset p (-1) (-1) = Some t).
           { apply offset_reverse with (dr := 1) (df := 1). exact Eoff. }
           exact H.
      * exists (mkPiece c Pawn). split; [exact Ebp | reflexivity].
    + discriminate.
Qed.

(* Helper lemma: if knight attacks succeed in attacks_b, then attacks_spec holds *)
Lemma knight_attacks_b_true_spec : forall b c t,
  existsb (fun od =>
    let dr := fst od in
    let df := snd od in
    match offset t (-dr) (-df) with
    | Some s =>
        match b[s] with
        | Some pc => color_eqb (piece_color pc) c && ptype_eqb (piece_type pc) Knight
        | None => false
        end
    | None => false
    end) knight_offsets = true ->
  exists from, attacks_spec b from t /\ 
               exists pc, b[from] = Some pc /\ piece_color pc = c.
Proof.
  intros b c t H.
  apply existsb_exists in H.
  destruct H as [[dr df] [Hin Hcheck]].
  simpl in Hcheck.
  destruct (offset t (-dr) (-df)) eqn:Eoff; try discriminate.
  destruct (b[p]) eqn:Ebp; try discriminate.
  apply andb_prop in Hcheck. destruct Hcheck as [Hcol Htyp].
  destruct p0 as [pc_col pc_typ].
  simpl in Hcol, Htyp.
  apply color_eqb_true_iff in Hcol.
  apply ptype_eqb_true_iff in Htyp.
  subst pc_col pc_typ.
  exists p.
  split.
  - unfold attacks_spec.
    rewrite Ebp. simpl.
    unfold knight_attacks_spec.
    split; [exact Ebp|].
    unfold knight_offsets in Hin.
    simpl in Hin.
    destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|F]]]]]]]]; try contradiction.
    + injection E. intros. subst dr df.
      left. simpl in Eoff.
      apply offset_reverse with (dr := (-2)) (df := (-1)). exact Eoff.
    + injection E. intros. subst dr df.
      right. left. simpl in Eoff.
      apply offset_reverse with (dr := (-2)) (df := 1). exact Eoff.
    + injection E. intros. subst dr df.
      right. right. left. simpl in Eoff.
      apply offset_reverse with (dr := 2) (df := (-1)). exact Eoff.
    + injection E. intros. subst dr df.
      right. right. right. left. simpl in Eoff.
      apply offset_reverse with (dr := 2) (df := 1). exact Eoff.
    + injection E. intros. subst dr df.
      right. right. right. right. left. simpl in Eoff.
      apply offset_reverse with (dr := (-1)) (df := (-2)). exact Eoff.
    + injection E. intros. subst dr df.
      right. right. right. right. right. left. simpl in Eoff.
      apply offset_reverse with (dr := (-1)) (df := 2). exact Eoff.
    + injection E. intros. subst dr df.
      right. right. right. right. right. right. left. simpl in Eoff.
      apply offset_reverse with (dr := 1) (df := (-2)). exact Eoff.
    + injection E. intros. subst dr df.
      right. right. right. right. right. right. right. simpl in Eoff.
      apply offset_reverse with (dr := 1) (df := 2). exact Eoff.
  - exists (mkPiece c Knight). split; [exact Ebp | reflexivity].
Qed.

(* Helper lemma: if king attacks succeed in attacks_b, then attacks_spec holds *)
Lemma king_attacks_b_true_spec : forall b c t,
  existsb (fun od =>
    let dr := fst od in
    let df := snd od in
    match offset t (-dr) (-df) with
    | Some s =>
        match b[s] with
        | Some pc => color_eqb (piece_color pc) c && ptype_eqb (piece_type pc) King
        | None => false
        end
    | None => false
    end) king_offsets = true ->
  exists from, attacks_spec b from t /\ 
               exists pc, b[from] = Some pc /\ piece_color pc = c.
Proof.
  intros b c t H.
  apply existsb_exists in H.
  destruct H as [[dr df] [Hin Hcheck]].
  simpl in Hcheck.
  destruct (offset t (-dr) (-df)) eqn:Eoff; try discriminate.
  destruct (b[p]) eqn:Ebp; try discriminate.
  apply andb_prop in Hcheck. destruct Hcheck as [Hcol Htyp].
  destruct p0 as [pc_col pc_typ].
  simpl in Hcol, Htyp.
  apply color_eqb_true_iff in Hcol.
  apply ptype_eqb_true_iff in Htyp.
  subst pc_col pc_typ.
  exists p.
  split.
  - unfold attacks_spec.
    rewrite Ebp. simpl.
    unfold king_attacks_spec.
    split; [exact Ebp|].
    unfold king_offsets in Hin.
    simpl in Hin.
    destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|F]]]]]]]]; try contradiction.
    + injection E. intros. subst dr df.
      left. simpl in Eoff.
      apply offset_reverse with (dr := (-1)) (df := 0). exact Eoff.
    + injection E. intros. subst dr df.
      right. left. simpl in Eoff.
      apply offset_reverse with (dr := 1) (df := 0). exact Eoff.
    + injection E. intros. subst dr df.
      right. right. left. simpl in Eoff.
      apply offset_reverse with (dr := 0) (df := (-1)). exact Eoff.
    + injection E. intros. subst dr df.
      right. right. right. left. simpl in Eoff.
      apply offset_reverse with (dr := 0) (df := 1). exact Eoff.
    + injection E. intros. subst dr df.
      right. right. right. right. left. simpl in Eoff.
      apply offset_reverse with (dr := (-1)) (df := (-1)). exact Eoff.
    + injection E. intros. subst dr df.
      right. right. right. right. right. left. simpl in Eoff.
      apply offset_reverse with (dr := (-1)) (df := 1). exact Eoff.
    + injection E. intros. subst dr df.
      right. right. right. right. right. right. left. simpl in Eoff.
      apply offset_reverse with (dr := 1) (df := (-1)). exact Eoff.
    + injection E. intros. subst dr df.
      right. right. right. right. right. right. right. simpl in Eoff.
      apply offset_reverse with (dr := 1) (df := 1). exact Eoff.
  - exists (mkPiece c King). split; [exact Ebp | reflexivity].
Qed.

(* The slider attack proofs are simplified to avoid offset_compose complexity *)

(* Simplified helper: first_piece_on_ray finds an occupied square *)
Lemma first_piece_on_ray_finds_piece : forall b s dr df fuel p,
  first_piece_on_ray b s dr df fuel = Some p ->
  b[p] <> None.
Proof.
  intros b s dr df fuel.
  generalize dependent s.
  induction fuel as [|fuel' IH]; intros s p H.
  - simpl in H. discriminate.
  - simpl in H.
    destruct (offset s dr df) as [s1|] eqn:Eoff; [|discriminate].
    destruct (b[s1]) as [pc|] eqn:Ebs1.
    + (* Found piece at s1 *)
      inversion H. subst p.
      rewrite Ebs1. discriminate.
    + (* s1 is empty, continue searching *)
      apply (IH s1). exact H.
Qed.


(* Helper 1: Extract direction from rook direction list *)
Lemma rook_dir_in_list : forall dr df,
  In (dr, df) ((1,0)%Z :: (-1,0)%Z :: (0,1)%Z :: (0,-1)%Z :: nil) ->
  (dr = 1 /\ df = 0) \/ (dr = -1 /\ df = 0) \/ (dr = 0 /\ df = 1) \/ (dr = 0 /\ df = -1).
Proof.
  intros dr df H.
  simpl in H.
  destruct H as [E|[E|[E|[E|F]]]]; try contradiction;
  injection E; intros; subst; auto.
Qed.

(* Helper 2: If first_piece_on_ray returns at distance 1, we have the reverse offset *)
Lemma first_piece_ray_distance_1 : forall b t dr df s,
  offset t (-dr) (-df) = Some s ->
  b[s] <> None ->
  offset s dr df = Some t.
Proof.
  intros b t dr df s H Hbs.
  replace dr with (- (-dr)) by lia.
  replace df with (- (-df)) by lia.
  apply offset_reverse. exact H.
Qed.

(* Helper 3: Line attack at distance 1 *)
Lemma line_attack_distance_1 : forall b from to dr df,
  offset from dr df = Some to ->
  b[from] <> None ->
  line_attacks_spec b from to dr df.
Proof.
  intros b from to dr df Hoff Hbf.
  unfold line_attacks_spec.
  exists 1%nat. split; [lia|].
  split.
  - change (Z.of_nat 1) with 1%Z.
    rewrite 2!Z.mul_1_l.
    exact Hoff.
  - unfold clear_path_n. exact I.
Qed.

(* Helper 4: Rook attack in positive rank direction *)
Lemma rook_attack_pos_rank : forall b from to c,
  b[from] = Some (mkPiece c Rook) ->
  offset from 1 0 = Some to ->
  line_attacks_spec b from to 1 0.
Proof.
  intros b from to c Hbf Hoff.
  apply line_attack_distance_1.
  - exact Hoff.
  - rewrite Hbf. discriminate.
Qed.

(* Helper 5: Rook attack in negative rank direction *)
Lemma rook_attack_neg_rank : forall b from to c,
  b[from] = Some (mkPiece c Rook) ->
  offset from (-1) 0 = Some to ->
  line_attacks_spec b from to (-1) 0.
Proof.
  intros b from to c Hbf Hoff.
  apply line_attack_distance_1.
  - exact Hoff.
  - rewrite Hbf. discriminate.
Qed.

(* Helper 6: Rook attack in positive file direction *)
Lemma rook_attack_pos_file : forall b from to c,
  b[from] = Some (mkPiece c Rook) ->
  offset from 0 1 = Some to ->
  line_attacks_spec b from to 0 1.
Proof.
  intros b from to c Hbf Hoff.
  apply line_attack_distance_1; [exact Hoff | rewrite Hbf; discriminate].
Qed.

(* Helper 7: Rook attack in negative file direction *)
Lemma rook_attack_neg_file : forall b from to c,
  b[from] = Some (mkPiece c Rook) ->
  offset from 0 (-1) = Some to ->
  line_attacks_spec b from to 0 (-1).
Proof.
  intros b from to c Hbf Hoff.
  apply line_attack_distance_1; [exact Hoff | rewrite Hbf; discriminate].
Qed.

(* Helper 8: Queen attack in positive rank direction *)
Lemma queen_attack_pos_rank : forall b from to c,
  b[from] = Some (mkPiece c Queen) ->
  offset from 1 0 = Some to ->
  line_attacks_spec b from to 1 0.
Proof.
  intros b from to c Hbf Hoff.
  apply line_attack_distance_1; [exact Hoff | rewrite Hbf; discriminate].
Qed.

(* Helper 9: Queen attack in negative rank direction *)
Lemma queen_attack_neg_rank : forall b from to c,
  b[from] = Some (mkPiece c Queen) ->
  offset from (-1) 0 = Some to ->
  line_attacks_spec b from to (-1) 0.
Proof.
  intros b from to c Hbf Hoff.
  apply line_attack_distance_1; [exact Hoff | rewrite Hbf; discriminate].
Qed.

(* Helper 10: Queen attack in positive file direction *)
Lemma queen_attack_pos_file : forall b from to c,
  b[from] = Some (mkPiece c Queen) ->
  offset from 0 1 = Some to ->
  line_attacks_spec b from to 0 1.
Proof.
  intros b from to c Hbf Hoff.
  apply line_attack_distance_1; [exact Hoff | rewrite Hbf; discriminate].
Qed.

(* Helper 11: Queen attack in negative file direction *)
Lemma queen_attack_neg_file : forall b from to c,
  b[from] = Some (mkPiece c Queen) ->
  offset from 0 (-1) = Some to ->
  line_attacks_spec b from to 0 (-1).
Proof.
  intros b from to c Hbf Hoff.
  apply line_attack_distance_1; [exact Hoff | rewrite Hbf; discriminate].
Qed.

(* Helper 12: Main helper for rook attack from first_piece_on_ray at distance 1 *)
Lemma rook_attack_from_ray_distance_1 : forall b t s c dr df,
  offset t (-dr) (-df) = Some s ->
  b[s] = Some (mkPiece c Rook) ->
  In (dr, df) ((1,0)%Z :: (-1,0)%Z :: (0,1)%Z :: (0,-1)%Z :: nil) ->
  exists from, attacks_spec b from t /\ b[from] = Some (mkPiece c Rook).
Proof.
  intros b t s c dr df Hoff Hbs Hdir.
  exists s. split.
  - unfold attacks_spec. rewrite Hbs. simpl.
    unfold rook_attacks_spec. split; [exact Hbs|].
    apply rook_dir_in_list in Hdir.
    destruct Hdir as [[Hr Hf]|[[Hr Hf]|[[Hr Hf]|[Hr Hf]]]]; subst dr df.
    + left. apply rook_attack_pos_rank with c.
      * exact Hbs.
      * apply first_piece_ray_distance_1 with b; [exact Hoff | rewrite Hbs; discriminate].
    + right. left. apply rook_attack_neg_rank with c.
      * exact Hbs.
      * apply first_piece_ray_distance_1 with b; [exact Hoff | rewrite Hbs; discriminate].
    + right. right. left. apply rook_attack_pos_file with c.
      * exact Hbs.
      * apply first_piece_ray_distance_1 with b; [exact Hoff | rewrite Hbs; discriminate].
    + right. right. right. apply rook_attack_neg_file with c.
      * exact Hbs.
      * apply first_piece_ray_distance_1 with b; [exact Hoff | rewrite Hbs; discriminate].
  - exact Hbs.
Qed.

(* Helper 13: Main helper for queen attack from first_piece_on_ray at distance 1 *)
Lemma queen_attack_from_ray_distance_1 : forall b t s c dr df,
  offset t (-dr) (-df) = Some s ->
  b[s] = Some (mkPiece c Queen) ->
  In (dr, df) ((1,0)%Z :: (-1,0)%Z :: (0,1)%Z :: (0,-1)%Z :: nil) ->
  exists from, attacks_spec b from t /\ b[from] = Some (mkPiece c Queen).
Proof.
  intros b t s c dr df Hoff Hbs Hdir.
  exists s. split.
  - unfold attacks_spec. rewrite Hbs. simpl.
    unfold queen_attacks_spec. split; [exact Hbs|].
    apply rook_dir_in_list in Hdir.
    destruct Hdir as [[Hr Hf]|[[Hr Hf]|[[Hr Hf]|[Hr Hf]]]]; subst dr df.
    + right. right. right. right. left. 
      apply queen_attack_pos_rank with c.
      * exact Hbs.
      * apply first_piece_ray_distance_1 with b; [exact Hoff | rewrite Hbs; discriminate].
    + right. right. right. right. right. left.
      apply queen_attack_neg_rank with c.
      * exact Hbs.
      * apply first_piece_ray_distance_1 with b; [exact Hoff | rewrite Hbs; discriminate].
    + right. right. right. right. right. right. left.
      apply queen_attack_pos_file with c.
      * exact Hbs.
      * apply first_piece_ray_distance_1 with b; [exact Hoff | rewrite Hbs; discriminate].
    + right. right. right. right. right. right. right.
      apply queen_attack_neg_file with c.
      * exact Hbs.
      * apply first_piece_ray_distance_1 with b; [exact Hoff | rewrite Hbs; discriminate].
  - exact Hbs.
Qed.

(* Helper: Bishop attack in positive rank, positive file direction *)
Lemma bishop_attack_pp : forall b from to c,
  b[from] = Some (mkPiece c Bishop) ->
  offset from 1 1 = Some to ->
  line_attacks_spec b from to 1 1.
Proof.
  intros b from to c Hbf Hoff.
  apply line_attack_distance_1; [exact Hoff | rewrite Hbf; discriminate].
Qed.

(* Helper: Bishop attack in positive rank, negative file direction *)
Lemma bishop_attack_pn : forall b from to c,
  b[from] = Some (mkPiece c Bishop) ->
  offset from 1 (-1) = Some to ->
  line_attacks_spec b from to 1 (-1).
Proof.
  intros b from to c Hbf Hoff.
  apply line_attack_distance_1; [exact Hoff | rewrite Hbf; discriminate].
Qed.

(* Helper: Bishop attack in negative rank, positive file direction *)
Lemma bishop_attack_np : forall b from to c,
  b[from] = Some (mkPiece c Bishop) ->
  offset from (-1) 1 = Some to ->
  line_attacks_spec b from to (-1) 1.
Proof.
  intros b from to c Hbf Hoff.
  apply line_attack_distance_1; [exact Hoff | rewrite Hbf; discriminate].
Qed.

(* Helper: Bishop attack in negative rank, negative file direction *)
Lemma bishop_attack_nn : forall b from to c,
  b[from] = Some (mkPiece c Bishop) ->
  offset from (-1) (-1) = Some to ->
  line_attacks_spec b from to (-1) (-1).
Proof.
  intros b from to c Hbf Hoff.
  apply line_attack_distance_1; [exact Hoff | rewrite Hbf; discriminate].
Qed.

(* Helper: Queen attack in positive rank, positive file direction *)
Lemma queen_attack_pp : forall b from to c,
  b[from] = Some (mkPiece c Queen) ->
  offset from 1 1 = Some to ->
  line_attacks_spec b from to 1 1.
Proof.
  intros b from to c Hbf Hoff.
  apply line_attack_distance_1; [exact Hoff | rewrite Hbf; discriminate].
Qed.

(* Helper: Queen attack in positive rank, negative file direction *)
Lemma queen_attack_pn : forall b from to c,
  b[from] = Some (mkPiece c Queen) ->
  offset from 1 (-1) = Some to ->
  line_attacks_spec b from to 1 (-1).
Proof.
  intros b from to c Hbf Hoff.
  apply line_attack_distance_1; [exact Hoff | rewrite Hbf; discriminate].
Qed.

(* Helper: Queen attack in negative rank, positive file direction *)
Lemma queen_attack_np : forall b from to c,
  b[from] = Some (mkPiece c Queen) ->
  offset from (-1) 1 = Some to ->
  line_attacks_spec b from to (-1) 1.
Proof.
  intros b from to c Hbf Hoff.
  apply line_attack_distance_1; [exact Hoff | rewrite Hbf; discriminate].
Qed.

(* Helper: Queen attack in negative rank, negative file direction *)
Lemma queen_attack_nn : forall b from to c,
  b[from] = Some (mkPiece c Queen) ->
  offset from (-1) (-1) = Some to ->
  line_attacks_spec b from to (-1) (-1).
Proof.
  intros b from to c Hbf Hoff.
  apply line_attack_distance_1; [exact Hoff | rewrite Hbf; discriminate].
Qed.

(* Helper: Extract direction from bishop direction list *)
Lemma bishop_dir_in_list : forall dr df,
  In (dr, df) ((1,1)%Z :: (1,-1)%Z :: (-1,1)%Z :: (-1,-1)%Z :: nil) ->
  (dr = 1 /\ df = 1) \/ (dr = 1 /\ df = -1) \/ (dr = -1 /\ df = 1) \/ (dr = -1 /\ df = -1).
Proof.
  intros dr df H.
  simpl in H.
  destruct H as [E|[E|[E|[E|F]]]]; try contradiction;
  injection E; intros; subst; auto.
Qed.

(* Helper: Main helper for bishop attack from first_piece_on_ray at distance 1 *)
Lemma bishop_attack_from_ray_distance_1 : forall b t s c dr df,
  offset t (-dr) (-df) = Some s ->
  b[s] = Some (mkPiece c Bishop) ->
  In (dr, df) ((1,1)%Z :: (1,-1)%Z :: (-1,1)%Z :: (-1,-1)%Z :: nil) ->
  exists from, attacks_spec b from t /\ b[from] = Some (mkPiece c Bishop).
Proof.
  intros b t s c dr df Hoff Hbs Hdir.
  exists s. split.
  - unfold attacks_spec. rewrite Hbs. simpl.
    unfold bishop_attacks_spec. split; [exact Hbs|].
    apply bishop_dir_in_list in Hdir.
    destruct Hdir as [[Hr Hf]|[[Hr Hf]|[[Hr Hf]|[Hr Hf]]]]; subst dr df.
    + left. apply bishop_attack_pp with c.
      * exact Hbs.
      * apply first_piece_ray_distance_1 with b; [exact Hoff | rewrite Hbs; discriminate].
    + right. left. apply bishop_attack_pn with c.
      * exact Hbs.
      * apply first_piece_ray_distance_1 with b; [exact Hoff | rewrite Hbs; discriminate].
    + right. right. left. apply bishop_attack_np with c.
      * exact Hbs.
      * apply first_piece_ray_distance_1 with b; [exact Hoff | rewrite Hbs; discriminate].
    + right. right. right. apply bishop_attack_nn with c.
      * exact Hbs.
      * apply first_piece_ray_distance_1 with b; [exact Hoff | rewrite Hbs; discriminate].
  - exact Hbs.
Qed.

(* Helper: Main helper for queen diagonal attack from first_piece_on_ray at distance 1 *)
Lemma queen_diagonal_attack_from_ray_distance_1 : forall b t s c dr df,
  offset t (-dr) (-df) = Some s ->
  b[s] = Some (mkPiece c Queen) ->
  In (dr, df) ((1,1)%Z :: (1,-1)%Z :: (-1,1)%Z :: (-1,-1)%Z :: nil) ->
  exists from, attacks_spec b from t /\ b[from] = Some (mkPiece c Queen).
Proof.
  intros b t s c dr df Hoff Hbs Hdir.
  exists s. split.
  - unfold attacks_spec. rewrite Hbs. simpl.
    unfold queen_attacks_spec. split; [exact Hbs|].
    apply bishop_dir_in_list in Hdir.
    destruct Hdir as [[Hr Hf]|[[Hr Hf]|[[Hr Hf]|[Hr Hf]]]]; subst dr df.
    + (* dr = 1, df = 1 *)
      left. apply queen_attack_pp with c.
      * exact Hbs.
      * apply first_piece_ray_distance_1 with b; [exact Hoff | rewrite Hbs; discriminate].
    + (* dr = 1, df = -1 *)
      right. left. apply queen_attack_pn with c.
      * exact Hbs.
      * apply first_piece_ray_distance_1 with b; [exact Hoff | rewrite Hbs; discriminate].
    + (* dr = -1, df = 1 *)
      right. right. left. apply queen_attack_np with c.
      * exact Hbs.
      * apply first_piece_ray_distance_1 with b; [exact Hoff | rewrite Hbs; discriminate].
    + (* dr = -1, df = -1 *)
      right. right. right. left. apply queen_attack_nn with c.
      * exact Hbs.
      * apply first_piece_ray_distance_1 with b; [exact Hoff | rewrite Hbs; discriminate].
  - exact Hbs.
Qed.

(* Helper: offset preserves bounds for intermediate position *)
Lemma offset_preserves_bounds : forall p dr df p',
  offset p dr df = Some p' ->
  (0 <= rankZ p' < 8) /\ (0 <= fileZ p' < 8).
Proof.
  intros p dr df p' H.
  split; [apply rankZ_bounds | apply fileZ_bounds].
Qed.

(* Helper: when offset succeeds, coordinates change correctly *)
Lemma offset_coord_change : forall p dr df p',
  offset p dr df = Some p' ->
  rankZ p' = rankZ p + dr /\ fileZ p' = fileZ p + df.
Proof.
  intros p dr df p' H.
  split.
  - apply offset_rankZ_recover with (df := df). exact H.
  - apply offset_fileZ_recover with (dr := dr). exact H.
Qed.

(* Helper: offset is deterministic *)
Lemma offset_deterministic : forall p dr df p1 p2,
  offset p dr df = Some p1 ->
  offset p dr df = Some p2 ->
  p1 = p2.
Proof.
  intros p dr df p1 p2 H1 H2.
  rewrite H1 in H2. injection H2. intro. exact H.
Qed.

(* Helper: offset with zero displacement is identity *)
Lemma offset_zero : forall p,
  offset p 0 0 = Some p.
Proof.
  intro p.
  unfold offset.
  rewrite Z.add_0_r. rewrite Z.add_0_r.
  assert (Hr: (0 <=? rankZ p) && (rankZ p <? 8) = true).
  { apply andb_true_intro. split; apply Z.leb_le || apply Z.ltb_lt; apply rankZ_bounds. }
  assert (Hf: (0 <=? fileZ p) && (fileZ p <? 8) = true).
  { apply andb_true_intro. split; apply Z.leb_le || apply Z.ltb_lt; apply fileZ_bounds. }
  rewrite Hr. rewrite Hf. simpl.
  destruct (lt_dec (Z.to_nat (rankZ p)) 8) as [HrLt|]; 
    [|exfalso; apply n; apply Z_to_nat_lt_8; apply rankZ_bounds].
  destruct (lt_dec (Z.to_nat (fileZ p)) 8) as [HfLt|];
    [|exfalso; apply n; apply Z_to_nat_lt_8; apply fileZ_bounds].
  f_equal.
  destruct p as [r f].
  assert (HrEq: Fin.of_nat_lt HrLt = r).
  { apply Fin.to_nat_inj. rewrite Fin.to_nat_of_nat.
    unfold rankZ. simpl.
    destruct (Fin.to_nat r) as [nr Hnr]. simpl.
    rewrite Nat2Z.id. reflexivity. }
  assert (HfEq: Fin.of_nat_lt HfLt = f).
  { apply Fin.to_nat_inj. rewrite Fin.to_nat_of_nat.
    unfold fileZ. simpl.
    destruct (Fin.to_nat f) as [nf Hnf]. simpl.
    rewrite Nat2Z.id. reflexivity. }
  rewrite HrEq. rewrite HfEq. reflexivity.
Qed.

(* Helper: first_piece_on_ray with fuel 0 returns None *)
Lemma first_piece_on_ray_fuel_0 : forall b s dr df,
  first_piece_on_ray b s dr df 0 = None.
Proof.
  intros. simpl. reflexivity.
Qed.

(* Helper: first_piece_on_ray finds first occupied square *)
Lemma first_piece_on_ray_occupied : forall b s dr df (fuel : nat) s1,
  (fuel > 0)%nat ->
  offset s dr df = Some s1 ->
  b[s1] <> None ->
  first_piece_on_ray b s dr df fuel = Some s1.
Proof.
  intros b s dr df fuel s1 Hfuel Hoff Hocc.
  destruct fuel; [lia|].
  simpl. rewrite Hoff.
  destruct (b[s1]) eqn:Ebs1; [reflexivity|].
  contradiction.
Qed.

(* Helper: first_piece_on_ray skips empty squares *)
Lemma first_piece_on_ray_skip_empty : forall b s dr df fuel s1,
  (fuel > 0)%nat ->
  offset s dr df = Some s1 ->
  b[s1] = None ->
  first_piece_on_ray b s dr df fuel = first_piece_on_ray b s1 dr df (fuel - 1).
Proof.
  intros b s dr df fuel s1 Hfuel Hoff Hemp.
  destruct fuel; [lia|].
  simpl. rewrite Hoff. rewrite Hemp.
  rewrite Nat.sub_0_r. reflexivity.
Qed.

(* Helper: first_piece_on_ray returns None when offset fails immediately *)
Lemma first_piece_on_ray_offset_fail : forall b s dr df fuel,
  offset s dr df = None ->
  first_piece_on_ray b s dr df fuel = None.
Proof.
  intros b s dr df fuel Hoff.
  destruct fuel; simpl; [reflexivity|].
  rewrite Hoff. reflexivity.
Qed.

(* Helper: first_piece_on_ray relates to line_attacks_spec *)
Lemma first_piece_line_attack_1 : forall b t s dr df,
  offset t (-dr) (-df) = Some s ->
  b[s] <> None ->
  line_attacks_spec b s t dr df.
Proof.
  intros b t s dr df Hoff Hbs.
  unfold line_attacks_spec.
  exists 1%nat. split; [lia|].
  split.
  - change (Z.of_nat 1) with 1%Z. 
    rewrite Z.mul_1_l. rewrite Z.mul_1_l.
    assert (H: offset s dr df = Some t).
    { replace dr with (- - dr) by ring.
      replace df with (- - df) by ring.
      apply offset_reverse. exact Hoff. }
    exact H.
  - simpl. exact I.
Qed.

(* Core insight: first_piece_on_ray at distance 1 means direct offset *)
Lemma first_piece_distance_1_offset : forall b s dr df s1,
  first_piece_on_ray b s dr df 1 = Some s1 ->
  offset s dr df = Some s1 /\ b[s1] <> None.
Proof.
  intros b s dr df s1 H.
  simpl in H.
  destruct (offset s dr df) as [s'|] eqn:Eoff; try discriminate.
  destruct (b[s']) eqn:Ebs'; try discriminate.
  injection H. intro Heq. subst s'.
  split; [reflexivity|].
  rewrite Ebs'. discriminate.
Qed.

(* Helper: clear_path_n with distance 0 is always true *)
Lemma clear_path_n_0 : forall b s dr df,
  clear_path_n b s dr df 0 = True.
Proof.
  intros. reflexivity.
Qed.

(* Helper: clear_path_n for successor *)
Lemma clear_path_n_S : forall b s dr df n,
  clear_path_n b s dr df (S n) = 
  match offset s dr df with
  | None => True
  | Some s' => b[s'] = None /\ clear_path_n b s' dr df n
  end.
Proof.
  intros. reflexivity.
Qed.

(* Helper: offset with n=1 *)
Lemma offset_mult_1 : forall p dr df p',
  offset p dr df = Some p' ->
  offset p (Z.of_nat 1 * dr) (Z.of_nat 1 * df) = Some p'.
Proof.
  intros p dr df p' H.
  change (Z.of_nat 1) with 1%Z.
  rewrite Z.mul_1_l. rewrite Z.mul_1_l.
  exact H.
Qed.

(* Helper: offset composition *)
Lemma offset_compose : forall p dr1 df1 dr2 df2 p1 p2,
  offset p dr1 df1 = Some p1 ->
  offset p1 dr2 df2 = Some p2 ->
  offset p (dr1 + dr2) (df1 + df2) = Some p2.
Proof.
  intros p dr1 df1 dr2 df2 p1 p2 H1 H2.
  apply offset_coord_change in H1 as [Hr1 Hf1].
  apply offset_coord_change in H2 as [Hr2 Hf2].
  unfold offset.
  rewrite Hr1 in Hr2. rewrite Hf1 in Hf2.
  replace (rankZ p + dr1 + dr2) with (rankZ p + (dr1 + dr2)) in Hr2 by ring.
  replace (fileZ p + df1 + df2) with (fileZ p + (df1 + df2)) in Hf2 by ring.
  rewrite <- Hr2. rewrite <- Hf2.
  assert (Hr_bounds: (0 <= rankZ p2 < 8)). { apply rankZ_bounds. }
  assert (Hf_bounds: (0 <= fileZ p2 < 8)). { apply fileZ_bounds. }
  assert (Hr_guard: (0 <=? rankZ p2) && (rankZ p2 <? 8) = true).
  { apply andb_true_intro. split; apply Z.leb_le || apply Z.ltb_lt; lia. }
  assert (Hf_guard: (0 <=? fileZ p2) && (fileZ p2 <? 8) = true).
  { apply andb_true_intro. split; apply Z.leb_le || apply Z.ltb_lt; lia. }
  rewrite Hr_guard. rewrite Hf_guard. simpl.
  destruct (lt_dec (Z.to_nat (rankZ p2)) 8) as [HrLt|]; 
    [|exfalso; apply n; apply Z_to_nat_lt_8; exact Hr_bounds].
  destruct (lt_dec (Z.to_nat (fileZ p2)) 8) as [HfLt|];
    [|exfalso; apply n; apply Z_to_nat_lt_8; exact Hf_bounds].
  f_equal.
  destruct p2 as [r2 f2].
  assert (HrEq: Fin.of_nat_lt HrLt = r2).
  { apply Fin.to_nat_inj. rewrite Fin.to_nat_of_nat.
    unfold rankZ in *. simpl.
    destruct (Fin.to_nat r2) as [nr2 Hnr2]. simpl in *.
    rewrite Nat2Z.id. reflexivity. }
  assert (HfEq: Fin.of_nat_lt HfLt = f2).
  { apply Fin.to_nat_inj. rewrite Fin.to_nat_of_nat.
    unfold fileZ in *. simpl.
    destruct (Fin.to_nat f2) as [nf2 Hnf2]. simpl in *.
    rewrite Nat2Z.id. reflexivity. }
  rewrite HrEq. rewrite HfEq. reflexivity.
Qed.

(* Helper: composing offset with multiples *)
Lemma offset_mult_S : forall p n dr df p',
  offset p (Z.of_nat n * dr) (Z.of_nat n * df) = Some p' ->
  forall p'', offset p' dr df = Some p'' ->
  offset p (Z.of_nat (S n) * dr) (Z.of_nat (S n) * df) = Some p''.
Proof.
  intros p n dr df p' H1 p'' H2.
  replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z by lia.
  rewrite Z.mul_add_distr_r. rewrite Z.mul_add_distr_r.
  rewrite Z.mul_1_l. rewrite Z.mul_1_l.
  apply offset_compose with (p1 := p').
  - exact H1.
  - exact H2.
Qed.

(* Helper: first_piece_on_ray gives us what we need for line_attacks_spec *)
Lemma first_piece_gives_line_attack : forall b fuel s t dr df,
  first_piece_on_ray b s dr df fuel = Some t ->
  exists n, (n > 0)%nat /\ (n <= fuel)%nat /\
  offset s (Z.of_nat n * dr) (Z.of_nat n * df) = Some t /\
  b[t] <> None /\
  clear_path_n b s dr df (n - 1).
Proof.
  intros b fuel.
  induction fuel; intros s t dr df H.
  - (* fuel = 0 *)
    (* first_piece_on_ray with fuel 0 returns None *)
    pose proof (first_piece_on_ray_fuel_0 b s dr df) as H0.
    rewrite H0 in H.
    inversion H. 
  - (* fuel = S fuel' *)
    simpl in H.
    destruct (offset s dr df) as [s1|] eqn:Eoff; [|discriminate].
    destruct (b[s1]) as [pc|] eqn:Ebs1.
    + (* Found piece at s1 - distance 1 *)
      injection H. intro Heq. subst t.
      exists 1%nat. split; [lia|]. split; [lia|].
      change (Z.of_nat 1) with 1%Z.
      rewrite Z.mul_1_l. rewrite Z.mul_1_l.
      split; [exact Eoff|].
      split; [rewrite Ebs1; discriminate|].
      rewrite Nat.sub_diag. reflexivity.
    + (* s1 is empty, continue searching *)
      apply IHfuel in H.
      destruct H as [n [Hn1 [Hn2 [Hoff [Hbt Hclear]]]]].
      exists (S n). split; [lia|]. split; [lia|].
      split.
      * (* We have: offset s dr df = Some s1 and offset s1 (n*dr) (n*df) = Some t *)
        (* We want: offset s ((S n)*dr) ((S n)*df) = Some t *)
        replace (Z.of_nat (S n)) with (1 + Z.of_nat n)%Z by lia.
        rewrite Z.mul_add_distr_r. rewrite Z.mul_add_distr_r.
        rewrite Z.mul_1_l. rewrite Z.mul_1_l.
        apply offset_compose with (p1 := s1).
        -- exact Eoff.
        -- exact Hoff.
      * split; [exact Hbt|].
        (* Show clear_path_n b s dr df ((S n) - 1) *)
        (* Since n comes from IH where n > 0, and we have clear_path_n b s1 dr df (n-1) *)
        replace ((S n) - 1)%nat with n by lia.
        (* We need to show clear_path_n b s dr df n *)
        (* Key insight: clear_path_n b s dr df n when n > 0 unfolds to check s->s1 is clear then recurse *)
        destruct n as [|n'] eqn:En.
        -- (* n = 0: contradicts n > 0 from IH *)
           lia.
        -- (* n = S n' *)
           (* clear_path_n b s dr df (S n') unfolds to check offset and recurse *)
           simpl. rewrite Eoff. split; [exact Ebs1|].
           (* Now goal is clear_path_n b s1 dr df n' *)
           (* From IH: clear_path_n b s1 dr df (n - 1) *)
           (* Since n = S n', we have (S n' - 1) = n' *)
           replace n' with (S n' - 1)%nat by lia.
           exact Hclear.
Qed.

(* Lemma: if rook/queen attacks succeed in attacks_b at distance 1, then attacks_spec holds *)
Lemma rook_attacks_b_true_spec_distance_1 : forall b c t,
  (existsb (fun od =>
    let dr := fst od in
    let df := snd od in
    match offset t (-dr) (-df) with
    | Some s =>
        match b[s] with
        | Some pc =>
            color_eqb (piece_color pc) c &&
            (ptype_eqb (piece_type pc) Rook || ptype_eqb (piece_type pc) Queen)
        | None => false
        end
    | None => false
    end) ((1,0)%Z :: (-1,0)%Z :: (0,1)%Z :: (0,-1)%Z :: nil)) = true ->
  exists from, attacks_spec b from t /\
               exists pc, b[from] = Some pc /\ piece_color pc = c.
Proof.
  intros b c t H.
  apply existsb_exists in H.
  destruct H as [[dr df] [Hin Hray]].
  simpl in Hray.
  destruct (offset t (-dr) (-df)) as [s1|] eqn:Eoff1; try discriminate.
  destruct (b[s1]) as [pc1|] eqn:Ebs1; try discriminate.
  apply andb_prop in Hray. destruct Hray as [Hcol Htype].
  apply color_eqb_true_iff in Hcol.
  apply orb_prop in Htype.
  destruct Htype as [HRook | HQueen].
  - (* It's a Rook *)
    apply ptype_eqb_true_iff in HRook.
    assert (pc1 = mkPiece c Rook).
    { destruct pc1. simpl in *. subst. reflexivity. }
    subst pc1.
    destruct (@rook_attack_from_ray_distance_1 b t s1 c dr df Eoff1 Ebs1 Hin) as [from [Hattack Hfrom]].
    exists from. split; [exact Hattack|].
    exists (mkPiece c Rook). split; [exact Hfrom | reflexivity].
  - (* It's a Queen *)
    apply ptype_eqb_true_iff in HQueen.
    assert (pc1 = mkPiece c Queen).
    { destruct pc1. simpl in *. subst. reflexivity. }
    subst pc1.
    destruct (@queen_attack_from_ray_distance_1 b t s1 c dr df Eoff1 Ebs1 Hin) as [from [Hattack Hfrom]].
    exists from. split; [exact Hattack|].
    exists (mkPiece c Queen). split; [exact Hfrom | reflexivity].
Qed.


(* Helper: negation of direction vectors *)
Lemma negate_direction : forall dr df,
  (- - dr = dr) /\ (- - df = df).
Proof.
  intros. split; ring.
Qed.

(* Helper: multiplication simplification for Z.of_nat n *)
Lemma Z_of_nat_mult_1 : forall n,
  Z.of_nat n * 1 = Z.of_nat n.
Proof.
  intro n. ring.
Qed.

Lemma Z_of_nat_mult_neg1 : forall n,
  Z.of_nat n * (-1) = -(Z.of_nat n).
Proof.
  intro n. ring.
Qed.

(* Helper: clear_path_n for specific n values *)
Lemma clear_path_n_1 : forall b s dr df,
  clear_path_n b s dr df 0 = True.
Proof.
  intros. reflexivity.
Qed.

(* Helper: offset reversal from first_piece_gives_line_attack *)  
Lemma offset_from_first_piece : forall b t s dr df,
  first_piece_on_ray b t (-dr) (-df) 7 = Some s ->
  exists n', (n' > 0)%nat /\ (n' <= 7)%nat /\
  offset t (Z.of_nat n' * (-dr)) (Z.of_nat n' * (-df)) = Some s.
Proof.
  intros b t s dr df Hfirst.
  apply first_piece_gives_line_attack in Hfirst.
  destruct Hfirst as [n' [Hn1 [Hn2 [Hoff [Hbs Hclear]]]]].
  exists n'. split; [exact Hn1|]. split; [exact Hn2|].
  exact Hoff.
Qed.

(* Helper: transform offset from target perspective to source perspective *)
Lemma offset_reverse_mult : forall t s n dr df,
  offset t (Z.of_nat n * (-dr)) (Z.of_nat n * (-df)) = Some s ->
  offset s (Z.of_nat n * dr) (Z.of_nat n * df) = Some t.
Proof.
  intros t s n dr df H.
  replace (Z.of_nat n * dr) with (- (Z.of_nat n * (-dr))) by ring.
  replace (Z.of_nat n * df) with (- (Z.of_nat n * (-df))) by ring.
  apply offset_reverse. exact H.
Qed.

(* Helper: build line_attacks_spec from first_piece_on_ray result *)
Lemma build_line_attack_from_first_piece : forall b s t dr df n,
  b[s] = Some (mkPiece White Bishop) \/
  b[s] = Some (mkPiece Black Bishop) \/
  b[s] = Some (mkPiece White Queen) \/
  b[s] = Some (mkPiece Black Queen) ->
  (n > 0)%nat ->
  offset s (Z.of_nat n * dr) (Z.of_nat n * df) = Some t ->
  clear_path_n b s dr df (n - 1) ->
  line_attacks_spec b s t dr df.
Proof.
  intros b s t dr df n Hpiece Hn Hoff Hclear.
  unfold line_attacks_spec.
  exists n. split; [exact Hn|]. split; [exact Hoff|]. 
  replace (Nat.pred n) with (n - 1)%nat by lia. exact Hclear.
Qed.

(* Helper: extract piece info and build attack *)
Lemma bishop_piece_builds_attack : forall b s t c dr df n,
  b[s] = Some (mkPiece c Bishop) ->
  (n > 0)%nat ->
  offset s (Z.of_nat n * dr) (Z.of_nat n * df) = Some t ->
  clear_path_n b s dr df (n - 1) ->
  In (dr, df) ((1,1)%Z :: (1,-1)%Z :: (-1,1)%Z :: (-1,-1)%Z :: nil) ->
  bishop_attacks_spec b s t c.
Proof.
  intros b s t c dr df n Hbs Hn Hoff Hclear Hdir.
  unfold bishop_attacks_spec.
  split; [exact Hbs|].
  apply bishop_dir_in_list in Hdir.
  destruct Hdir as [[Hr Hf]|[[Hr Hf]|[[Hr Hf]|[Hr Hf]]]]; subst dr df.
  - left. unfold line_attacks_spec. exists n. split; [exact Hn|]. split; [exact Hoff|]. 
    replace (Nat.pred n) with (n - 1)%nat by lia. exact Hclear.
  - right. left. unfold line_attacks_spec. exists n. split; [exact Hn|]. split; [exact Hoff|]. 
    replace (Nat.pred n) with (n - 1)%nat by lia. exact Hclear.
  - right. right. left. unfold line_attacks_spec. exists n. split; [exact Hn|]. split; [exact Hoff|]. 
    replace (Nat.pred n) with (n - 1)%nat by lia. exact Hclear.
  - right. right. right. unfold line_attacks_spec. exists n. split; [exact Hn|]. split; [exact Hoff|]. 
    replace (Nat.pred n) with (n - 1)%nat by lia. exact Hclear.
Qed.

(* Helper: queen piece builds diagonal attack *)
Lemma queen_piece_builds_diagonal_attack : forall b s t c dr df n,
  b[s] = Some (mkPiece c Queen) ->
  (n > 0)%nat ->
  offset s (Z.of_nat n * dr) (Z.of_nat n * df) = Some t ->
  clear_path_n b s dr df (n - 1) ->
  In (dr, df) ((1,1)%Z :: (1,-1)%Z :: (-1,1)%Z :: (-1,-1)%Z :: nil) ->
  queen_attacks_spec b s t c.
Proof.
  intros b s t c dr df n Hbs Hn Hoff Hclear Hdir.
  unfold queen_attacks_spec.
  split; [exact Hbs|].
  apply bishop_dir_in_list in Hdir.
  destruct Hdir as [[Hr Hf]|[[Hr Hf]|[[Hr Hf]|[Hr Hf]]]]; subst dr df.
  - left. unfold line_attacks_spec. exists n. split; [exact Hn|]. split; [exact Hoff|]. 
    replace (Nat.pred n) with (n - 1)%nat by lia. exact Hclear.
  - right. left. unfold line_attacks_spec. exists n. split; [exact Hn|]. split; [exact Hoff|]. 
    replace (Nat.pred n) with (n - 1)%nat by lia. exact Hclear.
  - right. right. left. unfold line_attacks_spec. exists n. split; [exact Hn|]. split; [exact Hoff|]. 
    replace (Nat.pred n) with (n - 1)%nat by lia. exact Hclear.
  - right. right. right. left. unfold line_attacks_spec. exists n. split; [exact Hn|]. split; [exact Hoff|]. 
    replace (Nat.pred n) with (n - 1)%nat by lia. exact Hclear.
Qed.


Lemma bishop_attacks_b_true_spec_distance_1 : forall b c t,
  (existsb (fun od =>
    let dr := fst od in
    let df := snd od in
    match offset t (-dr) (-df) with
    | Some s =>
        match b[s] with
        | Some pc =>
            color_eqb (piece_color pc) c &&
            (ptype_eqb (piece_type pc) Bishop || ptype_eqb (piece_type pc) Queen)
        | None => false
        end
    | None => false
    end) ((1,1)%Z :: (1,-1)%Z :: (-1,1)%Z :: (-1,-1)%Z :: nil)) = true ->
  exists from, attacks_spec b from t /\
               exists pc, b[from] = Some pc /\ piece_color pc = c.
Proof.
  intros b c t H.
  (* Only handle distance-1 diagonal attacks *)
  apply existsb_exists in H.
  destruct H as [[dr df] [Hin Hray]].
  simpl in Hray.
  destruct (offset t (-dr) (-df)) as [s1|] eqn:Eoff1; try discriminate.
  destruct (b[s1]) as [pc1|] eqn:Ebs1; try discriminate.
  (* s1 has a piece - check the type and color *)
  apply andb_prop in Hray. destruct Hray as [Hcol Htype].
  apply color_eqb_true_iff in Hcol.
  apply orb_prop in Htype.
  destruct Htype as [HBishop | HQueen].
  - (* It's a Bishop *)
    apply ptype_eqb_true_iff in HBishop.
    assert (pc1 = mkPiece c Bishop).
    { destruct pc1. simpl in *. subst. reflexivity. }
    subst pc1.
    destruct (@bishop_attack_from_ray_distance_1 b t s1 c dr df Eoff1 Ebs1 Hin) as [from [Hattack Hfrom]].
    exists from. split; [exact Hattack|].
    exists (mkPiece c Bishop). split; [exact Hfrom | reflexivity].
  - (* It's a Queen *)
    apply ptype_eqb_true_iff in HQueen.
    assert (pc1 = mkPiece c Queen).
    { destruct pc1. simpl in *. subst. reflexivity. }
    subst pc1.
    destruct (@queen_diagonal_attack_from_ray_distance_1 b t s1 c dr df Eoff1 Ebs1 Hin) as [from [Hattack Hfrom]].
    exists from. split; [exact Hattack|].
    exists (mkPiece c Queen). split; [exact Hfrom | reflexivity].
Qed.

(* Helper: offset injectivity *)
Lemma offset_injective : forall p dr df p1 p2,
  offset p dr df = Some p1 ->
  offset p dr df = Some p2 ->
  p1 = p2.
Proof.
  intros p dr df p1 p2 H1 H2.
  rewrite H1 in H2.
  injection H2. intro. exact H.
Qed.


(* ========================================================================= *)
(* DECLARATIVE MOVE SEMANTICS                                               *)
(* ========================================================================= *)

(* Check if a square is empty or has an opponent piece *)
Definition can_capture (b : Board) (pos : Position) (c : Color) : Prop :=
  match b[pos] with
  | None => True
  | Some pc => piece_color pc = opposite_color c /\ piece_type pc <> King
  end.

(* Update castling rights after a move *)
Definition update_castling_rights (cr : CastlingRights) (from to : Position) : CastlingRights :=
  let cr1 := 
    if position_eqb from white_king_start then
      mkCastlingRights false false (black_king_side cr) (black_queen_side cr)
    else if position_eqb from black_king_start then
      mkCastlingRights (white_king_side cr) (white_queen_side cr) false false
    else cr in
  let cr2 :=
    if position_eqb from white_rook_king_side || position_eqb to white_rook_king_side then
      mkCastlingRights false (white_queen_side cr1) (black_king_side cr1) (black_queen_side cr1)
    else cr1 in
  let cr3 :=
    if position_eqb from white_rook_queen_side || position_eqb to white_rook_queen_side then
      mkCastlingRights (white_king_side cr2) false (black_king_side cr2) (black_queen_side cr2)
    else cr2 in
  let cr4 :=
    if position_eqb from black_rook_king_side || position_eqb to black_rook_king_side then
      mkCastlingRights (white_king_side cr3) (white_queen_side cr3) false (black_queen_side cr3)
    else cr3 in
  if position_eqb from black_rook_queen_side || position_eqb to black_rook_queen_side then
    mkCastlingRights (white_king_side cr4) (white_queen_side cr4) (black_king_side cr4) false
  else cr4.

(* Update en passant target after a move *)
Definition update_en_passant (b : Board) (from to : Position) : option Position :=
  match b[from] with
  | Some pc =>
      if ptype_eqb (piece_type pc) Pawn then
        let dr := Z.abs (rankZ to - rankZ from) in
        let df := Z.abs (fileZ to - fileZ from) in
        if Z.eqb dr 2 && Z.eqb df 0 then
          (* Pawn moved two squares vertically - set en passant target *)
          let mid_rank := (rankZ from + rankZ to) / 2 in
          offset (mkPos (pos_rank from) (pos_file from)) 
                 (mid_rank - rankZ from) 0
        else None
      else None
  | None => None
  end.

(* Helper: piece after promotion *)
Definition piece_after_promo (pc : Piece) (promo : option PieceType) : Piece :=
  match promo with 
  | None => pc 
  | Some pt => mkPiece (piece_color pc) pt 
  end.

(* Helper: apply en passant capture if applicable *)
Definition apply_en_passant_capture (st : GameState) (from to : Position) (b : Board) : Board :=
  match en_passant st with
  | Some ep =>
      if position_eqb to ep then
        match b[from] with
        | Some pc =>
            if ptype_eqb (piece_type pc) Pawn then
              match offset to (- forwardZ (piece_color pc)) 0 with
              | Some cap => b[cap := None]
              | None => b
              end
            else b
        | None => b
        end
      else b
  | None => b
  end.

(* Helper: compute next board after normal move *)
Definition next_board_normal (st : GameState) (from to : Position) (promo : option PieceType) : Board :=
  let b := board st in
  let b0 := apply_en_passant_capture st from to b in
  match b[from] with
  | Some pc =>
      let moved := piece_after_promo pc promo in
      (b0[from := None])[to := Some moved]
  | None => b0
  end.

(* Helper: compute halfmove clock after move *)
Definition halfmove_after (st : GameState) (from to : Position) : nat :=
  let b := board st in
  let was_capture :=
    match b[to] with
    | Some _ => true
    | None =>
        match en_passant st with
        | Some ep => position_eqb to ep
        | None => false
        end
    end in
  match b[from] with
  | Some pc =>
      if (ptype_eqb (piece_type pc) Pawn) || was_capture then 0%nat
      else S (halfmove st)
  | None => halfmove st
  end.

(* Helper: compute fullmove number after move *)
Definition fullmove_after (st : GameState) : nat :=
  match turn st with
  | Black => S (fullmove st)
  | White => fullmove st
  end.

(* Helper: compute next state after normal move *)
Definition next_state_normal (st : GameState) (from to : Position) (promo : option PieceType) : GameState :=
  let b' := next_board_normal st from to promo in
  let cr' := update_castling_rights (castling st) from to in
  let ep' := update_en_passant (board st) from to in
  mkGameState b' (opposite_color (turn st)) cr' ep' (halfmove_after st from to) (fullmove_after st).

(* Check if a pawn move is geometrically valid *)
Definition pawn_move_valid (b : Board) (c : Color) (from to : Position) : Prop :=
  let dr := forwardZ c in
  (* Forward one square *)
  (offset from dr 0 = Some to /\ b[to] = None) \/
  (* Forward two squares from starting rank *)
  ((c = White /\ rankZ from = 1) \/ (c = Black /\ rankZ from = 6)) /\
  offset from (2 * dr) 0 = Some to /\ b[to] = None /\
  (exists mid, offset from dr 0 = Some mid /\ b[mid] = None) \/
  (* Diagonal capture *)
  (offset from dr 1 = Some to \/ offset from dr (-1) = Some to) /\
  exists pc, b[to] = Some pc /\ piece_color pc = opposite_color c.

(* En passant capture validity *)
Definition ep_capture_valid (st: GameState) (from to: Position) (c: Color) : Prop :=
  en_passant st = Some to /\
  board st from = Some (mkPiece c Pawn) /\
  (offset from (forwardZ c) 1 = Some to \/ offset from (forwardZ c) (-1) = Some to) /\
  exists cap, offset to (- forwardZ c) 0 = Some cap /\
              board st cap = Some (mkPiece (opposite_color c) Pawn).

(* State-aware pawn move validity *)
Definition pawn_move_valid' (st: GameState) (from to: Position) : Prop :=
  let b := board st in
  let c := turn st in
  let dr := forwardZ c in
  (* forward 1 *)
  (offset from dr 0 = Some to /\ b[to] = None)
  \/
  (* forward 2 from start rank with empty mid *)
  (((c = White /\ rankZ from = 1) \/ (c = Black /\ rankZ from = 6)) /\
   offset from (2 * dr) 0 = Some to /\ b[to] = None /\
   exists mid, offset from dr 0 = Some mid /\ b[mid] = None)
  \/
  (* normal diagonal capture *)
  ((offset from dr 1 = Some to \/ offset from dr (-1) = Some to) /\
   exists pc, b[to] = Some pc /\ piece_color pc = opposite_color c)
  \/
  (* en passant capture *)
  ep_capture_valid st from to c.

(* Check if a non-pawn piece move is geometrically valid *)
Definition piece_move_valid (b : Board) (pt : PieceType) (c : Color) (from to : Position) : Prop :=
  match pt with
  | Pawn => False  (* Use pawn_move_valid instead *)
  | Knight => knight_attacks_spec b from to c
  | Bishop => bishop_attacks_spec b from to c
  | Rook => rook_attacks_spec b from to c
  | Queen => queen_attacks_spec b from to c
  | King => king_attacks_spec b from to c
  end.

(* Castling destinations and corridors *)
Definition king_dest (c: Color) (s: CastleSide) : Position :=
  match c, s with
  | White, KingSide => mkPos F1 (FS (FS (FS (FS (FS (FS F1)))))) (* g1 *)
  | White, QueenSide => mkPos F1 (FS (FS F1))                     (* c1 *)
  | Black, KingSide => mkPos (FS (FS (FS (FS (FS (FS (FS F1))))))) (FS (FS (FS (FS (FS (FS F1)))))) (* g8 *)
  | Black, QueenSide => mkPos (FS (FS (FS (FS (FS (FS (FS F1))))))) (FS (FS F1))                     (* c8 *)
  end.

Definition rook_start (c: Color) (s: CastleSide) : Position :=
  match c, s with
  | White, KingSide => white_rook_king_side 
  | White, QueenSide => white_rook_queen_side
  | Black, KingSide => black_rook_king_side 
  | Black, QueenSide => black_rook_queen_side
  end.

Definition rook_dest (c: Color) (s: CastleSide) : Position :=
  match c, s with
  | White, KingSide => mkPos F1 (FS (FS (FS (FS (FS F1)))))  (* f1 *)
  | White, QueenSide => mkPos F1 (FS (FS (FS F1)))           (* d1 *)
  | Black, KingSide => mkPos (FS (FS (FS (FS (FS (FS (FS F1))))))) (FS (FS (FS (FS (FS F1)))))  (* f8 *)
  | Black, QueenSide => mkPos (FS (FS (FS (FS (FS (FS (FS F1))))))) (FS (FS (FS F1)))           (* d8 *)
  end.

Definition king_corridor (c: Color) (s: CastleSide) : list Position :=
  match c, s with
  | White, KingSide => 
      [ mkPos F1 (FS (FS (FS (FS (FS F1)))))      (* f1 *)
      ; mkPos F1 (FS (FS (FS (FS (FS (FS F1)))))) (* g1 *) ]
  | White, QueenSide => 
      [ mkPos F1 (FS (FS (FS F1)))                 (* d1 *)
      ; mkPos F1 (FS (FS F1))                      (* c1 *) ]
  | Black, KingSide => 
      [ mkPos (FS (FS (FS (FS (FS (FS (FS F1))))))) (FS (FS (FS (FS (FS F1)))))      (* f8 *)
      ; mkPos (FS (FS (FS (FS (FS (FS (FS F1))))))) (FS (FS (FS (FS (FS (FS F1)))))) (* g8 *) ]
  | Black, QueenSide => 
      [ mkPos (FS (FS (FS (FS (FS (FS (FS F1))))))) (FS (FS (FS F1)))  (* d8 *)
      ; mkPos (FS (FS (FS (FS (FS (FS (FS F1))))))) (FS (FS F1))       (* c8 *) ]
  end.

Definition rook_corridor (c: Color) (s: CastleSide) : list Position :=
  match c, s with
  | White, QueenSide => 
      [ mkPos F1 (FS F1)                           (* b1 *)
      ; mkPos F1 (FS (FS F1))                      (* c1 *)
      ; mkPos F1 (FS (FS (FS F1))) ]               (* d1 *)
  | Black, QueenSide => 
      [ mkPos (FS (FS (FS (FS (FS (FS (FS F1))))))) (FS F1)          (* b8 *)
      ; mkPos (FS (FS (FS (FS (FS (FS (FS F1))))))) (FS (FS F1))     (* c8 *)
      ; mkPos (FS (FS (FS (FS (FS (FS (FS F1))))))) (FS (FS (FS F1))) (* d8 *) ]
  | _, KingSide => []  (* No rook corridor for kingside castling *)
  end.

Definition list_all_empty (b: Board) (ps: list Position) : Prop :=
  Forall (fun p => b[p] = None) ps.

Definition list_all_safe (b: Board) (attacker: Color) (ps: list Position) : Prop :=
  Forall (fun p => attacks_b b attacker p = false) ps.

Definition can_castle_spec (st: GameState) (s: CastleSide) : Prop :=
  let b := board st in
  let c := turn st in
  let ks := if color_eqb c White then white_king_start else black_king_start in
  let rs := rook_start c s in
  (* Check castling rights *)
  (match c, s with
   | White, KingSide => white_king_side (castling st) = true
   | White, QueenSide => white_queen_side (castling st) = true
   | Black, KingSide => black_king_side (castling st) = true
   | Black, QueenSide => black_queen_side (castling st) = true
   end) /\
  (* King and rook in position *)
  b[ks] = Some (mkPiece c King) /\
  b[rs] = Some (mkPiece c Rook) /\
  (* Corridor empty *)
  list_all_empty b (king_corridor c s ++ rook_corridor c s) /\
  (* Not currently in check *)
  in_check_b b c = false /\
  (* King's path not attacked *)
  list_all_safe b (opposite_color c) (ks :: king_corridor c s).

Definition next_state_castle (st: GameState) (s: CastleSide) : GameState :=
  let b := board st in
  let c := turn st in
  let ks := if color_eqb c White then white_king_start else black_king_start in
  let kd := king_dest c s in
  let rs := rook_start c s in
  let rd := rook_dest c s in
  let b' := (((b[ks := None])[rs := None])[kd := Some (mkPiece c King)])[rd := Some (mkPiece c Rook)] in
  let cr' :=
    match c with
    | White => mkCastlingRights false false (black_king_side (castling st)) (black_queen_side (castling st))
    | Black => mkCastlingRights (white_king_side (castling st)) (white_queen_side (castling st)) false false
    end in
  mkGameState b' (opposite_color c) cr' None (S (halfmove st)) (fullmove_after st).

(* Main step relation: declarative move semantics *)
Inductive Step : GameState -> Move -> GameState -> Prop :=
  | StepNormal : forall st from to promo,
      let b := board st in
      let c := turn st in
      
      (* Own piece at 'from' *)
      (exists pc, b[from] = Some pc /\ piece_color pc = c) ->
      
      (* Geometric validity for that piece *)
      (exists pc, b[from] = Some pc /\
        match piece_type pc with
        | Pawn => pawn_move_valid' st from to
        | pt => piece_move_valid b pt c from to
        end) ->
      
      (* Destination OK: empty or enemy (not a king) *)
      can_capture b to c ->
      
      (* Promotion constraints when present *)
      (match promo with
       | None => True
       | Some pt => is_valid_promotion pt = true /\
                    exists pc, b[from] = Some pc /\ piece_type pc = Pawn /\
                    ((c = White /\ rankZ to = 7) \/ (c = Black /\ rankZ to = 0))
       end) ->
      
      (* No self-check after the move *)
      in_check_b (next_board_normal st from to promo) c = false ->
      
      Step st (MNormal from to promo) (next_state_normal st from to promo)
      
  | StepCastle : forall st side,
      can_castle_spec st side ->
      Step st (MCastle side) (next_state_castle st side).

(* Theorem: Step is deterministic *)
Theorem Step_deterministic :
  forall st m st1 st2,
    Step st m st1 -> Step st m st2 -> st1 = st2.
Proof.
  intros st m st1 st2 H1 H2.
  destruct m as [from to promo|side].
  - (* MNormal *)
    inversion H1; subst.
    inversion H2; subst.
    reflexivity.
  - (* MCastle *)
    inversion H1; subst.
    inversion H2; subst.
    reflexivity.
Qed.

(* Terminal state classification *)
Definition no_moves (st: GameState) : Prop :=
  forall m st', ~ Step st m st'.

Definition is_checkmate (st: GameState) : Prop :=
  WFState st /\ no_moves st /\ in_check_b (board st) (turn st) = true.

Definition is_stalemate (st: GameState) : Prop :=
  WFState st /\ no_moves st /\ in_check_b (board st) (turn st) = false.

Theorem terminal_classification :
  forall st, WFState st -> no_moves st ->
  is_checkmate st \/ is_stalemate st.
Proof.
  intros st Hwf Hno.
  unfold is_checkmate, is_stalemate.
  destruct (in_check_b (board st) (turn st)) eqn:E.
  - left. split; [exact Hwf|]. split; [exact Hno|]. reflexivity.
  - right. split; [exact Hwf|]. split; [exact Hno|]. reflexivity.
Qed.

(* ========================================================================= *)
(* GEOMETRY VALIDATION FOR MOVES                                            *)
(* ========================================================================= *)

(* Boolean clear-path for exactly n steps ahead (ignores the destination square). *)
Fixpoint clear_path_n_b (b : Board) (from : Position) (dr df : Z) (n : nat) : bool :=
  match n with
  | 0%nat => true
  | S n' =>
      match offset from dr df with
      | Some p =>
          match b[p] with
          | None => clear_path_n_b b p dr df n'
          | Some _ => false
          end
      | None => false
      end
  end.

Fixpoint reaches_in_n (b: Board) (from to: Position) (dr df: Z) (n: nat) : bool :=
  match n with
  | O => false
  | S k =>
      match offset from dr df with
      | None => false
      | Some p1 =>
          if Nat.eqb k O then
            position_eqb p1 to
          else
            match b[p1] with
            | None => reaches_in_n b p1 to dr df k
            | Some _ => false
            end
      end
  end.

Definition check_line_move (b: Board) (from to: Position) (dr df: Z) : bool :=
  existsb (fun n => reaches_in_n b from to dr df n) (seq 1 7).

Definition pawn_move_valid_b (st: GameState) (from to: Position) : bool :=
  let b := board st in
  let c := turn st in
  let dr := forwardZ c in
  match offset from dr 0 with
  | Some p1 =>
      if position_eqb p1 to then
        match b[to] with None => true | _ => false end
      else
        match offset from (2 * dr) 0 with
        | Some p2 =>
            if position_eqb p2 to then
              let start_rank := if color_eqb c White then 1 else 6 in
              if Z.eqb (rankZ from) start_rank then
                match b[p1], b[p2] with
                | None, None => true
                | _, _ => false
                end
              else false
            else
              match offset from dr 1, offset from dr (-1) with
              | Some pl, Some pr =>
                  if position_eqb pl to || position_eqb pr to then
                    match b[to] with
                    | Some pc => negb (color_eqb (piece_color pc) c)
                    | None =>
                        match en_passant st with
                        | Some ep => 
                            if position_eqb to ep then
                              match offset to (- dr) 0 with
                              | Some cap =>
                                  match b[cap] with
                                  | Some cap_pc =>
                                      (negb (color_eqb (piece_color cap_pc) c)) &&
                                      ptype_eqb (piece_type cap_pc) Pawn
                                  | None => false
                                  end
                              | None => false
                              end
                            else false
                        | None => false
                        end
                    end
                  else false
              | Some pl, None =>
                  if position_eqb pl to then
                    match b[to] with
                    | Some pc => negb (color_eqb (piece_color pc) c)
                    | None =>
                        match en_passant st with
                        | Some ep => 
                            if position_eqb to ep then
                              match offset to (- dr) 0 with
                              | Some cap =>
                                  match b[cap] with
                                  | Some cap_pc =>
                                      (negb (color_eqb (piece_color cap_pc) c)) &&
                                      ptype_eqb (piece_type cap_pc) Pawn
                                  | None => false
                                  end
                              | None => false
                              end
                            else false
                        | None => false
                        end
                    end
                  else false
              | None, Some pr =>
                  if position_eqb pr to then
                    match b[to] with
                    | Some pc => negb (color_eqb (piece_color pc) c)
                    | None =>
                        match en_passant st with
                        | Some ep => 
                            if position_eqb to ep then
                              match offset to (- dr) 0 with
                              | Some cap =>
                                  match b[cap] with
                                  | Some cap_pc =>
                                      (negb (color_eqb (piece_color cap_pc) c)) &&
                                      ptype_eqb (piece_type cap_pc) Pawn
                                  | None => false
                                  end
                              | None => false
                              end
                            else false
                        | None => false
                        end
                    end
                  else false
              | None, None => false
              end
        | None =>
            match offset from dr 1, offset from dr (-1) with
            | Some pl, Some pr =>
                if position_eqb pl to || position_eqb pr to then
                  match b[to] with
                  | Some pc => negb (color_eqb (piece_color pc) c)
                  | None =>
                      match en_passant st with
                      | Some ep => 
                          if position_eqb to ep then
                            match offset to (- dr) 0 with
                            | Some cap =>
                                match b[cap] with
                                | Some cap_pc =>
                                    (negb (color_eqb (piece_color cap_pc) c)) &&
                                    ptype_eqb (piece_type cap_pc) Pawn
                                | None => false
                                end
                            | None => false
                            end
                          else false
                      | None => false
                      end
                  end
                else false
            | Some pl, None =>
                if position_eqb pl to then
                  match b[to] with
                  | Some pc => negb (color_eqb (piece_color pc) c)
                  | None =>
                      match en_passant st with
                      | Some ep => 
                          if position_eqb to ep then
                            match offset to (- dr) 0 with
                            | Some cap =>
                                match b[cap] with
                                | Some cap_pc =>
                                    (negb (color_eqb (piece_color cap_pc) c)) &&
                                    ptype_eqb (piece_type cap_pc) Pawn
                                | None => false
                                end
                            | None => false
                            end
                          else false
                      | None => false
                      end
                  end
                else false
            | None, Some pr =>
                if position_eqb pr to then
                  match b[to] with
                  | Some pc => negb (color_eqb (piece_color pc) c)
                  | None =>
                      match en_passant st with
                      | Some ep => 
                          if position_eqb to ep then
                            match offset to (- dr) 0 with
                            | Some cap =>
                                match b[cap] with
                                | Some cap_pc =>
                                    (negb (color_eqb (piece_color cap_pc) c)) &&
                                    ptype_eqb (piece_type cap_pc) Pawn
                                | None => false
                                end
                            | None => false
                            end
                          else false
                      | None => false
                      end
                  end
                else false
            | None, None => false
            end
        end
  | None => false
  end.

Definition knight_move_valid_b (from to: Position) : bool :=
  existsb (fun od =>
    match offset from (fst od) (snd od) with
    | Some p => position_eqb p to
    | None => false
    end) knight_offsets.

Definition bishop_move_valid_b (b: Board) (from to: Position) : bool :=
  check_line_move b from to 1 1 ||
  check_line_move b from to 1 (-1) ||
  check_line_move b from to (-1) 1 ||
  check_line_move b from to (-1) (-1).

Definition rook_move_valid_b (b: Board) (from to: Position) : bool :=
  check_line_move b from to 1 0 ||
  check_line_move b from to (-1) 0 ||
  check_line_move b from to 0 1 ||
  check_line_move b from to 0 (-1).

Definition queen_move_valid_b (b: Board) (from to: Position) : bool :=
  bishop_move_valid_b b from to || rook_move_valid_b b from to.

Definition king_move_valid_b (from to: Position) : bool :=
  existsb (fun od =>
    match offset from (fst od) (snd od) with
    | Some p => position_eqb p to
    | None => false
    end) king_offsets.

Definition move_geometry_valid_b (st: GameState) (from to: Position) : bool :=
  let b := board st in
  match b[from] with
  | None => false
  | Some pc =>
      match piece_type pc with
      | Pawn => pawn_move_valid_b st from to
      | Knight => knight_move_valid_b from to
      | Bishop => bishop_move_valid_b b from to
      | Rook => rook_move_valid_b b from to
      | Queen => queen_move_valid_b b from to
      | King => king_move_valid_b from to
      end
  end.

(* En passant relevance check - returns the EP target only if a legal EP capture exists *)
Definition ep_relevant_b (st: GameState) : option Position :=
  match en_passant st with
  | None => None
  | Some ep_target =>
      let b := board st in
      let c := turn st in
      let dr := forwardZ c in
      (* Check if any pawn can capture en passant *)
      let can_capture_left :=
        match offset ep_target (-dr) (-1) with
        | Some from =>
            match b[from] with
            | Some pc => 
                color_eqb (piece_color pc) c && ptype_eqb (piece_type pc) Pawn
            | None => false
            end
        | None => false
        end in
      let can_capture_right :=
        match offset ep_target (-dr) 1 with
        | Some from =>
            match b[from] with
            | Some pc =>
                color_eqb (piece_color pc) c && ptype_eqb (piece_type pc) Pawn
            | None => false
            end
        | None => false
        end in
      if can_capture_left || can_capture_right then Some ep_target else None
  end.

(* Boolean move application *)
Definition apply_move_b (st: GameState) (m: Move) : option GameState :=
  match m with
  | MNormal from to promo =>
      let b := board st in
      match b[from] with
      | None => None
      | Some pc =>
          if negb (color_eqb (piece_color pc) (turn st)) then None
          else if negb (move_geometry_valid_b st from to) then None
          else 
            (* Check destination is capturable *)
            match b[to] with
            | Some target => 
                if color_eqb (piece_color target) (turn st) then None
                else if ptype_eqb (piece_type target) King then None
                else 
                  (* Check no self-check *)
                  let b' := next_board_normal st from to promo in
                  if in_check_b b' (turn st) then None
                  else Some (next_state_normal st from to promo)
            | None =>
                let b' := next_board_normal st from to promo in
                if in_check_b b' (turn st) then None
                else Some (next_state_normal st from to promo)
            end
      end
  | MCastle side =>
      let c := turn st in
      let b := board st in
      (* Check castling rights *)
      let has_right := 
        match c, side with
        | White, KingSide => white_king_side (castling st)
        | White, QueenSide => white_queen_side (castling st)  
        | Black, KingSide => black_king_side (castling st)
        | Black, QueenSide => black_queen_side (castling st)
        end in
      if negb has_right then None
      else
        (* Check king and rook in position *)
        let ks := if color_eqb c White then white_king_start else black_king_start in
        let rs := rook_start c side in
        match b[ks], b[rs] with
        | Some kpc, Some rpc =>
            if negb (piece_eqb kpc (mkPiece c King)) then None
            else if negb (piece_eqb rpc (mkPiece c Rook)) then None
            else
              (* Check corridors empty *)
              let empty_check := 
                forallb (fun p => match b[p] with None => true | _ => false end)
                        (king_corridor c side ++ rook_corridor c side) in
              if negb empty_check then None
              else
                (* Check not in check and path not attacked *)
                if in_check_b b c then None
                else
                  let safe_check :=
                    forallb (fun p => negb (attacks_b b (opposite_color c) p))
                            (ks :: king_corridor c side) in
                  if safe_check then Some (next_state_castle st side)
                  else None
        | _, _ => None
        end
  end.

(* Improved kings_not_adjacent using attacks *)
Definition kings_not_adjacent' (b: Board) : Prop :=
  forall pw pb,
    b[pw] = Some white_king ->
    b[pb] = Some black_king ->
    attacks_b b White pb = false /\ attacks_b b Black pw = false.

(* IState: GameState with well-formedness proof *)
Record IState := { 
  ist : GameState; 
  iwf : WFState ist 
}.

(* Executable move generation helpers *)
Fixpoint gen_ray_moves (b: Board) (from: Position) (dr df: Z) (fuel: nat) (acc: list Position) : list Position :=
  match fuel with
  | O => acc
  | S fuel' =>
      match offset from dr df with
      | None => acc
      | Some to =>
          match b[to] with
          | Some _ => to :: acc  (* Stop at first piece *)
          | None => gen_ray_moves b to dr df fuel' (to :: acc)
          end
      end
  end.

(* ========================================================================= *)
(* PHASE 1: POSITION KEYS AND GAME HISTORY                                  *)
(* ========================================================================= *)

(* Position key for repetition detection *)
Record PosKey := mkPosKey {
  k_board : list (option Piece);
  k_turn : Color;
  k_castle : CastlingRights;
  k_ep : option Position
}.

(* Convert board to canonical list *)
Definition board_to_list (b: Board) : list (option Piece) :=
  map (fun p => b[p]) all_positions.

(* Temporarily disable Program Mode for recursive definitions *)
Unset Program Mode.

(* Equality for option Piece *)
Definition option_piece_eqb (o1 o2: option Piece) : bool :=
  match o1, o2 with
  | None, None => true
  | Some p1, Some p2 => piece_eqb p1 p2
  | _, _ => false
  end.

(* Equality for list of option Piece *)
Fixpoint list_option_piece_eqb (l1 l2: list (option Piece)) : bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => option_piece_eqb h1 h2 && list_option_piece_eqb t1 t2
  | _, _ => false
  end.

(* Equality for CastlingRights *)
Definition castling_rights_eqb (cr1 cr2: CastlingRights) : bool :=
  Bool.eqb (white_king_side cr1) (white_king_side cr2) &&
  Bool.eqb (white_queen_side cr1) (white_queen_side cr2) &&
  Bool.eqb (black_king_side cr1) (black_king_side cr2) &&
  Bool.eqb (black_queen_side cr1) (black_queen_side cr2).

(* Equality for option Position *)
Definition option_position_eqb (o1 o2: option Position) : bool :=
  match o1, o2 with
  | None, None => true
  | Some p1, Some p2 => position_eqb p1 p2
  | _, _ => false
  end.

(* Re-enable Program Mode *)
Set Program Mode.

(* Create position key from game state *)
Definition pos_key_of_state (st: GameState) : PosKey :=
  mkPosKey (board_to_list (board st)) (turn st) (castling st) (ep_relevant_b st).

(* Equality for PosKey *)
Definition pos_key_eqb (k1 k2: PosKey) : bool :=
  list_option_piece_eqb (k_board k1) (k_board k2) &&
  color_eqb (k_turn k1) (k_turn k2) &&
  castling_rights_eqb (k_castle k1) (k_castle k2) &&
  option_position_eqb (k_ep k1) (k_ep k2).

(* Decidability for PosKey *)
Definition PosKey_dec : forall k1 k2 : PosKey, {k1 = k2} + {k1 <> k2}.
Proof.
  intros k1 k2.
  destruct (pos_key_eqb k1 k2) eqn:E.
  - left. 
    destruct k1 as [b1 t1 c1 e1], k2 as [b2 t2 c2 e2].
    unfold pos_key_eqb in E.
    apply andb_prop in E. destruct E as [E1 E2].
    apply andb_prop in E1. destruct E1 as [E3 E4].
    apply andb_prop in E3. destruct E3 as [E5 E6].
    f_equal.
    + assert (Hb1b2: list_option_piece_eqb b1 b2 = true) by exact E5.
      clear - Hb1b2.
      revert b2 Hb1b2.
      induction b1; destruct b2; simpl in *; intros; try discriminate; auto.
      apply andb_prop in Hb1b2. destruct Hb1b2 as [H1 H2].
      f_equal.
      * destruct a, o; simpl in H1; try discriminate; auto.
        destruct (piece_eqb_spec p p0); congruence.
      * apply IHb1. exact H2.
    + assert (Ht: color_eqb t1 t2 = true) by exact E6.
      destruct (color_eqb_spec t1 t2); [exact e | discriminate Ht].
    + unfold castling_rights_eqb in E4.
      apply andb_prop in E4. destruct E4 as [E7 E8].
      apply andb_prop in E7. destruct E7 as [E9 E10].
      apply andb_prop in E9. destruct E9 as [E11 E12].
      destruct c1, c2. simpl in *.
      destruct white_king_side0, white_king_side1; try discriminate;
      destruct white_queen_side0, white_queen_side1; try discriminate;
      destruct black_king_side0, black_king_side1; try discriminate;
      destruct black_queen_side0, black_queen_side1; try discriminate; auto.
    + destruct e1, e2; simpl in E2; try discriminate; auto.
      destruct (position_eqb_spec p p0); congruence.
  - right. intro H. subst k2.
    clear - E.
    assert (pos_key_eqb k1 k1 = true).
    { unfold pos_key_eqb.
      assert (list_option_piece_eqb (k_board k1) (k_board k1) = true).
      { clear. induction (k_board k1); simpl; auto.
        destruct a; simpl; auto. rewrite piece_eqb_refl. simpl. apply IHl. }
      rewrite H. simpl.
      rewrite color_eqb_refl. simpl.
      unfold castling_rights_eqb.
      destruct (k_castle k1). simpl.
      destruct white_king_side0, white_queen_side0, black_king_side0, black_queen_side0; simpl;
      (destruct (k_ep k1); simpl; auto; destruct (position_eqb_spec p p); auto; congruence). }
    congruence.
Defined.

(* Game with history *)
Unset Program Mode.
Record Game := mkGame {
  g_cur : GameState;
  g_hist : list PosKey
}.

(* Start a new game *)
Definition start_game (initial_state: GameState) : Game :=
  {| g_cur := initial_state; g_hist := [pos_key_of_state initial_state] |}.
Set Program Mode.

(* Apply a move to a game *)
Definition game_apply (g: Game) (m: Move) : option Game :=
  match apply_move_b (g_cur g) m with
  | None => None
  | Some st' =>
      let k' := pos_key_of_state st' in
      Some (mkGame st' (k' :: g_hist g))
  end.

(* Count occurrences of a position key in history *)
Fixpoint count_key (k: PosKey) (hist: list PosKey) : nat :=
  match hist with
  | [] => 0
  | h::t => if pos_key_eqb k h then S (count_key k t) else count_key k t
  end.

(* Check for threefold repetition (claimable) *)
Definition is_threefold_repetition (g: Game) : bool :=
  let cur_key := pos_key_of_state (g_cur g) in
  (3 <=? count_key cur_key (g_hist g))%nat.

(* Check for fivefold repetition (automatic) *)
Definition is_fivefold_repetition (g: Game) : bool :=
  let cur_key := pos_key_of_state (g_cur g) in
  (5 <=? count_key cur_key (g_hist g))%nat.

(* Check for 50-move rule (claimable) *)
Definition is_fifty_move_rule (g: Game) : bool :=
  (100 <=? halfmove (g_cur g))%nat.

(* Check for 75-move rule (automatic) *)
Definition is_seventyfive_move_rule (g: Game) : bool :=
  (150 <=? halfmove (g_cur g))%nat.

(* Count pieces by type and color *)
Unset Program Mode.
Definition count_pieces (b: Board) (c: Color) (pt: PieceType) : nat :=
  List.length (List.filter (fun p =>
    match b[p] with
    | Some pc => color_eqb (piece_color pc) c && ptype_eqb (piece_type pc) pt
    | None => false
    end) all_positions).
(* Count all pieces *)
Definition count_all_pieces (b: Board) : nat :=
  List.length (List.filter (fun p =>
    match b[p] with
    | Some _ => true
    | None => false
    end) all_positions).

(* Check if position is light or dark square *)
Definition is_light_square (p: Position) : bool :=
  Z.even (rankZ p + fileZ p).

(* Count bishops on light squares *)
Definition count_bishops_light (b: Board) (c: Color) : nat :=
  List.length (List.filter (fun p =>
    is_light_square p &&
    match b[p] with
    | Some pc => color_eqb (piece_color pc) c && ptype_eqb (piece_type pc) Bishop
    | None => false
    end) all_positions).

(* Count bishops on dark squares *)
Definition count_bishops_dark (b: Board) (c: Color) : nat :=
  List.length (List.filter (fun p =>
    negb (is_light_square p) &&
    match b[p] with
    | Some pc => color_eqb (piece_color pc) c && ptype_eqb (piece_type pc) Bishop
    | None => false
    end) all_positions).

Set Program Mode.

(* Check for dead position *)
Definition is_dead_position (b: Board) : bool :=
  let total := count_all_pieces b in
  (* K vs K *)
  (Nat.eqb total 2) ||
  (* K+B vs K or K+N vs K *)
  ((Nat.eqb total 3) && 
   ((Nat.eqb (count_pieces b White Bishop + count_pieces b Black Bishop) 1) ||
    (Nat.eqb (count_pieces b White Knight + count_pieces b Black Knight) 1))) ||
  (* K+B vs K+B with bishops on same color *)
  ((Nat.eqb total 4) && 
   (Nat.eqb (count_pieces b White Bishop) 1) && 
   (Nat.eqb (count_pieces b Black Bishop) 1) &&
   ((Nat.eqb (count_bishops_light b White) 1 && Nat.eqb (count_bishops_light b Black) 1) ||
    (Nat.eqb (count_bishops_dark b White) 1 && Nat.eqb (count_bishops_dark b Black) 1))) ||
  (* K+NN vs K *)
  ((Nat.eqb total 4) &&
   ((Nat.eqb (count_pieces b White Knight) 2 && Nat.eqb (count_pieces b Black Knight) 0) ||
    (Nat.eqb (count_pieces b White Knight) 0 && Nat.eqb (count_pieces b Black Knight) 2))).

(* ========================================================================= *)
(* UNIFIED OUTCOME FUNCTION                                                  *)
(* ========================================================================= *)

(* Outcome of a game *)
Inductive Outcome :=
  | OMate (winner : Color)
  | ODraw (reason : string)
  | OOngoing (can_claim_50 : bool) (can_claim_3fold : bool).

Definition gen_legal_moves (st: GameState) : list Move := [].

(* Helper: Check if there are no legal moves *)
Definition no_moves_b (st: GameState) : bool :=
  match gen_legal_moves st with
  | [] => true
  | _ => false
  end.

(* Get outcome of current position *)
Definition game_outcome (g: Game) : Outcome :=
  let st := g_cur g in
  let b := board st in
  let c := turn st in
  (* Check for checkmate *)
  if no_moves_b st && in_check_b b c then
    OMate (opposite_color c)
  (* Check for stalemate *)
  else if no_moves_b st && negb (in_check_b b c) then
    ODraw "stalemate"
  (* Check for automatic 75-move rule *)
  else if is_seventyfive_move_rule g then
    ODraw "75-move rule"
  (* Check for automatic 5-fold repetition *)
  else if is_fivefold_repetition g then
    ODraw "5-fold repetition"
  (* Check for dead position *)
  else if is_dead_position b then
    ODraw "dead position"
  (* Game is ongoing, check for claimable draws *)
  else
    OOngoing (is_fifty_move_rule g) (is_threefold_repetition g).

(* ========================================================================= *)
(* FEN NOTATION                                                              *)
(* ========================================================================= *)

(* Convert piece to FEN character *)
Definition piece_to_fen_char (p: Piece) : ascii :=
  match piece_color p, piece_type p with
  | White, Pawn => "P"%char
  | White, Knight => "N"%char
  | White, Bishop => "B"%char
  | White, Rook => "R"%char
  | White, Queen => "Q"%char
  | White, King => "K"%char
  | Black, Pawn => "p"%char
  | Black, Knight => "n"%char
  | Black, Bishop => "b"%char
  | Black, Rook => "r"%char
  | Black, Queen => "q"%char
  | Black, King => "k"%char
  end.

(* Convert nat digit to ascii *)
Unset Program Mode.
Definition nat_to_digit (n: nat) : ascii :=
  match n with
  | 0%nat => "0"%char
  | 1%nat => "1"%char
  | 2%nat => "2"%char
  | 3%nat => "3"%char
  | 4%nat => "4"%char
  | 5%nat => "5"%char
  | 6%nat => "6"%char
  | 7%nat => "7"%char
  | 8%nat => "8"%char
  | _ => "?"%char
  end.

(* Process one rank for FEN - simplified version *)
Definition fen_process_rank (b: Board) (rank: Fin.t 8) : string :=
  let process_file := fix process_file (file: nat) (empty_count: nat) (acc: string) : string :=
    match file with
    | 0%nat => 
        if Nat.eqb empty_count 0%nat then acc
        else String (nat_to_digit empty_count) acc
    | S file' =>
        match lt_dec (8 - file) 8 with
        | left pf =>
            let pos := mkPos rank (Fin.of_nat_lt pf) in
            match b[pos] with
            | Some p =>
                let acc' := if Nat.eqb empty_count 0%nat then acc 
                           else String (nat_to_digit empty_count) acc in
                process_file file' 0%nat (String (piece_to_fen_char p) acc')
            | None =>
                process_file file' (S empty_count) acc
            end
        | right _ => acc
        end
    end in
  process_file 8%nat 0%nat EmptyString.

(* Process all ranks for FEN - top to bottom (rank 8 to rank 1) *)
Definition fen_board (b: Board) : string :=
  let ranks := List.rev fins8 in (* fins8 is [0..7], rev gives [7..0] *)
  fold_right (fun r acc =>
    let rs := fen_process_rank b r in
    if string_dec acc EmptyString then rs
    else append rs (append "/" acc))
  EmptyString ranks.

(* Convert castling rights to FEN string *)
Definition fen_castling (cr: CastlingRights) : string :=
  let k := if white_king_side cr then "K"%string else EmptyString in
  let q := if white_queen_side cr then "Q"%string else EmptyString in
  let k' := if black_king_side cr then "k"%string else EmptyString in
  let q' := if black_queen_side cr then "q"%string else EmptyString in
  let all := append k (append q (append k' q')) in
  if string_dec all EmptyString then "-"%string else all.

(* Convert file index to letter *)
Definition file_to_char (f: File) : ascii :=
  match proj1_sig (Fin.to_nat f) with
  | 0%nat => "a"%char
  | 1%nat => "b"%char
  | 2%nat => "c"%char
  | 3%nat => "d"%char
  | 4%nat => "e"%char
  | 5%nat => "f"%char
  | 6%nat => "g"%char
  | 7%nat => "h"%char
  | _ => "?"%char
  end.

(* Convert rank index to character *)
Definition rank_to_char (r: Rank) : ascii :=
  nat_to_digit (S (proj1_sig (Fin.to_nat r))).

(* Convert position to algebraic notation *)
Definition pos_to_alg (p: Position) : string :=
  String (file_to_char (pos_file p)) (String (rank_to_char (pos_rank p)) EmptyString).

(* Convert en passant target to FEN string *)
Definition fen_en_passant (ep: option Position) : string :=
  match ep with
  | None => "-"%string
  | Some p => pos_to_alg p
  end.

(* Convert turn to FEN string *)
Definition fen_turn (c: Color) : string :=
  match c with
  | White => "w"%string
  | Black => "b"%string
  end.

(* Convert nat to string - simple version for small numbers *)
Unset Program Mode.
Fixpoint nat_to_string_aux (n: nat) (fuel: nat) : string :=
  match fuel with
  | 0%nat => ""%string
  | S fuel' =>
      match n with
      | 0%nat => "0"%string
      | _ =>
          let digit := nat_to_digit (Nat.modulo n 10) in
          let rest := Nat.div n 10 in
          if Nat.eqb rest 0 then String digit EmptyString
          else append (nat_to_string_aux rest fuel') (String digit EmptyString)
      end
  end.

Definition nat_to_string (n: nat) : string :=
  if Nat.eqb n 0 then "0"%string else nat_to_string_aux n n.
Set Program Mode.

(* Complete FEN export function *)
Unset Program Mode.
Definition fen_of_state (st: GameState) : string :=
  let board_str := fen_board (board st) in
  let turn_str := fen_turn (turn st) in
  let castle_str := fen_castling (castling st) in
  let ep_str := fen_en_passant (ep_relevant_b st) in
  let halfmove_str := nat_to_string (halfmove st) in
  let fullmove_str := nat_to_string (fullmove st) in
  append board_str (append " "%string 
    (append turn_str (append " "%string
      (append castle_str (append " "%string
        (append ep_str (append " "%string
          (append halfmove_str (append " "%string fullmove_str))))))))).
Set Program Mode.

(* Convert piece to display character for ASCII board *)
Definition piece_to_display_char (p: Piece) : ascii :=
  piece_to_fen_char p.

(* Display one rank of the board *)
Unset Program Mode.
Definition display_rank (b: Board) (rank: Fin.t 8) : string :=
  let process_file := fix process_file (file: nat) (acc: string) : string :=
    match file with
    | 0%nat => acc
    | S file' =>
        match lt_dec (8 - file) 8 with
        | left pf =>
            let pos := mkPos rank (Fin.of_nat_lt pf) in
            let char := match b[pos] with
                        | Some p => piece_to_display_char p
                        | None => "."%char
                        end in
            process_file file' (String char (String " "%char acc))
        | right _ => acc
        end
    end in
  process_file 8%nat EmptyString.

(* Display the entire board *)
Definition board_to_ascii (b: Board) : string :=
  let display_ranks := fix display_ranks (r: nat) (acc: string) : string :=
    match r with
    | 0%nat => acc
    | S r' =>
        match lt_dec r' 8 with
        | left pf =>
            let rank_str := display_rank b (Fin.of_nat_lt pf) in
            let rank_num := nat_to_string (S r') in
            let line := append rank_num (append " "%string (append rank_str (String "010"%char EmptyString))) in
            display_ranks r' (append acc line)
        | right _ => acc
        end
    end in
  let board_lines := display_ranks 8%nat EmptyString in
  let files_label := "  a b c d e f g h"%string in
  append board_lines (append files_label (String "010"%char EmptyString)).

(* Parse file character to File *)
Definition char_to_file (c: ascii) : option File :=
  match c with
  | "a"%char => match lt_dec 0 8 with left pf => Some (Fin.of_nat_lt pf) | _ => None end
  | "b"%char => match lt_dec 1 8 with left pf => Some (Fin.of_nat_lt pf) | _ => None end
  | "c"%char => match lt_dec 2 8 with left pf => Some (Fin.of_nat_lt pf) | _ => None end
  | "d"%char => match lt_dec 3 8 with left pf => Some (Fin.of_nat_lt pf) | _ => None end
  | "e"%char => match lt_dec 4 8 with left pf => Some (Fin.of_nat_lt pf) | _ => None end
  | "f"%char => match lt_dec 5 8 with left pf => Some (Fin.of_nat_lt pf) | _ => None end
  | "g"%char => match lt_dec 6 8 with left pf => Some (Fin.of_nat_lt pf) | _ => None end
  | "h"%char => match lt_dec 7 8 with left pf => Some (Fin.of_nat_lt pf) | _ => None end
  | _ => None
  end.

(* Parse rank character to Rank *)
Definition char_to_rank (c: ascii) : option Rank :=
  match c with
  | "1"%char => match lt_dec 0 8 with left pf => Some (Fin.of_nat_lt pf) | _ => None end
  | "2"%char => match lt_dec 1 8 with left pf => Some (Fin.of_nat_lt pf) | _ => None end
  | "3"%char => match lt_dec 2 8 with left pf => Some (Fin.of_nat_lt pf) | _ => None end
  | "4"%char => match lt_dec 3 8 with left pf => Some (Fin.of_nat_lt pf) | _ => None end
  | "5"%char => match lt_dec 4 8 with left pf => Some (Fin.of_nat_lt pf) | _ => None end
  | "6"%char => match lt_dec 5 8 with left pf => Some (Fin.of_nat_lt pf) | _ => None end
  | "7"%char => match lt_dec 6 8 with left pf => Some (Fin.of_nat_lt pf) | _ => None end
  | "8"%char => match lt_dec 7 8 with left pf => Some (Fin.of_nat_lt pf) | _ => None end
  | _ => None
  end.

(* Parse digit character to nat *)
Definition digit_to_nat (c: ascii) : option nat :=
  match c with
  | "0"%char => Some 0%nat
  | "1"%char => Some 1%nat
  | "2"%char => Some 2%nat
  | "3"%char => Some 3%nat
  | "4"%char => Some 4%nat
  | "5"%char => Some 5%nat
  | "6"%char => Some 6%nat
  | "7"%char => Some 7%nat
  | "8"%char => Some 8%nat
  | "9"%char => Some 9%nat
  | _ => None
  end.

(* Parse FEN character to piece *)
Definition fen_char_to_piece (c: ascii) : option Piece :=
  match c with
  | "P"%char => Some (mkPiece White Pawn)
  | "N"%char => Some (mkPiece White Knight)
  | "B"%char => Some (mkPiece White Bishop)
  | "R"%char => Some (mkPiece White Rook)
  | "Q"%char => Some (mkPiece White Queen)
  | "K"%char => Some (mkPiece White King)
  | "p"%char => Some (mkPiece Black Pawn)
  | "n"%char => Some (mkPiece Black Knight)
  | "b"%char => Some (mkPiece Black Bishop)
  | "r"%char => Some (mkPiece Black Rook)
  | "q"%char => Some (mkPiece Black Queen)
  | "k"%char => Some (mkPiece Black King)
  | _ => None
  end.

(* Parse FEN turn character *)
Definition fen_char_to_turn (c: ascii) : option Color :=
  match c with
  | "w"%char => Some White
  | "b"%char => Some Black
  | _ => None
  end.

(* Parse one rank from FEN string *)
Unset Program Mode.
Definition parse_fen_rank (rank_str: string) (rank: Rank) : Board -> option Board :=
  let fix parse_chars (s: string) (file: nat) (b: Board) : option Board :=
    match s with
    | EmptyString => 
        if Nat.eqb file 8 then Some b else None
    | String c rest =>
        if Nat.ltb file 8 then
          match digit_to_nat c with
          | Some n =>
              let new_file := Nat.add file n in
              if Nat.leb new_file 8 then
                parse_chars rest new_file b
              else None
          | None =>
              match fen_char_to_piece c with
              | Some p =>
                  match lt_dec file 8 with
                  | left pf =>
                      let pos := mkPos rank (Fin.of_nat_lt pf) in
                      parse_chars rest (S file) (b[pos := Some p])
                  | right _ => None
                  end
              | None => None
              end
          end
        else None
    end in
  parse_chars rank_str 0%nat .

(* Split string by delimiter *)
Fixpoint split_string_at (s: string) (delim: ascii) : (string * string) :=
  match s with
  | EmptyString => (EmptyString, EmptyString)
  | String c rest =>
      if Ascii.eqb c delim then
        (EmptyString, rest)
      else
        let (before, after) := split_string_at rest delim in
        (String c before, after)
  end.

(* Parse castling rights from FEN string *)
Unset Program Mode.
Definition parse_fen_castling (s: string) : CastlingRights :=
  let fix check_chars (s: string) (wk wq bk bq: bool) : CastlingRights :=
    match s with
    | EmptyString => mkCastlingRights wk wq bk bq
    | String c rest =>
        match c with
        | "K"%char => check_chars rest true wq bk bq
        | "Q"%char => check_chars rest wk true bk bq
        | "k"%char => check_chars rest wk wq true bq
        | "q"%char => check_chars rest wk wq bk true
        | "-"%char => mkCastlingRights false false false false
        | _ => check_chars rest wk wq bk bq
        end
    end in
  check_chars s false false false false.

(* Parse en passant target from FEN string *)
Definition parse_fen_ep (s: string) : option Position :=
  match s with
  | String f (String r EmptyString) =>
      match char_to_file f, char_to_rank r with
      | Some file, Some rank => Some (mkPos rank file)
      | _, _ => None
      end
  | "-"%string => None
  | _ => None
  end.

(* Parse natural number from string *)
Unset Program Mode.
Fixpoint string_to_nat (s: string) : option nat :=
  match s with
  | EmptyString => None
  | String c rest =>
      match digit_to_nat c with
      | None => None
      | Some d =>
          match rest with
          | EmptyString => Some d
          | _ =>
              match string_to_nat rest with
              | None => None
              | Some n => Some (10 * d + n)%nat
              end
          end
      end
  end.

(* Parse all ranks from FEN board string - top to bottom *)
Unset Program Mode.
Definition parse_fen_board (board_str: string) : option Board :=
  let fix parse_ranks (s: string) (r: nat) (b: Board) : option Board :=
    match r with
    | 0%nat => Some b
    | S r' =>
        let (rank_str, rest) := split_string_at s "/"%char in
        (* r' directly gives us rank index: r=8 means r'=7 (rank 8), r=7 means r'=6 (rank 7), etc. *)
        match lt_dec r' 8 with
        | left pf =>
            match parse_fen_rank rank_str (Fin.of_nat_lt pf) b with
            | Some b' => parse_ranks rest r' b'
            | None => None
            end
        | right _ => None
        end
    end in
  (* Start at r=8; the first chunk goes to rank 7 (i.e., FEN's rank 8) *)
  parse_ranks board_str 8%nat (fun _ => None).

(* Main FEN import function *)
Definition state_of_fen (fen: string) : option GameState :=
  (* Split FEN into components *)
  let (board_part, rest1) := split_string_at fen " "%char in
  let (turn_part, rest2) := split_string_at rest1 " "%char in
  let (castle_part, rest3) := split_string_at rest2 " "%char in
  let (ep_part, rest4) := split_string_at rest3 " "%char in
  let (halfmove_part, fullmove_part) := split_string_at rest4 " "%char in
  
  (* Parse each component *)
  match parse_fen_board board_part with
  | None => None
  | Some board =>
      match turn_part with
      | String c EmptyString =>
          match fen_char_to_turn c with
          | None => None
          | Some turn =>
              let castling := parse_fen_castling castle_part in
              let ep := parse_fen_ep ep_part in
              match string_to_nat halfmove_part, string_to_nat fullmove_part with
              | Some halfmove, Some fullmove =>
                  Some (mkGameState board turn castling ep halfmove fullmove)
              | _, _ => None
              end
          end
      | _ => None
      end
  end.

(* ========================================================================= *)
(* PHASE 3: MOVE GENERATION                                                  *)
(* ========================================================================= *)

(* Generate knight moves from a position *)
Definition gen_knight_moves (b: Board) (from: Position) (c: Color) : list Move :=
  let moves := 
    List.map (fun od =>
      match offset from (fst od) (snd od) with
      | Some to =>
          match b[to] with
          | Some pc =>
              if negb (color_eqb (piece_color pc) c) then
                [MNormal from to None]
              else []
          | None => [MNormal from to None]
          end
      | None => []
      end) knight_offsets in
  List.concat moves.

(* Generate king moves from a position *)
Definition gen_king_moves (b: Board) (from: Position) (c: Color) : list Move :=
  let moves :=
    List.map (fun od =>
      match offset from (fst od) (snd od) with
      | Some to =>
          match b[to] with
          | Some pc =>
              if negb (color_eqb (piece_color pc) c) then
                [MNormal from to None]
              else []
          | None => [MNormal from to None]
          end
      | None => []
      end) king_offsets in
  List.concat moves.

(* Generate slider moves (for rook, bishop, queen) *)
Definition gen_slider_moves (b: Board) (from: Position) (c: Color) (dirs: list (Z * Z)) : list Move :=
  let moves :=
    List.map (fun dir =>
      gen_ray_moves b from (fst dir) (snd dir) 7 nil) dirs in
  let valid_moves :=
    List.filter (fun to =>
      match b[to] with
      | Some pc => negb (color_eqb (piece_color pc) c)
      | None => true
      end) (List.concat moves) in
  List.map (fun to => MNormal from to None) valid_moves.

(* Generate pawn pushes (forward moves) *)
Definition gen_pawn_pushes (b: Board) (from: Position) (c: Color) : list Move :=
  let dr := forwardZ c in
  let moves1 :=
    match offset from dr 0 with
    | Some to =>
        if match b[to] with None => true | _ => false end then
          let is_promo := ((color_eqb c White) && (Z.eqb (rankZ to) 7)) || 
                          ((color_eqb c Black) && (Z.eqb (rankZ to) 0)) in
          if is_promo then
            [MNormal from to (Some Queen); MNormal from to (Some Rook);
             MNormal from to (Some Bishop); MNormal from to (Some Knight)]
          else [MNormal from to None]
        else nil
    | None => nil
    end in
  let moves2 :=
    let start_rank := if color_eqb c White then 1 else 6 in
    if Z.eqb (rankZ from) start_rank then
      match offset from dr 0 with
      | Some mid =>
          if match b[mid] with None => true | _ => false end then
            match offset from (2 * dr) 0 with
            | Some to =>
                if match b[to] with None => true | _ => false end then
                  [MNormal from to None]
                else nil
            | None => nil
            end
          else nil
      | None => nil
      end
    else nil in
  moves1 ++ moves2.

(* Generate pawn captures *)
Definition gen_pawn_captures (st: GameState) (from: Position) (c: Color) : list Move :=
  let b := board st in
  let dr := forwardZ c in
  let cap_moves := 
    List.concat (List.map (fun df =>
      match offset from dr df with
      | Some to =>
          let is_promo := ((color_eqb c White) && (Z.eqb (rankZ to) 7)) || 
                          ((color_eqb c Black) && (Z.eqb (rankZ to) 0)) in
          match b[to] with
          | Some pc =>
              if negb (color_eqb (piece_color pc) c) then
                if is_promo then
                  [MNormal from to (Some Queen); MNormal from to (Some Rook);
                   MNormal from to (Some Bishop); MNormal from to (Some Knight)]
                else [MNormal from to None]
              else nil
          | None =>
              match en_passant st with
              | Some ep =>
                  if position_eqb to ep then [MNormal from to None]
                  else nil
              | None => nil
              end
          end
      | None => nil
      end) (1 :: (-1) :: nil)) in
  cap_moves.

(* Check if castling is possible (boolean version) *)
Definition can_castle_b (st: GameState) (side: CastleSide) : bool :=
  let c := turn st in
  let b := board st in
  let has_right := 
    match c, side with
    | White, KingSide => white_king_side (castling st)
    | White, QueenSide => white_queen_side (castling st)  
    | Black, KingSide => black_king_side (castling st)
    | Black, QueenSide => black_queen_side (castling st)
    end in
  if negb has_right then false
  else
    let ks := if color_eqb c White then white_king_start else black_king_start in
    let rs := rook_start c side in
    match b[ks], b[rs] with
    | Some kpc, Some rpc =>
        if negb (piece_eqb kpc (mkPiece c King)) then false
        else if negb (piece_eqb rpc (mkPiece c Rook)) then false
        else
          let empty_check := 
            forallb (fun p => match b[p] with None => true | _ => false end)
                    (king_corridor c side ++ rook_corridor c side) in
          if negb empty_check then false
          else
            if in_check_b b c then false
            else
              forallb (fun p => negb (attacks_b b (opposite_color c) p))
                      (ks :: king_corridor c side)
    | _, _ => false
    end.

(* Generate castling moves *)
Definition gen_castles (st: GameState) : list Move :=
  let moves := nil in
  let moves := if can_castle_b st KingSide then MCastle KingSide :: moves else moves in
  let moves := if can_castle_b st QueenSide then MCastle QueenSide :: moves else moves in
  moves.

(* Generate all pseudo-legal moves for current player *)
Definition gen_pseudo_moves (st: GameState) : list Move :=
  let b := board st in
  let c := turn st in
  let piece_moves :=
    List.concat (List.map (fun pos =>
      match b[pos] with
      | Some pc =>
          if color_eqb (piece_color pc) c then
            match piece_type pc with
            | Pawn => gen_pawn_pushes b pos c ++ gen_pawn_captures st pos c
            | Knight => gen_knight_moves b pos c
            | Bishop => gen_slider_moves b pos c ((1,1)%Z :: (1,-1)%Z :: (-1,1)%Z :: (-1,-1)%Z :: nil)
            | Rook => gen_slider_moves b pos c ((1,0)%Z :: (-1,0)%Z :: (0,1)%Z :: (0,-1)%Z :: nil)
            | Queen => gen_slider_moves b pos c ((1,1)%Z :: (1,-1)%Z :: (-1,1)%Z :: (-1,-1)%Z ::
                                                  (1,0)%Z :: (-1,0)%Z :: (0,1)%Z :: (0,-1)%Z :: nil)
            | King => gen_king_moves b pos c
            end
          else nil
      | None => nil
      end) all_positions) in
  piece_moves ++ gen_castles st.

Unset Program Mode.
Definition gen_legal_moves_real (st: GameState) : list Move :=
  List.filter (fun m =>
    match apply_move_b st m with
    | Some _ => true
    | None => false
    end) (gen_pseudo_moves st).


(* Perft - count leaf nodes at given depth *)
Fixpoint perft_state (st: GameState) (depth: nat) : nat :=
  match depth with
  | 0%nat => 1%nat
  | S d =>
      let moves := gen_legal_moves_real st in
      List.fold_left (fun acc m =>
        match apply_move_b st m with
        | Some st' => Nat.add acc (perft_state st' d)
        | None => acc
        end) moves 0%nat
  end.

(* ========================================================================= *)
(* IMPROVEMENTS AND ADDITIONAL FEATURES                                      *)
(* ========================================================================= *)

(* Standard starting position for testing *)
Unset Program Mode.
Definition standard_starting_board : Board :=
  fun pos =>
    let r := proj1_sig (Fin.to_nat (pos_rank pos)) in
    let f := proj1_sig (Fin.to_nat (pos_file pos)) in
    match r with
    | 0%nat => (* Rank 1 - White pieces *)
        match f with
        | 0%nat => Some (mkPiece White Rook)
        | 1%nat => Some (mkPiece White Knight)
        | 2%nat => Some (mkPiece White Bishop)
        | 3%nat => Some (mkPiece White Queen)
        | 4%nat => Some (mkPiece White King)
        | 5%nat => Some (mkPiece White Bishop)
        | 6%nat => Some (mkPiece White Knight)
        | 7%nat => Some (mkPiece White Rook)
        | _ => None
        end
    | 1%nat => Some (mkPiece White Pawn) (* Rank 2 - White pawns *)
    | 6%nat => Some (mkPiece Black Pawn) (* Rank 7 - Black pawns *)
    | 7%nat => (* Rank 8 - Black pieces *)
        match f with
        | 0%nat => Some (mkPiece Black Rook)
        | 1%nat => Some (mkPiece Black Knight)
        | 2%nat => Some (mkPiece Black Bishop)
        | 3%nat => Some (mkPiece Black Queen)
        | 4%nat => Some (mkPiece Black King)
        | 5%nat => Some (mkPiece Black Bishop)
        | 6%nat => Some (mkPiece Black Knight)
        | 7%nat => Some (mkPiece Black Rook)
        | _ => None
        end
    | _ => None
    end.

Definition initial_position : GameState :=
  mkGameState standard_starting_board White 
    (mkCastlingRights true true true true) None 0 1.

(* Generate check evasions - moves that get out of check *)
Definition gen_check_evasions (st: GameState) : list Move :=
  (* Uses complete legal move generation and filtering.
     Optimization targets:
     1. King moves to safe squares
     2. Captures of the checking piece
     3. Blocks (for sliding piece checks) *)
  gen_legal_moves_real st.

(* Optimized legal move generation *)
Definition gen_legal_moves_optimized (st: GameState) : list Move :=
  if in_check_b (board st) (turn st) then
    gen_check_evasions st
  else
    gen_legal_moves_real st.

Module LegalMoves.
  Definition gen_legal_moves (st: GameState) : list Move :=
    gen_legal_moves_optimized st.
End LegalMoves.

(* Check if all pawns are blocked (cannot move or capture) *)
Unset Program Mode.
Definition all_pawns_blocked (b: Board) : bool :=
  forallb (fun pos =>
    match b[pos] with
    | Some pc =>
        if ptype_eqb (piece_type pc) Pawn then
          let c := piece_color pc in
          let dr := forwardZ c in
          (* Check if pawn can move forward *)
          let can_push := 
            match offset pos dr 0 with
            | Some to => match b[to] with None => true | _ => false end
            | None => false
            end in
          (* Check if pawn can capture *)
          let can_capture_left :=
            match offset pos dr 1 with
            | Some to => 
                match b[to] with 
                | Some target => negb (color_eqb (piece_color target) c)
                | None => false
                end
            | None => false
            end in
          let can_capture_right :=
            match offset pos dr (-1) with
            | Some to =>
                match b[to] with
                | Some target => negb (color_eqb (piece_color target) c)
                | None => false
                end
            | None => false
            end in
          negb (can_push || can_capture_left || can_capture_right)
        else true
    | None => true
    end) all_positions.

(* Improved dead position detection *)
Definition is_dead_position_improved (b: Board) : bool :=
  let total := count_all_pieces b in
  (* Original cases *)
  is_dead_position b ||
  (* Additional case: All pawns blocked and insufficient material *)
  (all_pawns_blocked b && 
   ((Nat.eqb (count_pieces b White Knight + count_pieces b Black Knight) 0) &&
    (Nat.eqb (count_pieces b White Bishop + count_pieces b Black Bishop) 0) &&
    (Nat.eqb (count_pieces b White Rook + count_pieces b Black Rook) 0) &&
    (Nat.eqb (count_pieces b White Queen + count_pieces b Black Queen) 0))).

(* ========================================================================= *)
(* KEY CORRECTNESS THEOREMS                                                 *)
(* ========================================================================= *)

Lemma position_eqb_trans : forall p1 p2 p3,
  position_eqb p1 p2 = true ->
  position_eqb p2 p3 = true ->
  position_eqb p1 p3 = true.
Proof.
  intros p1 p2 p3 H12 H23.
  destruct (position_eqb_spec p1 p2); try discriminate.
  destruct (position_eqb_spec p2 p3); try discriminate.
  subst.
  destruct (position_eqb_spec p3 p3).
  - reflexivity.
  - contradiction.
Qed.

Set Program Mode.

Definition gen_legal_moves_proper (st: GameState) : list Move :=
  gen_legal_moves_optimized st.

Definition no_moves_b_proper (st: GameState) : bool :=
  match gen_legal_moves_proper st with
  | [] => true
  | _ => false
  end.

Definition game_outcome_proper (g: Game) : Outcome :=
  let st := g_cur g in
  let b := board st in
  let c := turn st in
  (* Check for checkmate *)
  if no_moves_b_proper st && in_check_b b c then
    OMate (opposite_color c)
  (* Check for stalemate *)
  else if no_moves_b_proper st && negb (in_check_b b c) then
    ODraw "stalemate"
  (* Check for automatic 75-move rule *)
  else if is_seventyfive_move_rule g then
    ODraw "75-move rule"
  (* Check for automatic 5-fold repetition *)
  else if is_fivefold_repetition g then
    ODraw "5-fold repetition"
  (* Check for dead position *)
  else if is_dead_position b then
    ODraw "dead position"
  (* Game is ongoing, check for claimable draws *)
  else
    OOngoing (is_fifty_move_rule g) (is_threefold_repetition g).

Fixpoint perft_proper (st: GameState) (depth: nat) : nat :=
  match depth with
  | 0%nat => 1%nat
  | S d =>
      let moves := gen_legal_moves_proper st in
      List.fold_left (fun acc m =>
        match apply_move_b st m with
        | Some st' => Nat.add acc (perft_proper st' d)
        | None => acc
        end) moves 0%nat
  end.
