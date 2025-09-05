(*
  ChessTotal.v — a total formalization of chess in Coq

  Coordinates:
    Position.(rank) 0..7 from White back rank upward (0=a1 rank),
    Position.(file) 0..7 from a..h.
  offset p dr df: rank += dr, file += df (dr/df : Z).
  White forward = +1 rank; Black forward = -1 rank.

  This file provides:
  - Piece/board/state definitions
  - Attack detection
  - Pseudo-legal move generation (with "no-king-capture" guard)
  - Castling, en passant, promotion
  - apply_move that enforces geometry (via membership in generator) and no self-check
  - Repetition keys (3x claim / 5x automatic), 50/75-move rules
  - Dead position (insufficient material) check
  - Checkmate/stalemate detection
  - "Play" wrappers using coordinates and perft
  - Examples
  - OCaml extraction of a practical API

  The development is axiom-free.
*)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope nat_scope.
Open Scope Z_scope.

(* ---------- Core types & equality helpers ---------- *)

Inductive Color := White | Black.

Definition opposite_color (c:Color) : Color :=
  match c with White => Black | Black => White end.

Definition color_eqb (a b:Color) : bool :=
  match a,b with White,White => true | Black,Black => true | _,_ => false end.

Lemma color_eqb_refl : forall c, color_eqb c c = true.
Proof. intro c; destruct c; reflexivity. Qed.

Inductive PieceType := Pawn | Knight | Bishop | Rook | Queen | King.

Definition ptype_eqb (a b:PieceType) : bool :=
  match a,b with
  | Pawn,Pawn | Knight,Knight | Bishop,Bishop | Rook,Rook | Queen,Queen | King,King => true
  | _,_ => false
  end.

Lemma ptype_eqb_refl : forall k, ptype_eqb k k = true.
Proof. intro k; destruct k; reflexivity. Qed.

Record Piece := { pc_color : Color; pc_type : PieceType }.

Definition piece_eqb (x y:Piece) : bool :=
  color_eqb x.(pc_color) y.(pc_color) && ptype_eqb x.(pc_type) y.(pc_type).

Lemma piece_eqb_refl : forall p, piece_eqb p p = true.
Proof. intro p. unfold piece_eqb. now rewrite color_eqb_refl, ptype_eqb_refl. Qed.

Record Position := { rank : nat; file : nat }.

Definition pos (r f:nat) : Position := {| rank := r; file := f |}.

Definition position_eqb (a b:Position) : bool :=
  Nat.eqb a.(rank) b.(rank) && Nat.eqb a.(file) b.(file).

Lemma position_eqb_refl : forall p, position_eqb p p = true.
Proof. intro p. unfold position_eqb. now rewrite !Nat.eqb_refl. Qed.

(* Optional decidable equality for Position *)
Definition position_eq_dec (p q : Position) : {p = q} + {p <> q}.
Proof.
  destruct p as [r1 f1], q as [r2 f2].
  destruct (Nat.eq_dec r1 r2) as [Hr|Hr].
  - destruct (Nat.eq_dec f1 f2) as [Hf|Hf].
    + left. subst. reflexivity.
    + right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
Qed.

(* ---------- Board & coordinates ---------- *)

Definition in_bounds (p:Position) : bool :=
  Nat.ltb p.(rank) 8 && Nat.ltb p.(file) 8.

Definition pos_of_Z (r f:Z) : option Position :=
  if (0 <=? r) && (r <? 8) && (0 <=? f) && (f <? 8)
  then Some (pos (Z.to_nat r) (Z.to_nat f)) else None.

Definition offset (p:Position) (dr df:Z) : option Position :=
  pos_of_Z (Z.of_nat p.(rank) + dr) (Z.of_nat p.(file) + df).

Fixpoint range (n:nat) : list nat :=
  match n with O => [] | S k => range k ++ [k] end.

Definition all_positions : list Position :=
  flat_map (fun r => map (fun f => pos r f) (range 8)) (range 8).

Definition light_square (p:Position) : bool :=
  Nat.even (p.(rank) + p.(file)).

(* ---------- Board representation ---------- *)

Definition Board := Position -> option Piece.

Definition board_empty : Board := fun _ => None.
Definition board_get (b:Board) (p:Position) : option Piece := b p.
Definition board_set (b:Board) (p:Position) (x:option Piece) : Board :=
  fun q => if position_eqb q p then x else b q.

Notation "b [ p ]" := (board_get b p) (at level 9).
Notation "b [ p := x ]" := (board_set b p x) (at level 9).

Definition occ (b:Board) (p:Position) : bool :=
  match b p with Some _ => true | None => false end.

Definition occ_color (b:Board) (p:Position) (c:Color) : bool :=
  match b p with Some q => color_eqb q.(pc_color) c | None => false end.

(* ---------- Initial position ---------- *)

Definition mkp (c:Color) (k:PieceType) : option Piece :=
  Some {| pc_color := c; pc_type := k |}.

Definition place_pawns (b:Board) (c:Color) : Board :=
  let r := match c with White => 1%nat | Black => 6%nat end in
  fold_left (fun bb f => bb [ pos r f := mkp c Pawn ]) (range 8) b.

Definition place_backrank (b:Board) (c:Color) : Board :=
  let r := match c with White => 0%nat | Black => 7%nat end in
  let b := b [ pos r 0 := mkp c Rook ] in
  let b := b [ pos r 1 := mkp c Knight ] in
  let b := b [ pos r 2 := mkp c Bishop ] in
  let b := b [ pos r 3 := mkp c Queen ] in
  let b := b [ pos r 4 := mkp c King ] in
  let b := b [ pos r 5 := mkp c Bishop ] in
  let b := b [ pos r 6 := mkp c Knight ] in
  let b := b [ pos r 7 := mkp c Rook ] in
  b.

Definition initial_board : Board :=
  let b := board_empty in
  let b := place_backrank b White in
  let b := place_backrank b Black in
  let b := place_pawns b White in
  let b := place_pawns b Black in
  b.

(* ---------- Game state ---------- *)

Record CastleRights := { wks:bool; wqs:bool; bks:bool; bqs:bool }.

Definition cr_eqb (a b:CastleRights) : bool :=
  Bool.eqb a.(wks) b.(wks) && Bool.eqb a.(wqs) b.(wqs) &&
  Bool.eqb a.(bks) b.(bks) && Bool.eqb a.(bqs) b.(bqs).

Record GameState := {
  current_board : Board;
  current_turn  : Color;
  current_cast  : CastleRights;
  en_passant_target : option Position;
  halfmove_clock : nat;
  fullmove_number : nat
}.

Definition initial_castle : CastleRights :=
  {| wks := true; wqs := true; bks := true; bqs := true |}.

Definition initial_game_state : GameState :=
  {| current_board := initial_board;
     current_turn := White;
     current_cast := initial_castle;
     en_passant_target := None;
     halfmove_clock := 0;
     fullmove_number := 1 |}.

Definition forward (c:Color) : Z := match c with White => 1 | Black => -1 end.
Definition start_rank (c:Color) : nat := match c with White => 1 | Black => 6 end.
Definition back_rank  (c:Color) : nat := match c with White => 0 | Black => 7 end.
Definition last_rank  (c:Color) : nat := match c with White => 7 | Black => 0 end.

(* ---------- Attack detection ---------- *)

Fixpoint first_piece_on_ray (b:Board) (s:Position) (dr df:Z) (k:nat)
  : option (Position * Piece) :=
  match k with
  | O => None
  | S k' =>
    match offset s dr df with
    | None => None
    | Some s1 =>
        match b s1 with
        | Some p => Some (s1,p)
        | None => first_piece_on_ray b s1 dr df k'
        end
    end
  end.

Fixpoint collect_ray (b:Board) (c:Color) (s:Position) (dr df:Z) (k:nat)
  : list Position :=
  match k with
  | O => []
  | S k' =>
    match offset s dr df with
    | None => []
    | Some s1 =>
        match b s1 with
        | None => s1 :: collect_ray b c s1 dr df k'
        | Some p => if color_eqb p.(pc_color) c then [] else [s1]
        end
    end
  end.

Definition knight_offsets : list (Z*Z) :=
  [(1,2);(2,1);(2,-1);(1,-2);(-1,-2);(-2,-1);(-2,1);(-1,2)]%Z.
Definition king_offsets : list (Z*Z) :=
  [(1,1);(1,0);(1,-1);(0,1);(0,-1);(-1,1);(-1,0);(-1,-1)]%Z.
Definition rook_dirs   : list (Z*Z) := [(1,0);(-1,0);(0,1);(0,-1)]%Z.
Definition bishop_dirs : list (Z*Z) := [(1,1);(1,-1);(-1,1);(-1,-1)]%Z.
Definition queen_dirs  : list (Z*Z) := rook_dirs ++ bishop_dirs.

Definition attacks (b:Board) (c:Color) (t:Position) : bool :=
  let pawn_hit :=
    let r := t.(rank) in
    let f := t.(file) in
    match c with
    | White =>
        let s1 := pos_of_Z (Z.of_nat r - 1) (Z.of_nat f - 1) in
        let s2 := pos_of_Z (Z.of_nat r - 1) (Z.of_nat f + 1) in
        existsb (fun so =>
          match so with
          | Some s =>
              match b s with
              | Some p => color_eqb p.(pc_color) White && ptype_eqb p.(pc_type) Pawn
              | None => false
              end
          | None => false
          end) (s1 :: s2 :: nil)
    | Black =>
        let s1 := pos_of_Z (Z.of_nat r + 1) (Z.of_nat f - 1) in
        let s2 := pos_of_Z (Z.of_nat r + 1) (Z.of_nat f + 1) in
        existsb (fun so =>
          match so with
          | Some s =>
              match b s with
              | Some p => color_eqb p.(pc_color) Black && ptype_eqb p.(pc_type) Pawn
              | None => false
              end
          | None => false
          end) (s1 :: s2 :: nil)
    end in
  let knight_hit :=
    existsb (fun od =>
      let dr := fst od in let df := snd od in
      match offset t (-dr) (-df) with
      | Some s =>
          match b s with
          | Some p => color_eqb p.(pc_color) c && ptype_eqb p.(pc_type) Knight
          | None => false
          end
      | None => false
      end) knight_offsets in
  let king_hit :=
    existsb (fun od =>
      let dr := fst od in let df := snd od in
      match offset t (-dr) (-df) with
      | Some s =>
          match b s with
          | Some p => color_eqb p.(pc_color) c && ptype_eqb p.(pc_type) King
          | None => false
          end
      | None => false
      end) king_offsets in
  let slider_hit dirs ok :=
    existsb (fun od =>
      let dr := fst od in let df := snd od in
      match first_piece_on_ray b t (-dr) (-df) 7 with
      | Some (s,p) => color_eqb p.(pc_color) c && ok p.(pc_type)
      | None => false
      end) dirs in
  let rook_like   := slider_hit rook_dirs   (fun k => ptype_eqb k Rook   || ptype_eqb k Queen) in
  let bishop_like := slider_hit bishop_dirs (fun k => ptype_eqb k Bishop || ptype_eqb k Queen) in
  pawn_hit || knight_hit || king_hit || rook_like || bishop_like.

Fixpoint find_king_aux (b:Board) (c:Color) (ls:list Position) : option Position :=
  match ls with
  | [] => None
  | p::tl =>
      match b p with
      | Some q =>
          if color_eqb q.(pc_color) c && ptype_eqb q.(pc_type) King
          then Some p else find_king_aux b c tl
      | None => find_king_aux b c tl
      end
  end.

Definition find_king (b:Board) (c:Color) : option Position :=
  find_king_aux b c all_positions.

Definition in_check (st:GameState) (c:Color) : bool :=
  match find_king st.(current_board) c with
  | None => false
  | Some k => attacks st.(current_board) (opposite_color c) k
  end.

(* ---------- Moves & generation ---------- *)

Inductive CastleSide := KingSide | QueenSide.

Inductive Move :=
| MNormal (src dst:Position) (promo:option PieceType)
| MCastle (side:CastleSide).

Definition move_eqb (m1 m2:Move) : bool :=
  match m1, m2 with
  | MCastle KingSide,  MCastle KingSide  => true
  | MCastle QueenSide, MCastle QueenSide => true
  | MNormal s1 d1 p1, MNormal s2 d2 p2 =>
      position_eqb s1 s2 && position_eqb d1 d2 &&
      match p1,p2 with
      | None,None => true
      | Some k1, Some k2 => ptype_eqb k1 k2
      | _,_ => false
      end
  | _,_ => false
  end.

(* Destination guard: own piece forbidden, capturing *king* forbidden *)
Definition guard_dest (b:Board) (c:Color) (d:Position) : bool :=
  match b d with
  | None => true
  | Some q => negb (color_eqb q.(pc_color) c) && negb (ptype_eqb q.(pc_type) King)
  end.

Fixpoint gen_offsets (b:Board) (c:Color) (src:Position) (ofs:list (Z*Z)) : list Move :=
  match ofs with
  | [] => []
  | (dr,df)::tl =>
      let here :=
        match offset src dr df with
        | Some d => if guard_dest b c d then [MNormal src d None] else []
        | None => []
        end in
      here ++ gen_offsets b c src tl
  end.

Fixpoint gen_sliding (b:Board) (c:Color) (src:Position) (dirs:list (Z*Z)) (k:nat)
  : list Move :=
  match dirs with
  | [] => []
  | (dr,df)::tl =>
      let ray := collect_ray b c src dr df k in
      let here := map (fun d => MNormal src d None) ray in
      here ++ gen_sliding b c src tl k
  end.

Definition promo_kinds : list PieceType := [Queen;Rook;Bishop;Knight].

Definition gen_pawn (st:GameState) (c:Color) (src:Position) : list Move :=
  let b := st.(current_board) in
  let f := forward c in
  let last := last_rank c in
  let single :=
    match offset src f 0 with
    | Some d =>
        if occ b d then []
        else if Nat.eqb d.(rank) last
             then map (fun k => MNormal src d (Some k)) promo_kinds
             else [MNormal src d None]
    | None => []
    end in
  let double :=
    if Nat.eqb src.(rank) (start_rank c) then
      match offset src f 0, offset src (2*f) 0 with
      | Some d1, Some d2 =>
          if occ b d1 || occ b d2 then [] else [MNormal src d2 None]
      | _,_ => []
      end
    else [] in
  let cap_one (df:Z) : list Move :=
    match offset src f df with
    | Some d =>
        match b d with
        | Some p =>
            if color_eqb p.(pc_color) (opposite_color c) && negb (ptype_eqb p.(pc_type) King)
            then if Nat.eqb d.(rank) last
                 then map (fun k => MNormal src d (Some k)) promo_kinds
                 else [MNormal src d None]
            else []
        | None =>
            match st.(en_passant_target) with
            | Some ep => if position_eqb d ep then [MNormal src d None] else []
            | None => []
            end
        end
    | None => []
    end in
  single ++ double ++ cap_one (-1) ++ cap_one 1.

Definition gen_piece_moves (st:GameState) (src:Position) (p:Piece) : list Move :=
  let b := st.(current_board) in
  let c := p.(pc_color) in
  match p.(pc_type) with
  | Pawn   => gen_pawn st c src
  | Knight => gen_offsets b c src knight_offsets
  | Bishop => gen_sliding b c src bishop_dirs 7
  | Rook   => gen_sliding b c src rook_dirs 7
  | Queen  => gen_sliding b c src queen_dirs 7
  | King   => gen_offsets b c src king_offsets
  end.

(* ---------- Castling ---------- *)

Definition king_start   (c:Color) : Position := pos (back_rank c) 4.
Definition rook_start_k (c:Color) : Position := pos (back_rank c) 7.
Definition rook_start_q (c:Color) : Position := pos (back_rank c) 0.
Definition king_castle_dst (c:Color) (side:CastleSide) : Position :=
  match side with KingSide => pos (back_rank c) 6 | QueenSide => pos (back_rank c) 2 end.
Definition rook_castle_dst (c:Color) (side:CastleSide) : Position :=
  match side with KingSide => pos (back_rank c) 5 | QueenSide => pos (back_rank c) 3 end.

Definition side_right (cr:CastleRights) (c:Color) (side:CastleSide) : bool :=
  match c, side with
  | White,KingSide => cr.(wks) | White,QueenSide => cr.(wqs)
  | Black,KingSide => cr.(bks) | Black,QueenSide => cr.(bqs)
  end.

Definition can_castle (st:GameState) (c:Color) (side:CastleSide) : bool :=
  let b := st.(current_board) in
  let ks := king_start c in
  let rs := match side with KingSide => rook_start_k c | QueenSide => rook_start_q c end in
  let kd := king_castle_dst c side in
  let mid1 := match side with KingSide => offset ks 0 1 | QueenSide => offset ks 0 (-1) end in
  andb
  (side_right st.(current_cast) c side)
  (andb
    (match b ks, b rs with
     | Some pk, Some pr =>
         color_eqb pk.(pc_color) c && ptype_eqb pk.(pc_type) King &&
         color_eqb pr.(pc_color) c && ptype_eqb pr.(pc_type) Rook
     | _,_ => false
     end)
    (andb
      (match side with
       | KingSide =>
           match offset ks 0 1, offset ks 0 2 with
           | Some s1, Some s2 => negb (occ b s1) && negb (occ b s2)
           | _,_ => false
           end
       | QueenSide =>
           match offset ks 0 (-1), offset ks 0 (-2), offset ks 0 (-3) with
           | Some d1, Some c1, Some b1 =>
               negb (occ b d1) && negb (occ b c1) && negb (occ b b1)
           | _,_,_ => false
           end
       end)
      (andb
        (negb (in_check st c))
        (andb
          (match mid1 with Some s1 => negb (attacks b (opposite_color c) s1) | None => false end)
          (negb (attacks b (opposite_color c) kd)))))).

Definition gen_castles (st:GameState) : list Move :=
  let c := st.(current_turn) in
  let add side := if can_castle st c side then [MCastle side] else [] in
  add KingSide ++ add QueenSide.

(* ---------- Pseudo-legal membership gate ---------- *)

Definition pseudo_ok (st:GameState) (src dst:Position) (promo:option PieceType) : bool :=
  match st.(current_board) src with
  | Some p => existsb (move_eqb (MNormal src dst promo)) (gen_piece_moves st src p)
  | None => false
  end.

(* ---------- apply_move (geometry enforced + no self-check) ---------- *)

Definition is_promo_kind (k:PieceType) : bool :=
  match k with Queen | Rook | Bishop | Knight => true | _ => false end.

Definition disable_side_cr (cr:CastleRights) (c:Color) : CastleRights :=
  match c with
  | White => {| wks := false; wqs := false; bks := cr.(bks); bqs := cr.(bqs) |}
  | Black => {| wks := cr.(wks); wqs := cr.(wqs); bks := false; bqs := false |}
  end.

Definition disable_rook_from (cr:CastleRights) (c:Color) (r0:Position) : CastleRights :=
  match c with
  | White =>
      if position_eqb r0 (rook_start_k White)
      then {| wks := false; wqs := cr.(wqs); bks := cr.(bks); bqs := cr.(bqs) |}
      else if position_eqb r0 (rook_start_q White)
      then {| wks := cr.(wks); wqs := false; bks := cr.(bks); bqs := cr.(bqs) |}
      else cr
  | Black =>
      if position_eqb r0 (rook_start_k Black)
      then {| wks := cr.(wks); wqs := cr.(wqs); bks := false; bqs := cr.(bqs) |}
      else if position_eqb r0 (rook_start_q Black)
      then {| wks := cr.(wks); wqs := cr.(wqs); bks := cr.(bks); bqs := false |}
      else cr
  end.

Definition disable_rook_if_captured (cr:CastleRights) (victim:Color) (dst:Position) : CastleRights :=
  match victim with
  | White =>
      if position_eqb dst (rook_start_k White)
      then {| wks := false; wqs := cr.(wqs); bks := cr.(bks); bqs := cr.(bqs) |}
      else if position_eqb dst (rook_start_q White)
      then {| wks := cr.(wks); wqs := false; bks := cr.(bks); bqs := cr.(bqs) |}
      else cr
  | Black =>
      if position_eqb dst (rook_start_k Black)
      then {| wks := cr.(wks); wqs := cr.(wqs); bks := false; bqs := cr.(bqs) |}
      else if position_eqb dst (rook_start_q Black)
      then {| wks := cr.(wks); wqs := cr.(wqs); bks := cr.(bks); bqs := false |}
      else cr
  end.

Definition apply_move (st:GameState) (m:Move) : option GameState :=
  let b := st.(current_board) in
  let c := st.(current_turn) in
  let bump_full (c:Color) (f:nat) := match c with Black => S f | White => f end in
  match m with
  | MCastle side =>
      if can_castle st c side then
        let ks := king_start c in
        let kd := king_castle_dst c side in
        let rs := match side with KingSide => rook_start_k c | QueenSide => rook_start_q c end in
        let rd := rook_castle_dst c side in
        let b1 := b  [ ks := None ] in
        let b2 := b1 [ rs := None ] in
        let b3 := b2 [ kd := mkp c King ] in
        let b4 := b3 [ rd := mkp c Rook ] in
        let st' := {|
          current_board := b4;
          current_turn := opposite_color c;
          current_cast := disable_side_cr st.(current_cast) c;
          en_passant_target := None;
          halfmove_clock := S st.(halfmove_clock);
          fullmove_number := bump_full c st.(fullmove_number)
        |} in
        if in_check st' (opposite_color st'.(current_turn)) then None else Some st'
      else None
  | MNormal src dst promo =>
      match b src with
      | None => None
      | Some p =>
          if negb (color_eqb p.(pc_color) c) then None else
          if negb (pseudo_ok st src dst promo) then None else
          let is_pawn := ptype_eqb p.(pc_type) Pawn in
          let is_two_step :=
            is_pawn && Nat.eqb src.(rank) (start_rank c) &&
            match offset src (forward c) 0, offset src (2*forward c) 0 with
            | Some d1, Some d2 => position_eqb d2 dst && negb (occ b d1) && negb (occ b d2)
            | _,_ => false
            end in
          let dx := (Z.of_nat dst.(file)) - (Z.of_nat src.(file)) in
          let dy := (Z.of_nat dst.(rank)) - (Z.of_nat src.(rank)) in
          let is_diag := ((Z.abs dx =? 1) && (dy =? forward c))%bool in
          let ep_capture :=
            is_pawn && is_diag &&
            match st.(en_passant_target) with
            | Some ep => position_eqb dst ep
            | None => false
            end in
          let cap_square :=
            if ep_capture
            then match offset dst (- forward c) 0 with Some s => Some s | None => None end
            else Some dst in
          let promo_ok :=
            if is_pawn && Nat.eqb dst.(rank) (last_rank c)
            then match promo with Some k => is_promo_kind k | None => false end
            else match promo with Some _ => false | None => true end in
          if negb promo_ok then None else
          let capturing :=
            match cap_square with
            | Some cs =>
                if position_eqb cs dst
                then occ_color b cs (opposite_color c)
                else match b cs with
                     | Some q => color_eqb q.(pc_color) (opposite_color c) && ptype_eqb q.(pc_type) Pawn
                     | None => false
                     end
            | None => false
            end in
          let dst_ok :=
            if ep_capture then negb (occ b dst)
            else match b dst with None => true | Some _ => capturing end in
          if negb dst_ok then None else
          let b1 := b [ src := None ] in
          let b2 :=
            match cap_square with
            | Some cs => if capturing then b1 [ cs := None ] else b1
            | None => b1
            end in
          let moved_piece :=
            match promo, p.(pc_type) with
            | Some k, Pawn => {| pc_color := c; pc_type := k |}
            | _, _ => p
            end in
          let b3 := b2 [ dst := Some moved_piece ] in
          let cr1 :=
            match p.(pc_type) with
            | King => disable_side_cr st.(current_cast) c
            | Rook => disable_rook_from st.(current_cast) c src
            | _ => st.(current_cast)
            end in
          let cr2 := if capturing
                     then disable_rook_if_captured cr1 (opposite_color c)
                            (match cap_square with Some cs => cs | None => dst end)
                     else cr1 in
          let new_ep := if is_two_step then offset src (forward c) 0 else None in
          let new_hmc := if is_pawn || capturing then 0%nat else S st.(halfmove_clock) in
          let st' := {|
            current_board := b3;
            current_turn := opposite_color c;
            current_cast := cr2;
            en_passant_target := new_ep;
            halfmove_clock := new_hmc;
            fullmove_number := bump_full c st.(fullmove_number)
          |} in
          if in_check st' (opposite_color st'.(current_turn)) then None else Some st'
      end
  end.

(* ---------- Legal move list ---------- *)

Definition gen_pseudo (st:GameState) : list Move :=
  let b := st.(current_board) in
  let c := st.(current_turn) in
  let per (p:Position) : list Move :=
    match b p with
    | Some q => if color_eqb q.(pc_color) c then gen_piece_moves st p q else []
    | None => []
    end in
  flat_map per all_positions ++ gen_castles st.

Fixpoint filter_legal (st:GameState) (ms:list Move) : list Move :=
  match ms with
  | [] => []
  | m::tl =>
      match apply_move st m with
      | Some _ => m :: filter_legal st tl
      | None => filter_legal st tl
      end
  end.

Definition generate_legal_moves (st:GameState) : list Move :=
  filter_legal st (gen_pseudo st).

(* ---------- Repetition keys & EP relevance ---------- *)

Record PosKey := {
  pk_turn : Color;
  pk_cast : CastleRights;
  pk_ep   : option Position;
  pk_occ  : list (Position * Piece)
}.

Definition pair_eqb (a b:Position * Piece) : bool :=
  position_eqb (fst a) (fst b) && piece_eqb (snd a) (snd b).

Fixpoint list_eqb {A} (eqbA:A -> A -> bool) (xs ys:list A) : bool :=
  match xs,ys with
  | [],[] => true
  | x::xt, y::yt => eqbA x y && list_eqb eqbA xt yt
  | _,_ => false
  end.

Definition poskey_eqb (a b:PosKey) : bool :=
  color_eqb a.(pk_turn) b.(pk_turn) &&
  cr_eqb a.(pk_cast) b.(pk_cast) &&
  match a.(pk_ep), b.(pk_ep) with
  | None,None => true
  | Some x, Some y => position_eqb x y
  | _,_ => false
  end &&
  list_eqb pair_eqb a.(pk_occ) b.(pk_occ).

Fixpoint collect_occ (b:Board) (ls:list Position) : list (Position * Piece) :=
  match ls with
  | [] => []
  | p::tl =>
      match b p with
      | Some q => (p,q) :: collect_occ b tl
      | None => collect_occ b tl
      end
  end.

(* EP is relevant for repetition only if capturable from side to move *)
Definition ep_relevant (st:GameState) : option Position :=
  match st.(en_passant_target) with
  | None => None
  | Some ep =>
      let c := st.(current_turn) in
      let src_left  := offset ep (- forward c) (-1) in
      let src_right := offset ep (- forward c) ( 1) in
      let exists_ep_from (so:option Position) :=
        match so with
        | Some s =>
            match st.(current_board) s with
            | Some p => color_eqb p.(pc_color) c && ptype_eqb p.(pc_type) Pawn
            | None => false
            end
        | None => false
        end in
      if exists_ep_from src_left || exists_ep_from src_right then Some ep else None
  end.

Definition make_poskey (st:GameState) : PosKey :=
  {| pk_turn := st.(current_turn);
     pk_cast := st.(current_cast);
     pk_ep   := ep_relevant st;
     pk_occ  := collect_occ st.(current_board) all_positions |}.

Fixpoint count_pos (k:PosKey) (xs:list PosKey) : nat :=
  match xs with [] => 0 | x::tl => if poskey_eqb k x then S (count_pos k tl) else count_pos k tl end.

(* ---------- Game wrapper ---------- *)

Record Game := { g_cur : GameState; g_hist : list PosKey }.

Definition initial_game : Game :=
  {| g_cur := initial_game_state; g_hist := [make_poskey initial_game_state] |}.

Definition game_apply (g:Game) (m:Move) : option Game :=
  match apply_move g.(g_cur) m with
  | None => None
  | Some st' =>
      let k' := make_poskey st' in
      Some {| g_cur := st'; g_hist := k' :: g.(g_hist) |}
  end.

(* ---------- Draws & outcomes ---------- *)

Inductive GameResult :=
| Ongoing | Checkmate (loser:Color) | Stalemate (side:Color)
| DrawByDeadPosition | DrawByFiftyMoveClaim | DrawBySeventyFiveAutomatic
| DrawByThreefoldClaim | DrawByFivefoldAutomatic.

Definition threefold_claimable (g:Game) : bool :=
  Nat.leb 3 (count_pos (make_poskey g.(g_cur)) g.(g_hist)).

Definition fivefold_automatic (g:Game) : bool :=
  Nat.leb 5 (count_pos (make_poskey g.(g_cur)) g.(g_hist)).

Definition fifty_move_claimable (g:Game) : bool :=
  Nat.leb 100 g.(g_cur).(halfmove_clock).

Definition seventyfive_automatic (g:Game) : bool :=
  Nat.leb 150 g.(g_cur).(halfmove_clock).

(* ---------- Insufficient material (dead positions) ---------- *)

Record MatSummary := {
  wP:nat; wN:nat; wB:nat; wR:nat; wQ:nat;
  bP:nat; bN:nat; bB:nat; bR:nat; bQ:nat;
  wB_sq: list Position; bB_sq: list Position
}.

Definition ms_empty : MatSummary :=
  {| wP:=0; wN:=0; wB:=0; wR:=0; wQ:=0;
     bP:=0; bN:=0; bB:=0; bR:=0; bQ:=0;
     wB_sq := []; bB_sq := [] |}.

Fixpoint summarize_material (b:Board) (ls:list Position) (acc:MatSummary) : MatSummary :=
  match ls with
  | [] => acc
  | p::tl =>
      match b p with
      | None => summarize_material b tl acc
      | Some q =>
          let acc' :=
            match q.(pc_color), q.(pc_type) with
            | White,Pawn   => {| wP := S acc.(wP); wN := acc.(wN); wB := acc.(wB); wR := acc.(wR); wQ := acc.(wQ);
                                 bP := acc.(bP); bN := acc.(bN); bB := acc.(bB); bR := acc.(bR); bQ := acc.(bQ);
                                 wB_sq := acc.(wB_sq); bB_sq := acc.(bB_sq) |}
            | White,Knight => {| wP := acc.(wP); wN := S acc.(wN); wB := acc.(wB); wR := acc.(wR); wQ := acc.(wQ);
                                 bP := acc.(bP); bN := acc.(bN); bB := acc.(bB); bR := acc.(bR); bQ := acc.(bQ);
                                 wB_sq := acc.(wB_sq); bB_sq := acc.(bB_sq) |}
            | White,Bishop => {| wP := acc.(wP); wN := acc.(wN); wB := S acc.(wB); wR := acc.(wR); wQ := acc.(wQ);
                                 bP := acc.(bP); bN := acc.(bN); bB := acc.(bB); bR := acc.(bR); bQ := acc.(bQ);
                                 wB_sq := p :: acc.(wB_sq); bB_sq := acc.(bB_sq) |}
            | White,Rook   => {| wP := acc.(wP); wN := acc.(wN); wB := acc.(wB); wR := S acc.(wR); wQ := acc.(wQ);
                                 bP := acc.(bP); bN := acc.(bN); bB := acc.(bB); bR := acc.(bR); bQ := acc.(bQ);
                                 wB_sq := acc.(wB_sq); bB_sq := acc.(bB_sq) |}
            | White,Queen  => {| wP := acc.(wP); wN := acc.(wN); wB := acc.(wB); wR := acc.(wR); wQ := S acc.(wQ);
                                 bP := acc.(bP); bN := acc.(bN); bB := acc.(bB); bR := acc.(bR); bQ := acc.(bQ);
                                 wB_sq := acc.(wB_sq); bB_sq := acc.(bB_sq) |}
            | Black,Pawn   => {| wP := acc.(wP); wN := acc.(wN); wB := acc.(wB); wR := acc.(wR); wQ := acc.(wQ);
                                 bP := S acc.(bP); bN := acc.(bN); bB := acc.(bB); bR := acc.(bR); bQ := acc.(bQ);
                                 wB_sq := acc.(wB_sq); bB_sq := acc.(bB_sq) |}
            | Black,Knight => {| wP := acc.(wP); wN := acc.(wN); wB := acc.(wB); wR := acc.(wR); wQ := acc.(wQ);
                                 bP := acc.(bP); bN := S acc.(bN); bB := acc.(bB); bR := acc.(bR); bQ := acc.(bQ);
                                 wB_sq := acc.(wB_sq); bB_sq := acc.(bB_sq) |}
            | Black,Bishop => {| wP := acc.(wP); wN := acc.(wN); wB := acc.(wB); wR := acc.(wR); wQ := acc.(wQ);
                                 bP := acc.(bP); bN := acc.(bN); bB := S acc.(bB); bR := acc.(bR); bQ := acc.(bQ);
                                 wB_sq := acc.(wB_sq); bB_sq := p :: acc.(bB_sq) |}
            | Black,Rook   => {| wP := acc.(wP); wN := acc.(wN); wB := acc.(wB); wR := acc.(wR); wQ := acc.(wQ);
                                 bP := acc.(bP); bN := acc.(bN); bB := acc.(bB); bR := S acc.(bR); bQ := acc.(bQ);
                                 wB_sq := acc.(wB_sq); bB_sq := acc.(bB_sq) |}
            | Black,Queen  => {| wP := acc.(wP); wN := acc.(wN); wB := acc.(wB); wR := acc.(wR); wQ := acc.(wQ);
                                 bP := acc.(bP); bN := acc.(bN); bB := acc.(bB); bR := acc.(bR); bQ := S acc.(bQ);
                                 wB_sq := acc.(wB_sq); bB_sq := acc.(bB_sq) |}
            | _,King => acc
            end in
          summarize_material b tl acc'
      end
  end.

Definition bishops_all_same_color (ls:list Position) : bool :=
  match ls with
  | [] => true
  | s0::tl =>
      let c0 := light_square s0 in
      forallb (fun s => Bool.eqb (light_square s) c0) tl
  end.

Definition dead_position_simple (st:GameState) : bool :=
  let m := summarize_material st.(current_board) all_positions ms_empty in
  let no_heavy :=
    Nat.eqb m.(wP) 0 && Nat.eqb m.(bP) 0 &&
    Nat.eqb m.(wR) 0 && Nat.eqb m.(bR) 0 &&
    Nat.eqb m.(wQ) 0 && Nat.eqb m.(bQ) 0 in
  if negb no_heavy then false else
  let w_minor := (m.(wN) + m.(wB))%nat in
  let b_minor := (m.(bN) + m.(bB))%nat in
  match w_minor, b_minor with
  | O, O => true
  | S O, O => Nat.eqb m.(wN) 1 || Nat.eqb m.(wB) 1
  | O, S O => Nat.eqb m.(bN) 1 || Nat.eqb m.(bB) 1
  | S O, S O =>
      Nat.eqb m.(wN) 0 && Nat.eqb m.(bN) 0 &&
      bishops_all_same_color m.(wB_sq) &&
      bishops_all_same_color m.(bB_sq) &&
      match m.(wB_sq), m.(bB_sq) with
      | [sw], [sb] => Bool.eqb (light_square sw) (light_square sb)
      | _,_ => false
      end
  | _,_ => false
  end.

(* ---------- Outcome & convenience ---------- *)

Definition game_outcome (g:Game) : GameResult :=
  if fivefold_automatic g then DrawByFivefoldAutomatic else
  if seventyfive_automatic g then DrawBySeventyFiveAutomatic else
  if dead_position_simple g.(g_cur) then DrawByDeadPosition else
  if threefold_claimable g then DrawByThreefoldClaim else
  if fifty_move_claimable g then DrawByFiftyMoveClaim else
  let ms := generate_legal_moves g.(g_cur) in
  match ms with
  | _::_ => Ongoing
  | [] =>
      if in_check g.(g_cur) g.(g_cur).(current_turn)
      then Checkmate g.(g_cur).(current_turn)
      else Stalemate g.(g_cur).(current_turn)
  end.

Definition is_checkmate_state (st:GameState) : bool :=
  let ms := generate_legal_moves st in
  match ms with [] => in_check st st.(current_turn) | _ => false end.

Definition is_stalemate_state (st:GameState) : bool :=
  let ms := generate_legal_moves st in
  match ms with [] => negb (in_check st st.(current_turn)) | _ => false end.

Fixpoint play_moves (st:GameState) (moves:list Move) : option GameState :=
  match moves with
  | [] => Some st
  | m::tl =>
      match apply_move st m with
      | Some st' => play_moves st' tl
      | None => None
      end
  end.

(* ---------- “Play” helpers: coordinate wrappers & perft ---------- *)

(* Wrap a normal move in 0..7 coordinates (reject if out of bounds) *)
Definition mk_move_normal (r1 f1 r2 f2:nat) (promo:option PieceType) : option Move :=
  if (Nat.ltb r1 8 && Nat.ltb f1 8 && Nat.ltb r2 8 && Nat.ltb f2 8)%bool
  then Some (MNormal (pos r1 f1) (pos r2 f2) promo)
  else None.

(* List legal normal moves as coordinate 5-tuples: r1,f1,r2,f2, promo *)
Definition legal_normal_moves (st:GameState) : list (nat*nat*nat*nat*option PieceType) :=
  let ms := generate_legal_moves st in
  fold_right
    (fun m acc =>
       match m with
       | MNormal s d p => (rank s, file s, rank d, file d, p) :: acc
       | _ => acc
       end) nil ms.

(* List legal castles *)
Definition legal_castles (st:GameState) : list CastleSide :=
  let ms := generate_legal_moves st in
  fold_right
    (fun m acc => match m with MCastle side => side :: acc | _ => acc end)
    nil ms.

(* Apply a coordinate normal move, checking bounds; geometry & self-check are
   enforced inside apply_move via membership gate & filter logic. *)
Definition apply_move_normal_coords
  (st:GameState) (r1 f1 r2 f2:nat) (promo:option PieceType) : option GameState :=
  if (Nat.ltb r1 8 && Nat.ltb f1 8 && Nat.ltb r2 8 && Nat.ltb f2 8)%bool
  then apply_move st (MNormal (pos r1 f1) (pos r2 f2) promo)
  else None.

Definition apply_castle_side (st:GameState) (side:CastleSide) : option GameState :=
  apply_move st (MCastle side).

(* Perft for quick engine sanity checks *)
Fixpoint perft_state (st:GameState) (d:nat) : nat :=
  match d with
  | O => 1
  | S d' =>
      let ms := generate_legal_moves st in
      fold_left
        (fun acc m =>
           match apply_move st m with
           | Some st' => (acc + perft_state st' d')%nat
           | None => acc
           end) ms 0%nat
  end.

(* ---------- Examples ---------- *)

(* Scholar's Mate *)
Definition scholars_mate : list Move :=
  [ MNormal (pos 1 4) (pos 3 4) None;    (* 1. e4 *)
    MNormal (pos 6 4) (pos 4 4) None;    (* 1... e5 *)
    MNormal (pos 0 5) (pos 3 2) None;    (* 2. Bc4 *)
    MNormal (pos 7 1) (pos 5 2) None;    (* 2... Nc6 *)
    MNormal (pos 0 3) (pos 4 7) None;    (* 3. Qh5 *)
    MNormal (pos 7 6) (pos 5 5) None;    (* 3... Nf6?? *)
    MNormal (pos 4 7) (pos 6 5) None     (* 4. Qxf7# *)
  ].

Example scholars_mate_checkmate :
  match play_moves initial_game_state scholars_mate with
  | Some st => is_checkmate_state st = true
  | None => False
  end.
Proof. reflexivity. Qed.

(* Fool's Mate *)
Definition fools_mate : list Move :=
  [ MNormal (pos 1 5) (pos 2 5) None;    (* 1. f3 *)
    MNormal (pos 6 4) (pos 4 4) None;    (* 1... e5 *)
    MNormal (pos 1 6) (pos 3 6) None;    (* 2. g4?? *)
    MNormal (pos 7 3) (pos 3 7) None     (* 2... Qh4# *)
  ].

Example fools_mate_checkmate :
  match play_moves initial_game_state fools_mate with
  | Some st => is_checkmate_state st = true
  | None => False
  end.
Proof. reflexivity. Qed.

(* Simple castling example: 1.e4 e5 2.Nf3 Nc6 3.Bc4 Bc5 4.O-O is legal *)
Definition castle_kingside_white : list Move :=
  [ MNormal (pos 1 4) (pos 3 4) None;    (* 1. e4 *)
    MNormal (pos 6 4) (pos 4 4) None;    (* 1... e5 *)
    MNormal (pos 0 6) (pos 2 5) None;    (* 2. Nf3 *)
    MNormal (pos 7 1) (pos 5 2) None;    (* 2... Nc6 *)
    MNormal (pos 0 5) (pos 3 2) None;    (* 3. Bc4 *)
    MNormal (pos 7 5) (pos 4 2) None;    (* 3... Bc5 *)
    MCastle KingSide                     (* 4. O-O *)
  ].

Example castle_kingside_legal :
  match play_moves initial_game_state castle_kingside_white with
  | Some st =>
      st.(current_board) (pos 0 6) = Some {| pc_color := White; pc_type := King |} /\
      st.(current_board) (pos 0 5) = Some {| pc_color := White; pc_type := Rook |}
  | None => False
  end.
Proof. reflexivity. Qed.

(* En passant example: 1.e4 a6 2.e5 d5 3.exd6 e.p. *)
Definition en_passant_capture : list Move :=
  [ MNormal (pos 1 4) (pos 3 4) None;    (* 1. e4 *)
    MNormal (pos 6 0) (pos 5 0) None;    (* 1... a6 *)
    MNormal (pos 3 4) (pos 4 4) None;    (* 2. e5 *)
    MNormal (pos 6 3) (pos 4 3) None;    (* 2... d5 (two-step) *)
    MNormal (pos 4 4) (pos 5 3) None     (* 3. exd6 e.p. *)
  ].

Example en_passant_removes_pawn :
  match play_moves initial_game_state en_passant_capture with
  | Some st =>
      st.(current_board) (pos 4 3) = None /\
      st.(current_board) (pos 5 3) = Some {| pc_color := White; pc_type := Pawn |}
  | None => False
  end.
Proof. reflexivity. Qed.

(* ---------- Extraction ---------- *)

Extraction Language OCaml.
Extraction "chess_total"
  (* core types & helpers *)
  Color PieceType Piece Position CastleRights GameState Game Move GameResult
  (* state constructors *)
  initial_board initial_game_state initial_game
  (* move gen & application *)
  generate_legal_moves apply_move game_apply game_outcome
  is_checkmate_state is_stalemate_state
  (* repetition / draw rules *)
  threefold_claimable fivefold_automatic
  fifty_move_claimable seventyfive_automatic
  (* “play” wrappers *)
  mk_move_normal legal_normal_moves legal_castles
  apply_move_normal_coords apply_castle_side
  perft_state.
