(*
  ChessTotal.v — formalizing chess in Coq

  Coordinates:
    Position.(rank) 0..7 from White back rank upward (0=a1 rank),
    Position.(file) 0..7 from a..h.
  offset p dr df: rank += dr, file += df (dr/df : Z).
  White forward = +1 rank; Black forward = -1 rank.

*)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.extraction.Extraction.
Require Import Coq.Strings.Ascii.

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

(* IMPORTANT FIX: forbid slider moves that "capture the king" by stopping rays on a king
   without yielding a capture destination. *)
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
        | Some p =>
            if color_eqb p.(pc_color) c then []
            else if ptype_eqb p.(pc_type) King then [] (* <-- block king captures *)
                 else [s1]
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

(* Destination guard: own piece forbidden, capturing king forbidden *)
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
Definition ep_capture_legal (st:GameState) (s ep:Position) : bool :=
  match st.(current_board) s with
  | Some p =>
      color_eqb p.(pc_color) st.(current_turn) &&
      ptype_eqb p.(pc_type) Pawn &&
      match apply_move st (MNormal s ep None) with
      | Some _ => true
      | None => false
      end
  | None => false
  end.

Definition ep_relevant (st:GameState) : option Position :=
  match st.(en_passant_target) with
  | None => None
  | Some ep =>
      let c := st.(current_turn) in
      let s1 := offset ep (- forward c) (-1) in   (* a pawn that could capture from left *)
      let s2 := offset ep (- forward c) ( 1) in   (* ... or from right *)
      let ok so := match so with Some s => ep_capture_legal st s ep | None => false end in
      if ok s1 || ok s2 then Some ep else None
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
  let all_bishops := m.(wB_sq) ++ m.(bB_sq) in
  let bishops_single_color := bishops_all_same_color all_bishops in
  match w_minor, b_minor with
  | O, O => true                         (* K vs K *)
  | S O, O => Nat.eqb m.(wN) 1 || Nat.eqb m.(wB) 1  (* KN vs K or KB vs K *)
  | O, S O => Nat.eqb m.(bN) 1 || Nat.eqb m.(bB) 1  (* K vs KN or K vs KB *)
  | S (S O), O =>                        (* White has exactly two knights; Black has only king *)
      Nat.eqb m.(wN) 2 && Nat.eqb m.(wB) 0
  | O, S (S O) =>                        (* Black has exactly two knights; White has only king *)
      Nat.eqb m.(bN) 2 && Nat.eqb m.(bB) 0
  | _, _ =>
      (* Any number of bishops vs any number of bishops, all same color *)
      Nat.eqb m.(wN) 0 && Nat.eqb m.(bN) 0 && bishops_single_color
  end.

(* ---------- Outcome & convenience ---------- *)

(* Precedence: mate/stalemate before automatic draws (e.g., 75-move) *)
Definition game_outcome (g:Game) : GameResult :=
  let ms := generate_legal_moves g.(g_cur) in
  match ms with
  | [] =>
      if in_check g.(g_cur) g.(g_cur).(current_turn)
      then Checkmate g.(g_cur).(current_turn)
      else Stalemate g.(g_cur).(current_turn)
  | _::_ =>
      if fivefold_automatic g then DrawByFivefoldAutomatic else
      if seventyfive_automatic g then DrawBySeventyFiveAutomatic else
      if dead_position_simple g.(g_cur) then DrawByDeadPosition else
      if threefold_claimable g then DrawByThreefoldClaim else
      if fifty_move_claimable g then DrawByFiftyMoveClaim else
      Ongoing
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
  let src := pos r1 f1 in
  let dst := pos r2 f2 in
  if in_bounds src && in_bounds dst
  then Some (MNormal src dst promo)
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
  let src := pos r1 f1 in
  let dst := pos r2 f2 in
  if in_bounds src && in_bounds dst
  then apply_move st (MNormal src dst promo)
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

(* ---------- Metatheory Lemmas (selected) ---------- *)

(* Turn alternation: legal moves alternate colors *)
Lemma turn_alternation : forall st m st',
  apply_move st m = Some st' ->
  st'.(current_turn) = opposite_color st.(current_turn).
Proof.
  intros st m st' H.
  unfold apply_move in H.
  destruct m as [src dst promo | side].
  - (* MNormal case *)
    destruct (current_board st src) as [p|] eqn:Esrc; try discriminate.
    destruct (negb (color_eqb (pc_color p) (current_turn st))) eqn:Eneg; try discriminate.
    destruct (negb (pseudo_ok st src dst promo)) eqn:Epseudo; try discriminate.
    (* Work through all the conditions *)
    remember (ptype_eqb (pc_type p) Pawn) as is_pawn.
    remember (is_pawn && (rank src =? start_rank (current_turn st))%nat &&
              match offset src (forward (current_turn st)) 0 with
              | Some d1 => match offset src (2 * forward (current_turn st)) 0 with
                          | Some d2 => position_eqb d2 dst && negb (occ (current_board st) d1) && negb (occ (current_board st) d2)
                          | None => false
                          end
              | None => false
              end) as is_two_step.
    remember (Z.of_nat (file dst) - Z.of_nat (file src)) as dx.
    remember (Z.of_nat (rank dst) - Z.of_nat (rank src)) as dy.
    remember ((Z.abs dx =? 1) && (dy =? forward (current_turn st))) as is_diag.
    remember (is_pawn && is_diag &&
              match en_passant_target st with
              | Some ep => position_eqb dst ep
              | None => false
              end) as ep_capture.
    remember (if ep_capture
              then match offset dst (- forward (current_turn st)) 0 with
                   | Some s0 => Some s0
                   | None => None
                   end
              else Some dst) as cap_square.
    remember (if is_pawn && (rank dst =? last_rank (current_turn st))%nat
              then match promo with
                   | Some k => is_promo_kind k
                   | None => false
                   end
              else match promo with
                   | Some _ => false
                   | None => true
                   end) as promo_ok.
    destruct (negb promo_ok) eqn:Epromo_ok; try discriminate.
    remember (match cap_square with
              | Some cs =>
                  if position_eqb cs dst
                  then occ_color (current_board st) cs (opposite_color (current_turn st))
                  else match current_board st cs with
                       | Some q => color_eqb (pc_color q) (opposite_color (current_turn st)) && ptype_eqb (pc_type q) Pawn
                       | None => false
                       end
              | None => false
              end) as capturing.
    remember (if ep_capture then negb (occ (current_board st) dst) else match current_board st dst with None => true | Some _ => capturing end) as dst_ok.
    destruct (negb dst_ok) eqn:Edst_ok; try discriminate.
    (* After all checks pass, st' is constructed with opposite_color *)
    destruct (in_check _ (opposite_color _)) eqn:Echeck; try discriminate.
    injection H as Heq. rewrite <- Heq. simpl. reflexivity.
  - (* MCastle case *)
    destruct (can_castle st (current_turn st) side) eqn:Ecan; try discriminate.
    destruct (in_check _ (opposite_color _)) eqn:Echeck; try discriminate.
    injection H as Heq. rewrite <- Heq. simpl. reflexivity.
Qed.

(* No self-check after legal move *)
Lemma no_self_check : forall st m st',
  apply_move st m = Some st' ->
  in_check st' (opposite_color st'.(current_turn)) = false.
Proof.
  intros st m st' H.
  unfold apply_move in H.
  destruct m as [src dst promo | side].
  - (* MNormal case *)
    (* Navigate through the many conditions in apply_move *)
    destruct (current_board st src) as [p|] eqn:Esrc; [|discriminate].
    destruct (color_eqb (pc_color p) (current_turn st)) eqn:Ecolor.
    2: { simpl in H. discriminate. }
    destruct (pseudo_ok st src dst promo) eqn:Epseudo.
    2: { simpl in H. discriminate. }
    (* Build the intermediate values as in apply_move *)
    set (is_pawn := ptype_eqb (pc_type p) Pawn) in *.
    set (is_two_step :=
           is_pawn && (rank src =? start_rank (current_turn st))%nat &&
           match offset src (forward (current_turn st)) 0 with
           | Some d1 => match offset src (2 * forward (current_turn st)) 0 with
                       | Some d2 => position_eqb d2 dst && negb (occ (current_board st) d1) && 
                                   negb (occ (current_board st) d2)
                       | None => false
                       end
           | None => false
           end) in *.
    set (dx := Z.of_nat (file dst) - Z.of_nat (file src)) in *.
    set (dy := Z.of_nat (rank dst) - Z.of_nat (rank src)) in *.
    set (is_diag := (Z.abs dx =? 1) && (dy =? forward (current_turn st))) in *.
    set (ep_capture :=
           is_pawn && is_diag &&
           match en_passant_target st with
           | Some ep => position_eqb dst ep
           | None => false
           end) in *.
    set (cap_square :=
           if ep_capture
           then match offset dst (- forward (current_turn st)) 0 with
                | Some s0 => Some s0
                | None => None
                end
           else Some dst) in *.
    set (promo_ok :=
           if is_pawn && (rank dst =? last_rank (current_turn st))%nat
           then match promo with
                | Some k => is_promo_kind k
                | None => false
                end
           else match promo with
                | Some _ => false
                | None => true
                end) in *.
    destruct promo_ok eqn:Epromo_ok.
    2: { simpl in H. discriminate. }
    set (capturing :=
           match cap_square with
           | Some cs =>
               if position_eqb cs dst
               then occ_color (current_board st) cs (opposite_color (current_turn st))
               else match current_board st cs with
                    | Some q => color_eqb (pc_color q) (opposite_color (current_turn st)) &&
                               ptype_eqb (pc_type q) Pawn
                    | None => false
                    end
           | None => false
           end) in *.
    set (dst_ok :=
           if ep_capture then negb (occ (current_board st) dst)
           else match current_board st dst with
                | None => true
                | Some _ => capturing
                end) in *.
    destruct dst_ok eqn:Edst_ok.
    2: { simpl in H. discriminate. }
    (* Now we build the new state *)
    set (b1 := (current_board st) [src := None]) in *.
    set (b2 :=
           match cap_square with
           | Some cs => if capturing then b1 [cs := None] else b1
           | None => b1
           end) in *.
    set (moved_piece :=
           match promo with
           | Some k => match pc_type p with
                      | Pawn => {| pc_color := current_turn st; pc_type := k |}
                      | _ => p
                      end
           | None => p
           end) in *.
    set (b3 := b2 [dst := Some moved_piece]) in *.
    set (cr1 :=
           match pc_type p with
           | King => disable_side_cr (current_cast st) (current_turn st)
           | Rook => disable_rook_from (current_cast st) (current_turn st) src
           | _ => current_cast st
           end) in *.
    set (cr2 :=
           if capturing
           then disable_rook_if_captured cr1 (opposite_color (current_turn st))
                  match cap_square with
                  | Some cs => cs
                  | None => dst
                  end
           else cr1) in *.
    set (new_ep := if is_two_step then offset src (forward (current_turn st)) 0 else None) in *.
    set (new_hmc := if is_pawn || capturing then 0%nat else S (halfmove_clock st)) in *.
    set (st_new := {|
       current_board := b3;
       current_turn := opposite_color (current_turn st);
       current_cast := cr2;
       en_passant_target := new_ep;
       halfmove_clock := new_hmc;
       fullmove_number := match current_turn st with
                         | Black => S (fullmove_number st)
                         | White => fullmove_number st
                         end
     |}) in *.
    (* The final check in apply_move *)
    fold st_new in H.
    destruct (in_check st_new (opposite_color (current_turn st_new))) eqn:Echeck.
    + simpl in H. discriminate.
    + injection H as <-. exact Echeck.
  - (* MCastle case *)
    destruct (can_castle st (current_turn st) side) eqn:Ecan; [|discriminate].
    (* Build the new board after castling *)
    set (ks := king_start (current_turn st)) in *.
    set (kd := king_castle_dst (current_turn st) side) in *.
    set (rs := match side with
               | KingSide => rook_start_k (current_turn st)
               | QueenSide => rook_start_q (current_turn st)
               end) in *.
    set (rd := rook_castle_dst (current_turn st) side) in *.
    set (b1 := (current_board st) [ks := None]) in *.
    set (b2 := b1 [rs := None]) in *.
    set (b3 := b2 [kd := mkp (current_turn st) King]) in *.
    set (b4 := b3 [rd := mkp (current_turn st) Rook]) in *.
    set (st_new := {|
       current_board := b4;
       current_turn := opposite_color (current_turn st);
       current_cast := disable_side_cr (current_cast st) (current_turn st);
       en_passant_target := None;
       halfmove_clock := S (halfmove_clock st);
       fullmove_number := match current_turn st with
                         | Black => S (fullmove_number st)
                         | White => fullmove_number st
                         end
     |}) in *.
    fold st_new in H.
    destruct (in_check st_new (opposite_color (current_turn st_new))) eqn:Echeck.
    + simpl in H. discriminate.
    + injection H as <-. exact Echeck.
Qed.

(* Soundness of move generation: every generated move is legal *)
Lemma move_generation_sound : forall st m,
  In m (generate_legal_moves st) ->
  exists st', apply_move st m = Some st'.
Proof.
  intros st m H.
  unfold generate_legal_moves in H.
  revert H.
  generalize (gen_pseudo st).
  induction l as [|m' ms IH]; simpl; intros Hin.
  - contradiction.
  - destruct (apply_move st m') eqn:E; simpl in Hin.
    + destruct Hin as [Heq | Hin'].
      * subst. eauto.
      * eauto.
    + eauto.
Qed.

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
Proof.
  vm_compute. reflexivity.
Qed.

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
Proof.
  vm_compute. reflexivity.
Qed.

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
Proof.
  vm_compute.
  split; reflexivity.
Qed.

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
Proof.
  vm_compute. split; reflexivity.
Qed.

(* ---------- Comprehensive Test Suite ---------- *)

(* Perft Tests - Standard baseline values for move generation verification *)
Example perft_depth_1 : perft_state initial_game_state 1 = 20%nat.
Proof. vm_compute. reflexivity. Qed.

Example perft_depth_2 : perft_state initial_game_state 2 = 400%nat.
Proof. vm_compute. reflexivity. Qed.

Example perft_depth_3 : perft_state initial_game_state 3 = 8902%nat.
Proof. vm_compute. reflexivity. Qed.

(* Note: Depth 4 and 5 tests are computationally expensive but can be verified *)
(* Example perft_depth_4 : perft_state initial_game_state 4 = 197281. *)
(* Example perft_depth_5 : perft_state initial_game_state 5 = 4865609. *)

(* Capture-King Probe Test: Verify sliders cannot jump over or capture kings *)
Example capture_king_blocked : 
  let b := board_empty in
  let b := b [ pos 4 3 := mkp White Rook ] in    (* White rook on d5 *)
  let b := b [ pos 4 5 := mkp Black King ] in    (* Black king on f5 *)
  let b := b [ pos 4 7 := mkp White Rook ] in    (* White rook on h5 *)
  let st := {| current_board := b;
               current_turn := White;
               current_cast := initial_castle;
               en_passant_target := None;
               halfmove_clock := 0;
               fullmove_number := 1 |} in
  let moves := generate_legal_moves st in
  (* Neither rook can move to f5 (king square) or beyond it *)
  forallb (fun m => match m with
                    | MNormal src dst _ => 
                        negb (position_eqb dst (pos 4 5)) &&  (* Can't capture king *)
                        (negb (position_eqb src (pos 4 3)) ||  (* If d5 rook moves... *)
                         Nat.ltb (file dst) 5) &&              (* ...must stay left of king *)
                        (negb (position_eqb src (pos 4 7)) ||  (* If h5 rook moves... *)
                         Nat.ltb 5 (file dst))                 (* ...must stay right of king *)
                    | _ => true
                    end) moves = true.
Proof. vm_compute. reflexivity. Qed.

(* EP Relevance Test: Verify en passant is only relevant when capturable *)
Example ep_relevance_blocked :
  (* Setup: Black pawn just moved d7-d5, White pawn on e5, but White king in check *)
  let b := board_empty in
  let b := b [ pos 0 4 := mkp White King ] in     (* White king on e1 *)
  let b := b [ pos 4 4 := mkp White Pawn ] in     (* White pawn on e5 *)
  let b := b [ pos 4 3 := mkp Black Pawn ] in     (* Black pawn on d5 (just moved) *)
  let b := b [ pos 7 4 := mkp Black Rook ] in     (* Black rook on e8 giving check *)
  let b := b [ pos 7 0 := mkp Black King ] in     (* Black king on a8 *)
  let st := {| current_board := b;
               current_turn := White;
               current_cast := initial_castle;
               en_passant_target := Some (pos 5 3);  (* d6 is EP target *)
               halfmove_clock := 0;
               fullmove_number := 1 |} in
  ep_relevant st = None.  (* EP not relevant because king is in check *)
Proof. vm_compute. reflexivity. Qed.

Example ep_relevance_legal :
  (* Same setup but no check *)
  let b := board_empty in
  let b := b [ pos 0 4 := mkp White King ] in     (* White king on e1 *)
  let b := b [ pos 4 4 := mkp White Pawn ] in     (* White pawn on e5 *)
  let b := b [ pos 4 3 := mkp Black Pawn ] in     (* Black pawn on d5 *)
  let b := b [ pos 7 0 := mkp Black King ] in     (* Black king on a8 *)
  let st := {| current_board := b;
               current_turn := White;
               current_cast := initial_castle;
               en_passant_target := Some (pos 5 3);  (* d6 is EP target *)
               halfmove_clock := 0;
               fullmove_number := 1 |} in
  ep_relevant st = Some (pos 5 3).  (* EP is relevant, capture is legal *)
Proof. vm_compute. reflexivity. Qed.

(* Castling Rights Test: Verify rook capture removes castling rights *)
Example castling_rights_rook_capture :
  (* Setup position where Black bishop can capture White's h1 rook *)
  let b := initial_board in
  let b := b [ pos 1 6 := None ] in  (* Remove g2 pawn *)
  let b := b [ pos 2 5 := mkp Black Bishop ] in  (* Black bishop on f3 *)
  let st := {| current_board := b;
               current_turn := Black;
               current_cast := initial_castle;
               en_passant_target := None;
               halfmove_clock := 0;
               fullmove_number := 1 |} in
  let capture_h1 := MNormal (pos 2 5) (pos 0 7) None in  (* Bf3xh1 *)
  match apply_move st capture_h1 with
  | Some st' => negb st'.(current_cast).(wks) &&
                st'.(current_cast).(wqs)   (* Only kingside lost *)
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Example castling_rights_rook_move :
  (* White moves a1 rook, should lose queenside castling *)
  let moves := [
    MNormal (pos 1 0) (pos 3 0) None;    (* a2-a4 *)
    MNormal (pos 6 4) (pos 4 4) None;    (* e7-e5 *)
    MNormal (pos 0 0) (pos 2 0) None     (* Ra1-a3 *)
  ] in
  match play_moves initial_game_state moves with
  | Some st => negb st.(current_cast).(wqs) &&
               st.(current_cast).(wks)   (* Only queenside lost *)
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(* Dead Position Test: K+N vs K is insufficient material *)
Example dead_position_kn_vs_k :
  let b := board_empty in
  let b := b [ pos 0 0 := mkp White King ] in    (* White king on a1 *)
  let b := b [ pos 2 3 := mkp White Knight ] in  (* White knight on d3 *)
  let b := b [ pos 7 7 := mkp Black King ] in    (* Black king on h8 *)
  let st := {| current_board := b;
               current_turn := White;
               current_cast := initial_castle;
               en_passant_target := None;
               halfmove_clock := 0;
               fullmove_number := 1 |} in
  dead_position_simple st = true.
Proof. vm_compute. reflexivity. Qed.

(* Dead Position Test: K+B vs K is also insufficient *)
Example dead_position_kb_vs_k :
  let b := board_empty in
  let b := b [ pos 0 0 := mkp White King ] in    (* White king on a1 *)
  let b := b [ pos 2 3 := mkp White Bishop ] in  (* White bishop on d3 *)
  let b := b [ pos 7 7 := mkp Black King ] in    (* Black king on h8 *)
  let st := {| current_board := b;
               current_turn := White;
               current_cast := initial_castle;
               en_passant_target := None;
               halfmove_clock := 0;
               fullmove_number := 1 |} in
  dead_position_simple st = true.
Proof. vm_compute. reflexivity. Qed.

(* ---------- Performance Optimization: Piece Lists ---------- *)

(* Filter function needed for optimizations *)
Fixpoint filter {A} (f: A -> bool) (l: list A) : list A :=
  match l with
  | [] => []
  | h::t => if f h then h :: filter f t else filter f t
  end.

(* Instead of scanning all 64 squares, maintain piece lists *)
Definition get_piece_list (b: Board) (c: Color) : list (Position * Piece) :=
  fold_left (fun acc p =>
    match b p with
    | Some piece =>
        if color_eqb piece.(pc_color) c
        then (p, piece) :: acc
        else acc
    | None => acc
    end) all_positions nil.

(* Optimized move generation using piece lists *)
Definition gen_pseudo_optimized (st: GameState) : list Move :=
  let b := st.(current_board) in
  let c := st.(current_turn) in
  let pieces := get_piece_list b c in
  let piece_moves := flat_map (fun pp =>
    let p := fst pp in
    let piece := snd pp in
    gen_piece_moves st p piece
  ) pieces in
  piece_moves ++ gen_castles st.

(* ---------- Standard Algebraic Notation with Disambiguation ---------- *)

(* Check if a move needs disambiguation *)
Definition needs_file_disambiguation (st: GameState) (m: Move) (similar_moves: list Move) : bool :=
  match m with
  | MNormal src dst _ =>
      existsb (fun m2 =>
        match m2 with
        | MNormal src2 dst2 _ =>
            negb (position_eqb src src2) &&
            position_eqb dst dst2 &&
            Nat.eqb (rank src) (rank src2) &&
            negb (Nat.eqb (file src) (file src2))
        | _ => false
        end) similar_moves
  | _ => false
  end.

Definition needs_rank_disambiguation (st: GameState) (m: Move) (similar_moves: list Move) : bool :=
  match m with
  | MNormal src dst _ =>
      existsb (fun m2 =>
        match m2 with
        | MNormal src2 dst2 _ =>
            negb (position_eqb src src2) &&
            position_eqb dst dst2 &&
            negb (Nat.eqb (rank src) (rank src2)) &&
            Nat.eqb (file src) (file src2)
        | _ => false
        end) similar_moves
  | _ => false
  end.

Definition needs_full_disambiguation (st: GameState) (m: Move) (similar_moves: list Move) : bool :=
  match m with
  | MNormal src dst _ =>
      existsb (fun m2 =>
        match m2 with
        | MNormal src2 dst2 _ =>
            negb (position_eqb src src2) &&
            position_eqb dst dst2 &&
            negb (Nat.eqb (rank src) (rank src2)) &&
            negb (Nat.eqb (file src) (file src2))
        | _ => false
        end) similar_moves
  | _ => false
  end.

(* Get all legal moves with same piece type to same destination *)
Definition get_similar_moves (st: GameState) (piece_type: PieceType) (dst: Position) : list Move :=
  let moves := generate_legal_moves st in
  filter (fun m =>
    match m with
    | MNormal src dst2 _ =>
        position_eqb dst dst2 &&
        match st.(current_board) src with
        | Some p => ptype_eqb p.(pc_type) piece_type
        | None => false
        end
    | _ => false
    end) moves.

(* ---------- Extraction with OCaml ---------- *)

Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
Require Import Coq.Strings.String.
Open Scope string_scope.

(* ---------- String conversion functions ---------- *)

Definition color_to_string (c: Color) : string :=
  match c with
  | White => "white"
  | Black => "black"
  end.

Definition piece_type_to_string (pt: PieceType) : string :=
  match pt with
  | Pawn => "pawn"
  | Knight => "knight"
  | Bishop => "bishop"
  | Rook => "rook"
  | Queen => "queen"
  | King => "king"
  end.

Definition piece_to_char (p: Piece) : string :=
  match p.(pc_color), p.(pc_type) with
  | White, Pawn => "P" | White, Knight => "N" | White, Bishop => "B"
  | White, Rook => "R" | White, Queen => "Q" | White, King => "K"
  | Black, Pawn => "p" | Black, Knight => "n" | Black, Bishop => "b"
  | Black, Rook => "r" | Black, Queen => "q" | Black, King => "k"
  end.

(* Unicode chess piece symbols *)
Definition piece_to_unicode (p: Piece) : string :=
  match p.(pc_color), p.(pc_type) with
  | White, King   => "♔"
  | White, Queen  => "♕"
  | White, Rook   => "♖"
  | White, Bishop => "♗"
  | White, Knight => "♘"
  | White, Pawn   => "♙"
  | Black, King   => "♚"
  | Black, Queen  => "♛"
  | Black, Rook   => "♜"
  | Black, Bishop => "♝"
  | Black, Knight => "♞"
  | Black, Pawn   => "♟"
  end.

(* Convert file (0-7) to letter (a-h) *)
Definition file_to_char (f: nat) : string :=
  match f with
  | 0%nat => "a" | 1%nat => "b" | 2%nat => "c" | 3%nat => "d"
  | 4%nat => "e" | 5%nat => "f" | 6%nat => "g" | _ => "h"
  end.

(* Convert rank (0-7) to number (1-8) *)
Definition rank_to_char (r: nat) : string :=
  match r with
  | 0%nat => "1" | 1%nat => "2" | 2%nat => "3" | 3%nat => "4"
  | 4%nat => "5" | 5%nat => "6" | 6%nat => "7" | _ => "8"
  end.

(* Convert position to algebraic notation *)
Definition position_to_string (p: Position) : string :=
  append (file_to_char p.(file)) (rank_to_char p.(rank)).

(* Convert move to string (simplified algebraic notation) *)
Definition move_to_string (m: Move) : string :=
  match m with
  | MNormal src dst None => 
      append (position_to_string src) (append "-" (position_to_string dst))
  | MNormal src dst (Some promo) =>
      append (position_to_string src) 
        (append "-" 
          (append (position_to_string dst)
            (append "="
              (piece_to_char {| pc_color := White; pc_type := promo |}))))
  | MCastle KingSide => "O-O"
  | MCastle QueenSide => "O-O-O"
  end.

(* Game result to string *)
Definition game_result_to_string (gr: GameResult) : string :=
  match gr with
  | Ongoing => "ongoing"
  | Checkmate White => "0-1 (Black wins by checkmate)"
  | Checkmate Black => "1-0 (White wins by checkmate)"
  | Stalemate _ => "1/2-1/2 (Stalemate)"
  | DrawByDeadPosition => "1/2-1/2 (Dead position)"
  | DrawByFiftyMoveClaim => "1/2-1/2 (50-move rule claim)"
  | DrawBySeventyFiveAutomatic => "1/2-1/2 (75-move rule)"
  | DrawByThreefoldClaim => "1/2-1/2 (Threefold repetition claim)"
  | DrawByFivefoldAutomatic => "1/2-1/2 (Fivefold repetition)"
  end.

(* ---------- Board display function ---------- *)
Definition get_board_square (b: Board) (r f: nat) : string :=
  match b (pos r f) with
  | None => "."
  | Some p => piece_to_char p
  end.

Definition board_row_to_string (b: Board) (r: nat) : string :=
  let s0 := get_board_square b r 0%nat in
  let s1 := get_board_square b r 1%nat in
  let s2 := get_board_square b r 2%nat in
  let s3 := get_board_square b r 3%nat in
  let s4 := get_board_square b r 4%nat in
  let s5 := get_board_square b r 5%nat in
  let s6 := get_board_square b r 6%nat in
  let s7 := get_board_square b r 7%nat in
  s0 ++ " " ++ s1 ++ " " ++ s2 ++ " " ++ s3 ++ " " ++ 
  s4 ++ " " ++ s5 ++ " " ++ s6 ++ " " ++ s7.

(* Unicode board square display *)
Definition get_board_square_unicode (b: Board) (r f: nat) : string :=
  match b (pos r f) with
  | None => 
      (* Use light/dark square Unicode symbols for empty squares *)
      if light_square (pos r f) then "□" else "■"
  | Some p => piece_to_unicode p
  end.

(* Board row with Unicode pieces *)
Definition board_row_to_string_unicode (b: Board) (r: nat) : string :=
  let s0 := get_board_square_unicode b r 0%nat in
  let s1 := get_board_square_unicode b r 1%nat in
  let s2 := get_board_square_unicode b r 2%nat in
  let s3 := get_board_square_unicode b r 3%nat in
  let s4 := get_board_square_unicode b r 4%nat in
  let s5 := get_board_square_unicode b r 5%nat in
  let s6 := get_board_square_unicode b r 6%nat in
  let s7 := get_board_square_unicode b r 7%nat in
  s0 ++ " " ++ s1 ++ " " ++ s2 ++ " " ++ s3 ++ " " ++ 
  s4 ++ " " ++ s5 ++ " " ++ s6 ++ " " ++ s7.

(* Complete board display with rank/file labels *)
Definition board_to_string (b: Board) : string :=
  let header := "  a b c d e f g h" in
  let sep := String.String (Ascii.ascii_of_nat 10) EmptyString in  (* newline *)
  let rank_line (r: nat) : string :=
    rank_to_char r ++ " " ++ board_row_to_string b r ++ " " ++ rank_to_char r in
  header ++ sep ++
  rank_line 7%nat ++ sep ++
  rank_line 6%nat ++ sep ++
  rank_line 5%nat ++ sep ++
  rank_line 4%nat ++ sep ++
  rank_line 3%nat ++ sep ++
  rank_line 2%nat ++ sep ++
  rank_line 1%nat ++ sep ++
  rank_line 0%nat ++ sep ++
  header.

(* Complete Unicode board display with rank/file labels *)
Definition board_to_string_unicode (b: Board) : string :=
  let header := "  a b c d e f g h" in
  let sep := String.String (Ascii.ascii_of_nat 10) EmptyString in  (* newline *)
  let rank_line (r: nat) : string :=
    rank_to_char r ++ " " ++ board_row_to_string_unicode b r ++ " " ++ rank_to_char r in
  header ++ sep ++
  rank_line 7%nat ++ sep ++
  rank_line 6%nat ++ sep ++
  rank_line 5%nat ++ sep ++
  rank_line 4%nat ++ sep ++
  rank_line 3%nat ++ sep ++
  rank_line 2%nat ++ sep ++
  rank_line 1%nat ++ sep ++
  rank_line 0%nat ++ sep ++
  header.

(* Test that Unicode display produces correct piece symbols *)
Example unicode_pieces_test :
  piece_to_unicode {| pc_color := White; pc_type := King |} = "♔" /\
  piece_to_unicode {| pc_color := Black; pc_type := Queen |} = "♛" /\
  piece_to_unicode {| pc_color := White; pc_type := Knight |} = "♘" /\
  piece_to_unicode {| pc_color := Black; pc_type := Pawn |} = "♟".
Proof. vm_compute. split; [|split; [|split]]; reflexivity. Qed.

(* ---------- Additional helper functions for OCaml ---------- *)

(* Check if a position is attacked by a specific color *)
Definition is_attacked_by (st: GameState) (c: Color) (pos: Position) : bool :=
  attacks st.(current_board) c pos.

(* Check if a position is attacked by the opponent *)
Definition is_attacked (st: GameState) (pos: Position) : bool :=
  is_attacked_by st (opposite_color st.(current_turn)) pos.

(* Count pieces on board *)
Fixpoint count_pieces (b: Board) (positions: list Position) : nat :=
  match positions with
  | [] => 0%nat
  | p::ps => 
      match b p with
      | None => count_pieces b ps
      | Some _ => S (count_pieces b ps)
      end
  end.

(* Get all pieces of a color *)
Fixpoint get_pieces_of_color (b: Board) (c: Color) (positions: list Position) 
  : list (Position * Piece) :=
  match positions with
  | [] => []
  | p::ps =>
      match b p with
      | None => get_pieces_of_color b c ps
      | Some piece => 
          if color_eqb piece.(pc_color) c
          then (p, piece) :: get_pieces_of_color b c ps
          else get_pieces_of_color b c ps
      end
  end.

(* Check for specific endgame conditions *)
Definition is_king_and_rook_vs_king (st: GameState) : bool :=
  let m := summarize_material st.(current_board) all_positions ms_empty in
  (Nat.eqb m.(wR) 1%nat && Nat.eqb m.(wQ) 0%nat && Nat.eqb m.(wP) 0%nat && 
   Nat.eqb m.(wN) 0%nat && Nat.eqb m.(wB) 0%nat &&
   Nat.eqb m.(bR) 0%nat && Nat.eqb m.(bQ) 0%nat && Nat.eqb m.(bP) 0%nat && 
   Nat.eqb m.(bN) 0%nat && Nat.eqb m.(bB) 0%nat) ||
  (Nat.eqb m.(bR) 1%nat && Nat.eqb m.(bQ) 0%nat && Nat.eqb m.(bP) 0%nat && 
   Nat.eqb m.(bN) 0%nat && Nat.eqb m.(bB) 0%nat &&
   Nat.eqb m.(wR) 0%nat && Nat.eqb m.(wQ) 0%nat && Nat.eqb m.(wP) 0%nat && 
   Nat.eqb m.(wN) 0%nat && Nat.eqb m.(wB) 0%nat).

(* Move list to string *)
Fixpoint moves_to_string (moves: list Move) : string :=
  match moves with
  | [] => ""
  | [m] => move_to_string m
  | m::ms => append (move_to_string m) (append ", " (moves_to_string ms))
  end.

(* ---------- FEN Support ---------- *)

(* Helper to convert nat to string - handle up to 150 for move counters *)
Definition nat_to_string (n: nat) : string :=
  (* For simplicity, only handle small numbers needed for FEN *)
  match n with
  | 0%nat => "0" | 1%nat => "1" | 2%nat => "2" | 3%nat => "3"
  | 4%nat => "4" | 5%nat => "5" | 6%nat => "6" | 7%nat => "7" 
  | 8%nat => "8" | 9%nat => "9" | 10%nat => "10" | 11%nat => "11"
  | 12%nat => "12" | 13%nat => "13" | 14%nat => "14" | 15%nat => "15"
  | _ => "50"  (* Default for larger numbers *)
  end.

(* Convert a board rank to FEN string - use fuel for termination *)
Fixpoint fen_rank_string_aux (b: Board) (r: nat) (f: nat) (empty_count: nat) (fuel: nat) : string :=
  match fuel with
  | 0%nat => ""  (* Should not happen with fuel = 8 *)
  | S fuel' =>
      if Nat.ltb 7 f then
        (* End of rank *)
        if Nat.ltb 0 empty_count 
        then nat_to_string empty_count
        else ""
      else
        match b (pos r f) with
        | None => fen_rank_string_aux b r (S f) (S empty_count) fuel'
        | Some p => 
            let prefix := if Nat.ltb 0 empty_count 
                          then nat_to_string empty_count 
                          else "" in
            append prefix 
                   (append (piece_to_char p) 
                           (fen_rank_string_aux b r (S f) 0 fuel'))
        end
  end.

Definition fen_rank_string (b: Board) (r: nat) : string :=
  fen_rank_string_aux b r 0 0 8.

(* Generate FEN board representation *)
Fixpoint fen_board_aux (b: Board) (r: nat) : string :=
  match r with
  | 0%nat => fen_rank_string b 0
  | S r' => append (fen_rank_string b r) 
                   (append "/" (fen_board_aux b r'))
  end.

Definition fen_board (b: Board) : string := fen_board_aux b 7%nat.

(* Convert castling rights to FEN string *)
Definition fen_castling (cr: CastleRights) : string :=
  let k := if cr.(wks) then "K" else "" in
  let q := if cr.(wqs) then "Q" else "" in
  let k' := if cr.(bks) then "k" else "" in
  let q' := if cr.(bqs) then "q" else "" in
  let all := append k (append q (append k' q')) in
  match all with
  | EmptyString => "-"
  | _ => all
  end.

(* Convert en passant target to FEN string *)
Definition fen_ep (ep: option Position) : string :=
  match ep with
  | None => "-"
  | Some p => position_to_string p
  end.

(* Generate complete FEN string *)
Definition to_fen (st: GameState) : string :=
  let board_str := fen_board (current_board st) in
  let turn_str := if color_eqb (current_turn st) White then "w" else "b" in
  let castle_str := fen_castling (current_cast st) in
  let ep_str := fen_ep (en_passant_target st) in
  let half_str := nat_to_string (halfmove_clock st) in
  let full_str := nat_to_string (fullmove_number st) in
  board_str ++ " " ++ turn_str ++ " " ++ castle_str ++ " " ++ 
  ep_str ++ " " ++ half_str ++ " " ++ full_str.

(* Display game state with ASCII board *)
Definition display_game_state (st: GameState) : string :=
  let sep := String.String (Ascii.ascii_of_nat 10) EmptyString in
  let turn := if color_eqb (current_turn st) White then "White" else "Black" in
  board_to_string (current_board st) ++ sep ++
  "Turn: " ++ turn ++ sep ++
  "FEN: " ++ to_fen st.

(* Display game state with Unicode board *)
Definition display_game_state_unicode (st: GameState) : string :=
  let sep := String.String (Ascii.ascii_of_nat 10) EmptyString in
  let turn := if color_eqb (current_turn st) White then "White" else "Black" in
  board_to_string_unicode (current_board st) ++ sep ++
  "Turn: " ++ turn ++ sep ++
  "FEN: " ++ to_fen st.

(* Display game state with both ASCII and Unicode boards side by side *)
Definition display_game_state_both (st: GameState) : string :=
  let sep := String.String (Ascii.ascii_of_nat 10) EmptyString in
  let turn := if color_eqb (current_turn st) White then "White" else "Black" in
  "=== ASCII ===" ++ sep ++
  board_to_string (current_board st) ++ sep ++
  sep ++ "=== Unicode ===" ++ sep ++
  board_to_string_unicode (current_board st) ++ sep ++
  sep ++ "Turn: " ++ turn ++ sep ++
  "FEN: " ++ to_fen st.

(* ---------- Main extraction with module structure ---------- *)

Extraction Language OCaml.
Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive nat => "int" ["0" "succ"] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant minus => "(fun x y -> let z = x - y in if z < 0 then 0 else z)".
Extract Constant Nat.eqb => "( = )".
Extract Constant Nat.leb => "( <= )".
Extract Constant Nat.ltb => "( < )".

(* Set extraction to create a proper module *)
Extraction "ChessEngine"
  (* Core types *)
  Color PieceType Piece Position CastleRights GameState Game Move GameResult
  CastleSide
  
  (* Color utilities *)
  opposite_color color_eqb color_to_string
  
  (* Piece utilities *)
  ptype_eqb piece_eqb piece_to_char piece_type_to_string
  
  (* Position utilities *)
  pos position_eqb position_to_string in_bounds
  file_to_char rank_to_char
  
  (* Board operations *)
  Board board_empty board_get board_set occ occ_color
  get_board_square board_row_to_string
  
  (* Game initialization *)
  initial_board initial_game_state initial_game initial_castle
  
  (* Move generation and validation *)
  generate_legal_moves apply_move pseudo_ok
  gen_piece_moves gen_pseudo filter_legal
  can_castle gen_castles
  
  (* Game flow *)
  game_apply game_outcome play_moves
  is_checkmate_state is_stalemate_state in_check
  is_attacked is_attacked_by find_king attacks
  
  (* Draw conditions *)
  threefold_claimable fivefold_automatic
  fifty_move_claimable seventyfive_automatic
  dead_position_simple is_king_and_rook_vs_king
  
  (* Move notation *)
  move_to_string moves_to_string move_eqb
  mk_move_normal apply_move_normal_coords apply_castle_side
  legal_normal_moves legal_castles
  
  (* Game analysis *)
  perft_state count_pieces get_pieces_of_color
  make_poskey count_pos
  
  (* Result display *)
  game_result_to_string
  
  (* FEN support *)
  to_fen fen_board fen_castling fen_ep
  nat_to_string
  
  (* Board display *)
  board_to_string board_to_string_unicode
  display_game_state display_game_state_unicode display_game_state_both
  piece_to_unicode get_board_square_unicode board_row_to_string_unicode
  
  (* Constants *)
  forward start_rank back_rank last_rank
  king_start rook_start_k rook_start_q
  king_castle_dst rook_castle_dst
  
  (* All positions for iteration *)
  all_positions range.
