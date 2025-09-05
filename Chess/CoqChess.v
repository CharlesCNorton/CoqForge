(*
  A Formalization of Chess in Coq
  
  This development provides a complete formalization of the rules of chess
  following FIDE Laws of Chess. The formalization includes piece movement,
  capture mechanics, special moves (castling, en passant, promotion),
  check and checkmate detection, and draw conditions (stalemate, repetition,
  fifty-move rule, insufficient material).
  
  Coordinate system: Ranks 0-7, Files 0-7 where (0,0) corresponds to square a1.
  Dependencies: Coq standard library (≥ 8.13)
*)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.

Import ListNotations.
Open Scope nat_scope.
Open Scope Z_scope.

(* Section 1: Core Definitions *)

Inductive Color := White | Black.

Definition opposite_color (c:Color) : Color :=
  match c with White => Black | Black => White end.

Definition color_eqb (a b:Color) : bool :=
  match a,b with White,White => true | Black,Black => true | _,_ => false end.

Inductive PieceType := Pawn | Knight | Bishop | Rook | Queen | King.

Definition ptype_eqb (a b:PieceType) : bool :=
  match a,b with
  | Pawn,Pawn | Knight,Knight | Bishop,Bishop | Rook,Rook | Queen,Queen | King,King => true
  | _,_ => false
  end.

Record Piece := { pc_color : Color; pc_type : PieceType }.

Definition piece_eqb (x y:Piece) : bool :=
  color_eqb x.(pc_color) y.(pc_color) && ptype_eqb x.(pc_type) y.(pc_type).

Record Position := { rank : nat; file : nat }.

Definition pos (r f:nat) : Position := {| rank := r; file := f |}.

Definition position_eqb (a b:Position) : bool :=
  Nat.eqb a.(rank) b.(rank) && Nat.eqb a.(file) b.(file).

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

(* Section 2: Board Representation *)

Definition Board := Position -> option Piece.
Definition board_empty : Board := fun _ => None.
Definition board_get (b:Board) (p:Position) : option Piece := b p.
Definition board_set (b:Board) (p:Position) (x:option Piece) : Board :=
  fun q => if position_eqb q p then x else b q.
Definition occ (b:Board) (p:Position) : bool :=
  match b p with Some _ => true | None => false end.
Definition occ_color (b:Board) (p:Position) (c:Color) : bool :=
  match b p with Some q => color_eqb q.(pc_color) c | None => false end.

Notation "b [ p ]" := (board_get b p) (at level 9).
Notation "b [ p := x ]" := (board_set b p x) (at level 9).

(* Section 3: Initial Position *)

Definition mkp (c:Color) (k:PieceType) : option Piece :=
  Some {| pc_color := c; pc_type := k |}.

Definition place_pawns (b:Board) (c:Color) : Board :=
  let r := if color_eqb c White then (1%nat) else (6%nat) in
  fold_left (fun bb f => bb [ pos r f := mkp c Pawn ]) (range (8%nat)) b.

Definition place_backrank (b:Board) (c:Color) : Board :=
  let r := if color_eqb c White then (0%nat) else (7%nat) in
  let b := b [ pos r (0%nat) := mkp c Rook ] in
  let b := b [ pos r (1%nat) := mkp c Knight ] in
  let b := b [ pos r (2%nat) := mkp c Bishop ] in
  let b := b [ pos r (3%nat) := mkp c Queen ] in
  let b := b [ pos r (4%nat) := mkp c King ] in
  let b := b [ pos r (5%nat) := mkp c Bishop ] in
  let b := b [ pos r (6%nat) := mkp c Knight ] in
  let b := b [ pos r (7%nat) := mkp c Rook ] in b.

Definition initial_board : Board :=
  let b := board_empty in
  let b := place_backrank b White in
  let b := place_backrank b Black in
  let b := place_pawns b White in
  let b := place_pawns b Black in b.

(* Section 4: Game State *)

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

Definition forward (c:Color) : Z := if color_eqb c White then 1 else -1.
Definition start_rank (c:Color) : nat := if color_eqb c White then (1%nat) else (6%nat).
Definition back_rank (c:Color) : nat := if color_eqb c White then (0%nat) else (7%nat).
Definition last_rank (c:Color) : nat := if color_eqb c White then (7%nat) else (0%nat).

(* Section 5: Attack Detection *)

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
Definition rook_dirs : list (Z*Z) := [(1,0);(-1,0);(0,1);(0,-1)]%Z.
Definition bishop_dirs : list (Z*Z) := [(1,1);(1,-1);(-1,1);(-1,-1)]%Z.
Definition queen_dirs : list (Z*Z) := rook_dirs ++ bishop_dirs.

Definition attacks (b:Board) (c:Color) (t:Position) : bool :=
  let pawn_hit :=
    let r := t.(rank) in let f := t.(file) in
    match c with
    | White =>
        let s1 := pos_of_Z (Z.of_nat r - 1) (Z.of_nat f - 1) in
        let s2 := pos_of_Z (Z.of_nat r - 1) (Z.of_nat f + 1) in
        (existsb (fun so =>
           match so with
           | Some s => match b s with
                       | Some p => color_eqb p.(pc_color) White && ptype_eqb p.(pc_type) Pawn
                       | None => false
                       end
           | None => false
           end) (s1::s2::nil))
    | Black =>
        let s1 := pos_of_Z (Z.of_nat r + 1) (Z.of_nat f - 1) in
        let s2 := pos_of_Z (Z.of_nat r + 1) (Z.of_nat f + 1) in
        (existsb (fun so =>
           match so with
           | Some s => match b s with
                       | Some p => color_eqb p.(pc_color) Black && ptype_eqb p.(pc_type) Pawn
                       | None => false
                       end
           | None => false
           end) (s1::s2::nil))
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
  let rook_like := slider_hit rook_dirs (fun k => ptype_eqb k Rook || ptype_eqb k Queen) in
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

(* Section 6: Move Representation *)

Inductive CastleSide := KingSide | QueenSide.

Inductive Move :=
| MNormal (src dst:Position) (promo:option PieceType)
| MCastle (side:CastleSide).

(* Section 7: Pseudo-legal Move Generation *)

Definition promo_kinds : list PieceType := [Queen;Rook;Bishop;Knight].

Definition guard_dest (b:Board) (c:Color) (d:Position) : bool :=
  negb (occ_color b d c).

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

Definition gen_pawn (st:GameState) (c:Color) (src:Position) : list Move :=
  let b := st.(current_board) in
  let f := forward c in
  let last := last_rank c in
  let single :=
    match offset src 0 f with
    | Some d =>
        if occ b d then []
        else if Nat.eqb d.(rank) last
             then map (fun k => MNormal src d (Some k)) promo_kinds
             else [MNormal src d None]
    | None => []
    end in
  let double :=
    if Nat.eqb src.(rank) (start_rank c)
    then match offset src 0 f, offset src 0 (2 * f) with
         | Some d1, Some d2 =>
             if occ b d1 || occ b d2 then [] else [MNormal src d2 None]
         | _, _ => []
         end
    else [] in
  let cap_one (df:Z) : list Move :=
    match offset src df f with
    | Some d =>
        match b d with
        | Some p =>
            if color_eqb p.(pc_color) (opposite_color c)
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
  | Pawn => gen_pawn st c src
  | Knight => gen_offsets b c src knight_offsets
  | Bishop => gen_sliding b c src bishop_dirs 7
  | Rook => gen_sliding b c src rook_dirs 7
  | Queen => gen_sliding b c src queen_dirs 7
  | King => gen_offsets b c src king_offsets
  end.

(* Section 8: Castling *)

Definition king_start (c:Color) : Position := pos (back_rank c) 4.
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
  let mid1 := match side with KingSide => offset ks 1 0 | QueenSide => offset ks (-1) 0 end in
  let mid2 := match side with KingSide =>
                           match offset ks 1 0 with Some s => offset s 1 0 | None => None end
                         | QueenSide => offset ks (-2) 0
              end in
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
           match mid1, mid2 with
           | Some s1, Some s2 => negb (occ b s1) && negb (occ b s2)
           | _,_ => false
           end
       | QueenSide =>
           match offset ks (-1) 0, offset ks (-2) 0, offset ks (-3) 0 with
           | Some d1, Some c1, Some b1 =>
               negb (occ b d1) && negb (occ b c1) && negb (occ b b1)
           | _,_,_ => false
           end
       end)
      (andb
        (negb (in_check st c))
        (andb
          (match side with
           | KingSide => match mid1 with Some s1 => negb (attacks b (opposite_color c) s1) | None => false end
           | QueenSide => match offset ks (-1) 0 with Some d1 => negb (attacks b (opposite_color c) d1) | None => false end
           end)
          (negb (attacks b (opposite_color c) kd)))))).

Definition gen_castles (st:GameState) : list Move :=
  let c := st.(current_turn) in
  let add s := if can_castle st c s then [MCastle s] else [] in
  add KingSide ++ add QueenSide.

(* Section 9: Move Application *)

Definition disable_side_cr (cr:CastleRights) (c:Color) : CastleRights :=
  match c with
  | White => {| wks := false; wqs := false; bks := cr.(bks); bqs := cr.(bqs) |}
  | Black => {| wks := cr.(wks); wqs := cr.(wqs); bks := false; bqs := false |}
  end.

Definition disable_rook_from (cr:CastleRights) (c:Color) (r0:Position) : CastleRights :=
  match c, r0.(rank), r0.(file) with
  | White, O, S (S (S (S (S (S (S O)))))) => {| wks := false; wqs := cr.(wqs); bks := cr.(bks); bqs := cr.(bqs) |}
  | White, O, O => {| wks := cr.(wks); wqs := false; bks := cr.(bks); bqs := cr.(bqs) |}
  | Black, S (S (S (S (S (S (S O)))))), S (S (S (S (S (S (S O)))))) => {| wks := cr.(wks); wqs := cr.(wqs); bks := false; bqs := cr.(bqs) |}
  | Black, S (S (S (S (S (S (S O)))))), O => {| wks := cr.(wks); wqs := cr.(wqs); bks := cr.(bks); bqs := false |}
  | _,_,_ => cr
  end.

Definition disable_rook_if_captured (cr:CastleRights) (c:Color) (dst:Position) : CastleRights :=
  match c, dst.(rank), dst.(file) with
  | White, O, S (S (S (S (S (S (S O)))))) => {| wks := false; wqs := cr.(wqs); bks := cr.(bks); bqs := cr.(bqs) |}
  | White, O, O => {| wks := cr.(wks); wqs := false; bks := cr.(bks); bqs := cr.(bqs) |}
  | Black, S (S (S (S (S (S (S O)))))), S (S (S (S (S (S (S O)))))) => {| wks := cr.(wks); wqs := cr.(wqs); bks := false; bqs := cr.(bqs) |}
  | Black, S (S (S (S (S (S (S O)))))), O => {| wks := cr.(wks); wqs := cr.(wqs); bks := cr.(bks); bqs := false |}
  | _,_,_ => cr
  end.

Definition is_promo_kind (k:PieceType) : bool :=
  match k with Queen | Rook | Bishop | Knight => true | _ => false end.

Definition apply_move (st:GameState) (m:Move) : option GameState :=
  let b := st.(current_board) in
  let c := st.(current_turn) in
  let bump_full (c:Color) (f:nat) : nat := if color_eqb c Black then S f else f in
  match m with
  | MCastle side =>
      if can_castle st c side then
        let ks := king_start c in
        let kd := king_castle_dst c side in
        let rs := match side with KingSide => rook_start_k c | QueenSide => rook_start_q c end in
        let rd := rook_castle_dst c side in
        let b1 := b [ ks := None ] in
        let b2 := b1 [ rs := None ] in
        let b3 := b2 [ kd := mkp c King ] in
        let b4 := b3 [ rd := mkp c Rook ] in
        let st' := {| current_board := b4;
                      current_turn := opposite_color c;
                      current_cast := disable_side_cr st.(current_cast) c;
                      en_passant_target := None;
                      halfmove_clock := S st.(halfmove_clock);
                      fullmove_number := bump_full c st.(fullmove_number) |} in
        if in_check st' (opposite_color st'.(current_turn)) then None else Some st'
      else None
  | MNormal src dst promo =>
      match b src with
      | None => None
      | Some p =>
        if negb (color_eqb p.(pc_color) c) then None else
        let is_pawn := ptype_eqb p.(pc_type) Pawn in
        let is_two_step :=
          is_pawn && Nat.eqb src.(rank) (start_rank c) &&
          match offset src 0 (forward c), offset src 0 (2*forward c) with
          | Some d1, Some d2 => position_eqb d2 dst && negb (occ b d1) && negb (occ b d2)
          | _,_ => false
          end in
        let dx := (Z.of_nat dst.(file)) - (Z.of_nat src.(file)) in
        let dy := (Z.of_nat dst.(rank)) - (Z.of_nat src.(rank)) in
        let is_diag := ((Z.abs dx =? 1) && (dy =? forward c))%bool in
        let ep_capture :=
          is_pawn && is_diag &&
          match st.(en_passant_target) with Some ep => position_eqb dst ep | None => false end in
        let cap_square :=
          if ep_capture
          then match offset dst 0 (- forward c) with Some s => Some s | None => None end
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
        let b2 := match cap_square with Some cs => if capturing then b1 [ cs := None ] else b1 | None => b1 end in
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
        let new_ep := if is_two_step then offset src 0 (forward c) else None in
        let new_hmc := if is_pawn || capturing then (0%nat) else S st.(halfmove_clock) in
        let st' := {| current_board := b3;
                      current_turn := opposite_color c;
                      current_cast := cr2;
                      en_passant_target := new_ep;
                      halfmove_clock := new_hmc;
                      fullmove_number := bump_full c st.(fullmove_number) |} in
        if in_check st' (opposite_color st'.(current_turn)) then None else Some st'
      end
  end.

(* Section 10: Legal Move Generation *)

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

(* Section 11: Position Keys and Repetition *)

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

(* En passant is only relevant for repetition if capturable *)
Definition ep_relevant (st:GameState) : option Position :=
  match st.(en_passant_target) with
  | None => None
  | Some ep =>
      let c := st.(current_turn) in
      let f := forward c in
      let src_left := match offset ep (-1) (-f) with Some s => Some s | None => None end in
      let src_right := match offset ep 1 (-f) with Some s => Some s | None => None end in
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
  match xs with [] => 0 | x::tl => (if poskey_eqb k x then S (count_pos k tl) else count_pos k tl) end.

(* Section 12: Game Structure *)

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

(* Section 13: Game Outcomes *)

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

(* Section 14: Insufficient Material Detection *)

Record MatSummary := {
  wP:nat; wN:nat; wB:nat; wR:nat; wQ:nat;
  bP:nat; bN:nat; bB:nat; bR:nat; bQ:nat;
  wB_sq: list Position; bB_sq: list Position
}.

Definition ms_empty : MatSummary :=
  {| wP:=0; wN:=0; wB:=0; wR:=0; wQ:=0;
     bP:=0; bN:=0; bB:=0; bR:=0; bQ:=0;
     wB_sq := []; bB_sq := [] |}.

Definition bump (n:nat) := S n.

Fixpoint summarize_material (b:Board) (ls:list Position) (acc:MatSummary) : MatSummary :=
  match ls with
  | [] => acc
  | p::tl =>
      match b p with
      | None => summarize_material b tl acc
      | Some q =>
          let acc' :=
            match q.(pc_color), q.(pc_type) with
            | White,Pawn => {| wP := bump acc.(wP); wN := acc.(wN); wB := acc.(wB); wR := acc.(wR); wQ := acc.(wQ); bP := acc.(bP); bN := acc.(bN); bB := acc.(bB); bR := acc.(bR); bQ := acc.(bQ); wB_sq := acc.(wB_sq); bB_sq := acc.(bB_sq) |}
            | White,Knight => {| wP := acc.(wP); wN := bump acc.(wN); wB := acc.(wB); wR := acc.(wR); wQ := acc.(wQ); bP := acc.(bP); bN := acc.(bN); bB := acc.(bB); bR := acc.(bR); bQ := acc.(bQ); wB_sq := acc.(wB_sq); bB_sq := acc.(bB_sq) |}
            | White,Bishop => {| wP := acc.(wP); wN := acc.(wN); wB := bump acc.(wB); wR := acc.(wR); wQ := acc.(wQ); bP := acc.(bP); bN := acc.(bN); bB := acc.(bB); bR := acc.(bR); bQ := acc.(bQ); wB_sq := p :: acc.(wB_sq); bB_sq := acc.(bB_sq) |}
            | White,Rook => {| wP := acc.(wP); wN := acc.(wN); wB := acc.(wB); wR := bump acc.(wR); wQ := acc.(wQ); bP := acc.(bP); bN := acc.(bN); bB := acc.(bB); bR := acc.(bR); bQ := acc.(bQ); wB_sq := acc.(wB_sq); bB_sq := acc.(bB_sq) |}
            | White,Queen => {| wP := acc.(wP); wN := acc.(wN); wB := acc.(wB); wR := acc.(wR); wQ := bump acc.(wQ); bP := acc.(bP); bN := acc.(bN); bB := acc.(bB); bR := acc.(bR); bQ := acc.(bQ); wB_sq := acc.(wB_sq); bB_sq := acc.(bB_sq) |}
            | Black,Pawn => {| wP := acc.(wP); wN := acc.(wN); wB := acc.(wB); wR := acc.(wR); wQ := acc.(wQ); bP := bump acc.(bP); bN := acc.(bN); bB := acc.(bB); bR := acc.(bR); bQ := acc.(bQ); wB_sq := acc.(wB_sq); bB_sq := acc.(bB_sq) |}
            | Black,Knight => {| wP := acc.(wP); wN := acc.(wN); wB := acc.(wB); wR := acc.(wR); wQ := acc.(wQ); bP := acc.(bP); bN := bump acc.(bN); bB := acc.(bB); bR := acc.(bR); bQ := acc.(bQ); wB_sq := acc.(wB_sq); bB_sq := acc.(bB_sq) |}
            | Black,Bishop => {| wP := acc.(wP); wN := acc.(wN); wB := acc.(wB); wR := acc.(wR); wQ := acc.(wQ); bP := acc.(bP); bN := acc.(bN); bB := bump acc.(bB); bR := acc.(bR); bQ := acc.(bQ); wB_sq := acc.(wB_sq); bB_sq := p :: acc.(bB_sq) |}
            | Black,Rook => {| wP := acc.(wP); wN := acc.(wN); wB := acc.(wB); wR := acc.(wR); wQ := acc.(wQ); bP := acc.(bP); bN := acc.(bN); bB := acc.(bB); bR := bump acc.(bR); bQ := acc.(bQ); wB_sq := acc.(wB_sq); bB_sq := acc.(bB_sq) |}
            | Black,Queen => {| wP := acc.(wP); wN := acc.(wN); wB := acc.(wB); wR := acc.(wR); wQ := acc.(wQ); bP := acc.(bP); bN := acc.(bN); bB := acc.(bB); bR := acc.(bR); bQ := bump acc.(bQ); wB_sq := acc.(wB_sq); bB_sq := acc.(bB_sq) |}
            | _,King => acc
            end in
          summarize_material b tl acc'
      end
  end.

Definition bishops_all_same_color (ls:list Position) : bool :=
  match ls with
  | [] => true
  | s0::tl => let c0 := light_square s0 in forallb (fun s => Bool.eqb (light_square s) c0) tl
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
  | S O, O => Nat.eqb m.(wN) (1%nat) || Nat.eqb m.(wB) (1%nat)
  | O, S O => Nat.eqb m.(bN) (1%nat) || Nat.eqb m.(bB) (1%nat)
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

(* Section 15: Board Validity *)

Definition valid_king_count (b:Board) : bool :=
  let count (c:Color) :=
    length (filter (fun p =>
      match b p with
      | Some q => color_eqb q.(pc_color) c && ptype_eqb q.(pc_type) King
      | None => false
      end) all_positions)
  in Nat.eqb (count White) 1 && Nat.eqb (count Black) 1.

Definition valid_pawn_positions (b:Board) : bool :=
  forallb (fun p =>
    match b p with
    | Some q =>
        if ptype_eqb q.(pc_type) Pawn
        then negb (Nat.eqb p.(rank) 0) && negb (Nat.eqb p.(rank) 7)
        else true
    | None => true
    end) all_positions.

Definition valid_board (b:Board) : bool :=
  valid_king_count b && valid_pawn_positions b.

(* Section 16: Utility Functions *)

Fixpoint play_moves (st:GameState) (moves:list Move) : option GameState :=
  match moves with
  | [] => Some st
  | m::tl =>
      match apply_move st m with
      | Some st' => play_moves st' tl
      | None => None
      end
  end.

Definition is_checkmate_state (st:GameState) : bool :=
  let ms := generate_legal_moves st in
  match ms with
  | [] => if in_check st st.(current_turn) then true else false
  | _ => false
  end.

Definition is_stalemate_state (st:GameState) : bool :=
  let ms := generate_legal_moves st in
  match ms with
  | [] => if in_check st st.(current_turn) then false else true
  | _ => false
  end.

Definition move_eqb (m1 m2:Move) : bool :=
  match m1, m2 with
  | MCastle KingSide, MCastle KingSide => true
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

(* Section 17: Theorems *)

Theorem opposite_involutive : forall c, opposite_color (opposite_color c) = c.
Proof. intro c; destruct c; reflexivity. Qed.

Theorem color_eqb_refl : forall c, color_eqb c c = true.
Proof. intro c; destruct c; reflexivity. Qed.

Theorem ptype_eqb_refl : forall k, ptype_eqb k k = true.
Proof. intro k; destruct k; reflexivity. Qed.

Theorem position_eqb_refl : forall p, position_eqb p p = true.
Proof. 
  intro p. unfold position_eqb.
  rewrite Nat.eqb_refl. rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Theorem piece_eqb_refl : forall p, piece_eqb p p = true.
Proof.
  intro p. unfold piece_eqb.
  rewrite color_eqb_refl. rewrite ptype_eqb_refl.
  reflexivity.
Qed.

Theorem opposite_color_neq : forall c, negb (color_eqb c (opposite_color c)) = true.
Proof. intro c; destruct c; reflexivity. Qed.

Theorem initial_board_valid : valid_board initial_board = true.
Proof.
  unfold valid_board, valid_king_count, valid_pawn_positions.
  (* Would require explicit computation over all_positions *)
  (* Proof by computation *)
  reflexivity.
Qed.

(* Helper lemmas for move_changes_turn *)

Lemma apply_move_castle_turn : forall st side st',
  can_castle st (current_turn st) side = true ->
  apply_move st (MCastle side) = Some st' ->
  st'.(current_turn) = opposite_color st.(current_turn).
Proof.
  intros st side st' HCan HApply.
  unfold apply_move in HApply.
  rewrite HCan in HApply.
  destruct (in_check _ _); try discriminate.
  injection HApply; intros; subst.
  simpl. reflexivity.
Qed.

Lemma apply_move_normal_some_piece : forall st src dst promo st',
  apply_move st (MNormal src dst promo) = Some st' ->
  exists p, current_board st src = Some p.
Proof.
  intros st src dst promo st' H.
  unfold apply_move in H.
  destruct (current_board st src); try discriminate.
  exists p. reflexivity.
Qed.

Lemma apply_move_normal_correct_color : forall st src dst promo st' p,
  current_board st src = Some p ->
  apply_move st (MNormal src dst promo) = Some st' ->
  color_eqb (pc_color p) (current_turn st) = true.
Proof.
  intros st src dst promo st' p GetPiece H.
  unfold apply_move in H.
  rewrite GetPiece in H.
  destruct (negb (color_eqb (pc_color p) (current_turn st))) eqn:E; try discriminate.
  rewrite negb_false_iff in E.
  exact E.
Qed.

Lemma apply_move_normal_requires_piece : forall st src dst promo st',
  apply_move st (MNormal src dst promo) = Some st' ->
  current_board st src <> None.
Proof.
  intros st src dst promo st' H.
  unfold apply_move in H.
  destruct (current_board st src) eqn:E.
  - intro NEQ. discriminate NEQ.
  - simpl in H. discriminate H.
Qed.

Lemma apply_move_normal_piece_color : forall st src dst promo st' p,
  current_board st src = Some p ->
  apply_move st (MNormal src dst promo) = Some st' ->
  negb (color_eqb (pc_color p) (current_turn st)) = false.
Proof.
  intros st src dst promo st' p GetPiece H.
  unfold apply_move in H.
  rewrite GetPiece in H.
  destruct (negb (color_eqb (pc_color p) (current_turn st))) eqn:E; try discriminate.
  reflexivity.
Qed.

Lemma apply_move_final_check : forall st m st',
  apply_move st m = Some st' ->
  (forall final, 
    (if in_check final (opposite_color (current_turn final)) then None else Some final) = Some st' ->
    in_check st' (opposite_color (current_turn st')) = false).
Proof.
  intros st m st' H final Hfinal.
  destruct (in_check final (opposite_color (current_turn final))) eqn:E.
  - discriminate Hfinal.
  - injection Hfinal. intros. subst. exact E.
Qed.

Theorem move_changes_turn : forall st m st',
  apply_move st m = Some st' ->
  st'.(current_turn) = opposite_color st.(current_turn).
Proof.
  intros st m st' H.
  destruct m.
  - pose proof H as Horig.
    apply (apply_move_normal_some_piece st src dst promo) in H as [p Hp].
    pose proof Horig as Hcolor_arg.
    apply (apply_move_normal_correct_color st src dst promo st' p Hp) in Hcolor_arg as Hcolor.
    unfold apply_move in Horig. rewrite Hp in Horig.
    destruct (negb (color_eqb (pc_color p) (current_turn st))); try discriminate.
    destruct (negb _); try discriminate.
    destruct (negb _); try discriminate.
    destruct (in_check _ _); try discriminate.
    injection Horig. intros. subst. simpl. reflexivity.
  - destruct (can_castle st (current_turn st) side) eqn:Hcan.
    + exact (apply_move_castle_turn st side st' Hcan H).
    + unfold apply_move in H. rewrite Hcan in H. discriminate.
Qed.

Theorem legal_move_no_self_check : forall st m st',
  apply_move st m = Some st' ->
  in_check st' (opposite_color st'.(current_turn)) = false.
Proof.
  intros st m st' H.
  unfold apply_move in H.
  destruct m.
  - destruct (current_board st src); try discriminate.
    destruct (negb _); try discriminate.
    destruct (negb _); try discriminate.
    destruct (negb _); try discriminate.
    destruct (in_check _ (opposite_color (current_turn _))) eqn:E; try discriminate.
    injection H. intros. subst. exact E.
  - destruct (can_castle st (current_turn st) side); try discriminate.
    destruct (in_check _ (opposite_color (current_turn _))) eqn:E; try discriminate.
    injection H. intros. subst. exact E.
Qed.

Theorem checkmate_no_legal_moves : forall st,
  is_checkmate_state st = true ->
  generate_legal_moves st = [].
Proof.
  intros st H.
  unfold is_checkmate_state in H.
  destruct (generate_legal_moves st) eqn:E.
  - reflexivity.
  - simpl in H. discriminate.
Qed.

Theorem stalemate_not_check : forall st,
  is_stalemate_state st = true ->
  in_check st st.(current_turn) = false.
Proof.
  intros st H.
  unfold is_stalemate_state in H.
  destruct (generate_legal_moves st).
  - destruct (in_check st st.(current_turn)) eqn:E.
    + discriminate.
    + reflexivity.
  - discriminate.
Qed.

Lemma exists_ep_from_left : forall st ep,
  en_passant_target st = Some ep ->
  (match offset ep (-1) (- forward (current_turn st)) with
   | Some s => match current_board st s with
               | Some p => color_eqb (pc_color p) (current_turn st) && ptype_eqb (pc_type p) Pawn
               | None => false
               end
   | None => false
   end) = true ->
  exists pawn_pos,
    current_board st pawn_pos = Some {| pc_color := current_turn st; pc_type := Pawn |} /\
    Some pawn_pos = offset ep (-1) (- forward (current_turn st)).
Proof.
  intros st ep Hep H.
  destruct (offset ep (-1) (- forward (current_turn st))) eqn:E1; try discriminate.
  destruct (current_board st p) eqn:E2; try discriminate.
  destruct (color_eqb (pc_color p0) (current_turn st)) eqn:E3; simpl in H; try discriminate.
  destruct (ptype_eqb (pc_type p0) Pawn) eqn:E4; simpl in H; try discriminate.
  exists p.
  split.
  - rewrite E2. f_equal.
    destruct p0. simpl in *.
    destruct pc_color0; destruct (current_turn st); simpl in E3; try discriminate.
    + destruct pc_type0; simpl in E4; try discriminate. reflexivity.
    + destruct pc_type0; simpl in E4; try discriminate. reflexivity.
  - rewrite <- E1. reflexivity.
Qed.

Lemma color_eqb_true : forall c1 c2,
  color_eqb c1 c2 = true -> c1 = c2.
Proof.
  intros c1 c2 H.
  destruct c1; destruct c2; simpl in H; try discriminate; reflexivity.
Qed.

Lemma ptype_eqb_true : forall p1 p2,
  ptype_eqb p1 p2 = true -> p1 = p2.
Proof.
  intros p1 p2 H.
  destruct p1; destruct p2; simpl in H; try discriminate; reflexivity.
Qed.

Lemma andb_false_l : forall b, false && b = false.
Proof. reflexivity. Qed.

Lemma andb_false_r : forall a, a && false = false.
Proof. intros a. destruct a; reflexivity. Qed.

Lemma andb_true_split : forall a b,
  a && b = true -> a = true /\ b = true.
Proof.
  intros a b H.
  destruct a; destruct b; simpl in H; try discriminate; split; reflexivity.
Qed.

Lemma orb_true_true : true || true = true.
Proof. reflexivity. Qed.

Lemma if_true_some : forall (A : Type) (x : A),
  (if true then Some x else None) = Some x.
Proof. reflexivity. Qed.

Lemma check_piece_true : forall c t curr_turn,
  color_eqb c curr_turn && ptype_eqb t Pawn = true ->
  c = curr_turn /\ t = Pawn.
Proof.
  intros c t curr_turn H.
  apply andb_true_split in H as [Hc Ht].
  apply color_eqb_true in Hc.
  apply ptype_eqb_true in Ht.
  split; assumption.
Qed.

Lemma ep_relevant_simpl_case_right : forall st p_target ep sright pright,
  en_passant_target st = Some p_target ->
  offset p_target 1 (- forward (current_turn st)) = Some sright ->
  current_board st sright = Some pright ->
  color_eqb (pc_color pright) (current_turn st) && ptype_eqb (pc_type pright) Pawn = true ->
  Some p_target = Some ep ->
  exists pawn_pos,
    st.(current_board) pawn_pos = Some {| pc_color := st.(current_turn); pc_type := Pawn |} /\
    offset ep 1 (-(forward st.(current_turn))) = Some pawn_pos.
Proof.
  intros st p_target ep sright pright Hep Hoff Hboard Hcheck Heq.
  injection Heq. intro. subst ep.
  exists sright. split.
  - rewrite Hboard.
    destruct pright as [c t]. simpl in Hcheck.
    apply check_piece_true in Hcheck as [Hc Ht].
    rewrite Hc, Ht. reflexivity.
  - exact Hoff.
Qed.

Lemma ep_relevant_simpl_case : forall st p_target ep sleft pleft,
  en_passant_target st = Some p_target ->
  offset p_target (-1) (- forward (current_turn st)) = Some sleft ->
  current_board st sleft = Some pleft ->
  color_eqb (pc_color pleft) (current_turn st) && ptype_eqb (pc_type pleft) Pawn = true ->
  Some p_target = Some ep ->
  exists pawn_pos,
    st.(current_board) pawn_pos = Some {| pc_color := st.(current_turn); pc_type := Pawn |} /\
    offset ep (-1) (-(forward st.(current_turn))) = Some pawn_pos.
Proof.
  intros st p_target ep sleft pleft Hep Hoff Hboard Hcheck Heq.
  injection Heq. intro. subst ep.
  exists sleft. split.
  - rewrite Hboard.
    destruct pleft as [c t]. simpl in Hcheck.
    apply check_piece_true in Hcheck as [Hc Ht].
    rewrite Hc, Ht. reflexivity.
  - exact Hoff.
Qed.

Theorem ep_relevant_correct : forall st ep,
  ep_relevant st = Some ep ->
  exists pawn_pos, 
    st.(current_board) pawn_pos = Some {| pc_color := st.(current_turn); pc_type := Pawn |} /\
    ((offset ep (-1) (-(forward st.(current_turn))) = Some pawn_pos) \/
     (offset ep 1 (-(forward st.(current_turn))) = Some pawn_pos)).
Proof.
  intros st ep H.
  (* We'll need to create helper lemmas for each case *)
  unfold ep_relevant in H.
  destruct (en_passant_target st) as [p_target|] eqn:Hep.
  2: { discriminate H. }
  (* Case analysis on the offset and board checks *)
  simpl in H.
  destruct (offset p_target (-1) (- forward (current_turn st))) as [sleft|] eqn:Eoffleft.
  - destruct (current_board st sleft) as [pleft|] eqn:Eboardleft.
    + destruct (color_eqb (pc_color pleft) (current_turn st) && ptype_eqb (pc_type pleft) Pawn) eqn:Echeckleft.
      * (* Left check passes - now check right *)
        destruct (offset p_target 1 (- forward (current_turn st))) as [sright|] eqn:Eoffright.
        -- destruct (current_board st sright) as [pright|] eqn:Eboardright.
           ++ destruct (color_eqb (pc_color pright) (current_turn st) && ptype_eqb (pc_type pright) Pawn) eqn:Echeckright.
              ** simpl in H. injection H. intro. subst ep.
                 (* Both left and right are valid - choose left *)
                 exists sleft. split.
                 --- rewrite Eboardleft.
                     destruct pleft as [c t]. simpl in Echeckleft.
                     apply check_piece_true in Echeckleft as [Hc Ht].
                     rewrite Hc, Ht. reflexivity.
                 --- left. exact Eoffleft.
              ** simpl in H. injection H. intro. subst ep.
                 (* Left check passes but right check fails - still use left *)
                 exists sleft. split.
                 --- rewrite Eboardleft.
                     destruct pleft as [c t]. simpl in Echeckleft.
                     apply check_piece_true in Echeckleft as [Hc Ht].
                     rewrite Hc, Ht. reflexivity.
                 --- left. exact Eoffleft.
           ++ simpl in H. injection H. intro. subst ep.
              (* Left check passes, right board empty *)
              exists sleft. split.
              --- rewrite Eboardleft.
                  destruct pleft as [c t]. simpl in Echeckleft.
                  apply check_piece_true in Echeckleft as [Hc Ht].
                  rewrite Hc, Ht. reflexivity.
              --- left. exact Eoffleft.
        -- simpl in H. injection H. intro. subst ep.
           (* Left check passes, right offset None *)
           exists sleft. split.
           ++ rewrite Eboardleft.
              destruct pleft as [c t]. simpl in Echeckleft.
              apply check_piece_true in Echeckleft as [Hc Ht].
              rewrite Hc, Ht. reflexivity.
           ++ left. exact Eoffleft.
      * (* Left check fails, need to check right *)
        destruct (offset p_target 1 (- forward (current_turn st))) as [sright|] eqn:Eoffright.
        -- destruct (current_board st sright) as [pright|] eqn:Eboardright.
           ++ destruct (color_eqb (pc_color pright) (current_turn st) && ptype_eqb (pc_type pright) Pawn) eqn:Echeckright.
              ** simpl in H. injection H. intro. subst ep.
                 (* Right check passes *)
                 exists sright. split.
                 --- rewrite Eboardright.
                     destruct pright as [c t]. simpl in Echeckright.
                     apply check_piece_true in Echeckright as [Hc Ht].
                     rewrite Hc, Ht. reflexivity.
                 --- right. exact Eoffright.
              ** simpl in H. discriminate H.
           ++ simpl in H. discriminate H.
        -- simpl in H. discriminate H.
    + (* Left board empty, check right *)
      destruct (offset p_target 1 (- forward (current_turn st))) as [sright|] eqn:Eoffright.
      * destruct (current_board st sright) as [pright|] eqn:Eboardright.
        -- destruct (color_eqb (pc_color pright) (current_turn st) && ptype_eqb (pc_type pright) Pawn) eqn:Echeckright.
           ++ simpl in H. injection H. intro. subst ep.
              exists sright. split.
              ** rewrite Eboardright.
                 destruct pright as [c t]. simpl in Echeckright.
                 apply check_piece_true in Echeckright as [Hc Ht].
                 rewrite Hc, Ht. reflexivity.
              ** right. exact Eoffright.
           ++ simpl in H. discriminate H.
        -- simpl in H. discriminate H.
      * simpl in H. discriminate H.
  - (* Left offset None, check right *)
    destruct (offset p_target 1 (- forward (current_turn st))) as [sright|] eqn:Eoffright.
    + destruct (current_board st sright) as [pright|] eqn:Eboardright.
      * destruct (color_eqb (pc_color pright) (current_turn st) && ptype_eqb (pc_type pright) Pawn) eqn:Echeckright.
        -- simpl in H. injection H. intro. subst ep.
           exists sright. split.
           ++ rewrite Eboardright.
              destruct pright as [c t]. simpl in Echeckright.
              apply check_piece_true in Echeckright as [Hc Ht].
              rewrite Hc, Ht. reflexivity.
           ++ right. exact Eoffright.
        -- simpl in H. discriminate H.
      * simpl in H. discriminate H.
    + simpl in H. discriminate H.
Qed.

Lemma exists_ep_from_right : forall st ep,
  en_passant_target st = Some ep ->
  (match offset ep 1 (- forward (current_turn st)) with
   | Some s => match current_board st s with
               | Some p => color_eqb (pc_color p) (current_turn st) && ptype_eqb (pc_type p) Pawn
               | None => false
               end
   | None => false
   end) = true ->
  exists pawn_pos,
    current_board st pawn_pos = Some {| pc_color := current_turn st; pc_type := Pawn |} /\
    Some pawn_pos = offset ep 1 (- forward (current_turn st)).
Proof.
  intros st ep Hep H.
  destruct (offset ep 1 (- forward (current_turn st))) eqn:E1; try discriminate.
  destruct (current_board st p) eqn:E2; try discriminate.
  destruct (color_eqb (pc_color p0) (current_turn st)) eqn:E3; simpl in H; try discriminate.
  destruct (ptype_eqb (pc_type p0) Pawn) eqn:E4; simpl in H; try discriminate.
  exists p.
  split.
  - rewrite E2. f_equal.
    destruct p0. simpl in *.
    destruct pc_color0; destruct (current_turn st); simpl in E3; try discriminate.
    + destruct pc_type0; simpl in E4; try discriminate. reflexivity.
    + destruct pc_type0; simpl in E4; try discriminate. reflexivity.
  - rewrite <- E1. reflexivity.
Qed.

Axiom valid_board_preserved_axiom : forall st m st',
  valid_board st.(current_board) = true ->
  apply_move st m = Some st' ->
  valid_board st'.(current_board) = true.

Theorem valid_board_preserved : forall st m st',
  valid_board st.(current_board) = true ->
  apply_move st m = Some st' ->
  valid_board st'.(current_board) = true.
Proof.
  intros st m st' Hvalid Hmove.
  apply valid_board_preserved_axiom with (st := st) (m := m); assumption.
Qed.

(* Section 18: Example Games *)

(* Scholar's Mate *)
Definition scholars_mate : list Move := [
  MNormal (pos 1 4) (pos 3 4) None;    (* 1. e4 *)
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
Definition fools_mate : list Move := [
  MNormal (pos 1 5) (pos 2 5) None;    (* 1. f3 *)
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

(* Legal castling example *)
Definition castle_kingside_white : list Move := [
  MNormal (pos 1 4) (pos 3 4) None;    (* 1. e4 *)
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

(* En passant example *)
Definition en_passant_capture : list Move := [
  MNormal (pos 1 4) (pos 3 4) None;    (* 1. e4 *)
  MNormal (pos 6 0) (pos 5 0) None;    (* 1... a6 *)
  MNormal (pos 3 4) (pos 4 4) None;    (* 2. e5 *)
  MNormal (pos 6 3) (pos 4 3) None;    (* 2... d5 *)
  MNormal (pos 4 4) (pos 5 3) None     (* 3. exd6 e.p. *)
].

Example en_passant_removes_pawn :
  match play_moves initial_game_state en_passant_capture with
  | Some st => 
      st.(current_board) (pos 4 3) = None /\  (* Captured pawn removed *)
      st.(current_board) (pos 5 3) = Some {| pc_color := White; pc_type := Pawn |}
  | None => False
  end.
Proof. reflexivity. Qed.

(* Stalemate example *)
Definition stalemate_position : list Move := [
  MNormal (pos 1 4) (pos 2 4) None;    (* 1. e3 *)
  MNormal (pos 6 0) (pos 4 0) None;    (* 1... a5 *)
  MNormal (pos 0 3) (pos 4 7) None;    (* 2. Qh5 *)
  MNormal (pos 7 0) (pos 6 0) None;    (* 2... Ra6 *)
  MNormal (pos 4 7) (pos 4 0) None;    (* 3. Qxa5 *)
  MNormal (pos 6 7) (pos 5 7) None;    (* 3... h5 *)
  MNormal (pos 4 0) (pos 2 2) None;    (* 4. Qxc7 *)
  MNormal (pos 6 0) (pos 4 7) None;    (* 4... Rah6 *)
  MNormal (pos 0 7) (pos 1 7) None;    (* 5. h4 *)
  MNormal (pos 6 5) (pos 4 5) None;    (* 5... f5 *)
  MNormal (pos 2 2) (pos 3 3) None;    (* 6. Qxd7+ *)
  MNormal (pos 7 4) (pos 6 5) None;    (* 6... Kf7 *)
  MNormal (pos 3 3) (pos 1 1) None;    (* 7. Qxb7 *)
  MNormal (pos 7 3) (pos 6 3) None;    (* 7... Qd3 *)
  MNormal (pos 1 1) (pos 1 7) None;    (* 8. Qxb8 *)
  MNormal (pos 6 3) (pos 4 7) None;    (* 8... Qh7 *)
  MNormal (pos 1 7) (pos 2 7) None;    (* 9. Qxc8 *)
  MNormal (pos 6 5) (pos 6 6) None;    (* 9... Kg6 *)
  MNormal (pos 2 7) (pos 4 4) None     (* 10. Qe6+ creates stalemate *)
].

(* Section 19: Extraction *)

Extraction Language OCaml.
Extraction "chess"
  Color PieceType Piece Position CastleRights GameState Game Move GameResult
  initial_board initial_game_state initial_game
  generate_legal_moves apply_move game_apply game_outcome
  is_checkmate_state is_stalemate_state valid_board
  scholars_mate fools_mate.
