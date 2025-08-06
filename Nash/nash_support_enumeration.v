
(* nash_support_enumeration.v *)
(* 
   A formalization of support enumeration for finding all Nash equilibria
   in finite two-player games. This has not been previously formalized in Coq.
   
   Author: Charles Norton
   Date: August 6th 2025
*)

(* ================================================================= *)
(*                            IMPORTS                               *)
(* ================================================================= *)

(* Standard library *)
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Init.Datatypes.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Import ListNotations.

(* Rational numbers - comprehensive imports *)
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.Qfield.
Require Import Coq.QArith.Qreduction.
Require Import Coq.QArith.Qcanon.
Require Import Coq.QArith.QOrderedType.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qminmax.
Open Scope Q_scope.

(* Mathematical Components library *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import fintype.
From mathcomp Require Import matrix.
From mathcomp Require Import bigop.

(* Set up ssreflect *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.

(* Additional tactics and utilities *)
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid.

(* ================================================================= *)
(*                     RATIONAL COMPARISONS                         *)
(* ================================================================= *)

Section QBoolComparisons.

(* Define using Qcompare *)
Definition Qle_bool (x y : Q) : bool :=
  match x ?= y with
  | Lt => true
  | Eq => true
  | Gt => false
  end.

Definition Qlt_bool (x y : Q) : bool :=
  match x ?= y with
  | Lt => true
  | Eq => false
  | Gt => false
  end.

Definition Qeq_bool (x y : Q) : bool :=
  match x ?= y with
  | Lt => false
  | Eq => true
  | Gt => false
  end.

Definition Qge_bool (x y : Q) : bool :=
  Qle_bool y x.

Definition Qgt_bool (x y : Q) : bool :=
  Qlt_bool y x.

Definition Qneq_bool (x y : Q) : bool :=
  negb (Qeq_bool x y).

End QBoolComparisons.

(* ================================================================= *)
(*                         NOTATIONS                                *)
(* ================================================================= *)

(* Notation for rationals *)
Local Notation "0" := (0#1) : Q_scope.
Local Notation "1" := (1#1) : Q_scope.

(* Comparison notations *)
Notation "x <=? y" := (Qle_bool x y) (at level 70) : Q_scope.
Notation "x <? y" := (Qlt_bool x y) (at level 70) : Q_scope.
Notation "x =? y" := (Qeq_bool x y) (at level 70) : Q_scope.
Notation "x >=? y" := (Qge_bool x y) (at level 70) : Q_scope.
Notation "x >? y" := (Qgt_bool x y) (at level 70) : Q_scope.
Notation "x !=? y" := (Qneq_bool x y) (at level 70) : Q_scope.

(* Sum notation for lists *)
Notation "'\sum_{' x 'in' l '}' f" := 
  (fold_left Qplus (map f l) 0)
  (at level 41, x at level 0, l at level 10, f at level 41,
   format "'[' \sum_{ x  in  l } '/  '  f ']'") : Q_scope.

(* Product notation for lists *)  
Notation "'\prod_{' x 'in' l '}' f" :=
  (fold_left Qmult (map f l) 1)
  (at level 41, x at level 0, l at level 10, f at level 41,
   format "'[' \prod_{ x  in  l } '/  '  f ']'") : Q_scope.

(* Finite type notation *)
Notation "[ 'fin' n ]" := ('I_n) 
  (at level 0, format "[ 'fin'  n ]") : type_scope.

(* ================================================================= *)
(*                     UTILITY FUNCTIONS                            *)
(* ================================================================= *)

Section Utilities.

(* List utilities *)
Definition flatten {A : Type} (l : list (list A)) : list A :=
  fold_left (@app A) l [].

Definition cartesian_product {A B : Type} 
           (l1 : list A) (l2 : list B) : list (A * B) :=
  flatten (map (fun a => map (fun b => (a, b)) l2) l1).

(* Decidable equality for naturals *)
Definition beq_nat (n m : nat) : bool :=
  Nat.eqb n m.

(* List membership *)
Fixpoint mem_list {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
         (a : A) (l : list A) : bool :=
  match l with
  | [] => false
  | h :: t => 
      match eq_dec a h with
      | left _ => true
      | right _ => mem_list eq_dec a t
      end
  end.

(* Power set generation *)
Fixpoint powerset {A : Type} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | h :: t => 
      let ps := powerset t in
      ps ++ map (cons h) ps
  end.

(* Non-empty subsets only *)
Definition nonempty_powerset {A : Type} (l : list A) : list (list A) :=
  filter (fun s => match s with [] => false | _ => true end) (powerset l).

(* Check if a list has no duplicates *)
Fixpoint no_dup {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) 
         (l : list A) : bool :=
  match l with
  | [] => true
  | h :: t => andb (negb (mem_list eq_dec h t)) (no_dup eq_dec t)
  end.

End Utilities.


(* ================================================================= *)
(*                    BASIC DEFINITIONS                             *)
(* ================================================================= *)

Section GameBasics.

(* Player type *)
Inductive player : Type := P1 | P2.

Definition other (p : player) : player :=
  match p with
  | P1 => P2
  | P2 => P1
  end.

Lemma other_other (p : player) : other (other p) = p.
Proof.
  case: p; reflexivity.
Qed.

Lemma other_injective (p1 p2 : player) : other p1 = other p2 -> p1 = p2.
Proof.
  case: p1; case: p2; simpl; intros H.
  - reflexivity.
  - discriminate.
  - discriminate.
  - reflexivity.
Qed.

(* Decidable equality for players *)
Definition player_eq_dec (p1 p2 : player) : {p1 = p2} + {p1 <> p2}.
Proof.
  decide equality.
Defined.

End GameBasics.

Section GameTheory.

(* Game parameters *)
Variables (n1 n2 : nat).
Hypothesis n1_pos : (0 < n1)%nat.
Hypothesis n2_pos : (0 < n2)%nat.

(* Action spaces using finite types *)
Definition action (p : player) : Type :=
  match p with
  | P1 => [fin n1]
  | P2 => [fin n2]
  end.

(* Pure strategy profile *)
Definition pure_profile : Type := ([fin n1] * [fin n2])%type.

(* Utility functions *)
Definition utility_fn := pure_profile -> Q.

(* A game is a pair of utility functions *)
Record game := mkGame {
  u1 : utility_fn;  (* Player 1's utility *)
  u2 : utility_fn;  (* Player 2's utility *)
}.

(* Helper to get utility for either player *)
Definition utility (g : game) (p : player) : utility_fn :=
  match p with
  | P1 => u1 g
  | P2 => u2 g
  end.
  
(* Enumerate all actions for a player *)
Definition enum_actions (p : player) : list (action p) :=
  match p as p' return list (action p') with
  | P1 => enum [fin n1]
  | P2 => enum [fin n2]
  end.

(* Just check it compiles for now - we can prove properties later *)
Check enum_actions P1.
Check enum_actions P2.

(* Mixed strategy as probability distribution over actions *)
Record mixed_strategy (p : player) := mkMixed {
  prob_mass : action p -> Q;
  prob_nonneg : forall a, 0 <= prob_mass a;
  prob_sum_one : fold_left Qplus (map prob_mass (enum_actions p)) 0 = 1
}.

(* Mixed strategy profile *)
Definition mixed_profile := (mixed_strategy P1 * mixed_strategy P2)%type.

(* Expected utility under mixed strategies *)
Definition expected_utility (g : game) (p : player) (σ : mixed_profile) : Q :=
  let (σ1, σ2) := σ in
  fold_left Qplus
    (map (fun a1 => 
      fold_left Qplus
        (map (fun a2 =>
          (prob_mass σ1 a1) * (prob_mass σ2 a2) * 
          (utility g p (a1, a2)))
        (enum_actions P2))
      0)
    (enum_actions P1))
  0.
  
(* Support is a non-empty subset of actions *)
Record support (p : player) := mkSupport {
  actions_in_support : list (action p);
  support_nonempty : actions_in_support <> nil
}.

(* Check if action is in support *)
Definition in_support {p : player} (a : action p) (s : support p) : bool :=
  match p as p' return action p' -> support p' -> bool with
  | P1 => fun (a' : [fin n1]) (s' : support P1) => 
      List.existsb (fun x => Nat.eqb (nat_of_ord a') (nat_of_ord x)) (actions_in_support s')
  | P2 => fun (a' : [fin n2]) (s' : support P2) => 
      List.existsb (fun x => Nat.eqb (nat_of_ord a') (nat_of_ord x)) (actions_in_support s')
  end a s.

(* Best response value for a pure action against opponent's mixed strategy *)
Definition best_response_value (g : game) (p : player) 
          (a : action p) (σ_opp : mixed_strategy (other p)) : Q :=
  match p as p' return action p' -> mixed_strategy (other p') -> Q with
  | P1 => fun (a1 : [fin n1]) σ2 =>
      fold_left Qplus
        (map (fun a2 => (prob_mass σ2 a2) * (utility g P1 (a1, a2)))
             (enum_actions P2))
        0
  | P2 => fun (a2 : [fin n2]) σ1 =>
      fold_left Qplus
        (map (fun a1 => (prob_mass σ1 a1) * (utility g P2 (a1, a2)))
             (enum_actions P1))
        0
  end a σ_opp.
  
(* Check if all actions in support yield same payoff (indifference condition) *)
Definition indifferent_in_support (g : game) (p : player)
          (s : support p) (σ_opp : mixed_strategy (other p)) : bool :=
  let acts := actions_in_support s in
  match acts with
  | [] => false  
  | a :: rest =>
      let v := @best_response_value g p a σ_opp in
      List.forallb (fun a' => 
        Qeq_bool (@best_response_value g p a' σ_opp) v
      ) rest
  end.
  
  (* Check that all actions in support are best responses *)
Definition support_is_best_response (g : game) (p : player)
          (s : support p) (σ_opp : mixed_strategy (other p)) : bool :=
  match actions_in_support s with
  | [] => false
  | a :: _ =>
      let v_support := @best_response_value g p a σ_opp in
      List.forallb (fun a' => 
        if in_support a' s
        then true  (* Already checked in indifference *)
        else Qle_bool (@best_response_value g p a' σ_opp) v_support
      ) (enum_actions p)
  end.
  
  (* Check if mixed strategy is consistent with support *)
Definition consistent_with_support {p : player} 
          (σ : mixed_strategy p) (s : support p) : bool :=
  List.forallb (fun a => 
    if in_support a s 
    then Qlt_bool 0 (prob_mass σ a)
    else Qeq_bool (prob_mass σ a) 0
  ) (enum_actions p).
  
  (* Simple linear system representation *)
Record linear_system := mkSystem {
  num_vars : nat;
  num_constraints : nat;
  matrix : list (list Q);  (* Coefficient matrix *)
  rhs : list Q;            (* Right-hand side *)
}.

(* Row operations for Gaussian elimination *)

(* Scale a row by a non-zero rational *)
Definition scale_row (r : list Q) (c : Q) : list Q :=
  map (fun x => c * x) r.

(* Add c times row r1 to row r2 *)
Fixpoint add_scaled_row (r1 r2 : list Q) (c : Q) : list Q :=
  match r1, r2 with
  | [], _ => r2
  | _, [] => []
  | x1::r1', x2::r2' => (x2 + c * x1) :: add_scaled_row r1' r2' c
  end.

(* Swap two rows in a matrix *)
Definition swap_rows (m : list (list Q)) (i j : nat) : list (list Q) :=
  let ri := List.nth i m [] in
  let rj := List.nth j m [] in
  map (fun k => if Nat.eqb k i then rj
                else if Nat.eqb k j then ri
                else List.nth k m [])
      (iota 0 (List.length m)).

(* Find pivot row (row with non-zero element in column col starting from row start_row) *)
Fixpoint find_pivot_helper (m : list (list Q)) (col : nat) (rows : list nat) : option nat :=
  match rows with
  | [] => None
  | row :: rest =>
      let elem := List.nth col (List.nth row m []) 0 in
      if negb (Qeq_bool elem 0)
      then Some row
      else find_pivot_helper m col rest
  end.

Definition find_pivot (m : list (list Q)) (col : nat) (start_row : nat) : option nat :=
  find_pivot_helper m col (iota start_row (List.length m - start_row)).
  
(* Replace nth element in a list *)
Fixpoint list_replace {A : Type} (l : list A) (n : nat) (x : A) : list A :=
  match l, n with
  | [], _ => []
  | _ :: t, O => x :: t
  | h :: t, S n' => h :: list_replace t n' x
  end.

(* Eliminate column col below row pivot_row *)
Definition eliminate_column (m : list (list Q)) (b : list Q) 
                           (pivot_row col : nat) : (list (list Q) * list Q) :=
  let pivot_val := List.nth col (List.nth pivot_row m []) 0 in
  if Qeq_bool pivot_val 0 then (m, b)  (* Can't eliminate with zero pivot *)
  else
    let process_row := fun (acc : list (list Q) * list Q) (row_idx : nat) =>
      match acc with
      | (m_acc, b_acc) =>
          if Nat.eqb row_idx pivot_row then acc
          else
            let elem := List.nth col (List.nth row_idx m_acc []) 0 in
            if Qeq_bool elem 0 then acc  (* Already zero *)
            else
              let factor := -(elem / pivot_val) in
              let old_row := List.nth row_idx m_acc [] in
              let pivot_row_vals := List.nth pivot_row m_acc [] in
              let new_row := add_scaled_row pivot_row_vals old_row factor in
              let old_b := List.nth row_idx b_acc 0 in
              let pivot_b := List.nth pivot_row b_acc 0 in
              let new_b := old_b + factor * pivot_b in
              (list_replace m_acc row_idx new_row, list_replace b_acc row_idx new_b)
      end
    in
    fold_left process_row (iota 0 (List.length m)) (m, b).

(* Forward elimination - reduce to row echelon form *)
Fixpoint forward_elimination_aux (m : list (list Q)) (b : list Q) 
                                 (col row : nat) (fuel : nat) : (list (list Q) * list Q) :=
  match fuel with
  | O => (m, b)
  | S fuel' =>
      if Nat.ltb row (List.length m) && Nat.ltb col (List.length (List.hd [] m)) then
        match find_pivot m col row with
        | None => forward_elimination_aux m b (col + 1) row fuel'  (* No pivot, try next column *)
        | Some pivot_row =>
            (* Swap rows if needed *)
            let m' := if Nat.eqb pivot_row row then m else swap_rows m row pivot_row in
            let b' := if Nat.eqb pivot_row row then b else
                       let tmp_b := List.nth row b 0 in
                       let b1 := list_replace b row (List.nth pivot_row b 0) in
                       list_replace b1 pivot_row tmp_b in
            (* Eliminate column below pivot *)
            let (m'', b'') := eliminate_column m' b' row col in
            forward_elimination_aux m'' b'' (col + 1) (row + 1) fuel'
        end
      else (m, b)
  end.

Definition forward_elimination (m : list (list Q)) (b : list Q) : (list (list Q) * list Q) :=
  forward_elimination_aux m b 0 0 (List.length m * List.length (List.hd [] m)).

(* Find first non-zero element in a row *)
Fixpoint find_first_nonzero (r : list Q) (idx : nat) : option nat :=
  match r with
  | [] => None
  | h :: t => if negb (Qeq_bool h 0) then Some idx else find_first_nonzero t (idx + 1)
  end.

(* Compute sum of known variables in back substitution *)
Definition compute_known_sum (row : list Q) (solution : list Q) (start_col : nat) : Q :=
  fold_left Qplus 
    (map (fun i => (List.nth i row 0) * (List.nth i solution 0))
         (iota start_col (List.length row - start_col))) 0.

(* Back substitution for upper triangular system *)
Fixpoint back_substitution_aux (m : list (list Q)) (b : list Q) 
                               (row : nat) (solution : list Q) : option (list Q) :=
  match row with
  | O => 
      let r := List.nth 0 m [] in
      let pivot_col := find_first_nonzero r 0 in
      match pivot_col with
      | None => if Qeq_bool (List.nth 0 b 0) 0 then Some solution else None
      | Some col =>
          let pivot_val := List.nth col r 0 in
          let rhs := List.nth 0 b 0 in
          let sum := compute_known_sum r solution (col + 1) in
          let x_val := (rhs - sum) / pivot_val in
          Some (list_replace solution col x_val)
      end
  | S row' =>
      let r := List.nth row m [] in
      let pivot_col := find_first_nonzero r 0 in
      match pivot_col with
      | None => if Qeq_bool (List.nth row b 0) 0 then back_substitution_aux m b row' solution else None
      | Some col =>
          let pivot_val := List.nth col r 0 in
          let rhs := List.nth row b 0 in
          let sum := compute_known_sum r solution (col + 1) in
          let x_val := (rhs - sum) / pivot_val in
          back_substitution_aux m b row' (list_replace solution col x_val)
      end
  end.
  
  (* Solve linear system using Gaussian elimination *)
Definition solve_linear_system (sys : linear_system) : option (list Q) :=
  let m := matrix sys in
  let b := rhs sys in
  let n := num_vars sys in
  (* Forward elimination *)
  let (m_upper, b_upper) := forward_elimination m b in
  (* Back substitution *)
  let initial_solution := List.repeat 0 n in
  if Nat.eqb (List.length m) 0 then None
  else back_substitution_aux m_upper b_upper (List.length m - 1) initial_solution.
  
  (* Build indifference system for player p with support s *)
Definition build_indifference_system (g : game) (p : player) 
          (s : support p) : linear_system :=
  let acts := actions_in_support s in
  let n := List.length acts in
  match acts with
  | [] => mkSystem 0 0 [] []  (* Can't happen due to support_nonempty *)
  | a0 :: rest =>
      (* For each pair of actions in support, add equality constraint *)
      let constraints := map (fun a =>
        (* Constraint: BR(a0) - BR(a) = 0 *)
        let row := match p with
          | P1 => 
              (* Coefficients are differences in utilities *)
              map (fun (a2 : action P2) =>
                (utility g P1 (a0, a2)) - (utility g P1 (a, a2))
              ) (enum_actions P2)
          | P2 =>
              map (fun (a1 : action P1) =>
                (utility g P2 (a1, a0)) - (utility g P2 (a1, a))
              ) (enum_actions P1)
          end in
        row
      ) rest in
      (* Add probability sum = 1 constraint *)
      let prob_constraint := List.repeat 1 (match p with P1 => n2 | P2 => n1 end) in
      let all_constraints := constraints ++ [prob_constraint] in
      let rhs_vals := (List.repeat 0 (List.length rest)) ++ [1] in
      mkSystem (match p with P1 => n2 | P2 => n1 end) 
               (List.length all_constraints)
               all_constraints 
               rhs_vals
  end.
