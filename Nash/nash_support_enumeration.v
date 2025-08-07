
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
  match p as p' return support p' -> linear_system with
  | P1 => fun (s1 : support P1) =>
      match actions_in_support s1 with
      | [] => mkSystem 0 0 [] []
      | a0 :: rest =>
          let constraints := map (fun (a : action P1) =>
            map (fun (a2 : action P2) =>
              (utility g P1 (a0, a2)) - (utility g P1 (a, a2))
            ) (enum_actions P2)
          ) rest in
          let prob_constraint := List.repeat 1 n2 in
          let all_constraints := constraints ++ [prob_constraint] in
          let rhs_vals := (List.repeat 0 (List.length rest)) ++ [1] in
          mkSystem n2 (List.length all_constraints) all_constraints rhs_vals
      end
  | P2 => fun (s2 : support P2) =>
      match actions_in_support s2 with
      | [] => mkSystem 0 0 [] []
      | a0 :: rest =>
          let constraints := map (fun (a : action P2) =>
            map (fun (a1 : action P1) =>
              (utility g P2 (a1, a0)) - (utility g P2 (a1, a))
            ) (enum_actions P1)
          ) rest in
          let prob_constraint := List.repeat 1 n1 in
          let all_constraints := constraints ++ [prob_constraint] in
          let rhs_vals := (List.repeat 0 (List.length rest)) ++ [1] in
          mkSystem n1 (List.length all_constraints) all_constraints rhs_vals
      end
  end s.
  
(* Build mixed strategy from probabilities (returns None if invalid) *)
Definition build_mixed_from_probs_unchecked (p : player) (probs : list Q) 
          : (action p -> Q) :=
  match p as p' return (action p' -> Q) with
  | P1 => fun (a : [fin n1]) => List.nth (nat_of_ord a) probs 0
  | P2 => fun (a : [fin n2]) => List.nth (nat_of_ord a) probs 0
  end.
  
(* Check if probabilities are valid for a mixed strategy *)
Definition valid_probs (probs : list Q) : bool :=
  List.forallb (fun q => Qle_bool 0 q) probs && 
  Qeq_bool (fold_left Qplus probs 0) 1.
  
  (* Check if probability functions satisfy Nash conditions *)
Definition check_nash_conditions (g : game) 
          (s1 : support P1) (s2 : support P2)
          (prob1 : action P1 -> Q) (prob2 : action P2 -> Q) : bool :=
  (* Build pseudo mixed strategies for checking *)
  let check_indiff_1 := 
    match actions_in_support s1 with
    | [] => false
    | a :: rest =>
        let v := fold_left Qplus 
          (map (fun a2 => prob2 a2 * utility g P1 (a, a2)) (enum_actions P2)) 0 in
        List.forallb (fun a' =>
          let v' := fold_left Qplus 
            (map (fun a2 => prob2 a2 * utility g P1 (a', a2)) (enum_actions P2)) 0 in
          Qeq_bool v v'
        ) rest
    end in
  let check_indiff_2 := 
    match actions_in_support s2 with
    | [] => false  
    | a :: rest =>
        let v := fold_left Qplus
          (map (fun a1 => prob1 a1 * utility g P2 (a1, a)) (enum_actions P1)) 0 in
        List.forallb (fun a' =>
          let v' := fold_left Qplus
            (map (fun a1 => prob1 a1 * utility g P2 (a1, a')) (enum_actions P1)) 0 in
          Qeq_bool v v'
        ) rest
    end in
  check_indiff_1 && check_indiff_2.
  
(* Helper lemma: extract non-negativity from valid_probs *)
Lemma valid_probs_nonneg (probs : list Q) :
  valid_probs probs = true ->
  forall i, (i < List.length probs)%nat -> 0 <= List.nth i probs 0.
Proof.
  unfold valid_probs.
  intro H.
  destruct (andb_prop _ _ H) as [H_all H_sum].
  intros i Hi.
  clear H_sum H.
  revert i Hi.
  induction probs as [|h t IH]; intros i Hi.
  - simpl in Hi. inversion Hi.
  - destruct i.
    + simpl in H_all.
      destruct (andb_prop _ _ H_all) as [H_h _].
      simpl.
      unfold Qle_bool in H_h.
      destruct (0 ?= h) eqn:E.
      * (* Case: 0 = h *)
        apply Qeq_alt in E. rewrite <- E. apply Qle_refl.
      * (* Case: 0 < h *)
        apply Qlt_alt in E. apply Qlt_le_weak. exact E.
      * (* Case: 0 > h - impossible *)
        discriminate H_h.
    + simpl in H_all.
      destruct (andb_prop _ _ H_all) as [_ H_t].
      simpl.
      apply IH.
      * exact H_t.
      * simpl in Hi.
        by move: Hi; rewrite !ltnS.
Qed.

(* For now, let's just keep the weaker property *)
Lemma valid_probs_sum_one_Qeq (probs : list Q) :
  valid_probs probs = true ->
  Qeq (fold_left Qplus probs 0) 1.
Proof.
  unfold valid_probs.
  intro H.
  destruct (andb_prop _ _ H) as [_ H_sum].
  unfold Qeq_bool in H_sum.
  destruct (fold_left Qplus probs 0 ?= 1) eqn:E.
  - (* When Qcompare returns Eq, we have Qeq *)
    apply Qeq_alt.
    exact E.
  - discriminate H_sum.
  - discriminate H_sum.
Qed.

(* Redefine mixed strategy to use Qeq for the sum constraint *)
Record mixed_strategy_eq (p : player) := mkMixedEq {
  prob_mass_eq : action p -> Q;
  prob_nonneg_eq : forall a, 0 <= prob_mass_eq a;
  prob_sum_one_eq : Qeq (fold_left Qplus (map prob_mass_eq (enum_actions p)) 0) 1
}.

(* Mixed strategy profile with the new definition *)
Definition mixed_profile_eq := (mixed_strategy_eq P1 * mixed_strategy_eq P2)%type.

(* Expected utility works the same way *)
Definition expected_utility_eq (g : game) (p : player) (σ : mixed_profile_eq) : Q :=
  let (σ1, σ2) := σ in
  fold_left Qplus
    (map (fun a1 => 
      fold_left Qplus
        (map (fun a2 =>
          (prob_mass_eq σ1 a1) * (prob_mass_eq σ2 a2) * 
          (utility g p (a1, a2)))
        (enum_actions P2))
      0)
    (enum_actions P1))
  0.

(* Helper: length of probs matches number of actions *)
Lemma probs_length_P1 (probs : list Q) :
  List.length probs = n1 ->
  forall a : [fin n1], (nat_of_ord a < List.length probs)%nat.
Proof.
  intro H.
  intro a.
  rewrite H.
  exact (ltn_ord a).
Qed.

Lemma probs_length_P2 (probs : list Q) :
  List.length probs = n2 ->
  forall a : [fin n2], (nat_of_ord a < List.length probs)%nat.
Proof.
  intro H.
  intro a.
  rewrite H.
  exact (ltn_ord a).
Qed.

(* Simpler: just check if a probability list gives a valid mixed strategy *)
Definition check_mixed_strategy_P1 (probs : list Q) : bool :=
  (Nat.eqb (List.length probs) n1) &&
  valid_probs probs.

Definition check_mixed_strategy_P2 (probs : list Q) : bool :=
  (Nat.eqb (List.length probs) n2) &&
  valid_probs probs.
  
  (* Simple representation of a mixed strategy as a probability list *)
Definition mixed_as_probs_P1 := list Q.
Definition mixed_as_probs_P2 := list Q.

(* Check if two probability lists form a Nash equilibrium with given supports *)
Definition check_nash_with_probs (g : game) 
          (s1 : support P1) (s2 : support P2)
          (probs1 : mixed_as_probs_P1) (probs2 : mixed_as_probs_P2) : bool :=
  (* First check valid probabilities *)
  let valid1 := check_mixed_strategy_P1 probs1 in
  let valid2 := check_mixed_strategy_P2 probs2 in
  (* Build probability functions - using @ for explicit application *)
  let prob_fn1 := @build_mixed_from_probs_unchecked P1 probs1 in
  let prob_fn2 := @build_mixed_from_probs_unchecked P2 probs2 in
  (* Check Nash conditions *)
  let nash_ok := check_nash_conditions g s1 s2 prob_fn1 prob_fn2 in
  (* Check support consistency for P1 *)
  let support1_ok := List.forallb (fun a => 
    if in_support a s1 
    then Qlt_bool 0 (List.nth (nat_of_ord a) probs1 0)
    else Qeq_bool (List.nth (nat_of_ord a) probs1 0) 0
  ) (enum_actions P1) in
  (* Check support consistency for P2 *)
  let support2_ok := List.forallb (fun a => 
    if in_support a s2
    then Qlt_bool 0 (List.nth (nat_of_ord a) probs2 0)
    else Qeq_bool (List.nth (nat_of_ord a) probs2 0) 0
  ) (enum_actions P2) in
  (* Combine all checks *)
  valid1 && valid2 && nash_ok && support1_ok && support2_ok.
  
(* Find Nash equilibrium with given supports *)
Definition find_nash_with_support (g : game) 
          (s1 : support P1) (s2 : support P2) : option (mixed_as_probs_P1 * mixed_as_probs_P2) :=
  (* Build and solve linear system for P1 *)
  let sys1 := @build_indifference_system g P1 s1 in
  match solve_linear_system sys1 with
  | None => None
  | Some probs1 =>
      (* Build and solve linear system for P2 *)
      let sys2 := @build_indifference_system g P2 s2 in
      match solve_linear_system sys2 with
      | None => None
      | Some probs2 =>
          (* Check if the solution is valid *)
          if check_nash_with_probs g s1 s2 probs1 probs2
          then Some (probs1, probs2)
          else None
      end
  end.

(* Helper to create support from non-empty list *)
Program Definition support_from_nonempty_list (p : player) (acts : list (action p)) 
        (H : acts <> nil) : support p :=
  @mkSupport p acts H.

(* Generate all non-empty supports for P1 - simplified version *)
Definition all_supports_P1_simple : list (list (action P1)) :=
  nonempty_powerset (enum_actions P1).

(* Generate all non-empty supports for P2 - simplified version *)
Definition all_supports_P2_simple : list (list (action P2)) :=
  nonempty_powerset (enum_actions P2).

(* Helper lemma: cons is not nil *)
Lemma cons_not_nil {A : Type} (h : A) (t : list A) : h :: t <> [].
Proof.
  discriminate.
Qed.

(* Find Nash equilibrium for a specific support pair given as lists *)
Definition find_nash_with_support_lists (g : game) 
          (acts1 : list (action P1)) (acts2 : list (action P2)) 
          : option (mixed_as_probs_P1 * mixed_as_probs_P2) :=
  match acts1, acts2 with
  | [], _ => None
  | _, [] => None
  | h1 :: t1, h2 :: t2 =>
      (* Create supports with proofs *)
      let s1 := @mkSupport P1 (h1 :: t1) (@cons_not_nil (action P1) h1 t1) in
      let s2 := @mkSupport P2 (h2 :: t2) (@cons_not_nil (action P2) h2 t2) in
      find_nash_with_support g s1 s2
  end.
  
(* Main algorithm: find ALL Nash equilibria *)
Definition find_all_nash (g : game) : list (mixed_as_probs_P1 * mixed_as_probs_P2) :=
  let support_pairs := cartesian_product all_supports_P1_simple all_supports_P2_simple in
  fold_left (fun acc (pair : list (action P1) * list (action P2)) =>
    let (acts1, acts2) := pair in
    match find_nash_with_support_lists g acts1 acts2 with
    | None => acc
    | Some nash => nash :: acc
    end
  ) support_pairs [].
  
(* Test case: Battle of Sexes (2x2 game) *)
Section TestGame.

(* Override n1 and n2 to be 2 for this test *)
Let test_n1 := 2.
Let test_n2 := 2.

(* Create a simple 2x2 game utility function *)
Definition simple_utility_P1 (p : pure_profile) : Q :=
  let (a1, a2) := p in
  if (Nat.eqb (nat_of_ord a1) 0) && (Nat.eqb (nat_of_ord a2) 0) then 2#1  (* (0,0) -> 2 *)
  else if (Nat.eqb (nat_of_ord a1) 1) && (Nat.eqb (nat_of_ord a2) 1) then 1#1  (* (1,1) -> 1 *)
  else 0#1.  (* off-diagonal -> 0 *)

Definition simple_utility_P2 (p : pure_profile) : Q :=
  let (a1, a2) := p in
  if (Nat.eqb (nat_of_ord a1) 0) && (Nat.eqb (nat_of_ord a2) 0) then 1#1  (* (0,0) -> 1 *)
  else if (Nat.eqb (nat_of_ord a1) 1) && (Nat.eqb (nat_of_ord a2) 1) then 2#1  (* (1,1) -> 2 *)
  else 0#1.  (* off-diagonal -> 0 *)

Definition battle_of_sexes : game :=
  mkGame simple_utility_P1 simple_utility_P2.

End TestGame.

(* Test computation - this will take a while to run *)
Definition test_find_nash : list (mixed_as_probs_P1 * mixed_as_probs_P2) :=
  find_all_nash battle_of_sexes.

(* For debugging, let's also create a simpler test that just checks the supports *)
Definition test_supports : list (list (action P1)) * list (list (action P2)) :=
  (all_supports_P1_simple, all_supports_P2_simple).

(* Check that we can at least enumerate supports correctly *)
Eval compute in (List.length all_supports_P1_simple).
Eval compute in (List.length all_supports_P2_simple).

(* Check if a pure strategy profile is a Nash equilibrium *)
Definition is_pure_nash (g : game) (a1 : action P1) (a2 : action P2) : bool :=
  (* Check if P1 wants to deviate *)
  let u1_current := utility g P1 (a1, a2) in
  let p1_stable := List.forallb (fun a1' =>
    Qle_bool (utility g P1 (a1', a2)) u1_current
  ) (enum_actions P1) in
  (* Check if P2 wants to deviate *)
  let u2_current := utility g P2 (a1, a2) in
  let p2_stable := List.forallb (fun a2' =>
    Qle_bool (utility g P2 (a1, a2')) u2_current
  ) (enum_actions P2) in
  p1_stable && p2_stable.

(* Find all pure Nash equilibria *)
Definition find_pure_nash (g : game) : list (action P1 * action P2) :=
  let all_profiles := cartesian_product (enum_actions P1) (enum_actions P2) in
  filter (fun (p : action P1 * action P2) => 
    let (a1, a2) := p in is_pure_nash g a1 a2
  ) all_profiles.
  
  (* Test finding pure Nash equilibria in Battle of Sexes *)
Definition test_pure_nash := find_pure_nash battle_of_sexes.

(* Let's also create a simple printer for debugging *)
Definition show_pure_profile (p : action P1 * action P2) : nat * nat :=
  let (a1, a2) := p in
  (nat_of_ord a1, nat_of_ord a2).

(* Show the pure Nash equilibria as natural number pairs *)
Definition test_pure_nash_readable := map show_pure_profile test_pure_nash.

(* Simpler test: just check if (0,0) is a pure Nash *)
Definition test_00_nash : bool := is_pure_nash battle_of_sexes (Ordinal n1_pos) (Ordinal n2_pos).

(* Simpler: just count how many pure Nash equilibria we find *)
Definition count_pure_nash : nat := List.length test_pure_nash.

(* Try vm_compute for faster evaluation *)
Eval vm_compute in count_pure_nash.

(* Evaluate to see the pure Nash equilibria *)
Eval compute in test_pure_nash_readable.

(* ================================================================= *)
(*                    CORRECTNESS PROOFS                            *)
(* ================================================================= *)

Section Correctness.

(* First, let's formally define what a Nash equilibrium is *)
Definition is_nash_equilibrium (g : game) (σ : mixed_profile_eq) : Prop :=
  let (σ1, σ2) := σ in
  (* P1 cannot improve by deviating *)
  (forall σ1' : mixed_strategy_eq P1,
    expected_utility_eq g P1 (σ1', σ2) <= expected_utility_eq g P1 (σ1, σ2)) /\
  (* P2 cannot improve by deviating *)
  (forall σ2' : mixed_strategy_eq P2,
    expected_utility_eq g P2 (σ1, σ2') <= expected_utility_eq g P2 (σ1, σ2)).
    
(* Lemma 1: enum_actions for P1 gives all ordinals in order *)
Lemma enum_actions_P1_complete : 
  map (nat_of_ord (n:=n1)) (enum_actions P1) = iota 0 n1.
Proof.
  unfold enum_actions.
  simpl.
  (* Use the fact that enum gives all ordinals *)
  have ->: map (nat_of_ord (n:=n1)) (enum [fin n1]) = 
           map val (enum [fin n1]).
  { apply map_ext. intro x. reflexivity. }
  rewrite val_enum_ord.
  reflexivity.
Qed.

(* Helper: iota shift property - more general version *)
Lemma iota_shift_general m n : iota m.+1 n = map S (iota m n).
Proof.
  induction n as [|n' IH] in m |- *.
  - reflexivity.
  - simpl. f_equal. 
    apply (IH m.+1).
Qed.

(* Now the specific case we need *)
Lemma iota_shift n : iota 1 n = map S (iota 0 n).
Proof.
  exact (iota_shift_general 0 n).
Qed.

(* Lemma 2: Indexing into a list with iota 0 (length l) recovers the list *)
Lemma nth_iota_recover (l : list Q) :
  map (fun i => List.nth i l 0) (iota 0 (List.length l)) = l.
Proof.
  induction l as [|h t IH].
  - reflexivity.
  - simpl.
    f_equal.
    (* Use the iota_shift lemma *)
    rewrite iota_shift.
    rewrite -[LHS]map_comp.
    simpl.
    exact IH.
Qed.

(* Lemma 3a: Mapping nat_of_ord preserves function composition *)
Lemma map_enum_actions_comp (f : nat -> Q) :
  map (fun a : action P1 => f (nat_of_ord a)) (enum_actions P1) = 
  map f (map (nat_of_ord (n:=n1)) (enum_actions P1)).
Proof.
  rewrite map_comp.
  reflexivity.
Qed.

(* Lemma 3b: Simplify the double map using enum_actions_P1_complete *)
Lemma map_enum_to_iota (f : nat -> Q) :
  map f (map (nat_of_ord (n:=n1)) (enum_actions P1)) = map f (iota 0 n1).
Proof.
  f_equal.
  exact enum_actions_P1_complete.
Qed.

(* Lemma 3: Mapping through enum_actions and indexing gives back probs *)
Lemma map_enum_nth_probs (probs : list Q) :
  List.length probs = n1 ->
  map (fun a : action P1 => List.nth (nat_of_ord a) probs 0) (enum_actions P1) = probs.
Proof.
  intro H_len.
  rewrite (map_enum_actions_comp (fun i => List.nth i probs 0)).
  rewrite map_enum_to_iota.
  rewrite -H_len.
  exact (nth_iota_recover probs).
Qed.

(* Lemma 4: Sum preservation *)
Lemma sum_enum_actions_probs (probs : list Q) :
  List.length probs = n1 ->
  fold_left Qplus probs 0 = 
  fold_left Qplus (map (fun a : action P1 => List.nth (nat_of_ord a) probs 0) 
                       (enum_actions P1)) 0.
Proof.
  intro H_len.
  rewrite map_enum_nth_probs; auto.
Qed.

(* Lemma to get the sum property in the right form *)
Lemma valid_probs_sum_enum_P1 (probs : list Q) :
  List.length probs = n1 ->
  valid_probs probs = true ->
  Qeq (fold_left Qplus 
       (map (fun a : action P1 => List.nth (nat_of_ord a) probs 0) 
            (enum_actions P1)) 0) 1.
Proof.
  intros H_len H_valid.
  rewrite -sum_enum_actions_probs; auto.
  apply valid_probs_sum_one_Qeq.
  exact H_valid.
Qed.

(* Helper: Build the probability mass function from a list *)
Definition probs_to_mass_fn_P1 (probs : list Q) : action P1 -> Q :=
  fun a => List.nth (nat_of_ord a) probs 0.

(* Lemma: The mass function from valid probs is non-negative *)
Lemma probs_to_mass_fn_nonneg (probs : list Q) :
  List.length probs = n1 ->
  valid_probs probs = true ->
  forall a : action P1, 0 <= probs_to_mass_fn_P1 probs a.
Proof.
  intros H_len H_valid a.
  unfold probs_to_mass_fn_P1.
  apply valid_probs_nonneg; auto.
  apply probs_length_P1; auto.
Qed.

(* Helper: Build mixed strategy from valid probability list *)
Definition build_mixed_P1 (probs : list Q) (H_len : List.length probs = n1) 
           (H_valid : valid_probs probs = true) : mixed_strategy_eq P1 :=
  @mkMixedEq P1
    (probs_to_mass_fn_P1 probs)
    (@probs_to_mass_fn_nonneg probs H_len H_valid)
    (@valid_probs_sum_enum_P1 probs H_len H_valid).
    
    
(* Now we can complete the correspondence lemma *)
Lemma probs_to_mixed_P1 (probs : list Q) :
  check_mixed_strategy_P1 probs = true ->
  {σ : mixed_strategy_eq P1 | 
    forall a : action P1, prob_mass_eq σ a = List.nth (nat_of_ord a) probs 0}.
Proof.
  intro H.
  unfold check_mixed_strategy_P1 in H.
  destruct (andb_prop _ _ H) as [H_len H_valid].
  apply Nat.eqb_eq in H_len.
  
  exists (@build_mixed_P1 probs H_len H_valid).
  
  intro a.
  unfold build_mixed_P1, probs_to_mass_fn_P1.
  simpl.
  reflexivity.
Qed.

(* ============= Player 2 versions ============= *)

(* Lemma 1 for P2: enum_actions for P2 gives all ordinals in order *)
Lemma enum_actions_P2_complete : 
  map (nat_of_ord (n:=n2)) (enum_actions P2) = iota 0 n2.
Proof.
  unfold enum_actions.
  simpl.
  have ->: map (nat_of_ord (n:=n2)) (enum [fin n2]) = 
           map val (enum [fin n2]).
  { apply map_ext. intro x. reflexivity. }
  rewrite val_enum_ord.
  reflexivity.
Qed.

(* Lemma 3a for P2: Mapping nat_of_ord preserves function composition *)
Lemma map_enum_actions_comp_P2 (f : nat -> Q) :
  map (fun a : action P2 => f (nat_of_ord a)) (enum_actions P2) = 
  map f (map (nat_of_ord (n:=n2)) (enum_actions P2)).
Proof.
  rewrite map_comp.
  reflexivity.
Qed.

(* Lemma 3b for P2: Simplify the double map using enum_actions_P2_complete *)
Lemma map_enum_to_iota_P2 (f : nat -> Q) :
  map f (map (nat_of_ord (n:=n2)) (enum_actions P2)) = map f (iota 0 n2).
Proof.
  f_equal.
  exact enum_actions_P2_complete.
Qed.

(* Lemma 3 for P2: Mapping through enum_actions and indexing gives back probs *)
Lemma map_enum_nth_probs_P2 (probs : list Q) :
  List.length probs = n2 ->
  map (fun a : action P2 => List.nth (nat_of_ord a) probs 0) (enum_actions P2) = probs.
Proof.
  intro H_len.
  rewrite (map_enum_actions_comp_P2 (fun i => List.nth i probs 0)).
  rewrite map_enum_to_iota_P2.
  rewrite -H_len.
  exact (nth_iota_recover probs).
Qed.

(* Lemma 4 for P2: Sum preservation *)
Lemma sum_enum_actions_probs_P2 (probs : list Q) :
  List.length probs = n2 ->
  fold_left Qplus probs 0 = 
  fold_left Qplus (map (fun a : action P2 => List.nth (nat_of_ord a) probs 0) 
                       (enum_actions P2)) 0.
Proof.
  intro H_len.
  rewrite map_enum_nth_probs_P2; auto.
Qed.

(* Helper: Build the probability mass function from a list for P2 *)
Definition probs_to_mass_fn_P2 (probs : list Q) : action P2 -> Q :=
  fun a => List.nth (nat_of_ord a) probs 0.

(* Lemma: The mass function from valid probs is non-negative for P2 *)
Lemma probs_to_mass_fn_nonneg_P2 (probs : list Q) :
  List.length probs = n2 ->
  valid_probs probs = true ->
  forall a : action P2, 0 <= probs_to_mass_fn_P2 probs a.
Proof.
  intros H_len H_valid a.
  unfold probs_to_mass_fn_P2.
  apply valid_probs_nonneg; auto.
  apply probs_length_P2; auto.
Qed.

(* Lemma to get the sum property in the right form for P2 *)
Lemma valid_probs_sum_enum_P2 (probs : list Q) :
  List.length probs = n2 ->
  valid_probs probs = true ->
  Qeq (fold_left Qplus 
       (map (fun a : action P2 => List.nth (nat_of_ord a) probs 0) 
            (enum_actions P2)) 0) 1.
Proof.
  intros H_len H_valid.
  rewrite -sum_enum_actions_probs_P2; auto.
  apply valid_probs_sum_one_Qeq.
  exact H_valid.
Qed.

(* Helper: Build mixed strategy from valid probability list for P2 *)
Definition build_mixed_P2 (probs : list Q) (H_len : List.length probs = n2) 
           (H_valid : valid_probs probs = true) : mixed_strategy_eq P2 :=
  @mkMixedEq P2
    (probs_to_mass_fn_P2 probs)
    (@probs_to_mass_fn_nonneg_P2 probs H_len H_valid)
    (@valid_probs_sum_enum_P2 probs H_len H_valid).

(* Main correspondence lemma for P2 *)
Lemma probs_to_mixed_P2 (probs : list Q) :
  check_mixed_strategy_P2 probs = true ->
  {σ : mixed_strategy_eq P2 | 
    forall a : action P2, prob_mass_eq σ a = List.nth (nat_of_ord a) probs 0}.
Proof.
  intro H.
  unfold check_mixed_strategy_P2 in H.
  destruct (andb_prop _ _ H) as [H_len H_valid].
  apply Nat.eqb_eq in H_len.
  
  exists (@build_mixed_P2 probs H_len H_valid).
  
  intro a.
  unfold build_mixed_P2, probs_to_mass_fn_P2.
  simpl.
  reflexivity.
Qed.

(* ================================================================= *)
(*                SUPPORT CHARACTERIZATION THEOREM                  *)
(* ================================================================= *)

Section SupportCharacterization.

(* Define best response for a pure action *)
Definition is_best_response (g : game) (p : player) 
           (a : action p) (σ_opp : mixed_strategy_eq (other p)) : Prop :=
  forall a' : action p,
    best_response_value g p a' σ_opp <= best_response_value g p a σ_opp.

(* Define support of a mixed strategy *)
Definition supp_of_mixed {p : player} (σ : mixed_strategy_eq p) : list (action p) :=
  filter (fun a => negb (Qeq_bool (prob_mass_eq σ a) 0)) (enum_actions p).

(* Lemma: An action is in support iff it has positive probability *)
Lemma in_supp_iff_positive {p : player} (σ : mixed_strategy_eq p) (a : action p) :
  In a (supp_of_mixed σ) <-> 0 < prob_mass_eq σ a.
Proof.
  unfold supp_of_mixed.
  rewrite mem_filter.
  split.
  - move/andP => [H_neq H_enum].
    unfold Qeq_bool in H_neq.
    destruct (prob_mass_eq σ a ?= 0) eqn:E.
    + discriminate H_neq.
    + apply Qlt_alt. exact E.
    + discriminate H_neq.
  - intro H_pos.
    apply/andP; split.
    + unfold Qeq_bool.
      destruct (prob_mass_eq σ a ?= 0) eqn:E.
      * apply Qeq_alt in E. lra.
      * reflexivity.
      * apply Qgt_alt in E. lra.
    + apply mem_enum.
Qed.
 
