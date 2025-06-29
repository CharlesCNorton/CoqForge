(** * Simple Union-Find Data Structure
    
    A persistent union-find (disjoint-set) data structure implemented
    using functions, avoiding termination issues while maintaining
    simplicity and correctness.
    
    Based on Philip Zucker's blog post "A Simple, Probably-Not-Exp-Time 
    Disjoint Set in Coq" (https://www.philipzucker.com/simple-coq-union-find/)
    
    Author: Charles Norton
    Date: June 28th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

(** ** Overview
    
    Union-find (also known as disjoint-set) is a data structure that 
    maintains a partition of a set into disjoint subsets. It supports
    two main operations:
    
    - find: determine which subset a particular element is in
    - union: join two subsets into a single subset
    
    This implementation uses a functional representation where disjoint
    sets are represented as preimages of a function. This avoids the
    termination issues that arise with traditional pointer-based or
    array-based implementations while remaining purely functional.
    
    Key insight (from Zucker): The preimages of any total function 
    form disjoint sets over the domain. This allows us to represent
    the union-find structure as simply a function nat -> nat.
*)

(** ** Core Definitions *)

(** The union-find data structure is simply a function from nat to nat *)
Definition ds := nat -> nat.

(** Initialize with identity function - each element in its own set *)
Definition init_ds : ds := fun x => x.

(** Find the representative (root) of an element *)
Definition find_root (g : ds) x := g x.

(** Check if two elements are in the same set *)
Definition in_same_set (g : ds) x y := Nat.eqb (g x) (g y).

(** Union two sets by redirecting all elements with x's root to y's root *)
Definition union (g : ds) x y : ds :=
  let px := find_root g x in
  let py := find_root g y in
  fun z => 
    if Nat.eqb px (find_root g z) then py else find_root g z.

(** ** Basic Properties *)

(** Initial state assigns each element to its own set *)
Lemma find_root_init : forall x,
  find_root init_ds x = x.
Proof.
  reflexivity.
Qed.

(** Union is idempotent *)
Lemma union_same : forall g x,
  let g' := union g x x in
  find_root g' x = find_root g x.
Proof.
  intros g x.
  unfold union, find_root.
  simpl.
  rewrite Nat.eqb_refl.
  destruct (g x =? g x); reflexivity.
Qed.

(** After union x y, find_root of x equals find_root of y *)
Lemma union_connects : forall g x y,
  let g' := union g x y in
  find_root g' x = find_root g' y.
Proof.
  intros g x y.
  unfold union, find_root.
  simpl.
  rewrite Nat.eqb_refl.
  destruct (g x =? g y); reflexivity.
Qed.

(** If z was in same set as x, after union x y, z is in same set as y *)
Lemma in_same_set_after_union : forall g x y z,
  let g' := union g x y in
  in_same_set g x z = true ->
  in_same_set g' y z = true.
Proof.
  intros g x y z.
  unfold union, in_same_set, find_root.
  simpl.
  intro H.
  apply Nat.eqb_eq in H.
  rewrite H.
  rewrite Nat.eqb_refl.
  destruct (g z =? g y); apply Nat.eqb_refl.
Qed.

(** ** Derived Operations *)

(** Check if an element is a representative (root) *)
Definition is_root (g : ds) x : bool :=
  Nat.eqb (find_root g x) x.

(** Count the number of elements in a set (requires bounded domain) *)
Definition set_size (g : ds) (root : nat) (max_elem : nat) : nat :=
  let fix count_in_set n :=
    match n with
    | 0 => if Nat.eqb (g 0) root then 1 else 0
    | S n' => (if Nat.eqb (g (S n')) root then 1 else 0) + count_in_set n'
    end
  in count_in_set max_elem.

(** ** Examples *)

Example union_example : 
  let g0 := init_ds in
  let g1 := union g0 1 2 in
  let g2 := union g1 3 4 in
  let g3 := union g2 2 3 in
  (* Now 1,2,3,4 are all in the same set *)
  in_same_set g3 1 4 = true.
Proof.
  reflexivity.
Qed.

Example three_sets : 
  let g0 := init_ds in
  let g1 := union g0 1 2 in
  let g2 := union g1 3 4 in
  let g3 := union g2 5 6 in
  (* We have three disjoint sets: {1,2}, {3,4}, {5,6} *)
  (in_same_set g3 1 2 = true) /\
  (in_same_set g3 3 4 = true) /\
  (in_same_set g3 5 6 = true) /\
  (in_same_set g3 1 3 = false) /\
  (in_same_set g3 1 5 = false) /\
  (in_same_set g3 3 5 = false).
Proof.
  repeat split; reflexivity.
Qed.

(** ** Equivalence Relation Properties *)

(** Union-find maintains an equivalence relation *)
Theorem in_same_set_equiv : forall g,
  (forall x, in_same_set g x x = true) /\
  (forall x y, in_same_set g x y = in_same_set g y x) /\
  (forall x y z, in_same_set g x y = true -> in_same_set g y z = true -> in_same_set g x z = true).
Proof.
  intro g.
  unfold in_same_set.
  split; [|split].
  - intro x. apply Nat.eqb_refl.
  - intros x y. apply Nat.eqb_sym.
  - intros x y z H1 H2.
    apply Nat.eqb_eq in H1, H2.
    apply Nat.eqb_eq.
    congruence.
Qed.

(** ** Decision Procedures *)

(** Decidable equality for equivalence classes *)
Definition equiv_class_dec (g : ds) (x y : nat) : {in_same_set g x y = true} + {in_same_set g x y = false}.
Proof.
  unfold in_same_set.
  destruct (g x =? g y) eqn:E.
  - left. reflexivity.
  - right. reflexivity.
Defined.

(** Find all elements in the same equivalence class (bounded) *)
Definition equiv_class_members (g : ds) (x : nat) (bound : nat) : list nat :=
  filter (fun y => in_same_set g x y) (seq 0 (S bound)).

(** ** Counting and Size Operations *)

(** Count number of distinct representatives up to bound *)
Definition count_components (g : ds) (bound : nat) : nat :=
  length (nodup Nat.eq_dec (map g (seq 0 (S bound)))).

(** Get all representatives (roots) up to bound *)
Definition all_representatives (g : ds) (bound : nat) : list nat :=
  nodup Nat.eq_dec (map g (seq 0 (S bound))).

(** ** Conversion Functions *)

(** Convert to list of equivalence classes *)
Definition to_equiv_classes (g : ds) (bound : nat) : list (list nat) :=
  map (fun repr => equiv_class_members g repr bound) 
      (all_representatives g bound).

(** Build from equivalence relation *)
Definition from_equiv_rel (R : nat -> nat -> bool) (bound : nat) : ds :=
  fun x => 
    let fix find_min_equiv y :=
      match y with
      | 0 => if R x 0 then 0 else x
      | S y' => if R x y then y else find_min_equiv y'
      end
    in find_min_equiv bound.

(** ** Specification and Correctness *)

(** Abstract specification of union-find behavior *)
Record UFSpec (g : ds) : Prop := {
  uf_equiv : forall x y, in_same_set g x y = true <-> find_root g x = find_root g y;
  uf_union_spec : forall g' x y,
    g' = union g x y ->
    (forall z, in_same_set g x z = true -> in_same_set g' y z = true) /\
    (forall z, in_same_set g y z = true -> in_same_set g' x z = true) /\
    (in_same_set g' x y = true)
}.

(** Our implementation satisfies the specification *)
Theorem ds_satisfies_spec : forall g, UFSpec g.
Proof.
  intro g.
  constructor.
  - (* uf_equiv *)
    intros x y. unfold in_same_set, find_root.
    split; intro H.
    + apply Nat.eqb_eq in H. exact H.
    + rewrite H. apply Nat.eqb_refl.
  - (* uf_union_spec *)
    intros g' x y Hg'.
    split; [|split].
    + (* forall z, in_same_set g x z = true -> in_same_set g' y z = true *)
      intros z Hz. subst g'. apply in_same_set_after_union. exact Hz.
    + (* forall z, in_same_set g y z = true -> in_same_set g' x z = true *)
      intros z Hz. subst g'.
      unfold in_same_set in *.
      apply Nat.eqb_eq in Hz.
      apply Nat.eqb_eq.
      unfold union, find_root.
      destruct (g x =? g z) eqn:E1.
      * (* g x = g z *)
        apply Nat.eqb_eq in E1.
        rewrite Nat.eqb_refl.
        congruence.
      * (* g x ≠ g z *)
        rewrite Nat.eqb_refl.
        exact Hz.
    + (* in_same_set g' x y = true *)
      subst g'. 
      unfold in_same_set, union, find_root.
      rewrite Nat.eqb_refl.
      destruct (g x =? g y); apply Nat.eqb_refl.
Qed.


(** ** Integration with CCL Algorithm *)

(** Build union-find structure from a list of equivalences *)
Fixpoint build_from_equiv_list (pairs : list (nat * nat)) (g : ds) : ds :=
  match pairs with
  | [] => g
  | (x, y) :: rest => build_from_equiv_list rest (union g x y)
  end.

(** Convert equiv_table to list of equivalent pairs up to max_label *)
Definition equiv_table_to_pairs (equiv : nat -> nat -> bool) (max_label : nat) : list (nat * nat) :=
  let fix collect_pairs i j acc :=
    match i with
    | 0 => acc
    | S i' =>
        let fix collect_for_i j acc :=
          match j with
          | 0 => acc
          | S j' =>
              let acc' := if equiv i j && negb (Nat.eqb i j) then (i, j) :: acc else acc in
              collect_for_i j' acc'
          end
        in collect_pairs i' max_label (collect_for_i i acc)
    end
  in collect_pairs max_label max_label [].

(** Convert equiv_table to union-find structure *)
Definition equiv_table_to_ds (equiv : nat -> nat -> bool) (max_label : nat) : ds :=
  build_from_equiv_list (equiv_table_to_pairs equiv max_label) init_ds.

(** ** Properties of the Conversion *)

Lemma build_from_empty : forall g,
  build_from_equiv_list [] g = g.
Proof.
  reflexivity.
Qed.

Lemma build_from_cons : forall x y rest g,
  build_from_equiv_list ((x,y) :: rest) g = 
  build_from_equiv_list rest (union g x y).
Proof.
  reflexivity.
Qed.

(** ** Additional Examples and Applications *)

(** Example: Building from equivalence pairs *)
Example build_from_pairs_example :
  let pairs := [(1,2); (3,4); (2,3); (5,6)] in
  let g := build_from_equiv_list pairs init_ds in
  (in_same_set g 1 4 = true) /\
  (in_same_set g 1 5 = false) /\
  (in_same_set g 5 6 = true).
Proof.
  simpl. repeat split.
Qed.

(** Example: Simple pair union *)
Example simple_union_example :
  let g1 := union init_ds 0 1 in
  let g2 := union g1 2 3 in
  (in_same_set g2 0 1 = true) /\
  (in_same_set g2 2 3 = true) /\
  (in_same_set g2 0 2 = false).
Proof.
  simpl. repeat split.
Qed.

(** Example: Counting components *)
Example count_components_example :
  let g0 := init_ds in
  let g1 := union g0 0 1 in
  let g2 := union g1 2 3 in
  let g3 := union g2 4 5 in
  (* We have 3 components: {0,1}, {2,3}, {4,5} and singletons 6,7,8,9 *)
  count_components g3 9 = 7.
Proof.
  reflexivity.
Qed.

(** Example: Getting equivalence class members *)
Example equiv_class_example :
  let g := build_from_equiv_list [(1,2); (2,3); (5,6)] init_ds in
  equiv_class_members g 1 6 = [1; 2; 3].
Proof.
  reflexivity.
Qed.

(** Example: Converting from equivalence table - avoiding 0 *)
Example equiv_table_nonzero :
  (* Define equivalence where only 1~2 *)
  let equiv := fun x y => 
    match (x, y) with
    | (1, 1) | (1, 2) | (2, 1) | (2, 2) => true
    | (3, 3) => true
    | (4, 4) => true
    | _ => false
    end in
  let g := equiv_table_to_ds equiv 4 in
  (in_same_set g 1 2 = true) /\
  (in_same_set g 1 3 = false) /\
  (in_same_set g 3 4 = false).
Proof.
  compute.
  repeat split.
Qed.

(** Example: Simulating connected component labeling *)
Example ccl_simulation :
  (* Simulate finding connected components in a small 2x3 "image"
     where we connect horizontally adjacent pixels with same value:
     [1 1 2]
     [3 3 1]
     Pixels are numbered 0-5 (row-major order) *)
  let g := build_from_equiv_list [(0,1); (3,4)] init_ds in
  (* Check that we get correct components *)
  (in_same_set g 0 1 = true) /\   (* component {0,1} *)
  (in_same_set g 3 4 = true) /\   (* component {3,4} *)
  (in_same_set g 0 3 = false) /\  (* different components *)
  (in_same_set g 2 0 = false) /\  (* pixel 2 is separate *)
  (in_same_set g 5 0 = false).     (* pixel 5 is separate *)
Proof.
  simpl. repeat split.
Qed.

Require Import Coq.micromega.Lia.

(** Example: Converting to equivalence classes list *)
Example to_equiv_classes_example :
  let g := build_from_equiv_list [(0,1); (0,2); (3,4)] init_ds in
  let classes := to_equiv_classes g 5 in
  (* Should have 3 equivalence classes *)
  length classes = 3.
Proof.
  reflexivity.
Qed.

(** Example: Verifying equivalence relation properties on concrete instance *)
Example concrete_equiv_properties :
  let g := build_from_equiv_list [(1,2); (3,4); (2,3)] init_ds in
  (* Reflexivity *)
  (in_same_set g 1 1 = true) /\
  (* Symmetry *)
  (in_same_set g 1 4 = in_same_set g 4 1) /\
  (* Transitivity: 1~2 and 2~3 implies 1~3 *)
  (in_same_set g 1 2 = true -> 
   in_same_set g 2 3 = true -> 
   in_same_set g 1 3 = true).
Proof.
  repeat split; reflexivity.
Qed.

(** Example: Chain of unions - concrete version *)
Example union_chain_concrete :
  let g := fold_left (fun (g : ds) (pair : nat * nat) => 
                        let (x,y) := pair in union g x y)
                     [(0,1); (1,2); (2,3); (3,4); (4,5)]
                     init_ds in
  (* Check specific pairs to show all are connected *)
  (in_same_set g 0 5 = true) /\
  (in_same_set g 1 4 = true) /\
  (in_same_set g 2 3 = true) /\
  (in_same_set g 0 3 = true).
Proof.
  compute. repeat split.
Qed.

(** Example: Performance characteristics *)
Example performance_demo :
  (* After n unions, find can traverse up to n redirections *)
  let g1 := union init_ds 0 1 in  (* 0 -> 1 *)
  let g2 := union g1 1 2 in        (* 0 -> 1 -> 2 *)
  let g3 := union g2 2 3 in        (* 0 -> 1 -> 2 -> 3 *)
  (* Each find_root adds a layer *)
  (find_root g1 0 = 1) /\
  (find_root g2 0 = 2) /\
  (find_root g3 0 = 3).
Proof.
  repeat split; reflexivity.
Qed.

(** ** Notes on Usage

    These examples demonstrate:
    
    1. **Basic operations**: How to build and query the union-find structure
    2. **CCL integration**: How to convert pixel adjacency to components
    3. **Equivalence properties**: Verification that our structure maintains
       a proper equivalence relation
    4. **Performance**: The layered nature of the functional approach
*)
