(** * Count Occurrences as Filter Length
    
    This module provides the fundamental theorem relating count_occ to
    filter and length, which is surprisingly absent from Coq's standard library.
    
    Author: Charles C Norton
    Date: June 9th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.

(** ** Overview
    
    The count_occ function counts how many times an element appears in a list,
    given a decidable equality. This can be equivalently expressed as filtering
    the list for that element and taking the length.
    
    The theorem states: count_occ eq_dec l x = length (filter (eq_dec x) l),
    where we use a boolean equality test derived from the decidable equality.
    
    This equivalence is fundamental but missing from the standard library,
    forcing users to reprove it whenever they need to switch between counting
    and filtering perspectives.
    
    This property is useful for:
    - Converting between counting and filtering in proofs
    - Reasoning about frequency and occurrence properties
    - Optimizing algorithms that need both count and filtered results
    - Establishing connections between different list operations
    - Teaching the relationship between counting and filtering
*)

(** ** Main Theorem *)

Section CountOccFilter.
  Variable A : Type.
  Hypothesis eq_dec : forall x y : A, {x = y} + {x <> y}.

  (** count_occ is the same as length of filter with equality test *)
  Lemma count_occ_filter (x : A) (l : list A) :
    count_occ eq_dec l x = length (filter (fun y => if eq_dec x y then true else false) l).
  Proof.
    induction l as [|h t IH].
    - reflexivity.
    - simpl. 
      destruct (eq_dec h x) as [Heq|Hneq];
      destruct (eq_dec x h) as [Heq'|Hneq'].
      + simpl. f_equal. exact IH.
      + subst. contradiction.
      + subst. contradiction.
      + exact IH.
  Qed.
End CountOccFilter.

(** ** Alternative Formulations *)

Section CountOccFilterBool.
  Variable A : Type.
  Variable eqb : A -> A -> bool.
  Hypothesis eqb_eq : forall x y, eqb x y = true <-> x = y.

  (** Helper: filter with extensionally equal predicates *)
  Lemma filter_ext_eq (f g : A -> bool) (l : list A) :
    (forall x, f x = g x) -> filter f l = filter g l.
  Proof.
    intro H.
    induction l as [|h t IH].
    - reflexivity.
    - simpl. rewrite H. rewrite IH. reflexivity.
  Qed.

(** Version with boolean equality function *)
  Lemma count_occ_filter_bool (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A) :
    (forall a b, (if eq_dec a b then true else false) = eqb a b) ->
    count_occ eq_dec l x = length (filter (eqb x) l).
  Proof.
    intro H.
    rewrite count_occ_filter.
    f_equal.
    apply filter_ext_eq.
    intro y.
    apply H.
  Qed.

  (** Direct boolean version *)
  Lemma count_occ_filter_direct (eq_dec : forall x y : A, {x = y} + {x <> y}) :
    (forall x y, reflect (x = y) (eqb x y)) ->
    forall x l, count_occ eq_dec l x = length (filter (eqb x) l).
  Proof.
    intros Hrefl x l.
    induction l as [|h t IH].
    - reflexivity.
    - simpl.
      destruct (eq_dec h x) as [Heq|Hneq].
      + subst. destruct (Hrefl x x).
        * simpl. f_equal. exact IH.
        * contradiction.
      + destruct (Hrefl x h).
        * subst. contradiction.
        * exact IH.
  Qed.
End CountOccFilterBool.

(** ** Corollaries *)

Section CountOccProperties.
  Variable A : Type.
  Hypothesis eq_dec : forall x y : A, {x = y} + {x <> y}.

(** Element occurs iff it's in the filtered list *)
  Lemma count_occ_filter_In (x : A) (l : list A) :
    count_occ eq_dec l x > 0 <-> 
    In x (filter (fun y => if eq_dec x y then true else false) l).
  Proof.
    rewrite count_occ_filter.
    split.
    - intro H.
      destruct (filter _ l) eqn:Hf.
      + simpl in H. inversion H.
      + left. 
        assert (In a (a :: l0)) by (left; reflexivity).
        rewrite <- Hf in H0.
        apply filter_In in H0.
        destruct H0 as [_ H0].
        destruct (eq_dec x a); congruence.
    - intro H.
      destruct (filter _ l).
      + contradiction.
      + simpl. auto with arith.
  Qed.

(** Counting with constant false gives 0 *)
  Lemma count_occ_none (l : list A) (x : A) :
    (forall y, y <> x) ->
    count_occ eq_dec l x = 0.
  Proof.
    intro H.
    rewrite count_occ_filter.
    replace (filter (fun y => if eq_dec x y then true else false) l) with 
            (@nil A).
    - reflexivity.
    - symmetry. 
      induction l as [|h t IH].
      + reflexivity.
      + simpl. 
        destruct (eq_dec x h).
        * subst. specialize (H h). contradiction.
        * exact IH.
  Qed.
  
  (** Helper for filter composition *)
  Lemma filter_filter (P Q : A -> bool) (l : list A) :
    filter P (filter Q l) = filter (fun x => andb (Q x) (P x)) l.
  Proof.
    induction l as [|h t IH].
    - reflexivity.
    - simpl. destruct (Q h) eqn:HQ.
      + simpl. destruct (P h) eqn:HP.
        * simpl. f_equal. exact IH.
        * exact IH.
      + simpl. exact IH.
  Qed.

(** Counting in filtered list *)
  Lemma count_occ_filter_filter (P : A -> bool) (x : A) (l : list A) :
    count_occ eq_dec (filter P l) x = 
    if P x then count_occ eq_dec l x else 0.
  Proof.
    destruct (P x) eqn:HPx.
    - rewrite !count_occ_filter.
      rewrite filter_filter.
      f_equal.
      apply filter_ext_eq.
      intro y.
      simpl.
      destruct (eq_dec x y).
      + subst. rewrite HPx. reflexivity.
      + rewrite andb_false_r. reflexivity.
    - rewrite count_occ_filter.
      rewrite filter_filter.
      replace (filter (fun x0 : A => (P x0 && if eq_dec x x0 then true else false)%bool) l) with (@nil A).
      + reflexivity.
      + symmetry. 
        induction l as [|h t IH].
        * reflexivity.
        * simpl.
          destruct (P h && if eq_dec x h then true else false)%bool eqn:H.
          -- apply andb_true_iff in H. destruct H as [HPh Heq].
             destruct (eq_dec x h).
             ++ subst. rewrite HPx in HPh. discriminate.
             ++ discriminate.
          -- exact IH.
  Qed.
End CountOccProperties.

(** ** Examples *)

Example count_occ_filter_ex1 :
  count_occ Nat.eq_dec [1; 2; 3; 2; 1; 2] 2 = 
  length (filter (fun y => if Nat.eq_dec 2 y then true else false) [1; 2; 3; 2; 1; 2]).
Proof.
  apply count_occ_filter.
Qed.

Example count_occ_filter_compute :
  count_occ Nat.eq_dec [1; 2; 3; 2; 1; 2] 2 = 3.
Proof.
  reflexivity.
Qed.

(** Using boolean equality *)
Example count_occ_filter_bool_ex :
  count_occ Nat.eq_dec [5; 3; 5; 7; 5] 5 = 
  length (filter (Nat.eqb 5) [5; 3; 5; 7; 5]).
Proof.
  reflexivity.
Qed.

(** Counting characters *)
Require Import Coq.Strings.Ascii.

Example count_occ_ascii :
  count_occ ascii_dec ["a"; "b"; "a"; "c"; "a"]%char "a"%char = 3.
Proof.
  reflexivity.
Qed.

Example count_occ_filter_ascii :
  count_occ ascii_dec ["h"; "e"; "l"; "l"; "o"]%char "l"%char =
  length (filter (fun c => if ascii_dec "l"%char c then true else false) ["h"; "e"; "l"; "l"; "o"]%char).
Proof.
  apply count_occ_filter.
Qed.


(** ** Extended Properties *)

Section ExtendedProperties.
  Variable A : Type.
  Hypothesis eq_dec : forall x y : A, {x = y} + {x <> y}.

  (** Helper: partition and filter relationship *)
  Lemma partition_filter (P : A -> bool) (l : list A) :
    fst (partition P l) = filter P l.
  Proof.
    induction l as [|h t IH].
    - reflexivity.
    - simpl. destruct (P h); destruct (partition P t) eqn:Hpart; simpl in *.
      + f_equal. exact IH.
      + exact IH.
  Qed.

(** Relationship with partition *)
  Lemma count_occ_partition (x : A) (l : list A) :
    let (yes, no) := partition (fun y => if eq_dec x y then true else false) l in
    count_occ eq_dec l x = length yes.
  Proof.
    rewrite count_occ_filter.
    destruct (partition _ l) eqn:Hpart.
    simpl.
    f_equal.
    symmetry.
    assert (l0 = fst (l0, l1)) by reflexivity.
    rewrite H. rewrite <- Hpart.
    apply partition_filter.
  Qed.

  (** Sum of counts equals length for partitioning *)
  Lemma count_occ_sum (x y : A) (l : list A) :
    x <> y ->
    (forall z, In z l -> z = x \/ z = y) ->
    count_occ eq_dec l x + count_occ eq_dec l y = length l.
  Proof.
    intros Hneq Hall.
    rewrite !count_occ_filter.
    assert (H: forall z, In z l -> 
            (if eq_dec x z then true else false) = true \/
            (if eq_dec y z then true else false) = true).
    {
      intros z Hz.
      destruct (Hall z Hz).
      - subst. destruct (eq_dec x x); [left; reflexivity | contradiction].
      - subst. destruct (eq_dec x y).
        + subst. contradiction.
        + destruct (eq_dec y y); [right; reflexivity | contradiction].
    }
    clear Hall.
    induction l as [|h t IH].
    - reflexivity.
    - simpl.
      assert (In h (h :: t)) by (left; reflexivity).
      destruct (H h H0) as [Hx | Hy]; clear H0.
      + destruct (eq_dec x h).
        * simpl. rewrite <- IH.
          ** f_equal. destruct (eq_dec y h).
             -- subst. contradiction.
             -- reflexivity.
          ** intros. apply H. right. exact H0.
        * congruence.
      + destruct (eq_dec y h).
        * simpl. rewrite <- IH.
          ** rewrite plus_n_Sm. f_equal.
             destruct (eq_dec x h).
             -- subst. contradiction.
             -- reflexivity.
          ** intros. apply H. right. exact H0.
        * congruence.
  Qed.

  (** Multiplicity and filter relationship *)
  Lemma count_occ_repeat (x : A) (n : nat) :
    count_occ eq_dec (repeat x n) x = n.
  Proof.
    induction n.
    - reflexivity.
    - simpl. destruct (eq_dec x x).
      + f_equal. exact IHn.
      + contradiction.
  Qed.
End ExtendedProperties.

(** ** Notes
    
    This theorem bridges two fundamental list operations: counting occurrences
    and filtering. While both count_occ and filter are in the standard library,
    their relationship is not explicitly stated.
    
    The proof is straightforward by induction, but having this lemma available
    saves users from reproving it and makes the connection explicit. This is
    particularly useful when:
    
    1. Switching between algorithmic perspectives (counting vs. collecting)
    2. Optimizing code that needs both the count and the filtered elements
    3. Teaching the relationship between different list operations
    4. Proving properties that naturally involve both concepts
    
    The decidable equality requirement is necessary for count_occ but leads
    to a slightly awkward boolean test in the filter. Libraries like MathComp
    avoid this by using boolean equality throughout.
*)
