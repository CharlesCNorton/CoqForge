Require Import HoTT.Basics.
Require Import HoTT.Types.
Require Import HoTT.Pointed.Core.
Require Import HoTT.Truncations.Core.
Require Import HoTT.Truncations.Connectedness.
Require Import HoTT.Colimits.Pushout.

(** * Basic definitions and helper lemmas for wedge sums *)

(** Helper functions for the pushout *)
Definition wedge_f (X Y : pType) : Unit -> X := fun _ => point X.
Definition wedge_g (X Y : pType) : Unit -> Y := fun _ => point Y.

(** The carrier type of a wedge sum *)
Definition Wedge (X Y : pType) : Type :=
  Pushout (unit_name (point X)) (unit_name (point Y)).

(** The wedge sum of two pointed types *)
Definition pWedge (X Y : pType) : pType :=
  Build_pType (Wedge X Y) (pushl (point X)).

(** ** Basic lemmas about the wedge construction *)

(** The basepoint of the wedge *)
Lemma wedge_point (X Y : pType) : point (pWedge X Y) = pushl (point X).
Proof.
  reflexivity.
Qed.

(** The glue path in the wedge *)
Lemma wedge_glue (X Y : pType) : 
  pushl (point X) = pushr (point Y) :> Wedge X Y.
Proof.
  exact (pglue tt).
Qed.

(** ** Path construction lemmas *)

(** For 0-connected types, truncated elements are equal *)
Lemma connected_implies_tr_equal {A : Type} 
  (HA : IsConnected 0 A) (a b : A) :
  tr a = tr b :> Tr 0 A.
Proof.
  apply path_contr.
Qed.

Lemma wedge_glue_basepoints (X Y : pType) :
  pushl (point X) = pushr (point Y) :> Wedge X Y.
Proof.
  exact (pglue tt).
Qed.

(** ** Helper lemmas for truncations *)

(** Truncation of paths *)
Lemma tr_path {n : trunc_index} {A : Type} {x y : A} (p : x = y) :
  tr x = tr y :> Tr n A.
Proof.
  exact (ap tr p).
Qed.

(** ** Wedge elimination principle *)

Definition wedge_ind {X Y : pType} (P : Wedge X Y -> Type)
  (f : forall x : X, P (pushl x))
  (g : forall y : Y, P (pushr y))
  (p : transport P (pglue tt) (f (point X)) = g (point Y)) :
  forall w : Wedge X Y, P w.
Proof.
  refine (Pushout_ind P f g _).
  intro u; destruct u.
  exact p.
Defined.

(** ** Lemmas for the main theorem *)

(** The center of the wedge truncation *)
Definition wedge_truncation_center (n : trunc_index) (X Y : pType) : Tr n (Wedge X Y) :=
  tr (point (pWedge X Y)).

(** Helper: What does pglue do in our wedge? *)
Lemma wedge_pglue_eq (X Y : pType) (u : Unit) :
  pushl (point X) = pushr (point Y) :> Wedge X Y.
Proof.
  exact (pglue u).
Qed.

(** Helper: unit_name always returns the same point *)
Lemma unit_name_constant {A : Type} (a : A) (u u' : Unit) :
  unit_name a u = unit_name a u'.
Proof.
  destruct u, u'. reflexivity.
Qed.

(** Helper: pushl composed with unit_name gives the basepoint *)
Lemma pushl_unit_name_point (X Y : pType) (u : Unit) :
  pushl (unit_name (point X) u) = pushl (point X) :> Wedge X Y.
Proof.
  destruct u. reflexivity.
Qed.

(** Helper: Transport for equality goals in pushouts *)
Lemma transport_paths_pushout_pglue {A B C : Type} {f : B -> A} {g : B -> C} 
  (P : Pushout f g -> Type) (Q : forall w, P w) (b : B) :
  transport P (pglue b) (Q (pushl (f b))) = Q (pushr (g b)).
Proof.
  apply apD.
Qed.

(** Helper: Transport for equality with constant RHS *)
Lemma transport_paths_r_constant {A : Type} {n : trunc_index} 
  {x1 x2 : A} (p : x1 = x2) (y : Tr n A) (q : tr x1 = y) :
  transport (fun x => tr x = y) p q = ap tr p^ @ q.
Proof.
  destruct p. simpl. 
  rewrite concat_1p.
  reflexivity.
Qed.

(** Helper: Specific transport for our wedge case *)
Lemma transport_wedge_truncation_eq (n : trunc_index) (X Y : pType) :
  transport (fun w : Wedge X Y => tr w = tr (pushl (point X)) :> Tr n (Wedge X Y)) 
    (pglue tt)
    (1 : tr (pushl (point X)) = tr (pushl (point X)))
  = ap tr (pglue tt)^.
Proof.
  rewrite transport_paths_FlFr.
  rewrite ap_V.
  rewrite concat_p1.
  assert (H : ap (fun _ : Wedge X Y => tr (pushl (point X)) : Tr n (Wedge X Y)) (pglue tt) = 1).
  { apply ap_const. }
  rewrite H.
  exact (concat_p1 _).
Qed.

(** Helper: pushl after unit_name *)
Lemma pushl_unit_name_eq (X Y : pType) (u : Unit) :
  pushl (unit_name (point X) u) = pushl (point X) :> Wedge X Y.
Proof.
  destruct u. reflexivity.
Qed.

(** Helper: pushr composed with unit_name gives the basepoint *)
Lemma pushr_unit_name_point (X Y : pType) (u : Unit) :
  pushr (unit_name (point Y) u) = pushr (point Y) :> Wedge X Y.
Proof.
  destruct u. reflexivity.
Qed.

(** Helper: The truncation of the basepoint *)
Lemma wedge_truncation_basepoint (n : trunc_index) (X Y : pType) :
  wedge_truncation_center n X Y = tr (pushl (point X)) :> Tr n (Wedge X Y).
Proof.
  reflexivity.
Qed.

(** Helper: All left elements are the basepoint *)
Lemma wedge_pushl_all_equal (X Y : pType) (u : Unit) :
  pushl (unit_name (point X) u) = pushl (point X) :> Wedge X Y.
Proof.
  destruct u. reflexivity.
Qed.

(** Helper: All right elements are the basepoint *)
Lemma wedge_pushr_all_equal (X Y : pType) (u : Unit) :
  pushr (unit_name (point Y) u) = pushr (point Y) :> Wedge X Y.
Proof.
  destruct u. reflexivity.
Qed.

(** Helper: The left case *)
Definition wedge_left_case (n : trunc_index) (X Y : pType) (x : Unit) :
  tr (pushl (unit_name (point X) x)) = tr (pushl (point X)) :> Tr n (Wedge X Y).
Proof.
  destruct x. reflexivity.
Defined.

(** Helper: The right case *)
Definition wedge_right_case (n : trunc_index) (X Y : pType) (y : Unit) :
  tr (pushr (unit_name (point Y) y)) = tr (pushl (point X)) :> Tr n (Wedge X Y).
Proof.
  destruct y. exact (ap tr (pglue tt)^).
Defined.

(** The coherence condition: left and right cases agree on the glue *)
Lemma wedge_glue_coherence (n : trunc_index) (X Y : pType) (u : Unit) :
  transport (fun w : Wedge X Y => tr w = tr (pushl (point X)) :> Tr n (Wedge X Y))
    (pglue u)
    (wedge_left_case n X Y u) = 
  wedge_right_case n X Y u.
Proof.
  destruct u.
  unfold wedge_left_case, wedge_right_case.
  simpl.
  exact (transport_wedge_truncation_eq n X Y).
Qed.

(** Helper: In an n-connected type, all truncated elements are equal *)
Lemma tr_eq_of_connected {n : trunc_index} {A : Type} 
  (HA : IsConnected n A) (a b : A) :
  tr a = tr b :> Tr n A.
Proof.
  apply path_contr.
Qed.

(** Helper: For n-connected X, all left elements have equal truncations *)
Lemma tr_pushl_connected {n : trunc_index} {X Y : pType} 
  (HX : IsConnected n X) (x : X) :
  tr (pushl x) = tr (pushl (point X)) :> Tr n (Wedge X Y).
Proof.
  (* Use functoriality of truncation *)
  exact (ap (Trunc_functor n pushl) (path_contr (tr x) (tr (point X)))).
Defined.

(** Helper: For n-connected Y, all right elements have equal truncations to the basepoint *)
Lemma tr_pushr_connected {n : trunc_index} {X Y : pType} 
  (HY : IsConnected n Y) (y : Y) :
  tr (pushr y) = tr (pushl (point X)) :> Tr n (Wedge X Y).
Proof.
  (* First show tr (pushr y) = tr (pushr (point Y)) *)
  transitivity (tr (pushr (point Y)) : Tr n (Wedge X Y)).
  - exact (ap (Trunc_functor n (@pushr _ _ _ (unit_name (point X)) (unit_name (point Y)))) 
              (path_contr (tr y) (tr (point Y)))).
  (* Then use the glue path *)
  - exact (ap tr (pglue tt)^).
Defined.

(** Helper: tr_pushl_connected at the basepoint is reflexivity *)
Lemma tr_pushl_connected_point (n : trunc_index) (X Y : pType) 
  (HX : IsConnected n X) :
  tr_pushl_connected (Y:=Y) HX (point X) = 1.
Proof.
  unfold tr_pushl_connected.
  (* In a contractible type, the canonical path to the center is 1 when start = end *)
  assert (H : @path_contr (Tr n X) HX (tr (point X)) (tr (point X)) = idpath _).
  { apply path_ishprop. }
  rewrite H.
  (* ap f 1 = 1 *)
  exact (ap_1 _ _).
Qed.

(** Helper: tr_pushr_connected at the basepoint *)
Lemma tr_pushr_connected_point (n : trunc_index) (X Y : pType) 
  (HY : IsConnected n Y) :
  tr_pushr_connected (X:=X) HY (point Y) = ap tr (pglue tt)^.
Proof.
  unfold tr_pushr_connected.
  (* The first part: path_contr at the same point is 1 *)
  assert (H : @path_contr (Tr n Y) HY (tr (point Y)) (tr (point Y)) = idpath _).
  { apply path_ishprop. }
  rewrite H.
  rewrite (ap_1 _ _).
  (* 1 @ p = p *)
  apply concat_1p.
Qed.

(** Helper: The coherence condition for the main lemma *)
Lemma wedge_truncation_coherence (n : trunc_index) (X Y : pType) 
  (HX : IsConnected n X) (HY : IsConnected n Y) (u : Unit) :
  transport (fun w => tr w = tr (pushl (point X)) :> Tr n (Wedge X Y))
    (pglue u)
    (tr_pushl_connected HX (unit_name (point X) u))
  = tr_pushr_connected HY (unit_name (point Y) u).
Proof.
  destruct u.
  (* Let's understand what transport does here *)
  rewrite transport_paths_FlFr.
  (* ap of constant function is 1 *)
  rewrite ap_const.
  (* Now simplify the concatenation with 1 *)
  rewrite concat_p1.
  (* Use our lemmas about the values at basepoints *)
  rewrite tr_pushl_connected_point.
  rewrite tr_pushr_connected_point.
  (* (ap tr (pglue tt))^ @ 1 = ap tr (pglue tt)^ *)
  rewrite concat_p1.
  (* We need to show (ap tr (pglue tt))^ = ap tr (pglue tt)^ *)
  rewrite ap_V.
  reflexivity.
Qed.

(** Any element of the wedge has its truncation equal to the center *)
Lemma wedge_truncation_eq_center (n : trunc_index) (X Y : pType) 
  (HX : IsConnected n X) (HY : IsConnected n Y) 
  (w : Wedge X Y) :
  tr w = tr (pushl (point X)) :> Tr n (Wedge X Y).
Proof.
  unfold Wedge in *.
  refine (Pushout_ind 
    (fun w => tr w = tr (pushl (point X)) :> Tr n _)
    (tr_pushl_connected HX)
    (tr_pushr_connected HY)
    _ w).
  - (* Coherence *)
    exact (wedge_truncation_coherence n X Y HX HY).
Defined.

(** The wedge sum preserves n-connectedness *)
Theorem wedge_preserves_connectedness (n : trunc_index) (X Y : pType)
  (HX : IsConnected n X) (HY : IsConnected n Y) :
  IsConnected n (pWedge X Y).
Proof.
  (* To show n-connectedness, we need to show Tr n (Wedge X Y) is contractible *)
  apply (Build_Contr _ (tr (pushl (point X)))).
  (* Every element equals the center *)
  intro x.
  strip_truncations.
  symmetry.
  apply wedge_truncation_eq_center.
  - exact HX.
  - exact HY.
Defined.

(** * Examples of wedge sum connectivity *)

Require Import HoTT.Spaces.Circle.

(** First, let's prove that the circle is 0-connected *)
Lemma circle_0_connected : IsConnected 0 Circle.
Proof.
  (* A type is 0-connected if its 0-truncation is contractible *)
  (* For the circle, we can show any two points are merely equal *)
  apply (Build_Contr _ (tr base)).
  intro x.
  strip_truncations.
  (* Use circle induction *)
  apply (Circle_ind (fun c => tr base = tr c) (idpath _)).
  (* Loop case: Need to show transport preserves the path *)
  apply path_ishprop.
Defined.

(** Example 1: The wedge of two circles is 0-connected *)
Example wedge_circles_connected : IsConnected 0 (pWedge (Build_pType Circle base) (Build_pType Circle base)).
Proof.
  apply wedge_preserves_connectedness.
  - exact circle_0_connected.
  - exact circle_0_connected.
Defined.

(** Example 2: The wedge of a circle and a contractible type is 0-connected *)
Example wedge_circle_unit_connected : IsConnected 0 (pWedge (Build_pType Circle base) (Build_pType Unit tt)).
Proof.
  apply wedge_preserves_connectedness.
  - exact circle_0_connected.
  - (* Unit is 0-connected (actually contractible) *)
    apply contr_inhabited_hprop.
    + exact _.
    + apply tr. exact tt.
Defined.

(** Example 3: The wedge of two circles is 0-connected *)
Example wedge_two_circles_connected : IsConnected 0 (pWedge (Build_pType Circle base) (Build_pType Circle base)).
Proof.
  apply wedge_preserves_connectedness.
  - exact circle_0_connected.
  - exact circle_0_connected.
Defined.

(** Example 4: Bool is NOT 0-connected, so let's try a different example *)
(** The wedge of three circles is 0-connected *)
Example wedge_three_circles_connected : 
  IsConnected 0 (pWedge (Build_pType Circle base) 
                        (pWedge (Build_pType Circle base) 
                                (Build_pType Circle base))).
Proof.
  apply wedge_preserves_connectedness.
  - exact circle_0_connected.
  - apply wedge_preserves_connectedness.
    + exact circle_0_connected.
    + exact circle_0_connected.
Defined.

(** Example 5: Iterated wedge - bouquet of n circles is 0-connected *)
Fixpoint bouquet_circles (n : nat) : pType :=
  match n with
  | O => Build_pType Unit tt
  | S n' => pWedge (Build_pType Circle base) (bouquet_circles n')
  end.

Lemma bouquet_circles_connected (n : nat) : IsConnected 0 (bouquet_circles n).
Proof.
  induction n.
  - (* Base case: Unit is 0-connected *)
    simpl.
    apply contr_inhabited_hprop.
    + exact _.
    + apply tr. exact tt.
  - (* Inductive case: use wedge preservation *)
    simpl.
    apply wedge_preserves_connectedness.
    + exact circle_0_connected.
    + exact IHn.
Defined.

(** Novel Theorem: The fundamental group of a wedge of 1-connected spaces is trivial *)
Theorem wedge_simply_connected (X Y : pType)
  (HX : IsConnected 0.+1 X) (HY : IsConnected 0.+1 Y) :
  IsConnected 0.+1 (pWedge X Y).
Proof.
  (* This follows directly from our main theorem! *)
  exact (wedge_preserves_connectedness 0.+1 X Y HX HY).
Defined.

(** Corollary: The fundamental group is contractible *)
Corollary fundamental_group_wedge_trivial (X Y : pType)
  (HX : IsConnected 0.+1 X) (HY : IsConnected 0.+1 Y) :
  Contr (Tr 0 (point (pWedge X Y) = point (pWedge X Y))).
Proof.
  (* A space is 1-connected iff its fundamental group is contractible *)
  (* Use the equivalence between connectivity and loop space *)
  apply isconnected_loop.
  exact (wedge_simply_connected X Y HX HY).
Defined.
