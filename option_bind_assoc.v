(** * Option Bind Associativity
    
    This module provides the monadic bind operation for options and proves
    its associativity property, which is surprisingly absent from Coq's
    standard library.
    
    Author: Charles C Norton
    Date: June 9th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Init.Datatypes.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(** ** Overview
    
    The option type forms a monad, a fundamental pattern in functional
    programming for handling computations that may fail. The bind operation
    sequences option-returning computations, propagating None through the chain.
    
    The monadic bind satisfies three laws:
    - Left identity: bind (Some x) f = f x
    - Right identity: bind m Some = m  
    - Associativity: bind (bind m f) g = bind m (λx. bind (f x) g)
    
    This module defines bind and proves associativity, the most complex law.
    
    This property is useful for:
    - Chaining fallible computations without nested matches
    - Proving correctness of option-based algorithms
    - Building more complex monadic abstractions
    - Optimizing sequences of option operations
    - Teaching monadic programming patterns
*)

(** ** Main Definitions and Theorem *)

(** Monadic bind for options *)
Definition option_bind {A B : Type} (m : option A) (f : A -> option B) : option B :=
  match m with
  | None => None
  | Some x => f x
  end.

(** Bind associativity for options *)
Lemma option_bind_assoc {A B C : Type} (m : option A) (f : A -> option B) (g : B -> option C) :
  option_bind (option_bind m f) g = option_bind m (fun x => option_bind (f x) g).
Proof.
  destruct m; reflexivity.
Qed.

(** ** Monadic Laws *)

(** Left identity: bind (Some x) f = f x *)
Lemma option_bind_left_id {A B : Type} (x : A) (f : A -> option B) :
  option_bind (Some x) f = f x.
Proof.
  reflexivity.
Qed.

(** Right identity: bind m Some = m *)
Lemma option_bind_right_id {A : Type} (m : option A) :
  option_bind m Some = m.
Proof.
  destruct m; reflexivity.
Qed.

(** ** Notations *)

(** Standard monadic notations *)
Module OptionNotations.
  Notation "m >>= f" := (option_bind m f) (at level 50, left associativity).
  Notation "m >> n" := (option_bind m (fun _ => n)) (at level 50, left associativity).
End OptionNotations.

Import OptionNotations.

(** ** Derived Operations *)

(** Monadic map (lift a pure function) *)
Definition option_map {A B : Type} (f : A -> B) (m : option A) : option B :=
  m >>= (fun x => Some (f x)).

(** Join (flatten nested options) *)
Definition option_join {A : Type} (mm : option (option A)) : option A :=
  mm >>= (fun m => m).

(** Kleisli composition *)
Definition option_compose {A B C : Type} (g : B -> option C) (f : A -> option B) : A -> option C :=
  fun x => f x >>= g.

Notation "g <=< f" := (option_compose g f) (at level 51, right associativity).

(** ** Properties of Derived Operations *)

(** Map fusion *)
Lemma option_map_compose {A B C : Type} (f : B -> C) (g : A -> B) (m : option A) :
  option_map f (option_map g m) = option_map (fun x => f (g x)) m.
Proof.
  destruct m; reflexivity.
Qed.

(** Bind in terms of map and join *)
Lemma option_bind_map_join {A B : Type} (m : option A) (f : A -> option B) :
  m >>= f = option_join (option_map f m).
Proof.
  destruct m; reflexivity.
Qed.

(** ** Examples *)

Example option_bind_assoc_ex1 :
  option_bind (option_bind (Some 5) (fun x => Some (x + 3))) (fun y => Some (y * 2)) =
  option_bind (Some 5) (fun x => option_bind (Some (x + 3)) (fun y => Some (y * 2))).
Proof.
  apply option_bind_assoc.
Qed.

Example option_bind_assoc_ex2 :
  option_bind (option_bind None (fun x : nat => Some (x + 1))) (fun y => Some (y * 2)) =
  option_bind None (fun x => option_bind (Some (x + 1)) (fun y => Some (y * 2))).
Proof.
  apply option_bind_assoc.
Qed.

Example option_bind_assoc_ex3 :
  let safe_div (n : nat) (m : nat) : option nat :=
    if Nat.eqb m 0 then None else Some (n / m) in
  option_bind (option_bind (Some 20) (safe_div 100)) (safe_div 10) =
  option_bind (Some 20) (fun x => option_bind (safe_div 100 x) (safe_div 10)).
Proof.
  apply option_bind_assoc.
Qed.

(** Using notations *)
Example option_bind_notation :
  Some 10 >>= (fun x => Some (x * 2)) >>= (fun y => Some (y + 5)) =
  Some 10 >>= (fun x => Some (x * 2) >>= (fun y => Some (y + 5))).
Proof.
  apply option_bind_assoc.
Qed.

(** ** Extended Properties *)

(** Bind distributes over None *)
Lemma option_bind_none {A B : Type} (f : A -> option B) :
  None >>= f = None.
Proof.
  reflexivity.
Qed.

(** Bind with constant function *)
Lemma option_bind_const {A B : Type} (m : option A) (b : option B) :
  m >>= (fun _ => b) = m >> b.
Proof.
  reflexivity.
Qed.

(** Double bind simplification *)
Lemma option_bind_bind {A B : Type} (m : option A) (f : A -> option B) :
  m >>= (fun x => f x >>= Some) = m >>= f.
Proof.
  destruct m as [x|].
  - simpl. apply option_bind_right_id.
  - reflexivity.
Qed.

(** Bind respects equality *)
Lemma option_bind_ext {A B : Type} (m : option A) (f g : A -> option B) :
  (forall x, f x = g x) -> m >>= f = m >>= g.
Proof.
  intro H.
  destruct m; simpl.
  - apply H.
  - reflexivity.
Qed.

(** ** List Operations with Options *)

(** Sequence a list of options into an option of list *)
Fixpoint sequence {A : Type} (l : list (option A)) : option (list A) :=
  match l with
  | [] => Some []
  | x :: xs => x >>= (fun h => sequence xs >>= (fun t => Some (h :: t)))
  end.

(** Traverse a list with an option-producing function *)
Definition traverse {A B : Type} (f : A -> option B) (l : list A) : option (list B) :=
  sequence (map f l).

(** Sequence preserves length when successful *)
Lemma sequence_length {A : Type} (l : list (option A)) (res : list A) :
  sequence l = Some res -> length l = length res.
Proof.
  revert res.
  induction l as [|h t IH]; intros res Heq.
  - simpl in Heq. injection Heq. intro. subst. reflexivity.
  - simpl in Heq.
    destruct h as [x|]; [|discriminate].
    destruct (sequence t) as [t'|] eqn:Hseq; [|discriminate].
    simpl in Heq. injection Heq. intro. subst.
    simpl. f_equal.
    apply IH. reflexivity.
Qed.

(** ** Common Patterns *)

(** The "maybe" pattern - provide default for None *)
Definition option_default {A : Type} (d : A) (m : option A) : A :=
  match m with
  | None => d
  | Some x => x
  end.

(** Chain with default *)
Lemma option_bind_default {A B : Type} (m : option A) (f : A -> option B) (d : B) :
  option_default d (m >>= f) = 
  match m with
  | None => d
  | Some x => option_default d (f x)
  end.
Proof.
  destruct m; reflexivity.
Qed.

(** Filter with option *)
Definition option_filter {A : Type} (P : A -> bool) (m : option A) : option A :=
  m >>= (fun x => if P x then Some x else None).

(** Filter composition *)
Lemma option_filter_and {A : Type} (P Q : A -> bool) (m : option A) :
  option_filter P (option_filter Q m) = option_filter (fun x => andb (Q x) (P x)) m.
Proof.
  destruct m as [x|]; simpl.
  - destruct (Q x); simpl.
    + destruct (P x); reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

(** ** Notes
    
    The option monad is perhaps the simplest monad, modeling computations
    that can fail with None. Despite its simplicity and ubiquity, Coq's
    standard library doesn't provide the monadic interface.
    
    This is surprising given that:
    1. Option is used throughout the standard library
    2. Monadic bind greatly simplifies option-heavy code
    3. The proofs are all trivial (just case analysis)
    4. Many languages provide this by default (Haskell's Maybe,
       OCaml's Option module, Rust's Option, etc.)
    
    The associativity law is crucial for:
    - Refactoring chains of operations
    - Optimizing sequences of binds
    - Proving more complex monadic laws
    - Building monad transformers
    
    Libraries like ExtLib and stdpp do provide these definitions,
    but they should be in the standard library given how fundamental
    they are.
*)
