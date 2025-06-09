(** * Modular Addition Cancellation (Left)
    
    This module provides the fundamental property of modular addition that
    allows canceling the left operand, which is missing from Coq's standard
    library under a simple name.
    
    Author: Charles C Norton
    Date: June 9th 2025
    License: GNU Lesser General Public License Version 2.1
    
    Compatibility: Coq 8.20.1+
*)

Require Import Coq.Arith.Arith.

(** ** Overview
    
    The modular addition cancellation property states that when computing
    (a + b) mod c, we can first reduce a modulo c without changing the result:
    
    (a + b) mod c = ((a mod c) + b) mod c
    
    This property is fundamental for modular arithmetic as it allows us to
    keep intermediate results small during computation.
    
    This property is useful for:
    - Implementing efficient modular arithmetic
    - Cryptographic computations
    - Hash table implementations  
    - Circular buffer arithmetic
    - Preventing integer overflow in modular calculations
*)

(** ** Main Theorem *)

(** (a + b) mod c = ((a mod c) + b) mod c *)
Lemma mod_add_cancel_l (a b c : nat) : 
  c <> 0 -> (a + b) mod c = ((a mod c) + b) mod c.
Proof.
  intro H.
  rewrite Nat.add_mod_idemp_l.
  reflexivity.
  exact H.
Qed.

(** ** Alternative Names *)

(** Some users might look for this under different names *)
Lemma mod_add_reduce_l (a b c : nat) :
  c <> 0 -> (a + b) mod c = ((a mod c) + b) mod c.
Proof. apply mod_add_cancel_l. Qed.

Lemma mod_add_idemp_l (a b c : nat) :
  c <> 0 -> (a + b) mod c = ((a mod c) + b) mod c.
Proof. apply mod_add_cancel_l. Qed.

(** ** Corollaries *)

(** Right version *)
Lemma mod_add_cancel_r (a b c : nat) :
  c <> 0 -> (a + b) mod c = (a + (b mod c)) mod c.
Proof.
  intro H.
  rewrite Nat.add_comm.
  rewrite mod_add_cancel_l by assumption.
  rewrite Nat.add_comm.
  reflexivity.
Qed.

(** Both sides *)
Lemma mod_add_cancel_both (a b c : nat) :
  c <> 0 -> (a + b) mod c = ((a mod c) + (b mod c)) mod c.
Proof.
  intro H.
  rewrite mod_add_cancel_l by assumption.
  rewrite mod_add_cancel_r by assumption.
  reflexivity.
Qed.

Example mod_add_cancel_l_ex1 : (10 + 7) mod 3 = ((10 mod 3) + 7) mod 3.
Proof. reflexivity. Qed.

Example mod_add_cancel_l_ex2 : (25 + 13) mod 5 = ((25 mod 5) + 13) mod 5.
Proof. reflexivity. Qed.

(** Practical use: keeping numbers small *)
Example keep_small : forall a b : nat,
  a < 1000 -> b < 1000 -> 
  (a + b) mod 7 = ((a mod 7) + b) mod 7.
Proof.
  intros a b Ha Hb.
  apply mod_add_cancel_l.
  discriminate.
Qed.

(** Hash computation *)
Example hash_update : forall (hash data : nat),
  let modulus := 1009 in  (* prime number *)
  (hash * 31 + data) mod modulus = ((hash * 31) mod modulus + data) mod modulus.
Proof.
  intros.
  apply mod_add_cancel_l.
  unfold modulus. discriminate.
Qed.

(** ** Extended Properties *)

(** Iteration: multiple additions *)
Lemma mod_add_cancel_l_iter (a b c d : nat) :
  d <> 0 -> (a + b + c) mod d = (((a mod d) + b + c) mod d).
Proof.
  intro H.
  rewrite <- Nat.add_assoc.
  rewrite mod_add_cancel_l by assumption.
  rewrite Nat.add_assoc.
  reflexivity.
Qed.


(** Multiplication distributes *)
Lemma mod_mul_add_distr (a b c d : nat) :
  d <> 0 -> (a * (b + c)) mod d = (a * b + a * c) mod d.
Proof.
  intro H.
  rewrite Nat.mul_add_distr_l.
  reflexivity.
Qed.

(** ** Efficiency Note *)

(** This property is crucial for efficient modular arithmetic. Without it,
    intermediate results in a sequence of additions could grow arbitrarily
    large before the final modulo operation. By reducing after each addition,
    we keep all intermediate values less than the modulus.
    
    For example, computing (a₁ + a₂ + ... + aₙ) mod m efficiently:
    
    Naive: compute the full sum, then take modulo (risks overflow)
    Better: (((...((a₁ mod m) + a₂) mod m) + a₃) mod m) + ...) mod m
*)

(** ** Notes
    
    This lemma is available in the standard library as Nat.add_mod_idemp_l,
    but that name is not intuitive. The property is about "canceling" or
    "reducing" the left operand modulo c, not about idempotence.
    
    Many users search for this property under names like:
    - mod_add_cancel
    - mod_add_reduce
    - mod_add_left
    
    Having it available under these more intuitive names improves
    discoverability and code readability.
*) destruct n; simpl.
    + split; intro H; [discriminate | inversion H].
    + rewrite IH. split; auto with arith.
Qed.
Qed.
Proof. reflexivity. Qed.
Qed.
  - intros [x Hx].
    apply nth_error_Some_lt with x.
    exact Hx.
Qed.
