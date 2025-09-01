(* =============================================================================
   Formal Verification of Graceful Restart Mechanism for BGP
   
   Specification: RFC 4724 (S. Sangli, E. Chen, R. Fernando, J. Scudder, 
                            Y. Rekhter, January 2007)
   Target: BGP Graceful Restart
   
   Module: BGP Graceful Restart Formalization and Verification
   Author: Charles C Norton
   Date: September 1, 2025
   
   "'The time of preparation draws to an end. Let us begin the Great Work.'"
   
   ============================================================================= *)

From Coq Require Import
  List
  NArith.NArith
  Bool
  Arith
  Lia.

Import ListNotations.
Open Scope N_scope.

(* =============================================================================
   Section 1: Basic Types and Constants
   ============================================================================= *)

Definition byte := N.
Definition word16 := N.
Definition word32 := N.
Definition word64 := N.

(* Graceful Restart Constants *)
Definition GR_CAPABILITY_CODE : byte := 64.
Definition GR_RESTART_TIME_MAX : word16 := 4095.  (* 12 bits max *)
Definition GR_STALE_TIME_MAX : word16 := 4095.    (* For Long-Lived GR *)
Definition END_OF_RIB_MARKER_LEN : N := 0.        (* Empty UPDATE *)

(* Timer Constants (seconds) *)
Definition DEFAULT_RESTART_TIME : N := 120.
Definition DEFAULT_STALE_TIME : N := 300.
Definition DEFAULT_SELECTION_DEFERRAL_TIME : N := 360.
Definition LLGR_STALE_TIME : N := 86400.  (* 24 hours for Long-Lived GR *)

(* =============================================================================
   Section 2: Graceful Restart Capability (RFC 4724 Section 3)
   ============================================================================= *)

(* Restart Flags (first 4 bits) *)
Definition GR_FLAG_RESTART : N := 8.   (* Bit 0: Restart State *)
Definition GR_FLAG_NOTIFICATION : N := 4. (* Bit 1: Graceful Notification *)
Definition GR_FLAG_RESERVED : N := 3.   (* Bits 2-3: Reserved *)

(* AFI/SAFI Flags *)
Definition GR_AFI_FLAG_FORWARDING : N := 128. (* Bit 0: Forwarding State *)
Definition GR_AFI_FLAG_RESERVED : N := 127.   (* Bits 1-7: Reserved *)

Record GRTuple := {
  gr_afi : word16;
  gr_safi : byte;
  gr_flags : byte  (* Forwarding state preserved flag *)
}.

Record GracefulRestartCapability := {
  gr_cap_code : byte;           (* Must be 64 *)
  gr_cap_length : word16;
  gr_restart_flags : N;         (* 4 bits *)
  gr_restart_time : N;          (* 12 bits *)
  gr_tuples : list GRTuple
}.

(* Create GR capability *)
Definition create_gr_capability (restart_state : bool) (restart_time : N)
                               (families : list (word16 * byte * bool)) 
                               : GracefulRestartCapability :=
  let flags := if restart_state then GR_FLAG_RESTART else 0 in
  let tuples := map (fun '(afi, safi, fwd) =>
    {| gr_afi := afi;
       gr_safi := safi;
       gr_flags := if fwd then GR_AFI_FLAG_FORWARDING else 0 |}) families in
  {| gr_cap_code := GR_CAPABILITY_CODE;
     gr_cap_length := 2 + 4 * length tuples;
     gr_restart_flags := flags;
     gr_restart_time := N.min restart_time GR_RESTART_TIME_MAX;
     gr_tuples := tuples |}.

(* =============================================================================
   Section 3: Graceful Restart States (RFC 4724 Section 4)
   ============================================================================= *)

Inductive GRState :=
  | GR_NORMAL           (* Normal operation *)
  | GR_RESTARTING       (* Local restart in progress *)
  | GR_HELPER           (* Helping peer restart *)
  | GR_DISABLED.        (* GR not supported/disabled *)

Inductive GREvent :=
  | GR_SESSION_ESTABLISHED : GracefulRestartCapability -> GREvent
  | GR_SESSION_LOST : bool -> GREvent  (* true if hard reset *)
  | GR_RESTART_TIMER_EXPIRED
  | GR_STALE_TIMER_EXPIRED
  | GR_END_OF_RIB_RECEIVED : word16 -> byte -> GREvent
  | GR_END_OF_RIB_SENT : word16 -> byte -> GREvent
  | GR_ROUTE_SELECTION_COMPLETED
  | GR_FORWARDING_STATE_LOST.

(* =============================================================================
   Section 4: Graceful Restart Session State
   ============================================================================= *)

Record GRSession := {
  grs_state : GRState;
  grs_peer_id : word32;
  grs_local_restart_time : N;
  grs_peer_restart_time : N;
  grs_negotiated_families : list GRTuple;
  
  (* Timers *)
  grs_restart_timer : option N;
  grs_stale_timer : option N;
  grs_selection_deferral_timer : option N;
  
  (* Flags *)
  grs_peer_restarting : bool;
  grs_forwarding_preserved : bool;
  grs_eor_received : list (word16 * byte);  (* AFI/SAFI pairs *)
  grs_eor_sent : list (word16 * byte);
  
  (* Statistics *)
  grs_restart_count : N;
  grs_helper_count : N
}.

(* Initialize GR session *)
Definition init_gr_session (peer_id : word32) : GRSession :=
  {| grs_state := GR_DISABLED;
     grs_peer_id := peer_id;
     grs_local_restart_time := DEFAULT_RESTART_TIME;
     grs_peer_restart_time := 0;
     grs_negotiated_families := [];
     grs_restart_timer := None;
     grs_stale_timer := None;
     grs_selection_deferral_timer := None;
     grs_peer_restarting := false;
     grs_forwarding_preserved := false;
     grs_eor_received := [];
     grs_eor_sent := [];
     grs_restart_count := 0;
     grs_helper_count := 0 |}.

(* =============================================================================
   Section 5: State Machine Transitions (RFC 4724 Section 4)
   ============================================================================= *)

Definition gr_state_transition (session : GRSession) (event : GREvent) (now : N)
                              : GRSession * list N := (* Actions *)
  match session.(grs_state), event with
  
  (* Session established with GR capability *)
  | GR_DISABLED, GR_SESSION_ESTABLISHED cap =>
      let peer_restarting := N.testbit cap.(gr_restart_flags) 3 in
      if peer_restarting then
        (* Peer is restarting, become helper *)
        ({| grs_state := GR_HELPER;
            grs_peer_id := session.(grs_peer_id);
            grs_local_restart_time := session.(grs_local_restart_time);
            grs_peer_restart_time := cap.(gr_restart_time);
            grs_negotiated_families := cap
