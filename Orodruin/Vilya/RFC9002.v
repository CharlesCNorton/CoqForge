(* =============================================================================
   Formal Verification of QUIC Loss Detection and Congestion Control
   
   Specification: RFC 9002 (J. Iyengar, I. Swett, May 2021)
   Target: QUIC Loss Detection and Congestion Control
   
   Module: QUIC Loss Detection and Congestion Control Formalization
   Author: Charles C Norton
   Date: September 1, 2025
   
   "Every failure he taught them to perceive, and to mend ere the marring grew great."
   
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

(* Timer Granularity *)
Definition kGranularity : N := 1.  (* 1ms *)

(* Initial RTT Constants *)
Definition kInitialRtt : N := 333.  (* 333ms *)

(* Loss Detection Constants *)
Definition kPacketThreshold : N := 3.
Definition kTimeThreshold : N := 9.  (* 9/8 *)
Definition kMicroSecond : N := 1.
Definition kMilliSecond : N := 1000.

(* Congestion Control Constants *)
Definition kMaxDatagramSize : N := 1200.
Definition kInitialWindow : N := 10 * kMaxDatagramSize.
Definition kMinimumWindow : N := 2 * kMaxDatagramSize.
Definition kLossReductionFactor : N := 2.

(* PTO Constants *)
Definition kPtoGranularity : N := 1.  (* 1ms *)
Definition kMaxPtoBackoff : N := 6.

(* =============================================================================
   Section 2: Packet Number Spaces
   ============================================================================= *)

Inductive PacketNumberSpace :=
  | Initial
  | Handshake
  | ApplicationData.

(* =============================================================================
   Section 3: Sent Packet Information
   ============================================================================= *)

Record SentPacket := {
  packet_number : word64;
  ack_eliciting : bool;
  in_flight : bool;
  sent_bytes : N;
  time_sent : N;
  pn_space : PacketNumberSpace;
  ecn_codepoint : N;  (* 0=Not-ECT, 1=ECT(1), 2=ECT(0), 3=CE *)
  frames : list N  (* Simplified frame representation *)
}.

(* =============================================================================
   Section 4: Loss Detection State
   ============================================================================= *)

Record LossDetectionState := {
  (* Per-packet-number-space state *)
  ld_sent_packets : list SentPacket;
  ld_largest_acked : option word64;
  ld_latest_rtt : N;
  ld_smoothed_rtt : N;
  ld_rttvar : N;
  ld_min_rtt : N;
  ld_first_rtt_sample : N;
  
  (* Loss detection *)
  ld_loss_time : option N;
  ld_pto_count : N;
  ld_last_ack_eliciting_time : N;
  
  (* ECN counts *)
  ld_ecn_ce_count : N;
  ld_ecn_ect0_count : N;
  ld_ecn_ect1_count : N
}.

(* Initialize loss detection *)
Definition init_loss_detection : LossDetectionState :=
  {| ld_sent_packets := [];
     ld_largest_acked := None;
     ld_latest_rtt := 0;
     ld_smoothed_rtt := kInitialRtt;
     ld_rttvar := kInitialRtt / 2;
     ld_min_rtt := 0;
     ld_first_rtt_sample := 0;
     ld_loss_time := None;
     ld_pto_count := 0;
     ld_last_ack_eliciting_time := 0;
     ld_ecn_ce_count := 0;
     ld_ecn_ect0_count := 0;
     ld_ecn_ect1_count := 0 |}.

(* =============================================================================
   Section 5: RTT Estimation (RFC 9002 Section 5)
   ============================================================================= *)

Definition update_rtt (ld : LossDetectionState) (latest_rtt : N) 
                      (ack_delay : N) (now : N) : LossDetectionState :=
  let min_rtt := if N.eqb ld.(ld_min_rtt) 0 
                 then latest_rtt
                 else N.min ld.(ld_min_rtt) latest_rtt in
  
  (* Adjust for ack delay if not handshake *)
  let adjusted_rtt := if N.ltb ack_delay latest_rtt
                      then latest_rtt - ack_delay
                      else latest_rtt in
  
  if N.eqb ld.(ld_first_rtt_sample) 0 then
    (* First RTT sample *)
    {| ld_sent_packets := ld.(ld_sent_packets);
       ld_largest_acked := ld.(ld_largest_acked);
       ld_latest_rtt := latest_rtt;
       ld_smoothed_rtt := adjusted_rtt;
       ld_rttvar := adjusted_rtt / 2;
       ld_min_rtt := min_rtt;
       ld_first_rtt_sample := now;
       ld_loss_time := ld.(ld_loss_time);
       ld_pto_count := ld.(ld_pto_count);
       ld_last_ack_eliciting_time := ld.(ld_last_ack_eliciting_time);
       ld_ecn_ce_count := ld.(ld_ecn_ce_count);
       ld_ecn_ect0_count := ld.(ld_ecn_ect0_count);
       ld_ecn_ect1_count := ld.(ld_ecn_ect1_count) |}
  else
    (* Subsequent RTT samples *)
    let rtt_diff := if N.ltb ld.(ld_smoothed_rtt) adjusted_rtt
                    then adjusted_rtt - ld.(ld_smoothed_rtt)
                    else ld.(ld_smoothed_rtt) - adjusted_rtt in
    let rttvar := (3 * ld.(ld_rttvar) + rtt_diff) / 4 in
    let smoothed_rtt := (7 * ld.(ld_smoothed_rtt) + adjusted_rtt) / 8 in
    
    {| ld_sent_packets := ld.(ld_sent_packets);
       ld_largest_acked := ld.(ld_largest_acked);
       ld_latest_rtt := latest_rtt;
       ld_smoothed_rtt := smoothed_rtt;
       ld_rttvar := rttvar;
       ld_min_rtt := min_rtt;
       ld_first_rtt_sample := ld.(ld_first_rtt_sample);
       ld_loss_time := ld.(ld_loss_time);
       ld_pto_count := ld.(ld_pto_count);
       ld_last_ack_eliciting_time := ld.(ld_last_ack_eliciting_time);
       ld_ecn_ce_count := ld.(ld_ecn_ce_count);
       ld_ecn_ect0_count := ld.(ld_ecn_ect0_count);
       ld_ecn_ect1_count := ld.(ld_ecn_ect1_count) |}.

(* =============================================================================
   Section 6: Loss Detection (RFC 9002 Section 6)
   ============================================================================= *)

(* Determine which packets are lost *)
Definition detect_lost_packets (ld : LossDetectionState) (now : N) 
                              : list SentPacket * LossDetectionState :=
  match ld.(ld_largest_acked) with
  | None => ([], ld)
  | Some largest_acked =>
      let loss_delay := N.max kGranularity 
                              ((kTimeThreshold * N.max ld.(ld_latest_rtt) ld.(ld_smoothed_rtt)) / 8) in
      let lost_send_time := now - loss_delay in
      
      let partition_packets (packets : list SentPacket) :=
        fold_left (fun acc pkt =>
          if orb (N.ltb (pkt.(packet_number) + kPacketThreshold) largest_acked)
                 (andb pkt.(in_flight) (N.leb pkt.(time_sent) lost_send_time))
          then (pkt :: fst acc, snd acc)
          else (fst acc, pkt :: snd acc))
        packets ([], [])
      in
      
      let (lost, remaining) := partition_packets ld.(ld_sent_packets) in
      (lost, {| ld_sent_packets := remaining;
                ld_largest_acked := ld.(ld_largest_acked);
                ld_latest_rtt := ld.(ld_latest_rtt);
                ld_smoothed_rtt := ld.(ld_smoothed_rtt);
                ld_rttvar := ld.(ld_rttvar);
                ld_min_rtt := ld.(ld_min_rtt);
                ld_first_rtt_sample := ld.(ld_first_rtt_sample);
                ld_loss_time := None;
                ld_pto_count := 0;
                ld_last_ack_eliciting_time := ld.(ld_last_ack_eliciting_time);
                ld_ecn_ce_count := ld.(ld_ecn_ce_count);
                ld_ecn_ect0_count := ld.(ld_ecn_ect0_count);
                ld_ecn_ect1_count := ld.(ld_ecn_ect1_count) |})
  end.

(* =============================================================================
   Section 7: Probe Timeout (PTO) Calculation (RFC 9002 Section 6.2)
   ============================================================================= *)

Definition compute_pto (ld : LossDetectionState) : N :=
  let pto := ld.(ld_smoothed_rtt) + N.max ld.(ld_rttvar) (4 * kGranularity) in
  pto * (N.shiftl 1 (N.min ld.(ld_pto_count) kMaxPtoBackoff)).

(* Set PTO timer *)
Definition set_pto_timer (ld : LossDetectionState) (now : N) : option N :=
  if existsb (fun pkt => pkt.(ack_eliciting)) ld.(ld_sent_packets) then
    Some (now + compute_pto ld)
  else
    None.

(* =============================================================================
   Section 8: Congestion Control State (RFC 9002 Section 7)
   ============================================================================= *)

Record CongestionControl := {
  cc_bytes_in_flight : N;
  cc_congestion_window : N;
  cc_congestion_recovery_start_time : option N;
  cc_ssthresh : N;
  cc_ecn_ce_counter : N;
  
  (* Pacing *)
  cc_pacing_rate : N;
  
  (* Statistics *)
  cc_bytes_sent : N;
  cc_bytes_acked : N;
  cc_bytes_lost : N
}.

(* Initialize congestion control *)
Definition init_congestion_control : CongestionControl :=
  {| cc_bytes_in_flight := 0;
     cc_congestion_window := kInitialWindow;
     cc_
