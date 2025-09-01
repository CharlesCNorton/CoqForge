(* =============================================================================
   Formal Verification of Path MTU Discovery
   
   Specification: RFC 1191 (J. Mogul, S. Deering, November 1990)
   Target: Path MTU Discovery for IPv4
   
   Module: Path MTU Discovery Formalization and Verification
   Author: Charles C Norton
   Date: September 1, 2025
   
   "Each word that Annatar spoke seemed to open doors long shut in their understanding."
   
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

(* Path MTU Constants (RFC 1191 Section 3) *)
Definition MIN_IPV4_MTU : N := 68.          (* Minimum IPv4 MTU *)
Definition MIN_PMTU : N := 576.             (* Minimum recommended PMTU *)
Definition DEFAULT_PMTU : N := 1500.        (* Ethernet default *)
Definition MAX_IPV4_HEADER : N := 60.       (* Maximum IPv4 header size *)

(* Plateau MTU values (RFC 1191 Section 7) *)
Definition MTU_PLATEAU_TABLE : list N :=
  [65535;  (* Maximum IPv4 packet *)
   32000;  (* Just in case *)
   17914;  (* 16Mb IBM Token Ring *)
   8166;   (* IEEE 802.4 *)
   4352;   (* FDDI *)
   4464;   (* IEEE 802.5 (4Mb max) *)
   2002;   (* IEEE 802.5 (4Mb recommended) *)
   1492;   (* IEEE 802.3 *)
   1500;   (* Ethernet *)
   1006;   (* SLIP/ARPANET *)
   576;    (* X.25 Networks *)
   508;    (* ARCNET *)
   296;    (* Point-to-Point (low delay) *)
   MIN_IPV4_MTU].

(* Timer Constants *)
Definition PMTU_TIMEOUT : N := 600000.       (* 10 minutes in milliseconds *)
Definition PMTU_RAISE_TIMER : N := 600000.   (* 10 minutes *)
Definition PMTU_PROBE_INTERVAL : N := 30000. (* 30 seconds *)

(* =============================================================================
   Section 2: ICMP Processing (RFC 1191 Section 4)
   ============================================================================= *)

(* ICMP Type 3 (Destination Unreachable) Codes *)
Definition ICMP_FRAG_NEEDED : byte := 4.

Record ICMPFragNeeded := {
  icmp_unused : word16;      (* Unused in original RFC 1191 *)
  icmp_next_hop_mtu : word16; (* Next-hop MTU (RFC 1191 Section 4) *)
  icmp_original_header : list byte;
  icmp_original_data : list byte  (* First 8 bytes of original *)
}.

(* Extract MTU from ICMP message *)
Definition extract_mtu_from_icmp (msg : ICMPFragNeeded) : N :=
  if N.eqb msg.(icmp_next_hop_mtu) 0 then
    (* Old router - estimate from original packet size *)
    estimate_mtu_from_packet msg.(icmp_original_header)
  else
    msg.(icmp_next_hop_mtu).

(* Estimate MTU using plateau table *)
Definition estimate_mtu_from_packet (header : list byte) : N :=
  (* Extract total length from IP header *)
  let packet_size := get_ip_total_length header in
  find_next_lower_plateau packet_size.

Definition find_next_lower_plateau (current_size : N) : N :=
  let fix find_plateau (table : list N) :=
    match table with
    | [] => MIN_PMTU
    | mtu :: rest =>
        if N.ltb mtu current_size then mtu
        else find_plateau rest
    end
  in find_plateau MTU_PLATEAU_TABLE.

Definition get_ip_total_length (header : list byte) : N :=
  match header with
  | _ :: _ :: len_high :: len_low :: _ =>
      len_high * 256 + len_low
  | _ => MIN_PMTU
  end.

(* =============================================================================
   Section 3: Path MTU Cache Entry (RFC 1191 Section 5)
   ============================================================================= *)

Record PMTUCacheEntry := {
  pmtu_destination : word32;
  pmtu_value : N;
  pmtu_last_updated : N;      (* Timestamp *)
  pmtu_last_decreased : N;    (* Last time MTU was decreased *)
  pmtu_last_increased : N;    (* Last time we tried to increase *)
  pmtu_locked : bool;          (* Don't increase if recently decreased *)
  pmtu_probe_count : N;        (* Number of probes sent *)
  pmtu_df_bit : bool          (* Don't Fragment bit setting *)
}.

(* Initialize PMTU entry *)
Definition init_pmtu_entry (dest : word32) : PMTUCacheEntry :=
  {| pmtu_destination := dest;
     pmtu_value := DEFAULT_PMTU;
     pmtu_last_updated := 0;
     pmtu_last_decreased := 0;
     pmtu_last_increased := 0;
     pmtu_locked := false;
     pmtu_probe_count := 0;
     pmtu_df_bit := true |}.

(* =============================================================================
   Section 4: Path MTU Discovery State Machine (RFC 1191 Section 5.1)
   ============================================================================= *)

Inductive PMTUState :=
  | PMTUActive      (* Actively discovering *)
  | PMTUPlateau     (* Found plateau value *)
  | PMTUProbing     (* Probing for larger MTU *)
  | PMTUDisabled.   (* PMTUD disabled *)

Record PMTUDiscovery := {
  pmtu_cache : list PMTUCacheEntry;
  pmtu_state : PMTUState;
  pmtu_host_mtu : N;          (* Local interface MTU *)
  pmtu_enable_discovery : bool;
  pmtu_enable_plateau : bool   (* Use plateau table *)
}.

(* Process ICMP Fragmentation Needed *)
Definition process_frag_needed (pd : PMTUDiscovery) (dest : word32) 
                              (icmp : ICMPFragNeeded) (now : N) 
                              : PMTUDiscovery :=
  let new_mtu := extract_mtu_from_icmp icmp in
  
  (* Find or create cache entry *)
  let update_entry (entry : PMTUCacheEntry) :=
    if N.eqb entry.(pmtu_destination) dest then
      if N.ltb new_mtu entry.(pmtu_value) then
        (* Decrease PMTU *)
        {| pmtu_destination := dest;
           pmtu_value := N.max MIN_PMTU new_mtu;
           pmtu_last_updated := now;
           pmtu_last_decreased := now;
           pmtu_last_increased := entry.(pmtu_last_increased);
           pmtu_locked := true;
           pmtu_probe_count := 0;
           pmtu_df_bit := true |}
      else
        entry
    else
      entry
  in
  
  {| pmtu_cache := map update_entry pd.(pmtu_cache);
     pmtu_state := pd.(pmtu_state);
     pmtu_host_mtu := pd.(pmtu_host_mtu);
     pmtu_enable_discovery := pd.(pmtu_enable_discovery);
     pmtu_enable_plateau := pd.(pmtu_enable_plateau) |}.

(* =============================================================================
   Section 5: Setting Don't Fragment Bit (RFC 1191 Section 6.1)
   ============================================================================= *)

Definition should_set_df_bit (pd : PMTUDiscovery) (dest : word32) : bool :=
  if pd.(pmtu_enable_discovery) then
    let find_entry (entries : list PMTUCacheEntry) :=
      find (fun e => N.eqb e.(pmtu_destination) dest) entries
    in
    match find_entry pd.(pmtu_cache) with
    | Some entry => entry.(pmtu_df_bit)
    | None => true  (* Default to setting DF *)
    end
  else
    false.

(* Check if packet size requires fragmentation *)
Definition needs_fragmentation (packet_size : N) (pmtu : N) : bool :=
  N.ltb pmtu packet_size.

(* =============================================================================
   Section 6: PMTU Aging and Timeout (RFC 1191 Section 6.3)
   ============================================================================= *)

Definition age_pmtu_entries (pd : PMTUDiscovery) (now : N) : PMTUDiscovery :=
  let age_entry (entry : PMTUCacheEntry) :=
    if N.ltb PMTU_TIMEOUT (now - entry.(pmtu_last_updated)) then
      (* Entry expired - reset to default *)
      {| pmtu_destination := entry.(pmtu_destination);
         pmtu_value := DEFAULT_PMTU;
         pmtu_last_updated := now;
         pmtu_last_decreased := entry.(pmtu_last_decreased);
         pmtu_last_increased := now;
         pmtu_locked := false;
         pmtu_probe_
