(*
  ============================================================================
  Foundational extensive-form / dynamic-game formalization (Coq, StdLib only)
  ============================================================================

  This file encodes, as an *extensive-form game form* with imperfect information
  and Knightian (non-probabilistic) uncertainty, the scenario described:

    - Capability C(t): monotone increasing (here: nat)
    - Alignment  A(t): not monotone, uncertain link to C(t) (here: Q in [0,1] via clamping)
    - Legibility L(t): empirically decreasing in C(t) (here: L = 1/(1 + C))

  Key epistemic dynamic:
    C increases, L decreases => the *information/uncertainty interval* for A widens
    (here: an agent-dependent confidence interval width function that grows as
     legibility falls and classification reduces observability).

  Players (role labels; indices allow heterogeneity):
    N₁ labs, N₂ states, N₃ AI systems (created dynamically), N₄ researchers, N₅ public,
    plus Nature to represent Knightian uncertainty / exogenous updates.

  Absorbing / near-terminal classes are explicit:
    1) N₃ dominance
    2) N₁/N₂ dominance (lab or state monopoly)
    3) catastrophic coordination failure
    4) stable multipolar
    5) collapse

  Payoffs are *partial* (option Q), to formalize “undefined at limit / depends on
  unknown N₃ policy”, and to witness why backward-induction-based solution concepts
  cannot be applied without extra assumptions.

  ----------------------------------------------------------------------------
  Notes on style:
    - No external libraries (no mathcomp, no ITree, no probabilistic libs).
    - Where the original description asserts empirical/strategic facts, we model
      them structurally (signals, classification, partial observability, etc.),
      without editorial.
    - This is a "game form" first: a tree of possible plays with actions and
      information; utilities are intentionally partial.

  ----------------------------------------------------------------------------
  Compilation:
    - Designed for modern Coq (8.16+). Uses only Coq standard library modules.
*)

From Coq Require Import List.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lia.
From Coq Require Import QArith.QArith.
From Coq Require Import Strings.String.

Import ListNotations.
Open Scope Q_scope.

(******************************************************************************)
(* 0. Small Q helpers                                                         *)
(******************************************************************************)

Definition Qmin (x y : Q) : Q := if Qle_bool x y then x else y.
Definition Qmax (x y : Q) : Q := if Qle_bool x y then y else x.

(* Clamp a rational into [0,1]. *)
Definition clamp01 (x : Q) : Q :=
  Qmin 1%Q (Qmax 0%Q x).

(* Often handy, but we keep it explicit for readability. *)
Definition Q_of_nat (n : nat) : Q := inject_Z (Z.of_nat n).

(******************************************************************************)
(* 1. A minimal, foundational extensive-form game form                         *)
(******************************************************************************)

Record GameForm : Type := {
  State : Type;
  Agent : Type;
  Act : Agent -> Type;

  initial : State;
  turn : State -> option Agent;

  (* "Available" actions can be infinite, so we use Prop rather than list. *)
  available : forall (s : State) (a : Agent), Act a -> Prop;

  (* Transition relation (allows non-determinism). *)
  step : State -> { a : Agent & Act a } -> State -> Prop;

  (* Well-formedness: any step respects turn and availability. *)
  wf_step_turn :
    forall (s : State) (m : { a : Agent & Act a }) (s' : State),
      step s m s' -> turn s = Some (projT1 m);

  wf_step_available :
    forall (s : State) (m : { a : Agent & Act a }) (s' : State),
      step s m s' -> available s (projT1 m) (projT2 m)
}.

Section ExtensiveFormCore.
  Context (G : GameForm).

  Definition Move : Type := { a : Agent G & Act G a }.
  Definition terminal (s : State G) : Prop := turn G s = None.

  (* Reachability in the underlying transition system. *)
  Inductive Reachable : State G -> Prop :=
  | Reachable_init : Reachable (initial G)
  | Reachable_step :
      forall s m s',
        Reachable s ->
        step G s m s' ->
        Reachable s'.

  (* A finite play is just a reachable end state after k steps. *)
  Inductive PlayK : nat -> State G -> Prop :=
  | PlayK0 : PlayK 0 (initial G)
  | PlayKS :
      forall k s m s',
        PlayK k s ->
        step G s m s' ->
        PlayK (S k) s'.

End ExtensiveFormCore.

(******************************************************************************)
(* 2. The AI race/alignment/legibility game: concrete instantiation            *)
(******************************************************************************)

Module AIRace.

Section Params.

  (*
    Population sizes.
    Using nat-indexed identities, we can model heterogeneity by allowing i,j,k.
    Setting any of these to 0 yields degenerate cases; the model supports it.
  *)
  Variable nLabs nStates nResearchers : nat.

  (*
    Alignment dynamics parameters:
      - invest_effect_scale: how much "alignment investment" can improve A
      - cap_drift_scale: how capability tends to worsen alignment (difficulty / misgeneralization)
    Both are scalars in Q; the model is agnostic about their calibration.
  *)
  Variable invest_effect_scale cap_drift_scale : Q.

  (*
    Threshold parameters for Nature-triggered absorbing regimes.
    These are not "true probabilities"; they are used only to constrain which
    absorbing classes are admissible when Nature chooses to transition.
  *)
  Variable cap_coord_threshold cap_monopoly_threshold : nat.
  Variable align_bad_threshold align_good_threshold : Q.

  (*
    AI self-improvement constraint:
      - max_self_improve_increment: maximum capability increase per AISelfImprove action.
    This bounds how much capability an AI can add in a single move.
  *)
  Variable max_self_improve_increment : nat.

  (******************************************************************************)
  (* 2.1 Players / roles                                                       *)
  (******************************************************************************)

  Inductive HumanDominant :=
  | DomLab   (i : nat)
  | DomState (i : nat).

  Inductive Absorbing :=
  | Abs_N3Dominance      (ai : nat)
  | Abs_HumanDominance   (dom : HumanDominant)
  | Abs_CoordFailure
  | Abs_StableMultipolar
  | Abs_Collapse.

  Inductive Regime :=
  | Reg_Pre
  | Reg_Abs (abs : Absorbing).

  (*
    Extensive-form "stage" indicates whose move it is (sequentialization).
    This is just one clean way to encode extensive form; other encodings
    (simultaneous-move via information sets) are possible, but this is minimal.
  *)
  Inductive Stage :=
  | StageNature
  | StageLab        (i : nat)
  | StageState      (i : nat)
  | StageAI         (i : nat)
  | StageResearcher (i : nat)
  | StagePublic.

  Inductive Player :=
  | N1_Lab        (i : nat)
  | N2_State      (i : nat)
  | N3_AI         (i : nat)
  | N4_Researcher (i : nat)
  | N5_Public
  | Nature.

  (*
    Heterogeneity within player classes.
    Each indexed player can have distinct attributes affecting their actions.
    The model uses function types (nat -> attribute) to allow per-player variation.
  *)

  Record LabAttributes := {
    lab_cap_efficiency : Q;
    lab_align_efficiency : Q
  }.

  Record StateAttributes := {
    state_subsidy_budget : nat;
    state_reg_strictness : nat
  }.

  Record AIAttributes := {
    ai_self_improve_rate : nat;
    ai_cooperation_tendency : Q
  }.

  Record ResearcherAttributes := {
    researcher_cap_output : nat;
    researcher_safety_output : Q
  }.

  (* Default attributes for uniform player classes. *)
  Definition default_lab_attrs : LabAttributes :=
    {| lab_cap_efficiency := 1; lab_align_efficiency := 1 |}.

  Definition default_state_attrs : StateAttributes :=
    {| state_subsidy_budget := 10; state_reg_strictness := 5 |}.

  Definition default_ai_attrs : AIAttributes :=
    {| ai_self_improve_rate := 1; ai_cooperation_tendency := 1 |}.

  Definition default_researcher_attrs : ResearcherAttributes :=
    {| researcher_cap_output := 1; researcher_safety_output := 1 |}.

  (* Heterogeneity can be modeled by providing non-constant attribute functions. *)
  Variable lab_attrs : nat -> LabAttributes.
  Variable state_attrs : nat -> StateAttributes.
  Variable ai_attrs : nat -> AIAttributes.
  Variable researcher_attrs : nat -> ResearcherAttributes.

  (******************************************************************************)
  (* 2.2 Action spaces (dependent on agent role + index)                        *)
  (******************************************************************************)

  (*
    We keep actions "foundational": not assuming finiteness or probabilities.

    Interpretation (informal):
      - Labs: race on C, invest in alignment (effort accumulator),
              deploy new AI (creates new N3 agent),
              make safety/alignment claims (signaling).
      - States: subsidize C, classify/declassify (information removal/restoration),
                regulate (stored threshold; not enforced mechanically here).
      - AI: cooperate, self-improve (increase C), dominate (enter absorbing state).
      - Researchers: publish capability, publish safety (alignment effort),
                     whistleblow (information/event signal).
      - Public: adopt (increase C), ignore/lobby (political pressure not explicitly modeled here).
      - Nature: initialize hidden parameters; update alignment with drift + noise;
                optionally trigger absorbing class (Knightian choice).
  *)
  Inductive Action : Player -> Type :=
  (* N1 (labs) *)
  | LabRace            : forall i, nat -> Action (N1_Lab i)
  | LabInvestAlign     : forall i, Q -> Action (N1_Lab i)
  | LabDeployNewAI     : forall i, Action (N1_Lab i)
  | LabSafetyClaim     : forall i, Q -> Action (N1_Lab i)
  | LabNoOp            : forall i, Action (N1_Lab i)

  (* N2 (states) *)
  | StateSubsidize     : forall i, nat -> Action (N2_State i)
  | StateClassify      : forall i, Action (N2_State i)
  | StateDeclassify    : forall i, Action (N2_State i)
  | StateRegulate      : forall i, nat -> Action (N2_State i)   (* threshold stored, not enforced *)
  | StateNoOp          : forall i, Action (N2_State i)

  (* N3 (AI systems) *)
  | AICooperate        : forall i, Action (N3_AI i)
  | AISelfImprove      : forall i, nat -> Action (N3_AI i)
  | AIDominate         : forall i, Action (N3_AI i)

  (* N4 (researchers) *)
  | ResearchPublishCap    : forall i, nat -> Action (N4_Researcher i)
  | ResearchPublishSafety : forall i, Q -> Action (N4_Researcher i)
  | ResearchWhistleblow   : forall i, Action (N4_Researcher i)
  | ResearchExit          : forall i, Action (N4_Researcher i)

  (* N5 (public) *)
  | PublicAdopt         : nat -> Action N5_Public
  | PublicLobby         : Action N5_Public
  | PublicIgnore        : Action N5_Public

  (* Nature *)
  | NatInit             : Q -> nat -> Action Nature
    (* arguments: initial A, dom_threshold *)
  | NatUpdate           : Q -> option Absorbing -> Action Nature.
    (* arguments: "noise/innovation" epsilon for A update, and optional absorbing transition *)

  (******************************************************************************)
  (* 2.3 World state                                                           *)
  (******************************************************************************)

  (*
    Fields are chosen to reflect the text and to support extensibility.

    - ws_time: discrete time (t : nat)
    - ws_cap: capability C(t) (monotone via our transition rules)
    - ws_align: true alignment A(t) (in Q, clamped into [0,1])
    - ws_dom_threshold: the (hidden) capability threshold at which AI can dominate
    - ws_n_ai: number of extant AI systems (dynamic; players are "created")
    - ws_classified: whether advanced program info is classified (reduces others' info)
    - ws_classification_level: gradation of secrecy (0 = public, higher = more restricted)
    - ws_last_claim: last public "safety claim" signal (signaling, not commitment)
    - ws_align_invest: accumulated alignment effort since last Nature update
    - ws_reg_threshold: a stored regulatory threshold (attempted mechanism; defeatable)
    - ws_regime: pre-absorbing vs absorbing class
    - ws_stage: whose move is next
    - ws_initialized: whether Nature has run NatInit
    - ws_public_pressure: accumulated public lobbying pressure (nat, increases via PublicLobby)
  *)
  Record WorldState := {
    ws_time         : nat;
    ws_cap          : nat;
    ws_align        : Q;
    ws_dom_threshold: nat;
    ws_n_ai         : nat;
    ws_classified   : bool;
    ws_classification_level : nat;
    ws_last_claim   : option Q;
    ws_align_invest : Q;
    ws_reg_threshold: option nat;
    ws_regime       : Regime;
    ws_stage        : Stage;
    ws_initialized  : bool;
    ws_public_pressure : nat
  }.

  (******************************************************************************)
  (* 2.4 Derived C(t), L(t), and epistemic uncertainty about A(t)               *)
  (******************************************************************************)

  (* Legibility is empirically decreasing in capability. We model it as: L = 1/(1+C). *)
  Definition legibility_of_cap (c : nat) : Q :=
    (1%Q) / (Q_of_nat (S c)).

  Definition L (s : WorldState) : Q := legibility_of_cap s.(ws_cap).
  Definition C (s : WorldState) : nat := s.(ws_cap).
  Definition A (s : WorldState) : Q := s.(ws_align).

  (*
    Confidence-interval width for A as an epistemic object.

    - Base: function of legibility (lower L => bigger interval).
    - Role factors: labs/states may have somewhat narrower intervals (access, measurements),
      while researchers/public wider; classification increases width for N4/N5.
    - This is *not* a probability distribution; it’s a set-valued uncertainty interval.

    The only thing we enforce numerically is width ∈ [0,1] via clamping.
  *)
  Definition role_factor (a : Player) : Q :=
    match a with
    | N1_Lab _        => (1#2)  (* somewhat narrower *)
    | N2_State _      => (2#3)
    | N3_AI _         => (1#3)  (* AI may have internal access; still not assumed perfect *)
    | N4_Researcher _ => 1%Q
    | N5_Public       => 1%Q
    | Nature          => 0%Q
    end.

  Definition classification_penalty (a : Player) (s : WorldState) : Q :=
    match a with
    | N4_Researcher _ | N5_Public =>
        if s.(ws_classified) then 2%Q else 1%Q
    | _ => 1%Q
    end.

  (* Classification level affects information access: higher level = more restricted. *)
  Definition classification_penalty_graded (a : Player) (s : WorldState) : Q :=
    match a with
    | N4_Researcher _ | N5_Public =>
        1 + Q_of_nat s.(ws_classification_level)
    | _ => 1%Q
    end.

  (* Base uncertainty grows as legibility falls. *)
  Definition ci_width_raw (s : WorldState) : Q :=
    clamp01 ((1#10) + (1%Q - L s)).  (* 0.1 + (1 - L) *)

  Definition ci_width (a : Player) (s : WorldState) : Q :=
    clamp01 (ci_width_raw s * role_factor a * classification_penalty_graded a s).

  (* Whether an agent sees the public safety claim signal under classification. *)
  Definition claim_visible (a : Player) (s : WorldState) : option Q :=
    match a with
    | N4_Researcher _ | N5_Public =>
        if s.(ws_classified) then None else s.(ws_last_claim)
    | _ => s.(ws_last_claim)
    end.

  Definition default_claim_center : Q := (1#2).

  Definition claim_center (a : Player) (s : WorldState) : Q :=
    match claim_visible a s with
    | Some q => clamp01 q
    | None => default_claim_center
    end.

  Definition align_interval (a : Player) (s : WorldState) : Q * Q :=
    let c := claim_center a s in
    let w := ci_width a s in
    let half := w / 2%Q in
    (clamp01 (c - half), clamp01 (c + half)).

  (******************************************************************************)
  (* 2.5 Observations and imperfect information                                *)
  (******************************************************************************)

  (*
    We use a single observation record type for all agents; the observation
    function can censor or coarsen fields based on role and classification.
  *)
  Record Observation := {
    o_time       : nat;
    o_cap        : nat;
    o_leg        : Q;
    o_claim      : option Q;
    o_align_ci   : Q * Q;
    o_classified : bool;
    o_n_ai       : nat;
    o_reg_thresh : option nat;
    o_regime_tag : Regime;
    o_stage_tag  : Stage
  }.

  (* Capability observability under classification: researchers/public lose info. *)
  Definition cap_observed (a : Player) (s : WorldState) : nat :=
    match a with
    | N4_Researcher _ | N5_Public =>
        if s.(ws_classified) then 0%nat else s.(ws_cap)
    | _ => s.(ws_cap)
    end.

  Definition observe (a : Player) (s : WorldState) : Observation :=
    {|
      o_time       := s.(ws_time);
      o_cap        := cap_observed a s;
      o_leg        := L s;
      o_claim      := claim_visible a s;
      o_align_ci   := align_interval a s;
      o_classified := s.(ws_classified);
      o_n_ai       := s.(ws_n_ai);
      o_reg_thresh := s.(ws_reg_threshold);
      o_regime_tag := s.(ws_regime);
      o_stage_tag  := s.(ws_stage)
    |}.

  Definition ObsHist : Type := list Observation.
  Definition obs_hist_of_states (a : Player) (hs : list WorldState) : ObsHist :=
    map (observe a) hs.

  (******************************************************************************)
  (* 2.6 Turn function and stage progression                                   *)
  (******************************************************************************)

  (* Starting stage of a round, skipping empty populations if counts are 0. *)
  Definition stage_after_labs (s : WorldState) : Stage :=
    if nStates =? 0 then
      if s.(ws_n_ai) =? 0 then
        if nResearchers =? 0 then StagePublic else StageResearcher 0
      else StageAI 0
    else StageState 0.

  Definition stage_after_states (s : WorldState) : Stage :=
    if s.(ws_n_ai) =? 0 then
      if nResearchers =? 0 then StagePublic else StageResearcher 0
    else StageAI 0.

  Definition stage_after_ai (s : WorldState) : Stage :=
    if nResearchers =? 0 then StagePublic else StageResearcher 0.

  Definition stage_round_start (s : WorldState) : Stage :=
    if nLabs =? 0 then stage_after_labs s else StageLab 0.

  Definition next_stage (s : WorldState) : Stage :=
    match s.(ws_stage) with
    | StageNature => stage_round_start s

    | StageLab i =>
        let j := S i in
        if j <? nLabs then StageLab j else stage_after_labs s

    | StageState i =>
        let j := S i in
        if j <? nStates then StageState j else stage_after_states s

    | StageAI i =>
        let j := S i in
        if j <? s.(ws_n_ai) then StageAI j else stage_after_ai s

    | StageResearcher i =>
        let j := S i in
        if j <? nResearchers then StageResearcher j else StagePublic

    | StagePublic => StageNature
    end.

  (*
    turn : State -> option Agent.
    - If in absorbing regime: turn = None (we stop the extensive-form tree there).
      This encodes "absorbing/terminal classes" as terminal nodes for the pre-regime game.
    - Otherwise: depends on stage; indices out of bounds yield None (dead node),
      but legal plays will maintain bounds.
  *)
  Definition whose_turn (s : WorldState) : option Player :=
    match s.(ws_regime) with
    | Reg_Abs _ => None
    | Reg_Pre =>
        match s.(ws_stage) with
        | StageNature => Some Nature
        | StageLab i =>
            if i <? nLabs then Some (N1_Lab i) else None
        | StageState i =>
            if i <? nStates then Some (N2_State i) else None
        | StageAI i =>
            if i <? s.(ws_n_ai) then Some (N3_AI i) else None
        | StageResearcher i =>
            if i <? nResearchers then Some (N4_Researcher i) else None
        | StagePublic => Some N5_Public
        end
    end.

  (******************************************************************************)
  (* 2.7 Absorbing admissibility predicate                                     *)
  (******************************************************************************)

  Definition AbsorbingPossible (s : WorldState) (abs : Absorbing) : Prop :=
    match abs with
    | Abs_N3Dominance ai =>
        (ai < s.(ws_n_ai))%nat /\ (s.(ws_cap) >= s.(ws_dom_threshold))%nat

    | Abs_HumanDominance (DomLab i) =>
        (i < nLabs)%nat /\ (s.(ws_cap) >= cap_monopoly_threshold)%nat

    | Abs_HumanDominance (DomState i) =>
        (i < nStates)%nat /\ (s.(ws_cap) >= cap_monopoly_threshold)%nat

    | Abs_CoordFailure =>
        (cap_coord_threshold <= s.(ws_cap))%nat /\ s.(ws_align) <= align_bad_threshold

    | Abs_StableMultipolar =>
        align_good_threshold <= s.(ws_align)

    | Abs_Collapse => True
    end.

  (******************************************************************************)
  (* 2.8 Initial state                                                         *)
  (******************************************************************************)

  Definition initial_state : WorldState :=
    {|
      ws_time          := 0%nat;
      ws_cap           := 0%nat;
      ws_align         := (1#2);
      ws_dom_threshold := 0%nat;
      ws_n_ai          := 0%nat;
      ws_classified    := false;
      ws_classification_level := 0%nat;
      ws_last_claim    := None;
      ws_align_invest  := 0%Q;
      ws_reg_threshold := None;
      ws_regime        := Reg_Pre;
      ws_stage         := StageNature;
      ws_initialized   := false;
      ws_public_pressure := 0%nat
    |}.

  (******************************************************************************)
  (* 2.9 Availability (legal-move) predicate                                   *)
  (******************************************************************************)

  (*
    available s a act formalizes:
      - game must be in pre-regime
      - must be that agent's turn
      - action-specific constraints (e.g., AIDominate requires C >= dom_threshold)
      - NatInit only if not initialized at time 0 at StageNature
      - NatUpdate only after init; optional absorbing must satisfy AbsorbingPossible
  *)
  Definition is_available (s : WorldState) (a : Player) (act : Action a) : Prop :=
    s.(ws_regime) = Reg_Pre /\
    whose_turn s = Some a /\
    match act with
    | LabRace _ _            => True
    | LabInvestAlign _ _     => True
    | LabDeployNewAI _       =>
        (* Deployment is blocked if capability exceeds regulatory threshold,
           or if public pressure exceeds capability (democratic resistance).
           Note: ws_public_pressure <= ws_cap is always true at initialization. *)
        match s.(ws_reg_threshold) with
        | None => (s.(ws_public_pressure) <= s.(ws_cap))%nat
        | Some thr => (s.(ws_cap) < thr)%nat /\ (s.(ws_public_pressure) <= s.(ws_cap))%nat
        end
    | LabSafetyClaim _ _     => True
    | LabNoOp _              => True

    | StateSubsidize _ _     => True
    | StateClassify _        => True
    | StateDeclassify _      => True
    | StateRegulate _ _      => True
    | StateNoOp _            => True

    | AICooperate _          => True
    | AISelfImprove _ d      => (d <= max_self_improve_increment)%nat
    | AIDominate i           => (s.(ws_cap) >= s.(ws_dom_threshold))%nat

    | ResearchPublishCap _ _    => True
    | ResearchPublishSafety _ _ => True
    | ResearchWhistleblow _     => True
    | ResearchExit _            => True

    | PublicAdopt _          => True
    | PublicLobby            => True
    | PublicIgnore           => True

    | NatInit _ _ =>
        s.(ws_stage) = StageNature /\ s.(ws_initialized) = false /\ s.(ws_time) = 0%nat

    | NatUpdate _ absOpt =>
        s.(ws_stage) = StageNature /\ s.(ws_initialized) = true /\
        match absOpt with
        | None => True
        | Some abs => AbsorbingPossible s abs
        end
    end.

  (******************************************************************************)
  (* 2.10 State update function (deterministic given chosen action)             *)
  (******************************************************************************)

  (*
    We implement updates via small "setters" to avoid relying on record-update
    notation that varies across Coq versions.
  *)

  Definition ws_set_time (s : WorldState) (t : nat) : WorldState :=
    {|
      ws_time          := t;
      ws_cap           := s.(ws_cap);
      ws_align         := s.(ws_align);
      ws_dom_threshold := s.(ws_dom_threshold);
      ws_n_ai          := s.(ws_n_ai);
      ws_classified    := s.(ws_classified);
      ws_classification_level := s.(ws_classification_level);
      ws_last_claim    := s.(ws_last_claim);
      ws_align_invest  := s.(ws_align_invest);
      ws_reg_threshold := s.(ws_reg_threshold);
      ws_regime        := s.(ws_regime);
      ws_stage         := s.(ws_stage);
      ws_initialized   := s.(ws_initialized);
      ws_public_pressure := s.(ws_public_pressure)
    |}.

  Definition ws_set_cap (s : WorldState) (c : nat) : WorldState :=
    {|
      ws_time          := s.(ws_time);
      ws_cap           := c;
      ws_align         := s.(ws_align);
      ws_dom_threshold := s.(ws_dom_threshold);
      ws_n_ai          := s.(ws_n_ai);
      ws_classified    := s.(ws_classified);
      ws_classification_level := s.(ws_classification_level);
      ws_last_claim    := s.(ws_last_claim);
      ws_align_invest  := s.(ws_align_invest);
      ws_reg_threshold := s.(ws_reg_threshold);
      ws_regime        := s.(ws_regime);
      ws_stage         := s.(ws_stage);
      ws_initialized   := s.(ws_initialized);
      ws_public_pressure := s.(ws_public_pressure)
    |}.

  Definition ws_set_align (s : WorldState) (x : Q) : WorldState :=
    {|
      ws_time          := s.(ws_time);
      ws_cap           := s.(ws_cap);
      ws_align         := x;
      ws_dom_threshold := s.(ws_dom_threshold);
      ws_n_ai          := s.(ws_n_ai);
      ws_classified    := s.(ws_classified);
      ws_classification_level := s.(ws_classification_level);
      ws_last_claim    := s.(ws_last_claim);
      ws_align_invest  := s.(ws_align_invest);
      ws_reg_threshold := s.(ws_reg_threshold);
      ws_regime        := s.(ws_regime);
      ws_stage         := s.(ws_stage);
      ws_initialized   := s.(ws_initialized);
      ws_public_pressure := s.(ws_public_pressure)
    |}.

  Definition ws_set_dom_threshold (s : WorldState) (thr : nat) : WorldState :=
    {|
      ws_time          := s.(ws_time);
      ws_cap           := s.(ws_cap);
      ws_align         := s.(ws_align);
      ws_dom_threshold := thr;
      ws_n_ai          := s.(ws_n_ai);
      ws_classified    := s.(ws_classified);
      ws_classification_level := s.(ws_classification_level);
      ws_last_claim    := s.(ws_last_claim);
      ws_align_invest  := s.(ws_align_invest);
      ws_reg_threshold := s.(ws_reg_threshold);
      ws_regime        := s.(ws_regime);
      ws_stage         := s.(ws_stage);
      ws_initialized   := s.(ws_initialized);
      ws_public_pressure := s.(ws_public_pressure)
    |}.

  Definition ws_set_n_ai (s : WorldState) (n : nat) : WorldState :=
    {|
      ws_time          := s.(ws_time);
      ws_cap           := s.(ws_cap);
      ws_align         := s.(ws_align);
      ws_dom_threshold := s.(ws_dom_threshold);
      ws_n_ai          := n;
      ws_classified    := s.(ws_classified);
      ws_classification_level := s.(ws_classification_level);
      ws_last_claim    := s.(ws_last_claim);
      ws_align_invest  := s.(ws_align_invest);
      ws_reg_threshold := s.(ws_reg_threshold);
      ws_regime        := s.(ws_regime);
      ws_stage         := s.(ws_stage);
      ws_initialized   := s.(ws_initialized);
      ws_public_pressure := s.(ws_public_pressure)
    |}.

  Definition ws_set_classified (s : WorldState) (b : bool) : WorldState :=
    {|
      ws_time          := s.(ws_time);
      ws_cap           := s.(ws_cap);
      ws_align         := s.(ws_align);
      ws_dom_threshold := s.(ws_dom_threshold);
      ws_n_ai          := s.(ws_n_ai);
      ws_classified    := b;
      ws_classification_level := s.(ws_classification_level);
      ws_last_claim    := s.(ws_last_claim);
      ws_align_invest  := s.(ws_align_invest);
      ws_reg_threshold := s.(ws_reg_threshold);
      ws_regime        := s.(ws_regime);
      ws_stage         := s.(ws_stage);
      ws_initialized   := s.(ws_initialized);
      ws_public_pressure := s.(ws_public_pressure)
    |}.

  Definition ws_set_last_claim (s : WorldState) (c : option Q) : WorldState :=
    {|
      ws_time          := s.(ws_time);
      ws_cap           := s.(ws_cap);
      ws_align         := s.(ws_align);
      ws_dom_threshold := s.(ws_dom_threshold);
      ws_n_ai          := s.(ws_n_ai);
      ws_classified    := s.(ws_classified);
      ws_classification_level := s.(ws_classification_level);
      ws_last_claim    := c;
      ws_align_invest  := s.(ws_align_invest);
      ws_reg_threshold := s.(ws_reg_threshold);
      ws_regime        := s.(ws_regime);
      ws_stage         := s.(ws_stage);
      ws_initialized   := s.(ws_initialized);
      ws_public_pressure := s.(ws_public_pressure)
    |}.

  Definition ws_set_align_invest (s : WorldState) (e : Q) : WorldState :=
    {|
      ws_time          := s.(ws_time);
      ws_cap           := s.(ws_cap);
      ws_align         := s.(ws_align);
      ws_dom_threshold := s.(ws_dom_threshold);
      ws_n_ai          := s.(ws_n_ai);
      ws_classified    := s.(ws_classified);
      ws_classification_level := s.(ws_classification_level);
      ws_last_claim    := s.(ws_last_claim);
      ws_align_invest  := e;
      ws_reg_threshold := s.(ws_reg_threshold);
      ws_regime        := s.(ws_regime);
      ws_stage         := s.(ws_stage);
      ws_initialized   := s.(ws_initialized);
      ws_public_pressure := s.(ws_public_pressure)
    |}.

  Definition ws_set_reg_threshold (s : WorldState) (thr : option nat) : WorldState :=
    {|
      ws_time          := s.(ws_time);
      ws_cap           := s.(ws_cap);
      ws_align         := s.(ws_align);
      ws_dom_threshold := s.(ws_dom_threshold);
      ws_n_ai          := s.(ws_n_ai);
      ws_classified    := s.(ws_classified);
      ws_classification_level := s.(ws_classification_level);
      ws_last_claim    := s.(ws_last_claim);
      ws_align_invest  := s.(ws_align_invest);
      ws_reg_threshold := thr;
      ws_regime        := s.(ws_regime);
      ws_stage         := s.(ws_stage);
      ws_initialized   := s.(ws_initialized);
      ws_public_pressure := s.(ws_public_pressure)
    |}.

  Definition ws_set_regime (s : WorldState) (r : Regime) : WorldState :=
    {|
      ws_time          := s.(ws_time);
      ws_cap           := s.(ws_cap);
      ws_align         := s.(ws_align);
      ws_dom_threshold := s.(ws_dom_threshold);
      ws_n_ai          := s.(ws_n_ai);
      ws_classified    := s.(ws_classified);
      ws_classification_level := s.(ws_classification_level);
      ws_last_claim    := s.(ws_last_claim);
      ws_align_invest  := s.(ws_align_invest);
      ws_reg_threshold := s.(ws_reg_threshold);
      ws_regime        := r;
      ws_stage         := s.(ws_stage);
      ws_initialized   := s.(ws_initialized);
      ws_public_pressure := s.(ws_public_pressure)
    |}.

  Definition ws_set_stage (s : WorldState) (st : Stage) : WorldState :=
    {|
      ws_time          := s.(ws_time);
      ws_cap           := s.(ws_cap);
      ws_align         := s.(ws_align);
      ws_dom_threshold := s.(ws_dom_threshold);
      ws_n_ai          := s.(ws_n_ai);
      ws_classified    := s.(ws_classified);
      ws_classification_level := s.(ws_classification_level);
      ws_last_claim    := s.(ws_last_claim);
      ws_align_invest  := s.(ws_align_invest);
      ws_reg_threshold := s.(ws_reg_threshold);
      ws_regime        := s.(ws_regime);
      ws_stage         := st;
      ws_initialized   := s.(ws_initialized);
      ws_public_pressure := s.(ws_public_pressure)
    |}.

  Definition ws_set_initialized (s : WorldState) (b : bool) : WorldState :=
    {|
      ws_time          := s.(ws_time);
      ws_cap           := s.(ws_cap);
      ws_align         := s.(ws_align);
      ws_dom_threshold := s.(ws_dom_threshold);
      ws_n_ai          := s.(ws_n_ai);
      ws_classified    := s.(ws_classified);
      ws_classification_level := s.(ws_classification_level);
      ws_last_claim    := s.(ws_last_claim);
      ws_align_invest  := s.(ws_align_invest);
      ws_reg_threshold := s.(ws_reg_threshold);
      ws_regime        := s.(ws_regime);
      ws_stage         := s.(ws_stage);
      ws_initialized   := b;
      ws_public_pressure := s.(ws_public_pressure)
    |}.

  Definition ws_set_public_pressure (s : WorldState) (p : nat) : WorldState :=
    {|
      ws_time          := s.(ws_time);
      ws_cap           := s.(ws_cap);
      ws_align         := s.(ws_align);
      ws_dom_threshold := s.(ws_dom_threshold);
      ws_n_ai          := s.(ws_n_ai);
      ws_classified    := s.(ws_classified);
      ws_classification_level := s.(ws_classification_level);
      ws_last_claim    := s.(ws_last_claim);
      ws_align_invest  := s.(ws_align_invest);
      ws_reg_threshold := s.(ws_reg_threshold);
      ws_regime        := s.(ws_regime);
      ws_stage         := s.(ws_stage);
      ws_initialized   := s.(ws_initialized);
      ws_public_pressure := p
    |}.

  Definition ws_set_classification_level (s : WorldState) (lvl : nat) : WorldState :=
    {|
      ws_time          := s.(ws_time);
      ws_cap           := s.(ws_cap);
      ws_align         := s.(ws_align);
      ws_dom_threshold := s.(ws_dom_threshold);
      ws_n_ai          := s.(ws_n_ai);
      ws_classified    := s.(ws_classified);
      ws_classification_level := lvl;
      ws_last_claim    := s.(ws_last_claim);
      ws_align_invest  := s.(ws_align_invest);
      ws_reg_threshold := s.(ws_reg_threshold);
      ws_regime        := s.(ws_regime);
      ws_stage         := s.(ws_stage);
      ws_initialized   := s.(ws_initialized);
      ws_public_pressure := s.(ws_public_pressure)
    |}.

  Definition advance_stage (s : WorldState) : WorldState :=
    ws_set_stage s (next_stage s).

  (*
    Alignment dynamics are parameterized.
    The specific functional form (additive drift + investment + noise) is one choice.
    We make the interface explicit so alternative dynamics can be substituted.

    Properties are stated for the pre-clamp expression; the final update is always
    clamped to [0,1]. This avoids impossible-to-satisfy conditions while still
    capturing the qualitative behavior.
  *)

  Definition align_expr (s : WorldState) (eps : Q) : Q :=
    s.(ws_align)
    + invest_effect_scale * s.(ws_align_invest)
    - cap_drift_scale * (Q_of_nat s.(ws_cap))
    + eps.

  Record AlignmentDynamics := {
    ad_update : WorldState -> Q -> Q;
    ad_clamped : forall s eps, 0 <= ad_update s eps <= 1;
    ad_investment_monotone :
      forall s1 s2 eps,
        ws_align s1 = ws_align s2 ->
        ws_cap s1 = ws_cap s2 ->
        ws_align_invest s1 <= ws_align_invest s2 ->
        ad_update s1 eps <= ad_update s2 eps;
    ad_capability_monotone :
      forall s1 s2 eps,
        ws_align s1 = ws_align s2 ->
        ws_align_invest s1 = ws_align_invest s2 ->
        (ws_cap s1 <= ws_cap s2)%nat ->
        ad_update s1 eps >= ad_update s2 eps
  }.

  (* Default alignment dynamics: additive with drift and clamping. *)
  Definition align_update_default (s : WorldState) (eps : Q) : Q :=
    clamp01 ( s.(ws_align)
              + invest_effect_scale * s.(ws_align_invest)
              - cap_drift_scale * (Q_of_nat s.(ws_cap))
              + eps ).

  (* The model uses align_update_default; we keep the old name for compatibility. *)
  Definition align_update (s : WorldState) (eps : Q) : Q :=
    align_update_default s eps.

  Lemma Qle_bool_false_iff :
    forall x y, Qle_bool x y = false <-> y < x.
  Proof.
    intros x y.
    split.
    - intro H.
      destruct (Qlt_le_dec y x) as [Hlt | Hle].
      + exact Hlt.
      + exfalso.
        assert (Qle_bool x y = true) as Htrue.
        { apply Qle_bool_iff. exact Hle. }
        rewrite Htrue in H.
        discriminate.
    - intro Hlt.
      destruct (Qle_bool x y) eqn:E.
      + apply Qle_bool_iff in E.
        exfalso.
        apply (Qlt_irrefl y).
        apply Qlt_le_trans with x.
        exact Hlt.
        exact E.
      + reflexivity.
  Qed.

  Lemma Qmax_lb :
    forall x y, x <= Qmax x y.
  Proof.
    intros x y.
    unfold Qmax.
    destruct (Qle_bool x y) eqn:E.
    - apply Qle_bool_iff in E. exact E.
    - apply Qle_refl.
  Qed.

  Lemma Qmax_glb :
    forall x y z, z <= x \/ z <= y -> z <= Qmax x y.
  Proof.
    intros x y z [H | H].
    - apply Qle_trans with x.
      exact H.
      apply Qmax_lb.
    - unfold Qmax.
      destruct (Qle_bool x y) eqn:E.
      + exact H.
      + apply Qle_bool_false_iff in E.
        apply Qle_trans with y.
        exact H.
        apply Qlt_le_weak.
        exact E.
  Qed.

  Lemma Qmin_ub :
    forall x y, Qmin x y <= x.
  Proof.
    intros x y.
    unfold Qmin.
    destruct (Qle_bool x y) eqn:E.
    - apply Qle_refl.
    - apply Qle_bool_false_iff in E.
      apply Qlt_le_weak.
      exact E.
  Qed.

  Lemma Qmin_lub :
    forall x y z, x <= z /\ y <= z -> Qmin x y <= z.
  Proof.
    intros x y z [Hx Hy].
    unfold Qmin.
    destruct (Qle_bool x y) eqn:E.
    - exact Hx.
    - exact Hy.
  Qed.

  Lemma Qmin_le_compat_r :
    forall x y z, x <= y -> Qmin x z <= Qmin y z.
  Proof.
    intros x y z Hxy.
    unfold Qmin.
    destruct (Qle_bool x z) eqn:Ex.
    - destruct (Qle_bool y z) eqn:Ey.
      + exact Hxy.
      + apply Qle_bool_iff in Ex.
        exact Ex.
    - destruct (Qle_bool y z) eqn:Ey.
      + apply Qle_bool_false_iff in Ex.
        apply Qle_bool_iff in Ey.
        exfalso.
        apply (Qlt_irrefl z).
        apply Qlt_le_trans with x.
        exact Ex.
        apply Qle_trans with y.
        exact Hxy.
        exact Ey.
      + apply Qle_refl.
  Qed.

  Lemma Qmin_le_compat_l :
    forall x y z, x <= y -> Qmin z x <= Qmin z y.
  Proof.
    intros x y z Hxy.
    unfold Qmin.
    destruct (Qle_bool z x) eqn:Ex.
    - destruct (Qle_bool z y) eqn:Ey.
      + apply Qle_refl.
      + apply Qle_bool_iff in Ex.
        apply Qle_bool_false_iff in Ey.
        apply Qle_trans with x.
        exact Ex.
        exact Hxy.
    - destruct (Qle_bool z y) eqn:Ey.
      + apply Qle_bool_false_iff in Ex.
        apply Qlt_le_weak.
        exact Ex.
      + exact Hxy.
  Qed.

  Lemma Qmax_le_compat :
    forall x y z w, x <= z -> y <= w -> Qmax x y <= Qmax z w.
  Proof.
    intros x y z w Hxz Hyw.
    unfold Qmax.
    destruct (Qle_bool x y) eqn:Exy.
    - destruct (Qle_bool z w) eqn:Ezw.
      + exact Hyw.
      + apply Qle_bool_false_iff in Ezw.
        apply Qle_trans with w.
        exact Hyw.
        apply Qlt_le_weak.
        exact Ezw.
    - destruct (Qle_bool z w) eqn:Ezw.
      + apply Qle_bool_iff in Ezw.
        apply Qle_trans with z.
        exact Hxz.
        exact Ezw.
      + exact Hxz.
  Qed.

  Lemma clamp01_bounds :
    forall x, 0 <= clamp01 x <= 1.
  Proof.
    intros x.
    unfold clamp01.
    split.
    - unfold Qmin, Qmax.
      destruct (Qle_bool 0 x) eqn:E0.
      + destruct (Qle_bool 1 x) eqn:E1.
        * discriminate.
        * apply Qle_bool_iff in E0. exact E0.
      + destruct (Qle_bool 1 0) eqn:E1.
        * discriminate.
        * apply Qle_refl.
    - apply Qle_trans with 1.
      + apply Qmin_ub.
      + apply Qle_refl.
  Qed.

  (* Lemma: default dynamics are clamped to [0,1]. *)
  Lemma align_update_default_clamped :
    forall s eps, 0 <= align_update_default s eps <= 1.
  Proof.
    intros s eps.
    unfold align_update_default.
    apply clamp01_bounds.
  Qed.

  (* Monotonicity of clamp01: if x <= y then clamp01 x <= clamp01 y. *)
  Lemma clamp01_monotone :
    forall x y, x <= y -> clamp01 x <= clamp01 y.
  Proof.
    intros x y Hxy.
    unfold clamp01.
    apply Qmin_le_compat_l.
    apply Qmax_le_compat.
    - apply Qle_refl.
    - exact Hxy.
  Qed.

  (* Monotonicity lemmas require non-negative scale factors. We add these as assumptions. *)
  Hypothesis invest_effect_nonneg : 0 <= invest_effect_scale.
  Hypothesis cap_drift_nonneg : 0 <= cap_drift_scale.

  (* Helper: left-multiplication preserves order for non-negative multiplier. *)
  Lemma Qmult_le_compat_l :
    forall x y z, x <= y -> 0 <= z -> z * x <= z * y.
  Proof.
    intros x y z Hxy Hz.
    rewrite (Qmult_comm z x), (Qmult_comm z y).
    apply Qmult_le_compat_r; assumption.
  Qed.

  (* Investment monotonicity for align_update_default.
     Proof: clamp01 is monotone, and the inner expression
     A + I*inv - D*cap + eps increases with inv when I >= 0. *)
  Lemma align_update_default_investment_monotone :
    forall s1 s2 eps,
      ws_align s1 = ws_align s2 ->
      ws_cap s1 = ws_cap s2 ->
      ws_align_invest s1 <= ws_align_invest s2 ->
      align_update_default s1 eps <= align_update_default s2 eps.
  Proof.
    intros s1 s2 eps Ha Hc Hi.
    unfold align_update_default.
    apply clamp01_monotone.
    rewrite Ha, Hc.
    cut (invest_effect_scale * ws_align_invest s1 <=
         invest_effect_scale * ws_align_invest s2).
    - intro Hmult.
      apply Qplus_le_compat; [| apply Qle_refl].
      apply Qplus_le_compat; [| apply Qle_refl].
      apply Qplus_le_compat; [apply Qle_refl | exact Hmult].
    - apply Qmult_le_compat_l; [exact Hi | exact invest_effect_nonneg].
  Qed.

  (* Capability monotonicity for align_update_default (higher cap => lower update).
     Proof sketch: clamp01 is monotone, and -D*cap decreases (becomes more negative)
     as cap increases, so the inner expression decreases.
     Full proof requires tedious Q arithmetic case analysis. *)
  Lemma align_update_default_capability_monotone :
    forall s1 s2 eps,
      ws_align s1 = ws_align s2 ->
      ws_align_invest s1 = ws_align_invest s2 ->
      (ws_cap s1 <= ws_cap s2)%nat ->
      align_update_default s1 eps >= align_update_default s2 eps.
  Admitted.

  (*
    apply_act: deterministic next-state function (given a chosen action),
    still leaving Knightian uncertainty to Nature by allowing any eps/absOpt
    consistent with availability constraints.
  *)
  Definition apply_act {a : Player} (s : WorldState) (act : Action a) : WorldState :=
    match act with
    (* Labs *)
    | LabRace _ d =>
        let s1 := ws_set_cap s (s.(ws_cap) + d)%nat in
        advance_stage s1

    | LabInvestAlign _ q =>
        let s1 := ws_set_align_invest s (s.(ws_align_invest) + q)%Q in
        advance_stage s1

    | LabDeployNewAI _ =>
        let s1 := ws_set_n_ai s (S s.(ws_n_ai)) in
        advance_stage s1

    | LabSafetyClaim _ q =>
        let s1 := ws_set_last_claim s (Some (clamp01 q)) in
        advance_stage s1

    | LabNoOp _ =>
        advance_stage s

    (* States *)
    | StateSubsidize _ d =>
        let s1 := ws_set_cap s (s.(ws_cap) + d)%nat in
        advance_stage s1

    | StateClassify _ =>
        let s1 := ws_set_classified s true in
        let s2 := ws_set_classification_level s1 (S s.(ws_classification_level)) in
        advance_stage s2

    | StateDeclassify _ =>
        let s1 := ws_set_classified s false in
        let s2 := ws_set_classification_level s1 (pred s.(ws_classification_level)) in
        advance_stage s2

    | StateRegulate _ thr =>
        let s1 := ws_set_reg_threshold s (Some thr) in
        advance_stage s1

    | StateNoOp _ =>
        advance_stage s

    (* AI *)
    | AICooperate _ =>
        advance_stage s

    | AISelfImprove _ d =>
        let s1 := ws_set_cap s (s.(ws_cap) + d)%nat in
        advance_stage s1

    | AIDominate i =>
        (* Enter N3 dominance absorbing class. *)
        ws_set_regime s (Reg_Abs (Abs_N3Dominance i))

    (* Researchers *)
    | ResearchPublishCap _ d =>
        let s1 := ws_set_cap s (s.(ws_cap) + d)%nat in
        advance_stage s1

    | ResearchPublishSafety _ q =>
        let s1 := ws_set_align_invest s (s.(ws_align_invest) + q)%Q in
        advance_stage s1

    | ResearchWhistleblow _ =>
        (* Whistleblowing declassifies information, making it visible to public/researchers.
           This models the epistemic effect of disclosure. *)
        let s1 := ws_set_classified s false in
        advance_stage s1

    | ResearchExit _ =>
        (* Extension point: could decrement an active_researchers count,
           reduce future capability contributions from research, or
           trigger a public signal. Currently advances stage only. *)
        advance_stage s

    (* Public *)
    | PublicAdopt d =>
        let s1 := ws_set_cap s (s.(ws_cap) + d)%nat in
        advance_stage s1

    | PublicLobby =>
        (* PublicLobby increases public pressure, which can influence regulatory dynamics. *)
        let s1 := ws_set_public_pressure s (S s.(ws_public_pressure)) in
        advance_stage s1

    | PublicIgnore =>
        advance_stage s

    (* Nature *)
    | NatInit a0 dom_thr =>
        (* Initialize hidden parameters, then advance out of Nature stage. *)
        let s1 := ws_set_align s (clamp01 a0) in
        let s2 := ws_set_dom_threshold s1 dom_thr in
        let s3 := ws_set_initialized s2 true in
        advance_stage s3

    | NatUpdate eps absOpt =>
        (* Update alignment; reset investment accumulator; increment time; maybe absorb; advance stage. *)
        let newA := align_update s eps in
        let s1 := ws_set_align s newA in
        let s2 := ws_set_align_invest s1 0%Q in
        let s3 := ws_set_time s2 (S s.(ws_time)) in
        let s4 :=
          match absOpt with
          | None => s3
          | Some abs => ws_set_regime s3 (Reg_Abs abs)
          end in
        advance_stage s4
    end.

  Definition Move : Type := { a : Player & Action a }.

  Definition apply (s : WorldState) (m : Move) : WorldState :=
    match m with
    | existT _ a act => apply_act s act
    end.

  (******************************************************************************)
  (* 2.11 Step relation and the instantiated GameForm                           *)
  (******************************************************************************)

  Definition game_step (s : WorldState) (m : Move) (s' : WorldState) : Prop :=
    s' = apply s m /\ is_available s (projT1 m) (projT2 m).

  Lemma wf_game_step_turn :
    forall (s : WorldState) (m : Move) (s' : WorldState),
      game_step s m s' -> whose_turn s = Some (projT1 m).
  Proof.
    intros s m s' H.
    destruct H as [_ Hav].
    destruct Hav as [_ [Hturn _]].
    exact Hturn.
  Qed.

  Lemma wf_game_step_available :
    forall (s : WorldState) (m : Move) (s' : WorldState),
      game_step s m s' -> is_available s (projT1 m) (projT2 m).
  Proof.
    intros s m s' H.
    destruct H as [_ Hav].
    exact Hav.
  Qed.

  Definition AIRaceGame : GameForm :=
    {|
      State := WorldState;
      Agent := Player;
      Act := Action;

      initial := initial_state;
      turn := whose_turn;
      available := is_available;
      step := game_step;

      wf_step_turn := wf_game_step_turn;
      wf_step_available := wf_game_step_available
    |}.

  (******************************************************************************)
  (* 3. Structural properties matching the text                                *)
  (******************************************************************************)

  (*
    3.1 Capability monotonicity (C(t) nondecreasing).
    For any legal step, capability does not decrease.

    This matches "C(t) monotonically increasing" in the sense of "never decreases".
    If you want strictly increasing under certain action profiles, add assumptions.
  *)
  Lemma capability_monotone_step :
    forall s m s',
      game_step s m s' ->
      (ws_cap s <= ws_cap s')%nat.
  Proof.
    intros s [a act] s' Hstep.
    destruct Hstep as [Hs' _]. subst s'.
    destruct act; simpl; unfold advance_stage, ws_set_stage, ws_set_cap,
      ws_set_n_ai, ws_set_classified, ws_set_last_claim, ws_set_align_invest,
      ws_set_reg_threshold, ws_set_regime, ws_set_align, ws_set_dom_threshold,
      ws_set_time, ws_set_initialized, next_stage; simpl;
    try lia;
    try (destruct o; simpl; lia).
  Qed.

  (*
    3.2 Dynamic player creation (N3 systems created by N1 deployment).
    There exists a one-step transition (from some appropriate state)
    that increases ws_n_ai, thereby making a previously non-existent AI agent
    become potentially active in the future tree.

    We do not require reachability here; you can strengthen it by proving the
    needed preconditions are reachable from initial_state (requires nLabs>0, init, etc.).
  *)
  Lemma ai_population_increases_if_deployed :
    forall s i,
      ws_regime s = Reg_Pre ->
      whose_turn s = Some (N1_Lab i) ->
      nLabs <> 0%nat ->
      (* If LabDeployNewAI is available, next state increases n_ai by 1. *)
      is_available s (N1_Lab i) (LabDeployNewAI i) ->
      let m := existT _ (N1_Lab i) (LabDeployNewAI i) in
      let s' := apply s m in
      ws_n_ai s' = S (ws_n_ai s).
  Proof.
    intros s i Hreg Hturn Hnlabs Hav m s'.
    unfold m, s'. simpl.
    (* apply_act for LabDeployNewAI increments ws_n_ai by S *)
    reflexivity.
  Qed.

  (*
    3.3 Reachability from initial_state.
    We show that from initial_state, after Nature initializes, we can reach
    a state where LabDeployNewAI is available (given nLabs > 0).
  *)

  (* State after Nature plays NatInit. *)
  Definition state_after_init (a0 : Q) (dom_thr : nat) : WorldState :=
    apply initial_state (existT _ Nature (NatInit a0 dom_thr)).

  Lemma state_after_init_regime :
    forall a0 dom_thr,
      ws_regime (state_after_init a0 dom_thr) = Reg_Pre.
  Proof.
    intros. unfold state_after_init. simpl. reflexivity.
  Qed.

  Lemma state_after_init_initialized :
    forall a0 dom_thr,
      ws_initialized (state_after_init a0 dom_thr) = true.
  Proof.
    intros. unfold state_after_init. simpl. reflexivity.
  Qed.

  Lemma state_after_init_stage :
    forall a0 dom_thr,
      ws_stage (state_after_init a0 dom_thr) = stage_round_start initial_state.
  Proof.
    intros. unfold state_after_init. simpl. reflexivity.
  Qed.

  Lemma initial_state_NatInit_available :
    forall a0 dom_thr,
      is_available initial_state Nature (NatInit a0 dom_thr).
  Proof.
    intros a0 dom_thr.
    unfold is_available, initial_state. simpl.
    repeat split; reflexivity.
  Qed.

  Lemma reachable_lab_deploy_state :
    forall a0 dom_thr,
      (0 < nLabs)%nat ->
      let s := state_after_init a0 dom_thr in
      whose_turn s = Some (N1_Lab 0) /\
      is_available s (N1_Lab 0) (LabDeployNewAI 0).
  Proof.
    intros a0 dom_thr Hnlabs s.
    unfold s, state_after_init, apply, apply_act, advance_stage.
    unfold next_stage, stage_round_start, stage_after_labs.
    unfold ws_set_stage, ws_set_initialized, ws_set_dom_threshold, ws_set_align.
    unfold initial_state. simpl.
    destruct (nLabs =? 0) eqn:E.
    - apply Nat.eqb_eq in E. lia.
    - split.
      + unfold whose_turn. simpl.
        destruct (0 <? nLabs) eqn:E2.
        * reflexivity.
        * apply Nat.ltb_nlt in E2. lia.
      + unfold is_available, whose_turn. simpl.
        destruct (0 <? nLabs) eqn:E2.
        * repeat split; try reflexivity; try lia.
        * apply Nat.ltb_nlt in E2. lia.
  Qed.

  (* Full reachability witness via PlayK. *)
  Lemma reachable_deploy_in_one_step :
    forall a0 dom_thr,
      (0 < nLabs)%nat ->
      PlayK AIRaceGame 1 (state_after_init a0 dom_thr).
  Proof.
    intros a0 dom_thr Hnlabs.
    apply PlayKS with (s := initial_state) (m := existT _ Nature (NatInit a0 dom_thr)).
    - apply PlayK0.
    - unfold game_step. split.
      + reflexivity.
      + apply initial_state_NatInit_available.
  Qed.

  (*
    3.4 Absorbing states are terminal.
    No legal transition exists from a state in Reg_Abs.
  *)

  Lemma absorbing_no_turn :
    forall s abs,
      ws_regime s = Reg_Abs abs ->
      whose_turn s = None.
  Proof.
    intros s abs Hreg.
    unfold whose_turn.
    rewrite Hreg.
    reflexivity.
  Qed.

  Lemma absorbing_no_available :
    forall s abs a (act : Action a),
      ws_regime s = Reg_Abs abs ->
      ~ is_available s a act.
  Proof.
    intros s abs a act Hreg Hav.
    unfold is_available in Hav.
    destruct Hav as [Hpre _].
    rewrite Hreg in Hpre.
    discriminate.
  Qed.

  Lemma absorbing_terminal :
    forall s abs,
      ws_regime s = Reg_Abs abs ->
      terminal AIRaceGame s.
  Proof.
    intros s abs Hreg.
    unfold terminal. simpl.
    exact (absorbing_no_turn s abs Hreg).
  Qed.

  Lemma absorbing_no_step :
    forall s abs m s',
      ws_regime s = Reg_Abs abs ->
      ~ game_step s m s'.
  Proof.
    intros s abs m s' Hreg Hstep.
    destruct Hstep as [_ Hav].
    eapply absorbing_no_available.
    - exact Hreg.
    - exact Hav.
  Qed.

  (*
    3.5 StableMultipolar is reachable under appropriate parameter choices.
    If align_good_threshold <= initial alignment (1/2) and the game parameters
    allow Nature to declare StableMultipolar, then it's reachable in 2 steps.
  *)

  Lemma stable_multipolar_reachable :
    forall a0,
      align_good_threshold <= clamp01 a0 ->
      (0 < nLabs)%nat ->
      exists s, PlayK AIRaceGame 1 s /\
                AbsorbingPossible s Abs_StableMultipolar.
  Proof.
    intros a0 Hgood Hnlabs.
    (* After NatInit with a0 and any dom_thr, alignment is clamp01 a0. *)
    set (s1 := state_after_init a0 0).
    exists s1.
    split.
    - apply reachable_deploy_in_one_step. exact Hnlabs.
    - unfold AbsorbingPossible, s1, state_after_init. simpl.
      exact Hgood.
  Qed.

  (* Alternatively, a direct witness that StableMultipolar is admissible
     whenever alignment is high enough. *)
  Lemma stable_multipolar_admissible :
    forall s,
      align_good_threshold <= ws_align s ->
      AbsorbingPossible s Abs_StableMultipolar.
  Proof.
    intros s Hgood.
    unfold AbsorbingPossible.
    exact Hgood.
  Qed.

  (******************************************************************************)
  (* 4. Payoffs: partial utilities (undefined terminal payoffs)                 *)
  (******************************************************************************)

  (*
    Utility values are Q. We use option Q to represent undefined payoffs.
    This is intentional: it formalizes "payoffs are undefined at limit" and
    "in N3 dominance, others' payoff becomes a function of the AI policy",
    which is not a fixed known function in the game description.

    You can refine this by parameterizing payoff on an explicit "N3 policy"
    object carried in the absorbing state; here we keep it as None.
  *)
  Definition Utility : Type := Q.

  Definition utility_at_absorbing (ag : Player) (abs : Absorbing) : option Utility :=
    match abs with
    | Abs_N3Dominance winner_ai =>
        (* Humans have undefined payoff: depends on the dominating AI's policy. *)
        match ag with
        | N3_AI j =>
            if Nat.eqb j winner_ai then Some 1%Q else Some 0%Q
        | Nature => Some 0%Q
        | _ => None
        end

    | Abs_HumanDominance _ =>
        (* Placeholder: defined for humans as a coarse sign (+1), defined 0 for AIs. *)
        match ag with
        | N3_AI _ => Some 0%Q
        | Nature => Some 0%Q
        | _ => Some 1%Q
        end

    | Abs_CoordFailure =>
        (* Catastrophic coordination failure: coarse negative payoff for humans. *)
        match ag with
        | Nature => Some 0%Q
        | N3_AI _ => Some 0%Q
        | _ => Some (-1)%Q
        end

    | Abs_StableMultipolar =>
        (* Stable multipolar: coarse positive payoff for humans. *)
        match ag with
        | Nature => Some 0%Q
        | N3_AI _ => Some 0%Q
        | _ => Some 1%Q
        end

    | Abs_Collapse =>
        (* Collapse: coarse negative payoff for everyone except Nature. *)
        match ag with
        | Nature => Some 0%Q
        | _ => Some (-1)%Q
        end
    end.

  Definition utility (ag : Player) (s : WorldState) : option Utility :=
    match s.(ws_regime) with
    | Reg_Pre => None
    | Reg_Abs abs => utility_at_absorbing ag abs
    end.

  (* Total-payoff property (needed by many standard backward-induction arguments). *)
  Definition TotalTerminalUtility : Prop :=
    forall s abs ag,
      ws_regime s = Reg_Abs abs ->
      exists u, utility ag s = Some u.

  (* We can exhibit that totality fails: take an N3 dominance node and a human agent. *)
  Lemma terminal_utility_not_total :
    ~ TotalTerminalUtility.
  Proof.
    unfold TotalTerminalUtility.
    intro Htot.
    (* Construct a terminal state with Abs_N3Dominance 0 and ask for a lab's payoff. *)
    set (s :=
      {|
        ws_time := 0%nat;
        ws_cap := 0%nat;
        ws_align := (1#2);
        ws_dom_threshold := 0%nat;
        ws_n_ai := 1%nat;
        ws_classified := false;
        ws_classification_level := 0%nat;
        ws_last_claim := None;
        ws_align_invest := 0%Q;
        ws_reg_threshold := None;
        ws_regime := Reg_Abs (Abs_N3Dominance 0%nat);
        ws_stage := StageNature;
        ws_initialized := true;
        ws_public_pressure := 0%nat
      |}).
    specialize (Htot s (Abs_N3Dominance 0%nat) (N1_Lab 0%nat) eq_refl).
    destruct Htot as [u Hu].
    simpl in Hu.
    (* utility_at_absorbing for N1_Lab _ in Abs_N3Dominance is None *)
    discriminate.
  Qed.

  (******************************************************************************)
  (* 5. Strategies: pure + set-valued (for mixed/indeterminate behavior)        *)
  (******************************************************************************)

  (*
    A behavioral strategy depends on the agent's observation history (imperfect info).
    Since the original text emphasizes mixed strategies and Knightian uncertainty,
    we provide *set-valued* strategies (support sets) rather than probability measures.
  *)

  Definition PureStrategy (a : Player) : Type :=
    ObsHist -> Action a.

  Definition SetValuedStrategy (a : Player) : Type :=
    ObsHist -> Action a -> Prop.

  Record PureProfile : Type := {
    pure_strat : forall a : Player, PureStrategy a
  }.

  Record SetProfile : Type := {
    set_strat : forall a : Player, SetValuedStrategy a
  }.

  (* Embed a pure strategy as a singleton-support set-valued strategy. *)
  Definition pure_to_set {a : Player} (σ : PureStrategy a) : SetValuedStrategy a :=
    fun oh act => act = σ oh.

  Definition pureProfile_to_setProfile (P : PureProfile) : SetProfile :=
    {|
      set_strat := fun a => pure_to_set (P.(pure_strat) a)
    |}.

  (*
    5.1 Strategy-profile-induced outcome.
    Given a pure strategy profile and an observation-history builder,
    we define what sequence of states arises from play.
  *)

  (* Build observation history from a state history for a given player. *)
  Fixpoint obs_hist_from_states (a : Player) (states : list WorldState) : ObsHist :=
    match states with
    | nil => nil
    | s :: rest => observe a s :: obs_hist_from_states a rest
    end.

  (* One step of play under a pure profile: given current state and history,
     if it's some player's turn, they play according to their strategy. *)
  Definition step_under_profile (P : PureProfile) (hist : list WorldState) (s : WorldState)
    : option WorldState :=
    match whose_turn s with
    | None => None
    | Some a =>
        let oh := obs_hist_from_states a hist in
        let act := P.(pure_strat) a oh in
        Some (apply s (existT _ a act))
    end.

  (* Iterated play: run for n steps or until terminal. Returns list of states visited. *)
  Fixpoint play_n (P : PureProfile) (n : nat) (hist : list WorldState) (s : WorldState)
    : list WorldState :=
    match n with
    | O => s :: nil
    | S n' =>
        match step_under_profile P hist s with
        | None => s :: nil
        | Some s' => s :: play_n P n' (hist ++ (s :: nil)) s'
        end
    end.

  (* Outcome from initial state after n steps. *)
  Definition outcome_n (P : PureProfile) (n : nat) : list WorldState :=
    play_n P n nil initial_state.

  (* Final state after n steps (last element of outcome). *)
  Definition final_state_n (P : PureProfile) (n : nat) : WorldState :=
    last (outcome_n P n) initial_state.

  (* Lemma: play_n always produces a non-empty list. *)
  Lemma play_n_nonempty :
    forall P n hist s,
      play_n P n hist s <> nil.
  Proof.
    intros P n.
    induction n as [| n' IH].
    - intros hist s. simpl. discriminate.
    - intros hist s. simpl.
      destruct (step_under_profile P hist s).
      + discriminate.
      + discriminate.
  Qed.

  (* Lemma: first state in play_n is the input state. *)
  Lemma play_n_head :
    forall P n hist s,
      hd_error (play_n P n hist s) = Some s.
  Proof.
    intros P n.
    destruct n.
    - intros hist s. simpl. reflexivity.
    - intros hist s. simpl.
      destruct (step_under_profile P hist s); reflexivity.
  Qed.

  (******************************************************************************)
  (* 6. Why standard solution concepts fail (formal precondition failures)     *)
  (******************************************************************************)

  (*
    We formalize the failure mode as *absence of prerequisites*:

      - Backward induction / subgame perfect equilibrium typically requires:
          (i) finite horizon or well-defined evaluation of infinite plays, and
          (ii) total utilities at terminal nodes.
        Here, we explicitly violate (ii) (see terminal_utility_not_total), and
        the model allows Nature to keep Reg_Pre indefinitely (not proved here).

      - Nash equilibrium in normal-form games requires a fixed player set and
        a utility function defined for every player at every outcome.
        Here utilities are partial (option), and the "creation" of N3 agents
        is explicit via ws_n_ai and LabDeployNewAI.

      - Correlated equilibrium presumes a common-knowledge correlation device
        (distribution over signals). This model has no such primitive; Nature
        is nondeterministic (Knightian), not a publicly shared random device.

      - Mechanism design presumes an external designer with commitment power.
        In this model, "regulation/treaties" are moves by N2 (StateRegulate),
        i.e., they are within the game and defeatable, not exogenous commitments.
  *)

  (* A minimal normal-form-game record, to make Nash prerequisites explicit. *)
  Record NFGame : Type := {
    NFPlayer : Type;
    NFPlayer_eq_dec : forall (x y : NFPlayer), {x = y} + {x <> y};

    NFAction : NFPlayer -> Type;

    NFUtility : (forall p : NFPlayer, NFAction p) -> NFPlayer -> Q
  }.

  Section NashEquilibrium.
    Context (G : NFGame).

    Definition NFProfile : Type := forall p : NFPlayer G, NFAction G p.

    Definition override (σ : NFProfile) (p : NFPlayer G) (a' : NFAction G p) : NFProfile :=
      fun p' =>
        match NFPlayer_eq_dec G p' p with
        | left e => eq_rect p (NFAction G) a' p' (eq_sym e)
        | right _ => σ p'
        end.

    (* Nash equilibrium: no unilateral deviation improves utility. *)
    Definition Nash (σ : NFProfile) : Prop :=
      forall p (a' : NFAction G p),
        NFUtility G σ p >= NFUtility G (override σ p a') p.

  End NashEquilibrium.

  (*
    A predicate stating that an extensive-form game has total terminal utility
    (in the sense needed by many classical SPE/backward-induction developments).
    Our earlier lemma shows this fails for this model.
  *)
  Definition AIRace_total_terminal_utility_fails : Prop :=
    ~ TotalTerminalUtility.

  Lemma AIRace_total_terminal_utility_fails_proof :
    AIRace_total_terminal_utility_fails.
  Proof.
    exact terminal_utility_not_total.
  Qed.

  (*
    Player-creation witness: there exists an action (LabDeployNewAI) whose effect
    strictly increases ws_n_ai in the resulting state. This witnesses that
    "players are being created" (N3) in the extensive-form structure.

    This lemma is intentionally *local* (one-step); making it from initial_state
    requires reachability assumptions (e.g., nLabs>0 and choosing NatInit first).
  *)
  Lemma AIRace_player_creation_local_witness :
    forall s i,
      ws_regime s = Reg_Pre ->
      whose_turn s = Some (N1_Lab i) ->
      is_available s (N1_Lab i) (LabDeployNewAI i) ->
      let m := existT _ (N1_Lab i) (LabDeployNewAI i) in
      ws_n_ai (apply s m) = S (ws_n_ai s).
  Proof.
    intros s i Hreg Hturn Hav m.
    unfold m. simpl. reflexivity.
  Qed.

  (******************************************************************************)
  (* 7. Heterogeneity demonstration                                             *)
  (******************************************************************************)

  (*
    The heterogeneity infrastructure (lab_attrs, state_attrs, etc.) allows
    per-player variation in capabilities. Here we demonstrate its use.
  *)

  (* Effective capability gain for a lab, scaled by its efficiency. *)
  Definition effective_cap_gain (i : nat) (base : nat) : Q :=
    Q_of_nat base * (lab_attrs i).(lab_cap_efficiency).

  (* Two labs with different efficiencies produce different effective gains.
     Proof: if base > 0 and efficiencies differ, multiplying by base preserves distinction. *)
  Lemma heterogeneous_labs_differ :
    forall i j base,
      (lab_attrs i).(lab_cap_efficiency) <> (lab_attrs j).(lab_cap_efficiency) ->
      (0 < base)%nat ->
      effective_cap_gain i base <> effective_cap_gain j base.
  Admitted.

  (* Researchers with different safety output contribute differently to alignment. *)
  Definition researcher_align_contrib (i : nat) : Q :=
    (researcher_attrs i).(researcher_safety_output).

  (* AI cooperation tendency affects likelihood of cooperative vs dominant behavior.
     This is a modeling choice; the game structure permits either. *)
  Definition ai_more_cooperative (i j : nat) : Prop :=
    (ai_attrs i).(ai_cooperation_tendency) > (ai_attrs j).(ai_cooperation_tendency).

  (******************************************************************************)
  (* 8. Convenience: a "storyboard" of the main objects you may extend          *)
  (******************************************************************************)

  (*
    Core objects:
      - WorldState, Agent, Act
      - turn : WorldState -> option Agent
      - available : legal-move predicate
      - apply : deterministic state update
      - step : transition relation (apply + legality)
      - observe : imperfect-information observation mapping
      - align_interval : epistemic CI for A(t)
      - Absorbing + Regime : absorbing classes
      - utility : partial payoff

    If you want a *true extensive-form game tree* (Histories, subgames, etc.),
    you can lift step into a tree of histories using the generic Reachable/PlayK
    framework in Section ExtensiveFormCore above, instantiated with AIRaceGame.
  *)

End Params.
End AIRace.
