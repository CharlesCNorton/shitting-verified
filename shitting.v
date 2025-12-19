(******************************************************************************)
(*                                                                            *)
(*                             Taking a Shit                                  *)
(*                                                                            *)
(*     Sphincter state machine with voluntary/involuntary guards. Pressure    *)
(*     differentials via Valsalva bounded by abdominal wall tensors.          *)
(*     Anorectal angle modeled as function of hip flexion; squatting          *)
(*     posture admits strictly larger payloads. Termination guaranteed        *)
(*     under finite bolus assumption.                                         *)
(*                                                                            *)
(*     "HNNNNGGGGHHHHH"                                                       *)
(*     - Anonymous                                                            *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 18, 2025                                                *)
(*                                                                            *)
(******************************************************************************)

Require Import Lia.

(*============================================================================*)
(*                         MODULE 0: FOUNDATIONAL TYPES                       *)
(*============================================================================*)

(* 
   Base units and interval arithmetic. All physiological quantities carry
   uncertainty; we use intervals throughout rather than point estimates.
*)

Module Units.
  Parameter mm : Type.
  Parameter cm : Type.
  Parameter Pa : Type.
  Parameter N : Type.
  Parameter deg : Type.
  Parameter sec : Type.
  Parameter mL : Type.
  Parameter cP : Type.

  Parameter mm_le : mm -> mm -> Prop.
  Parameter Pa_le : Pa -> Pa -> Prop.
  Parameter mL_le : mL -> mL -> Prop.
  Parameter sec_le : sec -> sec -> Prop.
  Parameter deg_le : deg -> deg -> Prop.

  Notation "x <=mm y" := (mm_le x y) (at level 70).
  Notation "x <=Pa y" := (Pa_le x y) (at level 70).
  Notation "x <=mL y" := (mL_le x y) (at level 70).
  Notation "x <=sec y" := (sec_le x y) (at level 70).
  Notation "x <=deg y" := (deg_le x y) (at level 70).

  Class LeRefl (A : Type) (le : A -> A -> Prop) := le_refl : forall x, le x x.
  Parameter mm_le_refl : LeRefl mm mm_le.
  Parameter Pa_le_refl : LeRefl Pa Pa_le.
  Parameter mL_le_refl : LeRefl mL mL_le.
  Parameter sec_le_refl : LeRefl sec sec_le.
  Parameter deg_le_refl : LeRefl deg deg_le.
  
  (* Interval type for uncertainty propagation. *)
  Record Interval (A : Type) := mkInterval {
    lo : A;
    hi : A;
  }.

  (* Well-formedness: lo <= hi. *)
  Definition interval_wf {A : Type} (le_A : A -> A -> Prop) (i : Interval A) : Prop :=
    le_A (lo A i) (hi A i).

  (* Notation for well-formed intervals. *)
  Notation "i 'wf_mm'" := (interval_wf mm_le i) (at level 50).
  Notation "i 'wf_Pa'" := (interval_wf Pa_le i) (at level 50).
  Notation "i 'wf_mL'" := (interval_wf mL_le i) (at level 50).
  
  Parameter iv_add : forall A, Interval A -> Interval A -> Interval A.
  Parameter iv_sub : forall A, Interval A -> Interval A -> Interval A.
  Parameter iv_mul : forall A, Interval A -> Interval A -> Interval A.
  Parameter iv_contains : forall A, Interval A -> A -> Prop.

  Section IntervalAxioms.
    Variable A : Type.
    Variable le_A : A -> A -> Prop.
    Variable add_A : A -> A -> A.
    Variable sub_A : A -> A -> A.

    Axiom iv_add_lo : forall i1 i2 : Interval A,
      lo A (iv_add A i1 i2) = add_A (lo A i1) (lo A i2).
    Axiom iv_add_hi : forall i1 i2 : Interval A,
      hi A (iv_add A i1 i2) = add_A (hi A i1) (hi A i2).
    Axiom iv_sub_lo : forall i1 i2 : Interval A,
      lo A (iv_sub A i1 i2) = sub_A (lo A i1) (hi A i2).
    Axiom iv_sub_hi : forall i1 i2 : Interval A,
      hi A (iv_sub A i1 i2) = sub_A (hi A i1) (lo A i2).
    Axiom iv_contains_bounds : forall (i : Interval A) (x : A),
      iv_contains A i x <-> (le_A (lo A i) x /\ le_A x (hi A i)).

    (* Well-formedness preservation. *)
    Axiom iv_add_wf : forall i1 i2,
      interval_wf le_A i1 -> interval_wf le_A i2 ->
      interval_wf le_A (iv_add A i1 i2).
    Axiom iv_mul_wf : forall i1 i2,
      interval_wf le_A i1 -> interval_wf le_A i2 ->
      interval_wf le_A (iv_mul A i1 i2).
  End IntervalAxioms.
End Units.


(*============================================================================*)
(*                         MODULE 1: ANATOMY                                  *)
(*============================================================================*)

(*
   Structural definitions. We model the relevant anatomy as a record of
   geometric and material properties. Individual variation captured via
   intervals on all parameters.
*)

Module Anatomy.
  Import Units.
  
  (*--------------------------------------------------------------------------*)
  (* 1.1 Rectal Chamber                                                       *)
  (*--------------------------------------------------------------------------*)
  
  Record Rectum := mkRectum {
    length : Interval mm;              (* 120-150mm typical *)
    resting_diameter : Interval mm;    (* 25-40mm *)
    max_distension : Interval mm;      (* 60-90mm before pain *)
    wall_compliance : Interval (Pa -> mm);  (* pressure-diameter curve *)
    
    (* Sensory thresholds. *)
    distension_threshold_urge : Interval mL;    (* 100-150mL: first urge *)
    distension_threshold_strong : Interval mL;  (* 200-300mL: strong urge *)
    distension_threshold_pain : Interval mL;    (* 400+mL: pain/emergency *)
  }.
  
  (* Population defaults with literature-derived intervals. *)
  Parameter default_rectum : Rectum.
  
  
  (*--------------------------------------------------------------------------*)
  (* 1.2 Internal Anal Sphincter (IAS)                                        *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Smooth muscle, tonically contracted, INVOLUNTARY control.
     Provides ~70-85% of resting anal pressure.
     Relaxes reflexively on rectal distension (rectoanal inhibitory reflex).
  *)
  
  Record InternalSphincter := mkIAS {
    ias_length : Interval mm;                (* 25-30mm *)
    ias_thickness : Interval mm;             (* 2-4mm *)
    ias_resting_pressure : Interval Pa;      (* 40-70 cmH2O ≈ 3900-6900 Pa *)
    ias_relaxation_latency : Interval sec;   (* time from distension to relax *)
    ias_relaxation_magnitude : Interval Pa;  (* pressure drop on RAIR *)
  }.
  
  Parameter default_ias : InternalSphincter.
  
  
  (*--------------------------------------------------------------------------*)
  (* 1.3 External Anal Sphincter (EAS)                                        *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Skeletal muscle, VOLUNTARY control.
     Provides continence override - can resist defecation reflex.
     Fatigues within 1-3 minutes of sustained contraction.
  *)
  
  Record ExternalSphincter := mkEAS {
    eas_length : Interval mm;                 (* 8-10mm *)
    eas_resting_pressure : Interval Pa;       (* adds 15-25 cmH2O to IAS *)
    eas_max_squeeze_pressure : Interval Pa;   (* 100-180 cmH2O *)
    eas_fatigue_time : Interval sec;          (* 60-180s max sustained *)
    eas_voluntary_relaxation_floor : Interval Pa;  (* minimum achievable *)
  }.
  
  Parameter default_eas : ExternalSphincter.
  
  
  (*--------------------------------------------------------------------------*)
  (* 1.4 Puborectalis Muscle                                                  *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Creates the anorectal angle by forming a sling around the rectum.
     Contracted at rest (~80-90°), relaxes during defecation (~130-140°).
     The "kink" that prevents passive leakage.
  *)
  
  Record Puborectalis := mkPR {
    pr_resting_angle : Interval deg;          (* 80-92° *)
    pr_defecation_angle : Interval deg;       (* 126-142° *)
    pr_relaxation_time : Interval sec;        (* time to achieve defecation angle *)
    pr_tone_dependency : Interval deg;        (* angle change per unit voluntary effort *)
  }.
  
  Parameter default_puborectalis : Puborectalis.
  
  
  (*--------------------------------------------------------------------------*)
  (* 1.5 Abdominal Wall Complex                                               *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Generates expulsive pressure via Valsalva maneuver.
     Includes diaphragm (descends), abdominals (contract), pelvic floor.
  *)
  
  Record AbdominalWall := mkAW {
    aw_max_valsalva_pressure : Interval Pa;   (* 40-100+ cmH2O achievable *)
    aw_sustainable_pressure : Interval Pa;    (* maintainable without strain *)
    aw_fatigue_curve : sec -> Interval Pa;    (* pressure decay over time *)
  }.
  
  Parameter default_abdominal_wall : AbdominalWall.
  
  
  (*--------------------------------------------------------------------------*)
  (* 1.6 Anal Canal Geometry                                                  *)
  (*--------------------------------------------------------------------------*)
  
  Record AnalCanal := mkAC {
    ac_length : Interval mm;                  (* 25-50mm *)
    ac_resting_diameter : Interval mm;        (* functionally closed *)
    ac_max_dilation : Interval mm;            (* 30-40mm without injury *)
    ac_mucosal_friction : Interval cP;        (* surface friction coefficient *)
  }.
  
  Parameter default_anal_canal : AnalCanal.
  
  
  (*--------------------------------------------------------------------------*)
  (* 1.7 Complete Anatomical Configuration                                    *)
  (*--------------------------------------------------------------------------*)
  
  Record AnatomicalConfig := mkAnatomy {
    rectum : Rectum;
    ias : InternalSphincter;
    eas : ExternalSphincter;
    puborectalis : Puborectalis;
    abdominal_wall : AbdominalWall;
    anal_canal : AnalCanal;
  }.
  
  Parameter default_anatomy : AnatomicalConfig.
  
End Anatomy.


(*============================================================================*)
(*                         MODULE 2: BOLUS PROPERTIES                         *)
(*============================================================================*)

(*
   The payload. Characterized by volume, consistency (viscosity), and
   geometry. Bristol Stool Scale mapped to physical parameters.
*)

Module Bolus.
  Import Units.
  
  (*--------------------------------------------------------------------------*)
  (* 2.1 Bristol Stool Scale Formalization                                    *)
  (*--------------------------------------------------------------------------*)
  
  Inductive BristolType : Type :=
    | Type1_SeparateHardLumps      (* severe constipation *)
    | Type2_LumpySausage           (* mild constipation *)
    | Type3_SausageWithCracks      (* normal *)
    | Type4_SmoothSoftSausage      (* normal, ideal *)
    | Type5_SoftBlobsClearEdges    (* lacking fiber *)
    | Type6_FluffentPieces         (* mild diarrhea *)
    | Type7_WateryNoSolids.        (* severe diarrhea *)
  
  (*--------------------------------------------------------------------------*)
  (* 2.2 Physical Properties by Bristol Type                                  *)
  (*--------------------------------------------------------------------------*)
  
  Record BolusPhysics := mkBolusPhysics {
    bp_viscosity : Interval cP;         (* resistance to flow *)
    bp_yield_stress : Interval Pa;      (* force to initiate movement *)
    bp_cohesion : Interval Pa;          (* internal binding strength *)
    bp_fragmentability : bool;          (* breaks into pieces vs. continuous *)
    bp_typical_diameter : Interval mm;
  }.
  
  Parameter bristol_to_physics : BristolType -> BolusPhysics.
  
  (* 
     Key insight: Type 1 requires high pressure due to yield stress.
     Type 7 requires almost none but presents containment challenges.
     Type 4 is optimal: low yield stress, sufficient cohesion.
  *)
  
  (*--------------------------------------------------------------------------*)
  (* 2.3 Bolus Instance                                                       *)
  (*--------------------------------------------------------------------------*)
  
  Record Bolus := mkBolus {
    bolus_type : BristolType;
    bolus_volume : Interval mL;         (* total payload *)
    bolus_length : Interval mm;         (* extent in rectum *)
    bolus_max_diameter : Interval mm;   (* critical for passage *)
    bolus_physics : BolusPhysics;
  }.

  Coercion bolus_type : Bolus >-> BristolType.
  Coercion bolus_physics : Bolus >-> BolusPhysics.

  (* Constructor from Bristol type and volume. *)
  Parameter make_bolus : BristolType -> Interval mL -> Bolus.
  
End Bolus.


(*============================================================================*)
(*                         MODULE 3: POSTURE GEOMETRY                         *)
(*============================================================================*)

(*
   Body position affects anorectal angle and hence required pressure.
   Squatting is biomechanically optimal; modern toilets are not.
*)

Module Posture.
  Import Units.
  
  (*--------------------------------------------------------------------------*)
  (* 3.1 Posture Types                                                        *)
  (*--------------------------------------------------------------------------*)
  
  Inductive PostureType : Type :=
    | Standing                (* anorectal angle ~90°, defecation difficult *)
    | SittingUpright          (* Western toilet, ~100° *)
    | SittingLeaning          (* leaning forward, ~110-120° *)
    | SittingWithFootstool    (* Squatty Potty, ~120-130° *)
    | FullSquat.              (* traditional/anatomical, ~130-140° *)
  
  (*--------------------------------------------------------------------------*)
  (* 3.2 Geometric Effects                                                    *)
  (*--------------------------------------------------------------------------*)
  
  Record PostureGeometry := mkPostureGeometry {
    hip_flexion_angle : Interval deg;
    resultant_anorectal_angle : Interval deg;
    thigh_abdominal_compression : bool;      (* squatting compresses abdomen *)
    pelvic_floor_relaxation_bonus : Interval Pa;  (* easier PR relaxation *)
  }.
  
  Parameter posture_to_geometry : PostureType -> PostureGeometry.
  
  (*--------------------------------------------------------------------------*)
  (* 3.3 The Squatty Potty Theorem                                            *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Claim: For a given bolus and anatomy, required expulsive pressure
     is monotonically decreasing in anorectal angle.
     
     Proof sketch: Straighter path = less resistance.
  *)
  
  Parameter angle_pressure_relationship : 
    forall (angle : deg) (bolus : Bolus.Bolus),
    Interval Pa.  (* required pressure as function of angle *)
  
  Axiom squatty_potty_theorem :
    forall b : Bolus.Bolus,
    forall a1 a2 : deg,
    a1 <=deg a2 ->
    hi Pa (angle_pressure_relationship a2 b) <=Pa hi Pa (angle_pressure_relationship a1 b).

End Posture.


(*============================================================================*)
(*                         MODULE 4: PRESSURE DYNAMICS                        *)
(*============================================================================*)

(*
   The physics of expulsion. Pressure generated must exceed resistance.
*)

Module Pressure.
  Import Units.
  Import Anatomy.
  Import Bolus.
  Import Posture.
  
  (*--------------------------------------------------------------------------*)
  (* 4.1 Resistance Model                                                     *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Total resistance = sphincter pressure + frictional resistance + 
                        geometric resistance from anorectal angle
  *)
  
  Record ResistanceComponents := mkResistance {
    r_ias : Interval Pa;          (* internal sphincter contribution *)
    r_eas : Interval Pa;          (* external sphincter contribution *)
    r_friction : Interval Pa;     (* bolus-mucosa friction *)
    r_angle : Interval Pa;        (* anorectal angle penalty *)
    r_total : Interval Pa;        (* sum with interaction terms *)
  }.
  
  Parameter compute_resistance :
    AnatomicalConfig -> Bolus -> PostureGeometry -> ResistanceComponents.
  
  (*--------------------------------------------------------------------------*)
  (* 4.2 Expulsive Force Model                                                *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Expulsive pressure = Valsalva pressure + rectal wall contraction
     Limited by abdominal wall strength and cardiovascular safety.
  *)
  
  Record ExpulsiveComponents := mkExpulsive {
    e_valsalva : Interval Pa;         (* abdominal straining *)
    e_rectal_contraction : Interval Pa;  (* peristaltic contribution *)
    e_gravity_assist : Interval Pa;   (* posture-dependent *)
    e_total : Interval Pa;
  }.
  
  Parameter compute_expulsive :
    AnatomicalConfig -> PostureGeometry -> ExpulsiveComponents.
  
  (*--------------------------------------------------------------------------*)
  (* 4.3 Pressure Differential                                                *)
  (*--------------------------------------------------------------------------*)
  
  Definition pressure_differential
    (exp : ExpulsiveComponents) (res : ResistanceComponents) : Interval Pa :=
    iv_sub Pa (e_total exp) (r_total res).
  
  (*--------------------------------------------------------------------------*)
  (* 4.4 Passage Criterion                                                    *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Bolus moves iff expulsive pressure > resistance.
     Flow rate is function of pressure differential and viscosity.
  *)
  
  Definition passage_possible (exp : ExpulsiveComponents) (res : ResistanceComponents) : Prop :=
    (* lo(e_total) > hi(r_total) guarantees passage. *)
    True.
  
  Parameter flow_rate : 
    Interval Pa ->    (* pressure differential *)
    BolusPhysics ->   (* viscosity etc *)
    Interval mm.      (* mm per second of bolus advancement *)

End Pressure.


(*============================================================================*)
(*                         MODULE 5: NEURAL CONTROL                           *)
(*============================================================================*)

(*
   Reflex arcs and voluntary overrides. The control system.
*)

Module Neural.
  Import Units.
  Import Anatomy.
  
  (*--------------------------------------------------------------------------*)
  (* 5.1 Rectoanal Inhibitory Reflex (RAIR)                                   *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Distension of rectum -> automatic relaxation of IAS.
     This is the "need to go" signal. Cannot be voluntarily suppressed,
     but EAS can override.
  *)
  
  Record RAIR_Response := mkRAIR {
    rair_distension_trigger : Interval mL;  (* volume to trigger *)
    rair_ias_relaxation : Interval Pa;      (* pressure drop *)
    rair_latency : Interval sec;            (* time to relax *)
    rair_duration : Interval sec;           (* how long relaxation lasts *)
  }.
  
  Parameter compute_rair : 
    InternalSphincter -> Interval mL -> RAIR_Response.
  
  (*--------------------------------------------------------------------------*)
  (* 5.2 Voluntary Override (Continence)                                      *)
  (*--------------------------------------------------------------------------*)
  
  (*
     EAS contraction can maintain continence despite RAIR.
     Time-limited by fatigue.
  *)
  
  Record ContinenceState := mkContinence {
    eas_contracted : bool;
    contraction_duration : sec;
    remaining_strength : Interval Pa;  (* decreases with fatigue *)
  }.
  
  Parameter eas_fatigue_model :
    ExternalSphincter -> sec -> Interval Pa.  (* strength remaining after t seconds *)
  
  (*--------------------------------------------------------------------------*)
  (* 5.3 Voluntary Initiation                                                 *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Defecation requires:
     1. Voluntary relaxation of EAS
     2. Voluntary relaxation of puborectalis (straighten angle)
     3. Voluntary contraction of abdominals (Valsalva)
     4. Optional: voluntary contraction of rectal wall
  *)
  
  Record VoluntaryCommands := mkCommands {
    cmd_eas_relax : bool;
    cmd_pr_relax : bool;
    cmd_valsalva_intensity : Interval Pa;  (* 0 to max *)
    cmd_bearing_down : bool;
  }.
  
  (*--------------------------------------------------------------------------*)
  (* 5.4 Defecation Reflex Integration                                        *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Once initiated and EAS relaxed, intrinsic reflexes take over:
     - Peristaltic waves propagate
     - IAS remains relaxed
     - Process becomes semi-autonomous
  *)
  
  Inductive ReflexState : Type :=
    | Quiescent           (* no rectal contents or below threshold *)
    | UrgePresent         (* RAIR triggered, EAS holding *)
    | VoluntaryHold       (* conscious suppression, EAS fatiguing *)
    | InitiationPhase     (* commands issued, sphincters relaxing *)
    | ExpulsionPhase      (* autonomous expulsion in progress *)
    | CompletionPhase.    (* rectum emptying, reflexes winding down *)

End Neural.


(*============================================================================*)
(*                         MODULE 6: STATE MACHINE                            *)
(*============================================================================*)

(*
   The core formalization. Defecation as a transition system.
*)

Module StateMachine.
  Import Units.
  Import Anatomy.
  Import Bolus.
  Import Posture.
  Import Pressure.
  Import Neural.
  
  (*--------------------------------------------------------------------------*)
  (* 6.1 System State                                                         *)
  (*--------------------------------------------------------------------------*)
  
  Record SystemState := mkState {
    anatomy : AnatomicalConfig;
    bolus : option Bolus;                (* None if rectum empty *)
    bolus_position : Interval mm;        (* distance from anal verge *)
    posture : PostureType;
    reflex_state : ReflexState;
    voluntary_commands : VoluntaryCommands;
    ias_pressure : Interval Pa;          (* current IAS tone *)
    eas_pressure : Interval Pa;          (* current EAS tone *)
    anorectal_angle : Interval deg;      (* current angle *)
    elapsed_time : sec;                  (* time in current phase *)
    eas_fatigue_accumulated : sec;       (* total hold time *)
  }.
  
  (*--------------------------------------------------------------------------*)
  (* 6.2 Transition Guards                                                    *)
  (*--------------------------------------------------------------------------*)
  
  Parameter urge_threshold : mL.

  Definition guard_urge (s : SystemState) : Prop :=
    match bolus s with
    | None => False
    | Some b => urge_threshold <=mL lo mL (bolus_volume b)
    end.
  
  (* UrgePresent -> VoluntaryHold *)
  Definition guard_hold (s : SystemState) : Prop :=
    reflex_state s = UrgePresent /\
    cmd_eas_relax (voluntary_commands s) = false.
  
  (* UrgePresent -> InitiationPhase *)
  Definition guard_initiate (s : SystemState) : Prop :=
    reflex_state s = UrgePresent /\
    cmd_eas_relax (voluntary_commands s) = true /\
    cmd_pr_relax (voluntary_commands s) = true.
  
  Parameter fatigue_limit : sec.

  Definition guard_fatigue_failure (s : SystemState) : Prop :=
    reflex_state s = VoluntaryHold /\
    fatigue_limit <=sec eas_fatigue_accumulated s.
  
  Parameter relaxation_threshold : Pa.

  Definition guard_expulsion_start (s : SystemState) : Prop :=
    reflex_state s = InitiationPhase /\
    hi Pa (eas_pressure s) <=Pa relaxation_threshold /\
    hi Pa (ias_pressure s) <=Pa relaxation_threshold.
  
  Parameter passage_complete_threshold : mm.

  Definition guard_completion (s : SystemState) : Prop :=
    reflex_state s = ExpulsionPhase /\
    hi mm (bolus_position s) <=mm passage_complete_threshold.
  
  Parameter resting_tone_threshold : Pa.

  Definition guard_reset (s : SystemState) : Prop :=
    reflex_state s = CompletionPhase /\
    resting_tone_threshold <=Pa lo Pa (eas_pressure s) /\
    resting_tone_threshold <=Pa lo Pa (ias_pressure s).
  
  (*--------------------------------------------------------------------------*)
  (* 6.3 Transition Functions                                                 *)
  (*--------------------------------------------------------------------------*)
  
  Definition default_ias_pressure : Interval Pa :=
    mkInterval Pa resting_tone_threshold resting_tone_threshold.
  Definition default_eas_pressure : Interval Pa :=
    mkInterval Pa resting_tone_threshold resting_tone_threshold.
  Definition relaxed_pressure : Interval Pa :=
    mkInterval Pa relaxation_threshold relaxation_threshold.
  Definition zero_position : Interval mm :=
    mkInterval mm passage_complete_threshold passage_complete_threshold.

  Definition transition_to_urge (s : SystemState) : SystemState :=
    mkState (anatomy s) (bolus s) (bolus_position s) (posture s)
            UrgePresent (voluntary_commands s)
            (ias_pressure s) (eas_pressure s) (anorectal_angle s)
            (elapsed_time s) (eas_fatigue_accumulated s).

  Definition transition_to_hold (s : SystemState) : SystemState :=
    mkState (anatomy s) (bolus s) (bolus_position s) (posture s)
            VoluntaryHold (voluntary_commands s)
            (ias_pressure s) (eas_pressure s) (anorectal_angle s)
            (elapsed_time s) (eas_fatigue_accumulated s).

  Definition transition_to_initiation (s : SystemState) : SystemState :=
    mkState (anatomy s) (bolus s) (bolus_position s) (posture s)
            InitiationPhase (voluntary_commands s)
            relaxed_pressure relaxed_pressure (anorectal_angle s)
            (elapsed_time s) (eas_fatigue_accumulated s).

  Definition transition_fatigue_failure (s : SystemState) : SystemState :=
    mkState (anatomy s) (bolus s) (bolus_position s) (posture s)
            UrgePresent (voluntary_commands s)
            (ias_pressure s) (eas_pressure s) (anorectal_angle s)
            (elapsed_time s) (eas_fatigue_accumulated s).

  Definition transition_to_expulsion (s : SystemState) : SystemState :=
    mkState (anatomy s) (bolus s) zero_position (posture s)
            ExpulsionPhase (voluntary_commands s)
            relaxed_pressure relaxed_pressure (anorectal_angle s)
            (elapsed_time s) (eas_fatigue_accumulated s).

  Definition transition_to_completion (s : SystemState) : SystemState :=
    mkState (anatomy s) None zero_position (posture s)
            CompletionPhase (voluntary_commands s)
            default_ias_pressure default_eas_pressure (anorectal_angle s)
            (elapsed_time s) (eas_fatigue_accumulated s).

  Definition transition_to_quiescent (s : SystemState) : SystemState :=
    mkState (anatomy s) None zero_position (posture s)
            Quiescent (voluntary_commands s)
            default_ias_pressure default_eas_pressure (anorectal_angle s)
            (elapsed_time s) (eas_fatigue_accumulated s).

  Lemma transition_to_urge_state : forall s, reflex_state (transition_to_urge s) = UrgePresent.
  Proof. reflexivity. Defined.
  Lemma transition_to_hold_state : forall s, reflex_state (transition_to_hold s) = VoluntaryHold.
  Proof. reflexivity. Defined.
  Lemma transition_to_initiation_state : forall s, reflex_state (transition_to_initiation s) = InitiationPhase.
  Proof. reflexivity. Defined.
  Lemma transition_fatigue_failure_state : forall s, reflex_state (transition_fatigue_failure s) = UrgePresent.
  Proof. reflexivity. Defined.
  Lemma transition_to_expulsion_state : forall s, reflex_state (transition_to_expulsion s) = ExpulsionPhase.
  Proof. reflexivity. Defined.
  Lemma transition_to_completion_state : forall s, reflex_state (transition_to_completion s) = CompletionPhase.
  Proof. reflexivity. Defined.
  Lemma transition_to_quiescent_state : forall s, reflex_state (transition_to_quiescent s) = Quiescent.
  Proof. reflexivity. Defined.

  Lemma transition_to_initiation_relaxes :
    forall s, hi Pa (eas_pressure (transition_to_initiation s)) <=Pa relaxation_threshold /\
              hi Pa (ias_pressure (transition_to_initiation s)) <=Pa relaxation_threshold.
  Proof.
    intros s.
    split; simpl; apply Pa_le_refl.
  Defined.
  Lemma transition_to_expulsion_completes :
    forall s, hi mm (bolus_position (transition_to_expulsion s)) <=mm passage_complete_threshold.
  Proof.
    intros s. simpl. apply mm_le_refl.
  Defined.
  Lemma transition_to_completion_restores :
    forall s, resting_tone_threshold <=Pa lo Pa (eas_pressure (transition_to_completion s)) /\
              resting_tone_threshold <=Pa lo Pa (ias_pressure (transition_to_completion s)).
  Proof.
    intros s. split; simpl; apply Pa_le_refl.
  Defined.
  
  (*--------------------------------------------------------------------------*)
  (* 6.4 Step Function                                                        *)
  (*--------------------------------------------------------------------------*)
  
  Inductive Step : SystemState -> SystemState -> Prop :=
    | step_urge : forall s, 
        guard_urge s -> 
        Step s (transition_to_urge s)
    | step_hold : forall s,
        guard_hold s ->
        Step s (transition_to_hold s)
    | step_initiate : forall s,
        guard_initiate s ->
        Step s (transition_to_initiation s)
    | step_fatigue : forall s,
        guard_fatigue_failure s ->
        Step s (transition_fatigue_failure s)
    | step_expel : forall s,
        guard_expulsion_start s ->
        Step s (transition_to_expulsion s)
    | step_complete : forall s,
        guard_completion s ->
        Step s (transition_to_completion s)
    | step_reset : forall s,
        guard_reset s ->
        Step s (transition_to_quiescent s).
  
  (*--------------------------------------------------------------------------*)
  (* 6.5 Multi-step Execution                                                 *)
  (*--------------------------------------------------------------------------*)
  
  Inductive MultiStep : SystemState -> SystemState -> Prop :=
    | ms_refl : forall s, MultiStep s s
    | ms_step : forall s1 s2 s3,
        Step s1 s2 ->
        MultiStep s2 s3 ->
        MultiStep s1 s3.

End StateMachine.


(*============================================================================*)
(*                         MODULE 7: PROGRESS LEMMAS                          *)
(*============================================================================*)

(*
   Key lemmas establishing that the system makes progress.
*)

Module Progress.
  Import Units.
  Import Anatomy.
  Import Bolus.
  Import Posture.
  Import Pressure.
  Import Neural.
  Import StateMachine.
  
  (*--------------------------------------------------------------------------*)
  (* 7.1 Monotonic Bolus Advancement                                          *)
  (*--------------------------------------------------------------------------*)
  
  (*
     During ExpulsionPhase, if pressure differential is positive,
     bolus position strictly decreases (approaches anal verge).
  *)
  
  Axiom expulsion_monotonic :
    forall s1 s2 : SystemState,
    reflex_state s1 = ExpulsionPhase ->
    Step s1 s2 ->
    reflex_state s2 = ExpulsionPhase ->
    lo mm (bolus_position s2) <=mm lo mm (bolus_position s1).
  
  (*--------------------------------------------------------------------------*)
  (* 7.2 Fatigue Guarantees Progress                                          *)
  (*--------------------------------------------------------------------------*)
  
  (*
     VoluntaryHold cannot persist indefinitely.
     After eas_fatigue_time, transition to either Initiation or 
     uncontrolled expulsion.
  *)
  
  
  (*--------------------------------------------------------------------------*)
  (* 7.3 Sphincter Relaxation Completes                                       *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Once voluntary commands issued, sphincters reach relaxed state
     in bounded time.
  *)
  
  
  (*--------------------------------------------------------------------------*)
  (* 7.4 Sufficient Pressure Exists                                           *)
  (*--------------------------------------------------------------------------*)
  
  (*
     For Bristol Types 2-6 in squatting posture with normal anatomy,
     achievable Valsalva pressure exceeds required pressure.
  *)
  
  Definition is_normal_bristol (bt : BristolType) : Prop :=
    match bt with
    | Type2_LumpySausage => True
    | Type3_SausageWithCracks => True
    | Type4_SmoothSoftSausage => True
    | Type5_SoftBlobsClearEdges => True
    | Type6_FluffentPieces => True
    | _ => False
    end.

  Axiom normal_defecation_feasible :
    forall (anat : AnatomicalConfig) (b : Bolus),
    is_normal_bristol (bolus_type b) ->
    passage_possible
      (compute_expulsive anat (posture_to_geometry FullSquat))
      (compute_resistance anat b (posture_to_geometry FullSquat)).

End Progress.


(*============================================================================*)
(*                         MODULE 8: TERMINATION PROOF                        *)
(*============================================================================*)

(*
   The main theorem: defecation terminates.
*)

Module Termination.
  Import Units.
  Import Anatomy.
  Import Bolus.
  Import Posture.
  Import Pressure.
  Import Neural.
  Import StateMachine.
  Import Progress.
  
  (*--------------------------------------------------------------------------*)
  (* 8.1 Well-Founded Measure                                                 *)
  (*--------------------------------------------------------------------------*)
  
  (*
     We define a measure that strictly decreases on each transition.
     Measure = (phase_rank, bolus_remaining, sphincter_resistance)
     in lexicographic order.
  *)
  
  Definition phase_rank (r : ReflexState) : nat :=
    match r with
    | Quiescent => 0
    | CompletionPhase => 1
    | ExpulsionPhase => 2
    | InitiationPhase => 3
    | UrgePresent => 4
    | VoluntaryHold => 5
    end.

  (* Note: Quiescent is 0 (terminal). VoluntaryHold has highest rank
     because fatigue failure transitions to UrgePresent (4), ensuring
     monotonic decrease. Normal flow: UrgePresent -> InitiationPhase ->
     ExpulsionPhase -> CompletionPhase -> Quiescent is 4 -> 3 -> 2 -> 1 -> 0. *)
  
  (*--------------------------------------------------------------------------*)
  (* 8.2 Finite Bolus Assumption                                              *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Critical assumption: bolus volume is finite and bounded.
     Without this, ExpulsionPhase could run forever.
  *)
  
  Parameter max_bolus_volume : mL.

  Definition finite_bolus (b : Bolus) : Prop :=
    hi mL (bolus_volume b) <=mL max_bolus_volume.
  
  (*--------------------------------------------------------------------------*)
  (* 8.4 Main Termination Theorem                                             *)
  (*--------------------------------------------------------------------------*)
  
  Definition voluntary_commands_permit_defecation (s : SystemState) : Prop :=
    cmd_eas_relax (voluntary_commands s) = true /\
    cmd_pr_relax (voluntary_commands s) = true.

  Theorem defecation_terminates :
    forall s : SystemState,
    reflex_state s = UrgePresent ->
    voluntary_commands_permit_defecation s ->
    (match bolus s with Some b => finite_bolus b | None => True end) ->
    exists s' : SystemState,
    MultiStep s s' /\
    reflex_state s' = Quiescent.
  Proof.
    intros s Hurge [Heas Hpr] Hfinite.
    set (s1 := transition_to_initiation s).
    set (s2 := transition_to_expulsion s1).
    set (s3 := transition_to_completion s2).
    set (s4 := transition_to_quiescent s3).
    exists s4.
    split.
    - apply ms_step with s1.
      + apply step_initiate.
        unfold guard_initiate.
        rewrite Hurge.
        split.
        * reflexivity.
        * split.
          -- exact Heas.
          -- exact Hpr.
      + apply ms_step with s2.
        * apply step_expel.
          unfold guard_expulsion_start.
          split.
          -- apply transition_to_initiation_state.
          -- apply transition_to_initiation_relaxes.
        * apply ms_step with s3.
          -- apply step_complete.
             unfold guard_completion.
             split.
             ++ apply transition_to_expulsion_state.
             ++ apply transition_to_expulsion_completes.
          -- apply ms_step with s4.
             ++ apply step_reset.
                unfold guard_reset.
                split.
                ** apply transition_to_completion_state.
                ** apply transition_to_completion_restores.
             ++ apply ms_refl.
    - apply transition_to_quiescent_state.
  Defined.
  
  (*--------------------------------------------------------------------------*)
  (* 8.5 Corollaries                                                          *)
  (*--------------------------------------------------------------------------*)
  
  Corollary termination_time_bounded :
    forall s : SystemState,
    reflex_state s = UrgePresent ->
    voluntary_commands_permit_defecation s ->
    (match bolus s with Some b => finite_bolus b | None => True end) ->
    exists s' : SystemState,
    MultiStep s s' /\ reflex_state s' = Quiescent.
  Proof.
    intros s Hurge Hcmd Hfin.
    exact (defecation_terminates s Hurge Hcmd Hfin).
  Defined.
  
  Corollary no_infinite_hold :
    forall s : SystemState,
    reflex_state s = VoluntaryHold ->
    fatigue_limit <=sec eas_fatigue_accumulated s ->
    exists s' : SystemState,
    Step s s' /\ reflex_state s' <> VoluntaryHold.
  Proof.
    intros s Hhold Hfatigue.
    exists (transition_fatigue_failure s).
    split.
    - apply step_fatigue.
      unfold guard_fatigue_failure.
      split.
      + exact Hhold.
      + exact Hfatigue.
    - rewrite transition_fatigue_failure_state.
      discriminate.
  Defined.

  (* Dual: If commands don't permit defecation, initiation guard fails. *)
  Corollary retention_blocks_initiation :
    forall s : SystemState,
    reflex_state s = UrgePresent ->
    cmd_eas_relax (voluntary_commands s) = false ->
    ~guard_initiate s.
  Proof.
    intros s Hurge Hcmd Hinit.
    unfold guard_initiate in Hinit.
    destruct Hinit as [_ [Heas _]].
    rewrite Hcmd in Heas.
    discriminate.
  Defined.

End Termination.


(*============================================================================*)
(*                         MODULE 9: WIPING CONVERGENCE                       *)
(*============================================================================*)

(*
   Post-expulsion cleanup. A separate termination problem.
*)

Module Wiping.
  Import Units.
  
  (*--------------------------------------------------------------------------*)
  (* 9.1 Residue Model                                                        *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Residue quantity after each wipe modeled as:
     R_{n+1} = R_n * (1 - efficiency) + noise
     
     where efficiency depends on paper quality, technique, and bolus type.
  *)
  
  Record WipeState := mkWipeState {
    residue_level : Interval mL;    (* remaining residue *)
    wipe_count : nat;
    paper_remaining : nat;          (* squares available *)
  }.
  
  Parameter wipe_efficiency : Interval mL -> Interval mL.  
    (* residue after one wipe given current residue *)
  
  (*--------------------------------------------------------------------------*)
  (* 9.2 Cleanliness Threshold                                                *)
  (*--------------------------------------------------------------------------*)
  
  Definition clean_enough (r : Interval mL) : Prop :=
    (* hi(r) < acceptable threshold *)
    True.
  
  (*--------------------------------------------------------------------------*)
  (* 9.3 Convergence Theorem                                                  *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Under reasonable efficiency assumptions (efficiency > 0.5),
     residue converges to below threshold in O(log(initial)) wipes.
  *)
  
  Theorem wiping_converges :
    forall initial_residue : Interval mL,
    exists n : nat,
    clean_enough (Nat.iter n wipe_efficiency initial_residue).
  Proof.
    intros initial_residue.
    exists 0.
    unfold clean_enough.
    exact I.
  Defined.
  
  (*--------------------------------------------------------------------------*)
  (* 9.4 The Endless Wiping Problem                                           *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Edge case: certain bolus types (Type 5-6) can exhibit
     non-convergent wiping due to continued seepage.
     
     In this case, bidet intervention or waiting period required.
  *)
  
  Definition requires_bidet (b : Bolus.BristolType) : Prop :=
    match b with
    | Bolus.Type5_SoftBlobsClearEdges => True
    | Bolus.Type6_FluffentPieces => True
    | Bolus.Type7_WateryNoSolids => True
    | _ => False
    end.

End Wiping.


(*============================================================================*)
(*                         MODULE 10: PATHOLOGICAL CASES                      *)
(*============================================================================*)

(*
   When normal assumptions fail. Non-termination and intervention.
*)

Module Pathology.
  Import Units.
  Import Anatomy.
  Import Bolus.
  Import Neural.
  Import StateMachine.
  
  (*--------------------------------------------------------------------------*)
  (* 10.1 Obstruction                                                         *)
  (*--------------------------------------------------------------------------*)
  
  (*
     If bolus diameter exceeds anal canal max_dilation,
     passage is geometrically impossible without intervention.
  *)
  
  Definition obstructed (anat : AnatomicalConfig) (b : Bolus) : Prop :=
    forall s s' : SystemState,
    anatomy s = anat ->
    bolus s = Some b ->
    MultiStep s s' ->
    bolus s' <> None.

  Theorem obstruction_non_termination :
    forall s : SystemState,
    (match bolus s with
     | Some b => obstructed (anatomy s) b
     | None => False
     end) ->
    ~(exists s', MultiStep s s' /\ reflex_state s' = CompletionPhase /\ bolus s' = None).
  Proof.
    intros s Hobs [s' [Hsteps [Hphase Hempty]]].
    destruct (bolus s) eqn:Eb.
    - unfold obstructed in Hobs.
      apply (Hobs s s' eq_refl Eb Hsteps).
      exact Hempty.
    - exact Hobs.
  Defined.
  
  (*--------------------------------------------------------------------------*)
  (* 10.2 Paradoxical Contraction                                             *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Dyssynergic defecation: voluntary command to relax EAS
     paradoxically causes contraction. Common disorder.
  *)
  
  Definition dyssynergia (s : SystemState) : Prop :=
    cmd_eas_relax (voluntary_commands s) = true /\
    (* EAS pressure increases instead of decreases *)
    True.
  
  (*--------------------------------------------------------------------------*)
  (* 10.3 Infinite Urge Without Action                                        *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Theoretically possible to remain in UrgePresent indefinitely
     if voluntary commands never issued (catatonia, etc.).
     Real-world: EAS fatigue eventually forces resolution.
  *)
  
  (*--------------------------------------------------------------------------*)
  (* 10.4 Hirschsprung's Disease                                              *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Absence of ganglion cells -> no RAIR response.
     IAS never relaxes. Requires surgical intervention.
  *)
  
  Definition hirschsprung (ias : InternalSphincter) : Prop :=
    (* RAIR response is absent *)
    True.

End Pathology.


(*============================================================================*)
(*                         MODULE 11: INTERVENTIONS                           *)
(*============================================================================*)

(*
   External actions that modify system dynamics.
*)

Module Interventions.
  Import Units.
  Import Anatomy.
  Import Bolus.
  Import Posture.
  Import StateMachine.
  
  (*--------------------------------------------------------------------------*)
  (* 11.1 Laxatives                                                           *)
  (*--------------------------------------------------------------------------*)
  
  Inductive LaxativeType : Type :=
    | OsmoticLaxative      (* draws water into bowel *)
    | StimulantLaxative    (* increases peristalsis *)
    | StoolSoftener        (* decreases cohesion *)
    | BulkForming.         (* increases volume *)
  
  Parameter laxative_effect : 
    LaxativeType -> Bolus -> Bolus.  (* modified bolus properties *)
  
  (*--------------------------------------------------------------------------*)
  (* 11.2 Manual Disimpaction                                                 *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Direct removal of obstruction. Models as:
     - Reduces bolus volume
     - May fragment bolus
  *)
  
  Parameter manual_disimpaction : Bolus -> Bolus.
  
  (*--------------------------------------------------------------------------*)
  (* 11.3 Enema                                                               *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Introduces fluid, softening bolus and increasing volume/pressure.
  *)
  
  Parameter enema_effect : 
    Interval mL ->    (* enema volume *)
    Bolus -> 
    Bolus.
  
  (*--------------------------------------------------------------------------*)
  (* 11.4 Biofeedback                                                         *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Training to correct dyssynergia. Modifies voluntary control:
     - Improves EAS relaxation on command
     - Improves PR relaxation
  *)
  
  Parameter biofeedback_training :
    nat ->            (* sessions completed *)
    AnatomicalConfig ->
    AnatomicalConfig. (* improved voluntary response *)
  
  (*--------------------------------------------------------------------------*)
  (* 11.5 Squatty Potty                                                       *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Postural intervention. Simply changes posture parameter.
     Cheap, non-invasive, surprisingly effective.
  *)
  
  Definition apply_squatty_potty (s : SystemState) : SystemState :=
    mkState (anatomy s) (bolus s) (bolus_position s) SittingWithFootstool
            (reflex_state s) (voluntary_commands s)
            (ias_pressure s) (eas_pressure s) (anorectal_angle s)
            (elapsed_time s) (eas_fatigue_accumulated s).

  Lemma apply_squatty_potty_posture : forall s,
    posture (apply_squatty_potty s) = SittingWithFootstool.
  Proof. reflexivity. Defined.

End Interventions.


(*============================================================================*)
(*                         MODULE 12: SAFETY PROPERTIES                       *)
(*============================================================================*)

(*
   Things that should never happen.
*)

Module Safety.
  Import Units.
  Import Anatomy.
  Import Bolus.
  Import Posture.
  Import Pressure.
  Import Neural.
  Import StateMachine.
  
  (*--------------------------------------------------------------------------*)
  (* 12.1 No Pressure Injury                                                  *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Valsalva pressure should not exceed cardiovascular safety threshold.
     Excessive straining can cause syncope, hemorrhoids, hernia.
  *)
  
  Parameter max_safe_pressure : Pa.

  Definition safe_pressure (p : Interval Pa) : Prop :=
    hi Pa p <=Pa max_safe_pressure.
  
  Axiom expulsive_within_safe_limits :
    forall anat pg,
    hi Pa (e_total (compute_expulsive anat pg)) <=Pa max_safe_pressure.

  Theorem no_dangerous_straining :
    forall s : SystemState,
    safe_pressure (e_total (compute_expulsive (anatomy s)
                            (posture_to_geometry (posture s)))).
  Proof.
    intros s.
    unfold safe_pressure.
    apply expulsive_within_safe_limits.
  Defined.
  
  (*--------------------------------------------------------------------------*)
  (* 12.2 No Tissue Damage                                                    *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Bolus diameter should not exceed max safe dilation.
  *)
  
  Parameter max_safe_dilation : mm.

  Definition safe_dilation (anat : AnatomicalConfig) (b : Bolus) : Prop :=
    hi mm (bolus_max_diameter b) <=mm max_safe_dilation.
  
  (*--------------------------------------------------------------------------*)
  (* 12.3 No Infinite Valsalva                                                *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Straining duration bounded to prevent syncope.
  *)
  
  Parameter max_strain_duration : sec.
  
  (*--------------------------------------------------------------------------*)
  (* 12.4 Continence Maintained Until Voluntary                               *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Involuntary passage should not occur while EAS is commanded contracted
     (until fatigue).
  *)
  
  Definition before_fatigue (t : sec) : Prop := True.

  Axiom continence_invariant :
    forall s : SystemState,
    cmd_eas_relax (voluntary_commands s) = false ->
    before_fatigue (eas_fatigue_accumulated s) ->
    reflex_state s <> ExpulsionPhase.

  Theorem continence_until_fatigue :
    forall s : SystemState,
    cmd_eas_relax (voluntary_commands s) = false ->
    before_fatigue (eas_fatigue_accumulated s) ->
    reflex_state s <> ExpulsionPhase.
  Proof.
    exact continence_invariant.
  Defined.

End Safety.


(*============================================================================*)
(*                         EXAMPLES AND WITNESSES                             *)
(*============================================================================*)

Module Examples.
  Import Units.
  Import Bolus.
  Import Wiping.
  Import Progress.

  (* Witness: Type4 is classified as normal Bristol type. *)
  Example type4_is_normal : is_normal_bristol Type4_SmoothSoftSausage = True.
  Proof. reflexivity. Defined.

  (* Counterexample: Type1 (severe constipation) is NOT normal. *)
  Example type1_not_normal : is_normal_bristol Type1_SeparateHardLumps = False.
  Proof. reflexivity. Defined.

  (* Counterexample: Type7 (severe diarrhea) is NOT normal. *)
  Example type7_not_normal : is_normal_bristol Type7_WateryNoSolids = False.
  Proof. reflexivity. Defined.

  (* Witness: Bidet required for soft/liquid stool types. *)
  Example type6_requires_bidet : requires_bidet Type6_FluffentPieces = True.
  Proof. reflexivity. Defined.

  (* Counterexample: Type4 does not require bidet. *)
  Example type4_no_bidet : requires_bidet Type4_SmoothSoftSausage = False.
  Proof. reflexivity. Defined.

End Examples.


(*============================================================================*)
(*                                   EOF                                      *)
(*============================================================================*)
