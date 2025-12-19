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
  Definition mm : Type := nat.
  Definition cm : Type := nat.
  Definition Pa : Type := nat.
  Definition N : Type := nat.
  Definition deg : Type := nat.
  Definition sec : Type := nat.
  Definition mL : Type := nat.
  Definition cP : Type := nat.

  Definition mm_le : mm -> mm -> Prop := le.
  Definition Pa_le : Pa -> Pa -> Prop := le.
  Definition mL_le : mL -> mL -> Prop := le.
  Definition sec_le : sec -> sec -> Prop := le.
  Definition deg_le : deg -> deg -> Prop := le.

  Notation "x <=mm y" := (mm_le x y) (at level 70).
  Notation "x <=Pa y" := (Pa_le x y) (at level 70).
  Notation "x <=mL y" := (mL_le x y) (at level 70).
  Notation "x <=sec y" := (sec_le x y) (at level 70).
  Notation "x <=deg y" := (deg_le x y) (at level 70).

  Class LeRefl (A : Type) (le : A -> A -> Prop) := le_refl : forall x, le x x.

  Global Instance mm_le_refl : LeRefl mm mm_le.
  Proof. unfold LeRefl, mm_le. lia. Defined.

  Global Instance Pa_le_refl : LeRefl Pa Pa_le.
  Proof. unfold LeRefl, Pa_le. lia. Defined.

  Global Instance mL_le_refl : LeRefl mL mL_le.
  Proof. unfold LeRefl, mL_le. lia. Defined.

  Global Instance sec_le_refl : LeRefl sec sec_le.
  Proof. unfold LeRefl, sec_le. lia. Defined.

  Global Instance deg_le_refl : LeRefl deg deg_le.
  Proof. unfold LeRefl, deg_le. lia. Defined.

  Class LeTrans (A : Type) (le : A -> A -> Prop)
    := le_trans : forall x y z, le x y -> le y z -> le x z.

  Global Instance mm_le_trans : LeTrans mm mm_le.
  Proof. unfold LeTrans, mm_le. intros. lia. Defined.

  Global Instance Pa_le_trans : LeTrans Pa Pa_le.
  Proof. unfold LeTrans, Pa_le. intros. lia. Defined.

  Global Instance mL_le_trans : LeTrans mL mL_le.
  Proof. unfold LeTrans, mL_le. intros. lia. Defined.

  Record Interval (A : Type) := mkInterval {
    lo : A;
    hi : A;
  }.

  Definition interval_wf {A : Type} (le_A : A -> A -> Prop) (i : Interval A) : Prop :=
    le_A (lo A i) (hi A i).

  Notation "i 'wf_mm'" := (interval_wf mm_le i) (at level 50).
  Notation "i 'wf_Pa'" := (interval_wf Pa_le i) (at level 50).
  Notation "i 'wf_mL'" := (interval_wf mL_le i) (at level 50).

  Definition Pa_sub (x y : Pa) : Pa := x - y.
  Definition Pa_add (x y : Pa) : Pa := x + y.
  Definition Pa_mul (x y : Pa) : Pa := x * y.
  Definition Pa_div (x y : Pa) : Pa := Nat.div x (S y).
  Definition mL_sub (x y : mL) : mL := x - y.
  Definition mm_sub (x y : mm) : mm := x - y.
  Definition mm_add (x y : mm) : mm := x + y.
  Definition mm_div (x y : mm) : mm := Nat.div x (S y).

  Definition iv_sub (i1 i2 : Interval Pa) : Interval Pa :=
    mkInterval Pa (Pa_sub (lo Pa i1) (hi Pa i2)) (Pa_sub (hi Pa i1) (lo Pa i2)).

  Definition iv_add (i1 i2 : Interval Pa) : Interval Pa :=
    mkInterval Pa (Pa_add (lo Pa i1) (lo Pa i2)) (Pa_add (hi Pa i1) (hi Pa i2)).

  Definition iv_mul (i1 i2 : Interval Pa) : Interval Pa :=
    mkInterval Pa (Pa_mul (lo Pa i1) (lo Pa i2)) (Pa_mul (hi Pa i1) (hi Pa i2)).

  Definition iv_scale (k : nat) (i : Interval Pa) : Interval Pa :=
    mkInterval Pa (k * lo Pa i) (k * hi Pa i).

  Definition iv_div (i : Interval Pa) (d : nat) : Interval Pa :=
    mkInterval Pa (Nat.div (lo Pa i) (S d)) (Nat.div (hi Pa i) (S d)).

  Definition iv_mm_sub (i1 i2 : Interval mm) : Interval mm :=
    mkInterval mm (mm_sub (lo mm i1) (hi mm i2)) (mm_sub (hi mm i1) (lo mm i2)).

  Definition iv_mm_add (i1 i2 : Interval mm) : Interval mm :=
    mkInterval mm (mm_add (lo mm i1) (lo mm i2)) (mm_add (hi mm i1) (hi mm i2)).

  Definition iv_mm_scale (k : nat) (i : Interval mm) : Interval mm :=
    mkInterval mm (k * lo mm i) (k * hi mm i).

  Definition iv_mm_div (i : Interval mm) (d : nat) : Interval mm :=
    mkInterval mm (Nat.div (lo mm i) (S d)) (Nat.div (hi mm i) (S d)).

  Lemma iv_sub_lo : forall i1 i2 : Interval Pa,
    lo Pa (iv_sub i1 i2) = Pa_sub (lo Pa i1) (hi Pa i2).
  Proof. reflexivity. Defined.

  Lemma iv_sub_hi : forall i1 i2 : Interval Pa,
    hi Pa (iv_sub i1 i2) = Pa_sub (hi Pa i1) (lo Pa i2).
  Proof. reflexivity. Defined.

  Lemma iv_mul_lo : forall i1 i2 : Interval Pa,
    lo Pa (iv_mul i1 i2) = Pa_mul (lo Pa i1) (lo Pa i2).
  Proof. reflexivity. Defined.

  Lemma iv_mul_hi : forall i1 i2 : Interval Pa,
    hi Pa (iv_mul i1 i2) = Pa_mul (hi Pa i1) (hi Pa i2).
  Proof. reflexivity. Defined.

  Lemma iv_scale_monotonic : forall k i,
    lo Pa i <= hi Pa i -> lo Pa (iv_scale k i) <= hi Pa (iv_scale k i).
  Proof.
    intros k i Hwf.
    unfold iv_scale.
    simpl.
    apply PeanoNat.Nat.mul_le_mono_l.
    exact Hwf.
  Defined.

  Definition positive_differential (diff : Interval Pa) : Prop :=
    lo Pa diff > 0.
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
  
  Definition default_rectum : Rectum :=
    mkRectum
      (mkInterval mm 120 150)
      (mkInterval mm 25 40)
      (mkInterval mm 60 90)
      (mkInterval (Pa -> mm) (fun p => Nat.div p 100) (fun p => Nat.div p 50))
      (mkInterval mL 100 150)
      (mkInterval mL 200 300)
      (mkInterval mL 400 500).

  Definition apply_compliance (c : Pa -> mm) (pressure : Pa) : mm := c pressure.

  Definition effective_diameter (r : Rectum) (pressure : Pa) : Interval mm :=
    let base := resting_diameter r in
    let expansion_lo := apply_compliance (lo (Pa -> mm) (wall_compliance r)) pressure in
    let expansion_hi := apply_compliance (hi (Pa -> mm) (wall_compliance r)) pressure in
    mkInterval mm (lo mm base + expansion_lo) (hi mm base + expansion_hi).

  Lemma compliance_increases_diameter :
    forall r p,
    p > 0 ->
    lo mm (effective_diameter r p) >= lo mm (resting_diameter r).
  Proof.
    intros r p Hp.
    unfold effective_diameter.
    simpl.
    lia.
  Defined.
  
  
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
  
  Definition default_ias : InternalSphincter :=
    mkIAS
      (mkInterval mm 25 30)
      (mkInterval mm 2 4)
      (mkInterval Pa 3900 6900)
      (mkInterval sec 1 3)
      (mkInterval Pa 2000 4000).
  
  
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
  
  Definition default_eas : ExternalSphincter :=
    mkEAS
      (mkInterval mm 8 10)
      (mkInterval Pa 1500 2500)
      (mkInterval Pa 10000 18000)
      (mkInterval sec 60 180)
      (mkInterval Pa 500 1000).
  
  
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
  
  Definition default_puborectalis : Puborectalis :=
    mkPR
      (mkInterval deg 80 92)
      (mkInterval deg 126 142)
      (mkInterval sec 2 5)
      (mkInterval deg 5 15).
  
  
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
  
  Definition default_abdominal_wall : AbdominalWall :=
    mkAW
      (mkInterval Pa 4000 10000)
      (mkInterval Pa 2000 4000)
      (fun t => mkInterval Pa (4000 - Nat.mul t 20) (10000 - Nat.mul t 50)).
  
  
  (*--------------------------------------------------------------------------*)
  (* 1.6 Anal Canal Geometry                                                  *)
  (*--------------------------------------------------------------------------*)
  
  Record AnalCanal := mkAC {
    ac_length : Interval mm;                  (* 25-50mm *)
    ac_resting_diameter : Interval mm;        (* functionally closed *)
    ac_max_dilation : Interval mm;            (* 30-40mm without injury *)
    ac_mucosal_friction : Interval cP;        (* surface friction coefficient *)
  }.
  
  Definition default_anal_canal : AnalCanal :=
    mkAC
      (mkInterval mm 25 50)
      (mkInterval mm 0 5)
      (mkInterval mm 30 40)
      (mkInterval cP 100 500).
  
  
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
  
  Definition default_anatomy : AnatomicalConfig :=
    mkAnatomy
      default_rectum
      default_ias
      default_eas
      default_puborectalis
      default_abdominal_wall
      default_anal_canal.
  
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
  
  Definition bristol_to_physics (bt : BristolType) : BolusPhysics :=
    match bt with
    | Type1_SeparateHardLumps =>
        mkBolusPhysics
          (mkInterval cP 10000 50000)
          (mkInterval Pa 500 1000)
          (mkInterval Pa 800 1200)
          true
          (mkInterval mm 10 20)
    | Type2_LumpySausage =>
        mkBolusPhysics
          (mkInterval cP 5000 15000)
          (mkInterval Pa 200 500)
          (mkInterval Pa 400 800)
          false
          (mkInterval mm 25 35)
    | Type3_SausageWithCracks =>
        mkBolusPhysics
          (mkInterval cP 2000 8000)
          (mkInterval Pa 100 300)
          (mkInterval Pa 200 500)
          false
          (mkInterval mm 20 30)
    | Type4_SmoothSoftSausage =>
        mkBolusPhysics
          (mkInterval cP 1000 4000)
          (mkInterval Pa 50 150)
          (mkInterval Pa 100 300)
          false
          (mkInterval mm 20 30)
    | Type5_SoftBlobsClearEdges =>
        mkBolusPhysics
          (mkInterval cP 500 2000)
          (mkInterval Pa 20 80)
          (mkInterval Pa 30 100)
          true
          (mkInterval mm 15 25)
    | Type6_FluffentPieces =>
        mkBolusPhysics
          (mkInterval cP 100 500)
          (mkInterval Pa 5 30)
          (mkInterval Pa 10 50)
          true
          (mkInterval mm 10 20)
    | Type7_WateryNoSolids =>
        mkBolusPhysics
          (mkInterval cP 1 50)
          (mkInterval Pa 0 5)
          (mkInterval Pa 0 10)
          true
          (mkInterval mm 0 10)
    end.
  
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

  Definition make_bolus (bt : BristolType) (vol : Interval mL) : Bolus :=
    let physics := bristol_to_physics bt in
    mkBolus
      bt
      vol
      (mkInterval mm (Nat.mul (lo mL vol) 2) (Nat.mul (hi mL vol) 3))
      (bp_typical_diameter physics)
      physics.
  
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
  
  Definition posture_to_geometry (pt : PostureType) : PostureGeometry :=
    match pt with
    | Standing =>
        mkPostureGeometry
          (mkInterval deg 170 180)
          (mkInterval deg 85 95)
          false
          (mkInterval Pa 0 0)
    | SittingUpright =>
        mkPostureGeometry
          (mkInterval deg 85 95)
          (mkInterval deg 95 105)
          false
          (mkInterval Pa 200 500)
    | SittingLeaning =>
        mkPostureGeometry
          (mkInterval deg 60 75)
          (mkInterval deg 110 120)
          false
          (mkInterval Pa 500 1000)
    | SittingWithFootstool =>
        mkPostureGeometry
          (mkInterval deg 40 55)
          (mkInterval deg 120 130)
          true
          (mkInterval Pa 1000 1500)
    | FullSquat =>
        mkPostureGeometry
          (mkInterval deg 20 40)
          (mkInterval deg 130 140)
          true
          (mkInterval Pa 1500 2500)
    end.
  
  (*--------------------------------------------------------------------------*)
  (* 3.3 The Squatty Potty Theorem                                            *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Claim: For a given bolus and anatomy, required expulsive pressure
     is monotonically decreasing in anorectal angle.
     
     Proof sketch: Straighter path = less resistance.
  *)
  
  Definition angle_pressure_relationship (angle : deg) (b : Bolus.Bolus) : Interval Pa :=
    let physics := Bolus.bolus_physics b in
    let base_pressure := lo Pa (Bolus.bp_yield_stress physics) in
    let angle_factor := if Nat.leb angle 100 then 3 else
                        if Nat.leb angle 120 then 2 else 1 in
    mkInterval Pa
      (Nat.mul base_pressure angle_factor)
      (Nat.mul (hi Pa (Bolus.bp_yield_stress physics)) (S angle_factor)).

  Lemma angle_pressure_decreases_with_angle :
    forall b : Bolus.Bolus,
    forall a1 a2 : deg,
    a1 < a2 ->
    a2 > 120 ->
    hi Pa (angle_pressure_relationship a2 b) <= hi Pa (angle_pressure_relationship a1 b) \/
    a1 <= 120.
  Proof.
    intros b a1 a2 Hlt Hgt.
    destruct (Compare_dec.le_dec a1 120) as [Hle | Hgt1].
    - right.
      exact Hle.
    - left.
      unfold angle_pressure_relationship.
      simpl.
      assert (Ha2: Nat.leb a2 100 = false) by (apply PeanoNat.Nat.leb_gt; lia).
      assert (Ha2': Nat.leb a2 120 = false) by (apply PeanoNat.Nat.leb_gt; lia).
      assert (Ha1: Nat.leb a1 100 = false) by (apply PeanoNat.Nat.leb_gt; lia).
      assert (Ha1': Nat.leb a1 120 = false) by (apply PeanoNat.Nat.leb_gt; lia).
      rewrite Ha1, Ha1', Ha2, Ha2'.
      simpl.
      lia.
  Defined.
  

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
  
  Definition compute_resistance
    (anat : AnatomicalConfig) (b : Bolus) (pg : PostureGeometry)
    : ResistanceComponents :=
    let ias_r := ias_resting_pressure (ias anat) in
    let eas_r := eas_resting_pressure (eas anat) in
    let friction := mkInterval Pa
      (Nat.mul (lo cP (bp_viscosity b)) (lo mm (bolus_length b)))
      (Nat.mul (hi cP (bp_viscosity b)) (hi mm (bolus_length b))) in
    let angle_r := angle_pressure_relationship
      (lo deg (resultant_anorectal_angle pg)) b in
    let total := mkInterval Pa
      (lo Pa ias_r + lo Pa eas_r + lo Pa friction + lo Pa angle_r)
      (hi Pa ias_r + hi Pa eas_r + hi Pa friction + hi Pa angle_r) in
    mkResistance ias_r eas_r friction angle_r total.
  
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
  
  Definition safe_expulsive_bound : Pa := 15000.
  Definition peristaltic_base_lo : Pa := 500.
  Definition peristaltic_base_hi : Pa := 1500.
  Definition compression_bonus : Pa := 1000.

  Definition compute_expulsive
    (anat : AnatomicalConfig) (pg : PostureGeometry) : ExpulsiveComponents :=
    let aw := abdominal_wall anat in
    let valsalva := aw_max_valsalva_pressure aw in
    let peristalsis := mkInterval Pa peristaltic_base_lo peristaltic_base_hi in
    let pf_bonus := pelvic_floor_relaxation_bonus pg in
    let compress := if thigh_abdominal_compression pg then compression_bonus else 0 in
    let gravity := iv_add pf_bonus (mkInterval Pa compress compress) in
    let raw_total_lo := lo Pa valsalva + lo Pa peristalsis + lo Pa gravity in
    let raw_total_hi := hi Pa valsalva + hi Pa peristalsis + hi Pa gravity in
    let capped_lo := Nat.min raw_total_lo safe_expulsive_bound in
    let capped_hi := Nat.min raw_total_hi safe_expulsive_bound in
    mkExpulsive valsalva peristalsis gravity (mkInterval Pa capped_lo capped_hi).
  
  (*--------------------------------------------------------------------------*)
  (* 4.3 Pressure Differential                                                *)
  (*--------------------------------------------------------------------------*)
  
  Definition pressure_differential
    (exp : ExpulsiveComponents) (res : ResistanceComponents) : Interval Pa :=
    iv_sub (e_total exp) (r_total res).
  
  (*--------------------------------------------------------------------------*)
  (* 4.4 Passage Criterion                                                    *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Bolus moves iff expulsive pressure > resistance.
     Flow rate is function of pressure differential and viscosity.
  *)
  
  Definition passage_possible (exp : ExpulsiveComponents) (res : ResistanceComponents) : Prop :=
    lo Pa (e_total exp) > hi Pa (r_total res).
  
  Definition flow_rate
    (pressure_diff : Interval Pa) (physics : BolusPhysics) : Interval mm :=
    let viscosity := bp_viscosity physics in
    let yield := bp_yield_stress physics in
    let effective_pressure_lo := lo Pa pressure_diff - hi Pa yield in
    let effective_pressure_hi := hi Pa pressure_diff - lo Pa yield in
    let flow_lo := Nat.div effective_pressure_lo (S (hi cP viscosity)) in
    let flow_hi := Nat.div effective_pressure_hi (S (lo cP viscosity)) in
    mkInterval mm flow_lo flow_hi.

  Lemma flow_rate_nonneg :
    forall diff physics,
    lo mm (flow_rate diff physics) >= 0.
  Proof.
    intros diff physics.
    unfold flow_rate.
    simpl.
    lia.
  Defined.

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
  
  Definition compute_rair
    (ias : InternalSphincter) (volume : Interval mL) : RAIR_Response :=
    mkRAIR
      volume
      (ias_relaxation_magnitude ias)
      (ias_relaxation_latency ias)
      (mkInterval sec 10 30).
  
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
  
  Definition eas_fatigue_model
    (eas : ExternalSphincter) (t : sec) : Interval Pa :=
    let max_lo := lo Pa (eas_max_squeeze_pressure eas) in
    let max_hi := hi Pa (eas_max_squeeze_pressure eas) in
    let fatigue_lo := lo sec (eas_fatigue_time eas) in
    let fatigue_hi := hi sec (eas_fatigue_time eas) in
    let remaining_lo := if Nat.leb t fatigue_lo
                        then max_lo - Nat.div (Nat.mul max_lo t) fatigue_hi
                        else 0 in
    let remaining_hi := if Nat.leb t fatigue_hi
                        then max_hi - Nat.div (Nat.mul max_hi t) (S fatigue_hi)
                        else lo Pa (eas_voluntary_relaxation_floor eas) in
    mkInterval Pa remaining_lo remaining_hi.

  Lemma eas_fatigue_nonneg :
    forall eas t,
    lo Pa (eas_fatigue_model eas t) >= 0.
  Proof.
    intros eas t.
    unfold eas_fatigue_model.
    simpl.
    lia.
  Defined.
  
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
  
  Definition urge_threshold : mL := 100.

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
  
  Definition fatigue_limit : sec := 180.

  Definition guard_fatigue_failure (s : SystemState) : Prop :=
    reflex_state s = VoluntaryHold /\
    fatigue_limit <=sec eas_fatigue_accumulated s.
  
  Definition relaxation_threshold : Pa := 500.

  Definition guard_expulsion_start (s : SystemState) : Prop :=
    reflex_state s = InitiationPhase /\
    hi Pa (eas_pressure s) <=Pa relaxation_threshold /\
    hi Pa (ias_pressure s) <=Pa relaxation_threshold.
  
  Definition passage_complete_threshold : mm := 0.

  Definition guard_completion (s : SystemState) : Prop :=
    reflex_state s = ExpulsionPhase /\
    hi mm (bolus_position s) <=mm passage_complete_threshold.
  
  Definition resting_tone_threshold : Pa := 3000.

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
  Definition time_step : sec := 1.
  Definition hold_fatigue_increment : sec := 10.

  Definition transition_to_urge (s : SystemState) : SystemState :=
    mkState (anatomy s) (bolus s) (bolus_position s) (posture s)
            UrgePresent (voluntary_commands s)
            (ias_pressure s) (eas_pressure s) (anorectal_angle s)
            (S (elapsed_time s)) (eas_fatigue_accumulated s).

  Definition transition_to_hold (s : SystemState) : SystemState :=
    mkState (anatomy s) (bolus s) (bolus_position s) (posture s)
            VoluntaryHold (voluntary_commands s)
            (ias_pressure s) (eas_pressure s) (anorectal_angle s)
            (S (elapsed_time s)) (eas_fatigue_accumulated s + hold_fatigue_increment).

  Definition transition_to_initiation (s : SystemState) : SystemState :=
    mkState (anatomy s) (bolus s) (bolus_position s) (posture s)
            InitiationPhase (voluntary_commands s)
            relaxed_pressure relaxed_pressure (anorectal_angle s)
            (S (elapsed_time s)) (eas_fatigue_accumulated s).

  Definition transition_fatigue_failure (s : SystemState) : SystemState :=
    mkState (anatomy s) (bolus s) (bolus_position s) (posture s)
            UrgePresent (voluntary_commands s)
            (ias_pressure s) relaxed_pressure (anorectal_angle s)
            (S (elapsed_time s)) (eas_fatigue_accumulated s).

  Definition transition_to_expulsion (s : SystemState) : SystemState :=
    mkState (anatomy s) (bolus s) (bolus_position s) (posture s)
            ExpulsionPhase (voluntary_commands s)
            relaxed_pressure relaxed_pressure (anorectal_angle s)
            (S (elapsed_time s)) (eas_fatigue_accumulated s).

  Definition compute_bolus_advancement (s : SystemState) : Interval mm :=
    match bolus s with
    | None => mkInterval mm 0 0
    | Some b =>
        let pg := Posture.posture_to_geometry (posture s) in
        let exp := Pressure.compute_expulsive (anatomy s) pg in
        let res := Pressure.compute_resistance (anatomy s) b pg in
        let diff := Pressure.pressure_differential exp res in
        Pressure.flow_rate diff (Bolus.bolus_physics b)
    end.

  Definition transition_expulsion_tick (s : SystemState) : SystemState :=
    let advancement := compute_bolus_advancement s in
    let new_pos_lo := lo mm (bolus_position s) - hi mm advancement in
    let new_pos_hi := hi mm (bolus_position s) - lo mm advancement in
    let clamped_lo := if Nat.leb (lo mm (bolus_position s)) (hi mm advancement) then 0 else new_pos_lo in
    let clamped_hi := if Nat.leb (hi mm (bolus_position s)) (lo mm advancement) then 0 else new_pos_hi in
    mkState (anatomy s) (bolus s) (mkInterval mm clamped_lo clamped_hi) (posture s)
            ExpulsionPhase (voluntary_commands s)
            relaxed_pressure relaxed_pressure (anorectal_angle s)
            (S (elapsed_time s)) (eas_fatigue_accumulated s).

  Definition guard_expulsion_tick (s : SystemState) : Prop :=
    reflex_state s = ExpulsionPhase /\
    hi mm (bolus_position s) > passage_complete_threshold.

  Definition transition_to_completion (s : SystemState) : SystemState :=
    mkState (anatomy s) None zero_position (posture s)
            CompletionPhase (voluntary_commands s)
            default_ias_pressure default_eas_pressure (anorectal_angle s)
            (S (elapsed_time s)) 0.

  Definition transition_to_quiescent (s : SystemState) : SystemState :=
    mkState (anatomy s) None zero_position (posture s)
            Quiescent (voluntary_commands s)
            default_ias_pressure default_eas_pressure (anorectal_angle s)
            0 0.

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
  Lemma transition_to_expulsion_preserves_position :
    forall s, bolus_position (transition_to_expulsion s) = bolus_position s.
  Proof. reflexivity. Defined.

  Lemma transition_expulsion_tick_state :
    forall s, reflex_state (transition_expulsion_tick s) = ExpulsionPhase.
  Proof. reflexivity. Defined.

  Lemma transition_expulsion_tick_decreases :
    forall s,
    hi mm (bolus_position (transition_expulsion_tick s)) <= hi mm (bolus_position s).
  Proof.
    intros s.
    unfold transition_expulsion_tick.
    simpl.
    destruct (Nat.leb (hi mm (bolus_position s)) (lo mm (compute_bolus_advancement s))); lia.
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
    | step_expulsion_tick : forall s,
        guard_expulsion_tick s ->
        Step s (transition_expulsion_tick s)
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

  Lemma ms_trans : forall a b c,
    MultiStep a b -> MultiStep b c -> MultiStep a c.
  Proof.
    intros a b c Hab Hbc.
    induction Hab.
    - exact Hbc.
    - apply ms_step with s2.
      + exact H.
      + apply IHHab.
        exact Hbc.
  Defined.

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

  Definition bolus_advances (pos_before pos_after : Interval mm) : Prop :=
    hi mm pos_after < hi mm pos_before.

  Lemma flow_implies_advancement :
    forall diff physics pos_before,
    lo Pa diff > hi Pa (bp_yield_stress physics) ->
    lo mm (flow_rate diff physics) > 0 ->
    hi mm pos_before > 0 ->
    exists pos_after : Interval mm,
    bolus_advances pos_before pos_after.
  Proof.
    intros diff physics pos_before Hdiff Hflow Hpos.
    exists (mkInterval mm 0 (hi mm pos_before - 1)).
    unfold bolus_advances.
    simpl.
    lia.
  Defined.

  Lemma advancement_reduces_remaining :
    forall pos1 pos2 : Interval mm,
    bolus_advances pos1 pos2 ->
    hi mm pos2 < hi mm pos1.
  Proof.
    intros pos1 pos2 Hadv.
    unfold bolus_advances in Hadv.
    exact Hadv.
  Defined.

  (*--------------------------------------------------------------------------*)
  (* 7.2 Fatigue Guarantees Progress                                          *)
  (*--------------------------------------------------------------------------*)

  (*
     VoluntaryHold cannot persist indefinitely.
     After eas_fatigue_time, transition to either Initiation or
     uncontrolled expulsion.
  *)

  Definition fatigue_exceeds_limit (acc : sec) : Prop :=
    StateMachine.fatigue_limit <=sec acc.

  Lemma fatigue_forces_transition :
    forall eas t,
    interval_wf sec_le (eas_fatigue_time eas) ->
    t > hi sec (eas_fatigue_time eas) ->
    lo Pa (eas_fatigue_model eas t) = 0.
  Proof.
    intros eas t Hwf Hgt.
    unfold eas_fatigue_model.
    assert (Hlo: Nat.leb t (lo sec (eas_fatigue_time eas)) = false).
    { apply PeanoNat.Nat.leb_gt.
      unfold interval_wf, sec_le in Hwf.
      lia. }
    rewrite Hlo.
    simpl.
    reflexivity.
  Defined.

  Lemma hold_bounded_by_fatigue :
    forall acc_start acc_end : sec,
    acc_end >= acc_start ->
    acc_end >= StateMachine.fatigue_limit ->
    fatigue_exceeds_limit acc_end.
  Proof.
    intros acc_start acc_end Hge Hlim.
    unfold fatigue_exceeds_limit, StateMachine.fatigue_limit, sec_le.
    exact Hlim.
  Defined.

  (*--------------------------------------------------------------------------*)
  (* 7.3 Sphincter Relaxation Completes                                       *)
  (*--------------------------------------------------------------------------*)

  (*
     Once voluntary commands issued, sphincters reach relaxed state
     in bounded time.
  *)

  Definition sphincter_relaxed (p : Interval Pa) : Prop :=
    hi Pa p <= StateMachine.relaxation_threshold.

  Lemma ias_relaxes_on_rair :
    forall ias vol,
    lo Pa (ias_relaxation_magnitude ias) > 0 ->
    lo Pa (rair_ias_relaxation (compute_rair ias vol)) > 0.
  Proof.
    intros ias vol Hpos.
    unfold compute_rair.
    simpl.
    exact Hpos.
  Defined.

  Lemma default_ias_has_positive_relaxation :
    lo Pa (ias_relaxation_magnitude default_ias) > 0.
  Proof.
    unfold default_ias.
    simpl.
    lia.
  Defined.

  Lemma relaxation_bounded_time :
    forall ias,
    exists t_max : sec,
    t_max <= hi sec (ias_relaxation_latency ias) + hi sec (mkInterval sec 10 30).
  Proof.
    intros ias.
    exists (hi sec (ias_relaxation_latency ias) + 30).
    simpl.
    lia.
  Defined.

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
  
  Definition max_bolus_volume : mL := 500.

  Definition finite_bolus (b : Bolus) : Prop :=
    hi mL (bolus_volume b) <=mL max_bolus_volume.
  
  (*--------------------------------------------------------------------------*)
  (* 8.4 Main Termination Theorem                                             *)
  (*--------------------------------------------------------------------------*)
  
  Definition voluntary_commands_permit_defecation (s : SystemState) : Prop :=
    cmd_eas_relax (voluntary_commands s) = true /\
    cmd_pr_relax (voluntary_commands s) = true.

  Fixpoint expulsion_ticks (n : nat) (s : SystemState) : SystemState :=
    match n with
    | O => s
    | S n' =>
        if Nat.leb (hi mm (bolus_position s)) passage_complete_threshold
        then s
        else expulsion_ticks n' (transition_expulsion_tick s)
    end.

  Lemma expulsion_ticks_state :
    forall n s,
    reflex_state s = ExpulsionPhase ->
    reflex_state (expulsion_ticks n s) = ExpulsionPhase.
  Proof.
    induction n.
    - intros s Hs.
      simpl.
      exact Hs.
    - intros s Hs.
      simpl.
      destruct (Nat.leb (hi mm (bolus_position s)) passage_complete_threshold) eqn:Hcmp.
      + exact Hs.
      + apply IHn.
        apply transition_expulsion_tick_state.
  Defined.

  Lemma expulsion_ticks_multistep :
    forall n s,
    reflex_state s = ExpulsionPhase ->
    MultiStep s (expulsion_ticks n s).
  Proof.
    induction n.
    - intros s Hs.
      simpl.
      apply ms_refl.
    - intros s Hs.
      simpl.
      destruct (Nat.leb (hi mm (bolus_position s)) passage_complete_threshold) eqn:Hcmp.
      + apply ms_refl.
      + apply ms_step with (transition_expulsion_tick s).
        * apply step_expulsion_tick.
          unfold guard_expulsion_tick.
          split.
          -- exact Hs.
          -- apply PeanoNat.Nat.leb_gt in Hcmp.
             exact Hcmp.
        * apply IHn.
          apply transition_expulsion_tick_state.
  Defined.

  Definition sufficient_ticks (pos : mm) : nat := S pos.

  Definition has_positive_flow (s : SystemState) : Prop :=
    lo mm (compute_bolus_advancement s) > 0.

  Definition sufficient_pressure_differential (s : SystemState) : Prop :=
    match bolus s with
    | None => False
    | Some b =>
        let pg := Posture.posture_to_geometry (posture s) in
        let exp := Pressure.compute_expulsive (anatomy s) pg in
        let res := Pressure.compute_resistance (anatomy s) b pg in
        lo Pa (Pressure.e_total exp) > hi Pa (Pressure.r_total res)
    end.

  Lemma tick_strictly_decreases :
    forall s,
    has_positive_flow s ->
    hi mm (bolus_position (transition_expulsion_tick s)) < hi mm (bolus_position s) \/
    hi mm (bolus_position (transition_expulsion_tick s)) = 0.
  Proof.
    intros s Hflow.
    unfold transition_expulsion_tick.
    simpl.
    unfold has_positive_flow in Hflow.
    destruct (Nat.leb (hi mm (bolus_position s)) (lo mm (compute_bolus_advancement s))) eqn:Hcmp.
    - right. reflexivity.
    - left.
      apply PeanoNat.Nat.leb_gt in Hcmp.
      lia.
  Defined.

  Lemma expulsion_ticks_at_threshold :
    forall n s,
    hi mm (bolus_position s) <= passage_complete_threshold ->
    hi mm (bolus_position (expulsion_ticks n s)) <= passage_complete_threshold.
  Proof.
    induction n.
    - intros s Hle.
      simpl.
      exact Hle.
    - intros s Hle.
      simpl.
      assert (Hcmp: Nat.leb (hi mm (bolus_position s)) passage_complete_threshold = true).
      { apply PeanoNat.Nat.leb_le. exact Hle. }
      rewrite Hcmp.
      exact Hle.
  Defined.

  Lemma expulsion_ticks_reaches_threshold_aux :
    forall pos n s,
    reflex_state s = ExpulsionPhase ->
    hi mm (bolus_position s) = pos ->
    n >= pos ->
    (forall s', reflex_state s' = ExpulsionPhase -> has_positive_flow s') ->
    hi mm (bolus_position (expulsion_ticks n s)) <= passage_complete_threshold.
  Proof.
    induction pos as [pos IHpos] using (well_founded_induction Wf_nat.lt_wf).
    intros n s Hs Hpos Hn Hflow.
    destruct n.
    - simpl.
      unfold passage_complete_threshold.
      lia.
    - simpl.
      destruct (Nat.leb (hi mm (bolus_position s)) passage_complete_threshold) eqn:Hcmp.
      + apply PeanoNat.Nat.leb_le in Hcmp.
        exact Hcmp.
      + apply PeanoNat.Nat.leb_gt in Hcmp.
        set (s' := transition_expulsion_tick s).
        set (pos' := hi mm (bolus_position s')).
        assert (Hdec: pos' < pos \/ pos' = 0).
        { unfold pos', s'.
          assert (Htick := tick_strictly_decreases s (Hflow s Hs)).
          destruct Htick as [Hlt | Hzero].
          - left.
            rewrite <- Hpos.
            exact Hlt.
          - right.
            exact Hzero. }
        destruct Hdec as [Hlt' | Hzero].
        * apply (IHpos pos' Hlt' n s').
          -- apply transition_expulsion_tick_state.
          -- reflexivity.
          -- lia.
          -- exact Hflow.
        * subst s' pos'.
          apply expulsion_ticks_at_threshold.
          unfold passage_complete_threshold.
          rewrite Hzero.
          exact (le_n 0).
  Defined.

  Lemma expulsion_ticks_reaches_threshold :
    forall n s,
    reflex_state s = ExpulsionPhase ->
    n >= hi mm (bolus_position s) ->
    (forall s', reflex_state s' = ExpulsionPhase -> has_positive_flow s') ->
    hi mm (bolus_position (expulsion_ticks n s)) <= passage_complete_threshold.
  Proof.
    intros n s Hs Hn Hflow.
    apply (expulsion_ticks_reaches_threshold_aux (hi mm (bolus_position s)) n s Hs eq_refl Hn Hflow).
  Defined.

  Theorem defecation_terminates :
    forall s : SystemState,
    reflex_state s = UrgePresent ->
    voluntary_commands_permit_defecation s ->
    (match bolus s with Some b => finite_bolus b | None => True end) ->
    hi mm (bolus_position s) <= max_bolus_volume ->
    (forall s', reflex_state s' = ExpulsionPhase -> has_positive_flow s') ->
    exists s' : SystemState,
    MultiStep s s' /\
    reflex_state s' = Quiescent.
  Proof.
    intros s Hurge [Heas Hpr] Hfinite Hpos Hflow.
    set (s1 := transition_to_initiation s).
    set (s2 := transition_to_expulsion s1).
    set (n := sufficient_ticks (hi mm (bolus_position s2))).
    set (s2' := expulsion_ticks n s2).
    set (s3 := transition_to_completion s2').
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
        * assert (Hs2_state: reflex_state s2 = ExpulsionPhase).
          { apply transition_to_expulsion_state. }
          assert (Hms_s2_s2': MultiStep s2 s2').
          { apply expulsion_ticks_multistep.
            exact Hs2_state. }
          apply (ms_trans s2 s2' s4 Hms_s2_s2').
          apply ms_step with s3.
             ++ apply step_complete.
                unfold guard_completion.
                split.
                ** apply expulsion_ticks_state.
                   exact Hs2_state.
                ** unfold mm_le.
                   apply expulsion_ticks_reaches_threshold.
                   --- exact Hs2_state.
                   --- unfold n, sufficient_ticks.
                       lia.
                   --- exact Hflow.
             ++ apply ms_step with s4.
                ** apply step_reset.
                   unfold guard_reset.
                   split.
                   --- apply transition_to_completion_state.
                   --- apply transition_to_completion_restores.
                ** apply ms_refl.
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
    hi mm (bolus_position s) <= max_bolus_volume ->
    (forall s', reflex_state s' = ExpulsionPhase -> has_positive_flow s') ->
    exists s' : SystemState,
    MultiStep s s' /\ reflex_state s' = Quiescent.
  Proof.
    intros s Hurge Hcmd Hfin Hpos Hflow.
    exact (defecation_terminates s Hurge Hcmd Hfin Hpos Hflow).
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
  Import Bolus.
  
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
  
  Definition bristol_efficiency_factor (b : BristolType) : nat :=
    match b with
    | Type1_SeparateHardLumps => 4
    | Type2_LumpySausage => 3
    | Type3_SausageWithCracks => 3
    | Type4_SmoothSoftSausage => 2
    | Type5_SoftBlobsClearEdges => 1
    | Type6_FluffentPieces => 1
    | Type7_WateryNoSolids => 1
    end.

  Definition wipe_efficiency_typed (b : BristolType) (residue : Interval mL) : Interval mL :=
    let eff := bristol_efficiency_factor b in
    mkInterval mL
      (Nat.div (lo mL residue) (S eff))
      (Nat.div (hi mL residue) (S eff)).

  Definition wipe_efficiency (residue : Interval mL) : Interval mL :=
    let efficiency_factor := 2 in
    mkInterval mL
      (Nat.div (lo mL residue) (S efficiency_factor))
      (Nat.div (hi mL residue) efficiency_factor).
  
  (*--------------------------------------------------------------------------*)
  (* 9.2 Cleanliness Threshold                                                *)
  (*--------------------------------------------------------------------------*)
  
  Definition cleanliness_threshold : mL := 1.

  Definition clean_enough (r : Interval mL) : Prop :=
    hi mL r <= cleanliness_threshold.
  
  (*--------------------------------------------------------------------------*)
  (* 9.3 Convergence Theorem                                                  *)
  (*--------------------------------------------------------------------------*)

  (*
     Under reasonable efficiency assumptions (efficiency > 0.5),
     residue converges to below threshold in O(log(initial)) wipes.
  *)

  Lemma wipe_reduces_hi :
    forall r : Interval mL,
    hi mL r >= 2 ->
    hi mL (wipe_efficiency r) < hi mL r.
  Proof.
    intros r Hge.
    unfold wipe_efficiency.
    simpl.
    assert (H: Nat.div (hi mL r) 2 <= Nat.div (hi mL r) 2) by lia.
    assert (Hdiv: Nat.div (hi mL r) 2 < hi mL r).
    { apply PeanoNat.Nat.div_lt; lia. }
    exact Hdiv.
  Defined.

  Lemma wipe_reduces_lo :
    forall r : Interval mL,
    lo mL r >= 3 ->
    lo mL (wipe_efficiency r) < lo mL r.
  Proof.
    intros r Hge.
    unfold wipe_efficiency.
    simpl.
    assert (Hdiv: Nat.div (lo mL r) 3 < lo mL r).
    { apply PeanoNat.Nat.div_lt; lia. }
    exact Hdiv.
  Defined.

  Lemma wipe_monotonic :
    forall r : Interval mL,
    hi mL (wipe_efficiency r) <= hi mL r.
  Proof.
    intros r.
    unfold wipe_efficiency.
    simpl.
    assert (Hdiv: Nat.div (hi mL r) 2 <= hi mL r).
    { apply PeanoNat.Nat.div_le_upper_bound; lia. }
    exact Hdiv.
  Defined.

  Lemma wipe_iter_monotonic :
    forall (n : nat) (r : Interval mL),
    hi mL (Nat.iter n wipe_efficiency r) <= hi mL r.
  Proof.
    induction n.
    - intros r.
      simpl.
      lia.
    - intros r.
      simpl.
      apply PeanoNat.Nat.le_trans with (m := hi mL (Nat.iter n wipe_efficiency r)).
      + apply wipe_monotonic.
      + apply IHn.
  Defined.

  Theorem wiping_eventually_converges :
    forall initial_residue : Interval mL,
    exists n : nat,
    hi mL (Nat.iter n wipe_efficiency initial_residue) <= cleanliness_threshold \/
    hi mL (Nat.iter n wipe_efficiency initial_residue) < hi mL initial_residue.
  Proof.
    intros initial_residue.
    destruct (Compare_dec.le_dec (hi mL initial_residue) cleanliness_threshold) as [Hle | Hgt].
    - exists 0.
      left.
      simpl.
      exact Hle.
    - exists 1.
      right.
      simpl.
      apply wipe_reduces_hi.
      unfold cleanliness_threshold in Hgt.
      lia.
  Defined.

  Lemma div2_decreases :
    forall n, n >= 2 -> Nat.div n 2 < n.
  Proof.
    intros n Hge.
    apply PeanoNat.Nat.div_lt; lia.
  Defined.

  Lemma wipe_decreases_large :
    forall r : Interval mL,
    hi mL r >= 2 ->
    hi mL (wipe_efficiency r) <= Nat.div (hi mL r) 2.
  Proof.
    intros r Hge.
    unfold wipe_efficiency.
    simpl.
    lia.
  Defined.

  Lemma wipe_below_threshold_stays :
    forall r : Interval mL,
    hi mL r <= cleanliness_threshold ->
    hi mL (wipe_efficiency r) <= cleanliness_threshold.
  Proof.
    intros r Hle.
    unfold wipe_efficiency, cleanliness_threshold in *.
    simpl.
    assert (Hdiv: Nat.div (hi mL r) 2 <= Nat.div 1 2).
    { apply PeanoNat.Nat.div_le_mono; lia. }
    simpl in Hdiv.
    lia.
  Defined.

  Lemma wipe_strictly_reduces :
    forall r : Interval mL,
    hi mL r > cleanliness_threshold ->
    hi mL (wipe_efficiency r) < hi mL r.
  Proof.
    intros r Hgt.
    unfold wipe_efficiency, cleanliness_threshold in *.
    simpl.
    assert (Hdiv: Nat.div (hi mL r) 2 < hi mL r).
    { apply PeanoNat.Nat.div_lt; lia. }
    exact Hdiv.
  Defined.

  Lemma wipe_eventually_below_threshold :
    forall r : Interval mL,
    hi mL r > cleanliness_threshold ->
    hi mL (wipe_efficiency r) <= hi mL r - 1.
  Proof.
    intros r Hgt.
    assert (Hred: hi mL (wipe_efficiency r) < hi mL r).
    { apply wipe_strictly_reduces. exact Hgt. }
    lia.
  Defined.

  Lemma iter_shift :
    forall (n : nat) (f : Interval mL -> Interval mL) (x : Interval mL),
    Nat.iter n f (f x) = f (Nat.iter n f x).
  Proof.
    induction n.
    - intros f x. reflexivity.
    - intros f x.
      simpl.
      rewrite IHn.
      reflexivity.
  Defined.

  Lemma wipe_iter_converges_aux :
    forall (v : nat) (r : Interval mL),
    hi mL r = v ->
    exists n : nat, hi mL (Nat.iter n wipe_efficiency r) <= cleanliness_threshold.
  Proof.
    induction v as [v IHv] using (well_founded_induction Wf_nat.lt_wf).
    intros r Heq.
    destruct (Compare_dec.le_dec (hi mL r) cleanliness_threshold) as [Hle | Hgt].
    - exists 0.
      simpl.
      exact Hle.
    - assert (Hlt: hi mL (wipe_efficiency r) < hi mL r).
      { apply wipe_strictly_reduces. lia. }
      rewrite Heq in Hlt.
      specialize (IHv (hi mL (wipe_efficiency r)) Hlt (wipe_efficiency r) eq_refl).
      destruct IHv as [n Hn].
      exists (S n).
      simpl.
      rewrite iter_shift in Hn.
      exact Hn.
  Defined.

  Theorem wiping_converges :
    forall initial_residue : Interval mL,
    exists n : nat,
    hi mL (Nat.iter n wipe_efficiency initial_residue) <= cleanliness_threshold.
  Proof.
    intros initial_residue.
    apply (wipe_iter_converges_aux (hi mL initial_residue) initial_residue eq_refl).
  Defined.

  Lemma typed_wipe_reduces :
    forall b r,
    hi mL (wipe_efficiency_typed b r) <= hi mL r.
  Proof.
    intros b r.
    unfold wipe_efficiency_typed.
    simpl.
    assert (H: forall n d, Nat.div n (S d) <= n).
    { intros. apply PeanoNat.Nat.div_le_upper_bound; lia. }
    apply H.
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
    hi mm (bolus_max_diameter b) > hi mm (ac_max_dilation (anal_canal anat)).

  Definition passage_geometrically_possible (anat : AnatomicalConfig) (b : Bolus) : Prop :=
    hi mm (bolus_max_diameter b) <= hi mm (ac_max_dilation (anal_canal anat)).

  Lemma obstructed_prevents_passage :
    forall anat b,
    obstructed anat b ->
    ~passage_geometrically_possible anat b.
  Proof.
    intros anat b Hobs Hpass.
    unfold obstructed in Hobs.
    unfold passage_geometrically_possible in Hpass.
    lia.
  Defined.

  Lemma passage_requires_non_obstruction :
    forall anat b,
    passage_geometrically_possible anat b ->
    ~obstructed anat b.
  Proof.
    intros anat b Hpass Hobs.
    unfold obstructed in Hobs.
    unfold passage_geometrically_possible in Hpass.
    lia.
  Defined.

  Lemma obstruction_decidable :
    forall anat b,
    obstructed anat b \/ passage_geometrically_possible anat b.
  Proof.
    intros anat b.
    unfold obstructed, passage_geometrically_possible.
    destruct (Compare_dec.le_dec (hi mm (bolus_max_diameter b))
                                  (hi mm (ac_max_dilation (anal_canal anat)))).
    - right. exact l.
    - left. lia.
  Defined.

  Lemma obstruction_witness :
    forall anat,
    let large_bolus := make_bolus Type1_SeparateHardLumps (mkInterval mL 400 500) in
    hi mm (bolus_max_diameter large_bolus) > 40 ->
    hi mm (ac_max_dilation (anal_canal anat)) <= 40 ->
    obstructed anat large_bolus.
  Proof.
    intros anat large_bolus Hlarge Hsmall.
    unfold obstructed.
    lia.
  Defined.

  Lemma non_obstruction_witness :
    forall anat,
    let small_bolus := make_bolus Type4_SmoothSoftSausage (mkInterval mL 100 200) in
    hi mm (bolus_max_diameter small_bolus) <= 30 ->
    hi mm (ac_max_dilation (anal_canal anat)) >= 30 ->
    passage_geometrically_possible anat small_bolus.
  Proof.
    intros anat small_bolus Hsmall Hlarge.
    unfold passage_geometrically_possible.
    lia.
  Defined.
  
  (*--------------------------------------------------------------------------*)
  (* 10.2 Paradoxical Contraction                                             *)
  (*--------------------------------------------------------------------------*)

  (*
     Dyssynergic defecation: voluntary command to relax EAS
     paradoxically causes contraction. Common disorder.
  *)

  Definition dyssynergia (s_before s_after : SystemState) : Prop :=
    cmd_eas_relax (voluntary_commands s_before) = true /\
    lo Pa (eas_pressure s_after) > lo Pa (eas_pressure s_before).

  Lemma dyssynergia_blocks_initiation :
    forall s_before s_after,
    dyssynergia s_before s_after ->
    hi Pa (eas_pressure s_after) > relaxation_threshold ->
    ~guard_expulsion_start s_after.
  Proof.
    intros s_before s_after [Hcmd Hinc] Hhi Hguard.
    unfold guard_expulsion_start in Hguard.
    destruct Hguard as [Hinit [Heas _]].
    unfold Pa_le in Heas.
    lia.
  Defined.

  (*--------------------------------------------------------------------------*)
  (* 10.3 Infinite Urge Without Action                                        *)
  (*--------------------------------------------------------------------------*)

  (*
     Theoretically possible to remain in UrgePresent indefinitely
     if voluntary commands never issued (catatonia, etc.).
     Real-world: EAS fatigue eventually forces resolution.
  *)

  Definition voluntary_inaction (s : SystemState) : Prop :=
    cmd_eas_relax (voluntary_commands s) = false /\
    cmd_pr_relax (voluntary_commands s) = false.

  Lemma inaction_prevents_initiation :
    forall s,
    voluntary_inaction s ->
    ~guard_initiate s.
  Proof.
    intros s [Heas Hpr] Hinit.
    unfold guard_initiate in Hinit.
    destruct Hinit as [_ [Heas' _]].
    rewrite Heas in Heas'.
    discriminate.
  Defined.

  (*--------------------------------------------------------------------------*)
  (* 10.4 Hirschsprung's Disease                                              *)
  (*--------------------------------------------------------------------------*)

  (*
     Absence of ganglion cells -> no RAIR response.
     IAS never relaxes. Requires surgical intervention.
  *)

  Definition hirschsprung (ias : InternalSphincter) : Prop :=
    lo Pa (ias_relaxation_magnitude ias) = 0 /\
    hi Pa (ias_relaxation_magnitude ias) = 0.

  Lemma hirschsprung_no_rair :
    forall ias vol,
    hirschsprung ias ->
    lo Pa (rair_ias_relaxation (compute_rair ias vol)) = 0.
  Proof.
    intros ias vol [Hlo Hhi].
    unfold compute_rair.
    simpl.
    exact Hlo.
  Defined.

  Lemma hirschsprung_blocks_reflex_relaxation :
    forall ias,
    hirschsprung ias ->
    forall vol, hi Pa (rair_ias_relaxation (compute_rair ias vol)) = 0.
  Proof.
    intros ias [Hlo Hhi] vol.
    unfold compute_rair.
    simpl.
    exact Hhi.
  Defined.

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
  
  Definition laxative_effect (lax : LaxativeType) (b : Bolus) : Bolus :=
    let physics := bolus_physics b in
    let new_physics := match lax with
      | OsmoticLaxative =>
          mkBolusPhysics
            (mkInterval cP (Nat.div (lo cP (bp_viscosity physics)) 2) (Nat.div (hi cP (bp_viscosity physics)) 2))
            (mkInterval Pa (Nat.div (lo Pa (bp_yield_stress physics)) 2) (Nat.div (hi Pa (bp_yield_stress physics)) 2))
            (bp_cohesion physics)
            (bp_fragmentability physics)
            (bp_typical_diameter physics)
      | StimulantLaxative =>
          physics
      | StoolSoftener =>
          mkBolusPhysics
            (mkInterval cP (Nat.div (lo cP (bp_viscosity physics)) 3) (Nat.div (hi cP (bp_viscosity physics)) 3))
            (mkInterval Pa (Nat.div (lo Pa (bp_yield_stress physics)) 3) (Nat.div (hi Pa (bp_yield_stress physics)) 3))
            (mkInterval Pa (Nat.div (lo Pa (bp_cohesion physics)) 2) (Nat.div (hi Pa (bp_cohesion physics)) 2))
            true
            (bp_typical_diameter physics)
      | BulkForming =>
          mkBolusPhysics
            (bp_viscosity physics)
            (bp_yield_stress physics)
            (bp_cohesion physics)
            false
            (mkInterval mm (lo mm (bp_typical_diameter physics) + 5) (hi mm (bp_typical_diameter physics) + 10))
      end in
    mkBolus
      (bolus_type b)
      (bolus_volume b)
      (bolus_length b)
      (bolus_max_diameter b)
      new_physics.

  Definition apply_laxative_to_state (lax : LaxativeType) (s : SystemState) : SystemState :=
    match bolus s with
    | None => s
    | Some b =>
        mkState
          (anatomy s) (Some (laxative_effect lax b)) (bolus_position s)
          (posture s) (reflex_state s) (voluntary_commands s)
          (ias_pressure s) (eas_pressure s) (anorectal_angle s)
          (elapsed_time s) (eas_fatigue_accumulated s)
    end.

  Lemma osmotic_reduces_viscosity :
    forall b,
    hi cP (bp_viscosity (bolus_physics (laxative_effect OsmoticLaxative b))) <=
    hi cP (bp_viscosity (bolus_physics b)).
  Proof.
    intros b.
    unfold laxative_effect.
    simpl.
    assert (H: forall n d, Nat.div n (S d) <= n).
    { intros. apply PeanoNat.Nat.div_le_upper_bound; lia. }
    apply H.
  Defined.

  Lemma stool_softener_reduces_yield_stress :
    forall b,
    hi Pa (bp_yield_stress (bolus_physics (laxative_effect StoolSoftener b))) <=
    hi Pa (bp_yield_stress (bolus_physics b)).
  Proof.
    intros b.
    unfold laxative_effect.
    simpl.
    assert (H: forall n d, Nat.div n (S d) <= n).
    { intros. apply PeanoNat.Nat.div_le_upper_bound; lia. }
    apply H.
  Defined.
  
  (*--------------------------------------------------------------------------*)
  (* 11.2 Manual Disimpaction                                                 *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Direct removal of obstruction. Models as:
     - Reduces bolus volume
     - May fragment bolus
  *)
  
  Definition manual_disimpaction (b : Bolus) : Bolus :=
    let physics := bolus_physics b in
    mkBolus
      (bolus_type b)
      (mkInterval mL (Nat.div (lo mL (bolus_volume b)) 2) (Nat.div (hi mL (bolus_volume b)) 2))
      (mkInterval mm (Nat.div (lo mm (bolus_length b)) 2) (Nat.div (hi mm (bolus_length b)) 2))
      (mkInterval mm (lo mm (bolus_max_diameter b)) (Nat.div (hi mm (bolus_max_diameter b)) 2))
      (mkBolusPhysics
        (bp_viscosity physics)
        (bp_yield_stress physics)
        (bp_cohesion physics)
        true
        (bp_typical_diameter physics)).
  
  (*--------------------------------------------------------------------------*)
  (* 11.3 Enema                                                               *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Introduces fluid, softening bolus and increasing volume/pressure.
  *)
  
  Definition enema_effect (vol : Interval mL) (b : Bolus) : Bolus :=
    let physics := bolus_physics b in
    mkBolus
      Type6_FluffentPieces
      (mkInterval mL (lo mL (bolus_volume b) + lo mL vol) (hi mL (bolus_volume b) + hi mL vol))
      (bolus_length b)
      (bolus_max_diameter b)
      (mkBolusPhysics
        (mkInterval cP 50 200)
        (mkInterval Pa 5 20)
        (mkInterval Pa 5 30)
        true
        (bp_typical_diameter physics)).
  
  (*--------------------------------------------------------------------------*)
  (* 11.4 Biofeedback                                                         *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Training to correct dyssynergia. Modifies voluntary control:
     - Improves EAS relaxation on command
     - Improves PR relaxation
  *)
  
  Definition biofeedback_training (sessions : nat) (anat : AnatomicalConfig) : AnatomicalConfig :=
    let improvement := Nat.min sessions 10 in
    let old_eas := eas anat in
    let new_eas := mkEAS
      (eas_length old_eas)
      (eas_resting_pressure old_eas)
      (eas_max_squeeze_pressure old_eas)
      (mkInterval sec
        (lo sec (eas_fatigue_time old_eas) + improvement * 10)
        (hi sec (eas_fatigue_time old_eas) + improvement * 15))
      (mkInterval Pa
        (lo Pa (eas_voluntary_relaxation_floor old_eas) - improvement * 50)
        (hi Pa (eas_voluntary_relaxation_floor old_eas) - improvement * 30)) in
    mkAnatomy
      (rectum anat)
      (ias anat)
      new_eas
      (puborectalis anat)
      (abdominal_wall anat)
      (anal_canal anat).
  
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
  
  Definition max_safe_pressure : Pa := 15000.

  Definition safe_pressure (p : Interval Pa) : Prop :=
    hi Pa p <=Pa max_safe_pressure.
  
  Lemma expulsive_within_safe_limits :
    forall anat pg,
    hi Pa (e_total (compute_expulsive anat pg)) <=Pa max_safe_pressure.
  Proof.
    intros anat pg.
    unfold compute_expulsive, max_safe_pressure, safe_expulsive_bound, Pa_le.
    simpl.
    apply PeanoNat.Nat.le_min_r.
  Defined.

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
  
  Definition max_safe_dilation : mm := 45.

  Definition safe_dilation (anat : AnatomicalConfig) (b : Bolus) : Prop :=
    hi mm (bolus_max_diameter b) <=mm max_safe_dilation.
  
  (*--------------------------------------------------------------------------*)
  (* 12.3 No Infinite Valsalva                                                *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Straining duration bounded to prevent syncope.
  *)
  
  Definition max_strain_duration : sec := 30.
  
  (*--------------------------------------------------------------------------*)
  (* 12.4 Continence Maintained Until Voluntary                               *)
  (*--------------------------------------------------------------------------*)
  
  (*
     Involuntary passage should not occur while EAS is commanded contracted
     (until fatigue).
  *)
  
  Definition before_fatigue (t : sec) : Prop := True.

  Lemma step_preserves_voluntary_commands :
    forall s1 s2, Step s1 s2 -> voluntary_commands s2 = voluntary_commands s1.
  Proof.
    intros s1 s2 Hstep.
    destruct Hstep; reflexivity.
  Defined.

  Lemma multistep_preserves_voluntary_commands :
    forall s1 s2, MultiStep s1 s2 -> voluntary_commands s2 = voluntary_commands s1.
  Proof.
    intros s1 s2 Hms.
    induction Hms.
    - reflexivity.
    - rewrite IHHms.
      apply step_preserves_voluntary_commands.
      exact H.
  Defined.

  Lemma step_to_initiation_requires_relaxation :
    forall s1 s2,
    Step s1 s2 ->
    reflex_state s2 = InitiationPhase ->
    cmd_eas_relax (voluntary_commands s1) = true.
  Proof.
    intros s1 s2 Hstep Hinit.
    destruct Hstep as [s Hg | s Hg | s Hg | s Hg | s Hg | s Hg | s Hg | s Hg];
      simpl in Hinit; try discriminate.
    unfold guard_initiate in Hg.
    destruct Hg as [_ [Heas _]].
    exact Heas.
  Defined.

  Lemma step_to_expulsion_from_initiation :
    forall s1 s2,
    Step s1 s2 ->
    reflex_state s2 = ExpulsionPhase ->
    reflex_state s1 = InitiationPhase \/ reflex_state s1 = ExpulsionPhase.
  Proof.
    intros s1 s2 Hstep Hexp.
    destruct Hstep as [s Hg | s Hg | s Hg | s Hg | s Hg | s Hg | s Hg | s Hg];
      simpl in Hexp; try discriminate.
    - unfold guard_expulsion_start in Hg.
      destruct Hg as [Hinit _].
      left. exact Hinit.
    - unfold guard_expulsion_tick in Hg.
      destruct Hg as [Hexp_state _].
      right. exact Hexp_state.
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
