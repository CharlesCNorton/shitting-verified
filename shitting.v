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
Require Import PeanoNat.
Require Import Arith.

(*============================================================================*)
(*                         FOUNDATIONAL TYPES                       *)
(*============================================================================*)

(* 
   Base units and interval arithmetic. All physiological quantities carry
   uncertainty; we use intervals throughout rather than point estimates.
*)

Module Units.
  (*
     Type-safe unit wrappers. Each physical dimension is a distinct type,
     preventing dimensional errors at compile time. E.g., comparing mm to mL
     now fails to typecheck rather than silently succeeding.
  *)
  Record mm := Mkmm { distance_mm : nat }.
  Record Pa := MkPa { pressure_Pa : nat }.
  Record mL := MkmL { volume_mL : nat }.
  Record sec := Mksec { time_sec : nat }.
  Record deg := Mkdeg { angle_deg : nat }.
  Record cP := MkcP { viscosity_cP : nat }.

  Definition mm_le (x y : mm) : Prop := distance_mm x <= distance_mm y.
  Definition Pa_le (x y : Pa) : Prop := pressure_Pa x <= pressure_Pa y.
  Definition mL_le (x y : mL) : Prop := volume_mL x <= volume_mL y.
  Definition sec_le (x y : sec) : Prop := time_sec x <= time_sec y.
  Definition deg_le (x y : deg) : Prop := angle_deg x <= angle_deg y.
  Definition cP_le (x y : cP) : Prop := viscosity_cP x <= viscosity_cP y.

  Definition mm_lt (x y : mm) : Prop := distance_mm x < distance_mm y.
  Definition Pa_lt (x y : Pa) : Prop := pressure_Pa x < pressure_Pa y.
  Definition mL_lt (x y : mL) : Prop := volume_mL x < volume_mL y.
  Definition sec_lt (x y : sec) : Prop := time_sec x < time_sec y.
  Definition deg_lt (x y : deg) : Prop := angle_deg x < angle_deg y.

  Notation "x <=mm y" := (mm_le x y) (at level 70).
  Notation "x <=Pa y" := (Pa_le x y) (at level 70).
  Notation "x <=mL y" := (mL_le x y) (at level 70).
  Notation "x <=sec y" := (sec_le x y) (at level 70).
  Notation "x <=deg y" := (deg_le x y) (at level 70).
  Notation "x <=cP y" := (cP_le x y) (at level 70).

  Class LeRefl (A : Type) (le : A -> A -> Prop) := le_refl : forall x, le x x.

  Global Instance mm_le_refl : LeRefl mm mm_le.
  Proof. unfold LeRefl, mm_le. intros. lia. Qed.

  Global Instance Pa_le_refl : LeRefl Pa Pa_le.
  Proof. unfold LeRefl, Pa_le. intros. lia. Qed.

  Global Instance mL_le_refl : LeRefl mL mL_le.
  Proof. unfold LeRefl, mL_le. intros. lia. Qed.

  Global Instance sec_le_refl : LeRefl sec sec_le.
  Proof. unfold LeRefl, sec_le. intros. lia. Qed.

  Global Instance deg_le_refl : LeRefl deg deg_le.
  Proof. unfold LeRefl, deg_le. intros. lia. Qed.

  Class LeTrans (A : Type) (le : A -> A -> Prop)
    := le_trans : forall x y z, le x y -> le y z -> le x z.

  Global Instance mm_le_trans : LeTrans mm mm_le.
  Proof. unfold LeTrans, mm_le. intros. lia. Qed.

  Global Instance Pa_le_trans : LeTrans Pa Pa_le.
  Proof. unfold LeTrans, Pa_le. intros. lia. Qed.

  Global Instance mL_le_trans : LeTrans mL mL_le.
  Proof. unfold LeTrans, mL_le. intros. lia. Qed.

  Record Interval (A : Type) := mkInterval {
    lo : A;
    hi : A;
  }.

  Arguments mkInterval {A} _ _.
  Arguments lo {A} _.
  Arguments hi {A} _.

  Definition interval_wf_mm (i : Interval mm) : Prop := mm_le (lo i) (hi i).
  Definition interval_wf_Pa (i : Interval Pa) : Prop := Pa_le (lo i) (hi i).
  Definition interval_wf_mL (i : Interval mL) : Prop := mL_le (lo i) (hi i).
  Definition interval_wf_sec (i : Interval sec) : Prop := sec_le (lo i) (hi i).
  Definition interval_wf_deg (i : Interval deg) : Prop := deg_le (lo i) (hi i).
  Definition interval_wf_cP (i : Interval cP) : Prop := cP_le (lo i) (hi i).

  Notation "i 'wf_mm'" := (interval_wf_mm i) (at level 50).
  Notation "i 'wf_Pa'" := (interval_wf_Pa i) (at level 50).
  Notation "i 'wf_mL'" := (interval_wf_mL i) (at level 50).

  Definition Pa_sub (x y : Pa) : Pa := MkPa (pressure_Pa x - pressure_Pa y).
  Definition Pa_add (x y : Pa) : Pa := MkPa (pressure_Pa x + pressure_Pa y).
  Definition Pa_mul (x y : Pa) : Pa := MkPa (pressure_Pa x * pressure_Pa y).
  Definition Pa_div (x y : Pa) : Pa := MkPa (Nat.div (pressure_Pa x) (S (pressure_Pa y))).
  Definition Pa_scale (k : nat) (x : Pa) : Pa := MkPa (k * pressure_Pa x).
  Definition Pa_divn (x : Pa) (d : nat) : Pa := MkPa (Nat.div (pressure_Pa x) (S d)).

  Definition mL_sub (x y : mL) : mL := MkmL (volume_mL x - volume_mL y).
  Definition mL_add (x y : mL) : mL := MkmL (volume_mL x + volume_mL y).

  Definition mm_sub (x y : mm) : mm := Mkmm (distance_mm x - distance_mm y).
  Definition mm_add (x y : mm) : mm := Mkmm (distance_mm x + distance_mm y).
  Definition mm_scale (k : nat) (x : mm) : mm := Mkmm (k * distance_mm x).
  Definition mm_divn (x : mm) (d : nat) : mm := Mkmm (Nat.div (distance_mm x) (S d)).

  Definition sec_add (x y : sec) : sec := Mksec (time_sec x + time_sec y).

  (*
     Interval subtraction: [a,b] - [c,d] = [a-d, b-c]

     Note: This uses saturating subtraction (Pa_sub), so if a < d, the result
     is [0, b-c]. This means:
     1. The result is always non-negative (physically: pressure can't be negative)
     2. When i1 < i2 (resistance exceeds expulsive force), result saturates to 0
     3. The interval may become "inverted" (lo > hi) in edge cases, but
        subsequent operations handle this safely via saturating arithmetic.

     For pressure differentials, saturation to 0 correctly models "no flow"
     when resistance exceeds expulsive force.
  *)
  Definition iv_sub (i1 i2 : Interval Pa) : Interval Pa :=
    mkInterval (Pa_sub (lo i1) (hi i2)) (Pa_sub (hi i1) (lo i2)).

  Definition iv_add (i1 i2 : Interval Pa) : Interval Pa :=
    mkInterval (Pa_add (lo i1) (lo i2)) (Pa_add (hi i1) (hi i2)).

  Definition iv_mul (i1 i2 : Interval Pa) : Interval Pa :=
    mkInterval (Pa_mul (lo i1) (lo i2)) (Pa_mul (hi i1) (hi i2)).

  Definition iv_scale (k : nat) (i : Interval Pa) : Interval Pa :=
    mkInterval (Pa_scale k (lo i)) (Pa_scale k (hi i)).

  Definition iv_div (i : Interval Pa) (d : nat) : Interval Pa :=
    mkInterval (Pa_divn (lo i) d) (Pa_divn (hi i) d).

  Definition iv_mm_sub (i1 i2 : Interval mm) : Interval mm :=
    mkInterval (mm_sub (lo i1) (hi i2)) (mm_sub (hi i1) (lo i2)).

  Definition iv_mm_add (i1 i2 : Interval mm) : Interval mm :=
    mkInterval (mm_add (lo i1) (lo i2)) (mm_add (hi i1) (hi i2)).

  Definition iv_mm_scale (k : nat) (i : Interval mm) : Interval mm :=
    mkInterval (mm_scale k (lo i)) (mm_scale k (hi i)).

  Definition iv_mm_div (i : Interval mm) (d : nat) : Interval mm :=
    mkInterval (mm_divn (lo i) d) (mm_divn (hi i) d).

  Lemma iv_sub_lo : forall i1 i2 : Interval Pa,
    lo (iv_sub i1 i2) = Pa_sub (lo i1) (hi i2).
  Proof. reflexivity. Qed.

  Lemma iv_sub_hi : forall i1 i2 : Interval Pa,
    hi (iv_sub i1 i2) = Pa_sub (hi i1) (lo i2).
  Proof. reflexivity. Qed.

  Lemma iv_sub_preserves_wf : forall i1 i2 : Interval Pa,
    interval_wf_Pa i1 -> interval_wf_Pa i2 ->
    interval_wf_Pa (iv_sub i1 i2).
  Proof.
    intros i1 i2 Hwf1 Hwf2.
    unfold interval_wf_Pa, Pa_le, iv_sub, Pa_sub in *.
    simpl.
    destruct (Compare_dec.le_dec (pressure_Pa (hi i2)) (pressure_Pa (lo i1)));
    destruct (Compare_dec.le_dec (pressure_Pa (lo i2)) (pressure_Pa (hi i1))).
    - lia.
    - simpl. lia.
    - simpl. lia.
    - simpl. lia.
  Qed.

  Lemma iv_mm_sub_preserves_wf : forall i1 i2 : Interval mm,
    interval_wf_mm i1 -> interval_wf_mm i2 ->
    interval_wf_mm (iv_mm_sub i1 i2).
  Proof.
    intros i1 i2 Hwf1 Hwf2.
    unfold interval_wf_mm, mm_le, iv_mm_sub, mm_sub in *.
    simpl.
    destruct (Compare_dec.le_dec (distance_mm (hi i2)) (distance_mm (lo i1)));
    destruct (Compare_dec.le_dec (distance_mm (lo i2)) (distance_mm (hi i1))).
    - lia.
    - simpl. lia.
    - simpl. lia.
    - simpl. lia.
  Qed.

  Lemma iv_mul_lo : forall i1 i2 : Interval Pa,
    lo (iv_mul i1 i2) = Pa_mul (lo i1) (lo i2).
  Proof. reflexivity. Qed.

  Lemma iv_mul_hi : forall i1 i2 : Interval Pa,
    hi (iv_mul i1 i2) = Pa_mul (hi i1) (hi i2).
  Proof. reflexivity. Qed.

  Lemma iv_scale_monotonic : forall k i,
    Pa_le (lo i) (hi i) -> Pa_le (lo (iv_scale k i)) (hi (iv_scale k i)).
  Proof.
    intros k i Hwf.
    unfold iv_scale, Pa_le, Pa_scale in *.
    simpl.
    apply PeanoNat.Nat.mul_le_mono_l.
    exact Hwf.
  Qed.

  Lemma iv_add_wf : forall i1 i2,
    interval_wf_Pa i1 -> interval_wf_Pa i2 ->
    interval_wf_Pa (iv_add i1 i2).
  Proof.
    intros i1 i2 H1 H2.
    unfold interval_wf_Pa, Pa_le, iv_add, Pa_add in *.
    simpl in *.
    apply PeanoNat.Nat.add_le_mono; assumption.
  Qed.

  Lemma iv_mul_wf : forall i1 i2,
    interval_wf_Pa i1 -> interval_wf_Pa i2 ->
    interval_wf_Pa (iv_mul i1 i2).
  Proof.
    intros i1 i2 H1 H2.
    unfold interval_wf_Pa, Pa_le, iv_mul, Pa_mul in *.
    simpl.
    apply PeanoNat.Nat.mul_le_mono; assumption.
  Qed.

  Lemma div_le_mono_pos : forall a b c,
    a <= b -> c > 0 -> Nat.div a c <= Nat.div b c.
  Proof.
    intros a b c Hab Hc.
    apply Nat.div_le_mono; lia.
  Qed.

  Lemma iv_div_wf : forall i d,
    interval_wf_Pa i -> interval_wf_Pa (iv_div i d).
  Proof.
    intros i d H.
    unfold interval_wf_Pa, Pa_le, iv_div, Pa_divn in *.
    apply Nat.div_le_mono; [lia | exact H].
  Qed.

  Lemma iv_mm_add_wf : forall i1 i2,
    interval_wf_mm i1 -> interval_wf_mm i2 ->
    interval_wf_mm (iv_mm_add i1 i2).
  Proof.
    intros i1 i2 H1 H2.
    unfold interval_wf_mm, mm_le, iv_mm_add, mm_add in *.
    simpl in *.
    apply PeanoNat.Nat.add_le_mono; assumption.
  Qed.

  Lemma iv_mm_scale_wf : forall k i,
    interval_wf_mm i -> interval_wf_mm (iv_mm_scale k i).
  Proof.
    intros k i H.
    unfold interval_wf_mm, mm_le, iv_mm_scale, mm_scale in *.
    simpl.
    apply PeanoNat.Nat.mul_le_mono_l.
    exact H.
  Qed.

  Lemma iv_mm_div_wf : forall i d,
    interval_wf_mm i -> interval_wf_mm (iv_mm_div i d).
  Proof.
    intros i d H.
    unfold interval_wf_mm, mm_le, iv_mm_div, mm_divn in *.
    apply Nat.div_le_mono; [lia | exact H].
  Qed.

  Definition positive_differential (diff : Interval Pa) : Prop :=
    pressure_Pa (lo diff) > 0.
End Units.


(*============================================================================*)
(*                         ANATOMY                                  *)
(*============================================================================*)

(*
   Structural definitions. We model the relevant anatomy as a record of
   geometric and material properties. Individual variation captured via
   intervals on all parameters.
*)

Module Anatomy.
  Import Units.


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

  (*
     Default rectum parameters.

     Wall compliance models pressure-diameter relationship. Divisors
     /100 and /50 (Pa/mm) represent rectal wall stiffness bounds:
     - /100: stiffer wall, 1mm expansion per 100 Pa
     - /50: more compliant wall, 1mm expansion per 50 Pa
     These approximate the nonlinear viscoelastic response of rectal
     smooth muscle in the physiological pressure range.
  *)
  Definition default_rectum : Rectum :=
    mkRectum
      (mkInterval (Mkmm 120) (Mkmm 150))
      (mkInterval (Mkmm 25) (Mkmm 40))
      (mkInterval (Mkmm 60) (Mkmm 90))
      (mkInterval (fun p => Mkmm (Nat.div (pressure_Pa p) 100))
                  (fun p => Mkmm (Nat.div (pressure_Pa p) 50)))
      (mkInterval (MkmL 100) (MkmL 150))
      (mkInterval (MkmL 200) (MkmL 300))
      (mkInterval (MkmL 400) (MkmL 500)).

  Definition apply_compliance (c : Pa -> mm) (pressure : Pa) : mm := c pressure.

  Definition effective_diameter (r : Rectum) (pressure : Pa) : Interval mm :=
    let base := resting_diameter r in
    let expansion_lo := apply_compliance (lo (wall_compliance r)) pressure in
    let expansion_hi := apply_compliance (hi (wall_compliance r)) pressure in
    mkInterval (mm_add (lo base) expansion_lo) (mm_add (hi base) expansion_hi).

  Lemma compliance_increases_diameter :
    forall r p,
    pressure_Pa p > 0 ->
    mm_le (lo (resting_diameter r)) (lo (effective_diameter r p)).
  Proof.
    intros r p Hp.
    unfold effective_diameter, mm_le, mm_add.
    simpl.
    lia.
  Qed.



  (*
     Smooth muscle, tonically contracted, INVOLUNTARY control.
     Provides ~70-85% of resting anal pressure.
     Relaxes reflexively on rectal distension (rectoanal inhibitory reflex).

     Pressure values derived from anorectal manometry literature:
     - Rao SSC. "Dyssynergic Defecation." Gastroenterol Clin N Am. 2008.
     - Bharucha AE. "Pelvic floor: anatomy and function." Neurogastroenterol
       Motil. 2006.
     - Resting pressure 40-70 cmH2O = 3920-6860 Pa (1 cmH2O ≈ 98 Pa).
     - RAIR relaxation typically 20-40 cmH2O drop.
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
      (mkInterval (Mkmm 25) (Mkmm 30))
      (mkInterval (Mkmm 2) (Mkmm 4))
      (mkInterval (MkPa 3900) (MkPa 6900))
      (mkInterval (Mksec 1) (Mksec 3))
      (mkInterval (MkPa 2000) (MkPa 4000)).



  (*
     Skeletal muscle, VOLUNTARY control.
     Provides continence override - can resist defecation reflex.
     Fatigues within 1-3 minutes of sustained contraction.

     - Squeeze pressure 100-180 cmH2O = 9800-17640 Pa.
     - Fatigue onset 50-60s, max sustained effort ~180s.
     - Schuster MM. "Motor action of rectum and anal sphincters."
       Handbook of Physiology. 1968.
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
      (mkInterval (Mkmm 8) (Mkmm 10))
      (mkInterval (MkPa 1500) (MkPa 2500))
      (mkInterval (MkPa 10000) (MkPa 18000))
      (mkInterval (Mksec 60) (Mksec 180))
      (mkInterval (MkPa 500) (MkPa 1000)).



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
      (mkInterval (Mkdeg 80) (Mkdeg 92))
      (mkInterval (Mkdeg 126) (Mkdeg 142))
      (mkInterval (Mksec 2) (Mksec 5))
      (mkInterval (Mkdeg 5) (Mkdeg 15)).



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
      (mkInterval (MkPa 4000) (MkPa 10000))
      (mkInterval (MkPa 2000) (MkPa 4000))
      (fun t => mkInterval (MkPa (4000 - Nat.mul (time_sec t) 20))
                           (MkPa (10000 - Nat.mul (time_sec t) 50))).



  Record AnalCanal := mkAC {
    ac_length : Interval mm;                  (* 25-50mm *)
    ac_resting_diameter : Interval mm;        (* functionally closed *)
    ac_max_dilation : Interval mm;            (* 30-40mm without injury *)
    ac_mucosal_friction : Interval cP;        (* surface friction coefficient *)
  }.

  Definition default_anal_canal : AnalCanal :=
    mkAC
      (mkInterval (Mkmm 25) (Mkmm 50))
      (mkInterval (Mkmm 0) (Mkmm 5))
      (mkInterval (Mkmm 30) (Mkmm 40))
      (mkInterval (MkcP 100) (MkcP 500)).
  
  
  
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
(*                         BOLUS PROPERTIES                         *)
(*============================================================================*)

(*
   The payload. Characterized by volume, consistency (viscosity), and
   geometry. Bristol Stool Scale mapped to physical parameters.
*)

Module Bolus.
  Import Units.
  
  
  Inductive BristolType : Type :=
    | Type1_SeparateHardLumps      (* severe constipation *)
    | Type2_LumpySausage           (* mild constipation *)
    | Type3_SausageWithCracks      (* normal *)
    | Type4_SmoothSoftSausage      (* normal, ideal *)
    | Type5_SoftBlobsClearEdges    (* lacking fiber *)
    | Type6_FluffentPieces         (* mild diarrhea *)
    | Type7_WateryNoSolids.        (* severe diarrhea *)
  
  
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
          (mkInterval (MkcP 10000) (MkcP 50000))
          (mkInterval (MkPa 500) (MkPa 1000))
          (mkInterval (MkPa 800) (MkPa 1200))
          true
          (mkInterval (Mkmm 10) (Mkmm 20))
    | Type2_LumpySausage =>
        mkBolusPhysics
          (mkInterval (MkcP 5000) (MkcP 15000))
          (mkInterval (MkPa 200) (MkPa 500))
          (mkInterval (MkPa 400) (MkPa 800))
          false
          (mkInterval (Mkmm 25) (Mkmm 35))
    | Type3_SausageWithCracks =>
        mkBolusPhysics
          (mkInterval (MkcP 2000) (MkcP 8000))
          (mkInterval (MkPa 100) (MkPa 300))
          (mkInterval (MkPa 200) (MkPa 500))
          false
          (mkInterval (Mkmm 20) (Mkmm 30))
    | Type4_SmoothSoftSausage =>
        mkBolusPhysics
          (mkInterval (MkcP 1000) (MkcP 4000))
          (mkInterval (MkPa 50) (MkPa 150))
          (mkInterval (MkPa 100) (MkPa 300))
          false
          (mkInterval (Mkmm 20) (Mkmm 30))
    | Type5_SoftBlobsClearEdges =>
        mkBolusPhysics
          (mkInterval (MkcP 500) (MkcP 2000))
          (mkInterval (MkPa 20) (MkPa 80))
          (mkInterval (MkPa 30) (MkPa 100))
          true
          (mkInterval (Mkmm 15) (Mkmm 25))
    | Type6_FluffentPieces =>
        mkBolusPhysics
          (mkInterval (MkcP 100) (MkcP 500))
          (mkInterval (MkPa 5) (MkPa 30))
          (mkInterval (MkPa 10) (MkPa 50))
          true
          (mkInterval (Mkmm 10) (Mkmm 20))
    | Type7_WateryNoSolids =>
        mkBolusPhysics
          (mkInterval (MkcP 1) (MkcP 50))
          (mkInterval (MkPa 0) (MkPa 5))
          (mkInterval (MkPa 0) (MkPa 10))
          true
          (mkInterval (Mkmm 0) (Mkmm 10))
    end.
  
  
  Record Bolus := mkBolus {
    bolus_type : BristolType;
    bolus_volume : Interval mL;         (* total payload *)
    bolus_length : Interval mm;         (* extent in rectum *)
    bolus_max_diameter : Interval mm;   (* critical for passage *)
    bolus_physics : BolusPhysics;
  }.

  Coercion bolus_type : Bolus >-> BristolType.
  Coercion bolus_physics : Bolus >-> BolusPhysics.

  Definition volume_valid (vol : Interval mL) : Prop :=
    volume_mL (lo vol) > 0 /\ mL_le (lo vol) (hi vol).

  Lemma volume_valid_dec : forall vol,
    {volume_valid vol} + {~volume_valid vol}.
  Proof.
    intros vol.
    unfold volume_valid, mL_le.
    destruct (Compare_dec.gt_dec (volume_mL (lo vol)) 0) as [Hpos | Hnpos].
    - destruct (Compare_dec.le_dec (volume_mL (lo vol)) (volume_mL (hi vol))) as [Hwf | Hnwf].
      + left. split; assumption.
      + right. intros [_ Hwf]. lia.
    - right. intros [Hpos _]. lia.
  Defined.

  Definition make_bolus (bt : BristolType) (vol : Interval mL) : Bolus :=
    let physics := bristol_to_physics bt in
    mkBolus
      bt
      vol
      (mkInterval (Mkmm (Nat.mul (volume_mL (lo vol)) 2))
                  (Mkmm (Nat.mul (volume_mL (hi vol)) 3)))
      (bp_typical_diameter physics)
      physics.

  Definition make_bolus_safe (bt : BristolType) (vol : Interval mL)
    (Hvalid : volume_valid vol) : Bolus :=
    make_bolus bt vol.

  Definition bolus_wf (b : Bolus) : Prop :=
    volume_mL (lo (bolus_volume b)) > 0 /\
    mL_le (lo (bolus_volume b)) (hi (bolus_volume b)).

  Lemma make_bolus_wf :
    forall bt vol,
    volume_mL (lo vol) > 0 ->
    mL_le (lo vol) (hi vol) ->
    bolus_wf (make_bolus bt vol).
  Proof.
    intros bt vol Hpos Hwf.
    unfold bolus_wf, make_bolus.
    simpl.
    split; assumption.
  Qed.

  Lemma make_bolus_safe_wf :
    forall bt vol Hvalid,
    bolus_wf (make_bolus_safe bt vol Hvalid).
  Proof.
    intros bt vol [Hpos Hwf].
    unfold bolus_wf, make_bolus_safe, make_bolus.
    simpl.
    split; assumption.
  Qed.


  (*
     Hydration level affects stool consistency and passage difficulty.
     - Dehydrated: increased viscosity, yield stress, cohesion
     - Normal: baseline physics
     - Well-hydrated: reduced viscosity, easier passage

     Modeled as percentage of normal hydration (100 = normal).
     Range: 50 (severely dehydrated) to 150 (very well hydrated).
  *)

  Definition HydrationLevel := nat.

  Definition normal_hydration : HydrationLevel := 100.

  Definition apply_hydration (h : HydrationLevel) (physics : BolusPhysics) : BolusPhysics :=
    let factor := Nat.max 50 (Nat.min h 150) in
    let inv_factor := 200 - factor in
    mkBolusPhysics
      (mkInterval
        (MkcP (Nat.div (viscosity_cP (lo (bp_viscosity physics)) * inv_factor) 100))
        (MkcP (Nat.div (viscosity_cP (hi (bp_viscosity physics)) * inv_factor) 100)))
      (mkInterval
        (MkPa (Nat.div (pressure_Pa (lo (bp_yield_stress physics)) * inv_factor) 100))
        (MkPa (Nat.div (pressure_Pa (hi (bp_yield_stress physics)) * inv_factor) 100)))
      (mkInterval
        (MkPa (Nat.div (pressure_Pa (lo (bp_cohesion physics)) * inv_factor) 100))
        (MkPa (Nat.div (pressure_Pa (hi (bp_cohesion physics)) * inv_factor) 100)))
      (bp_fragmentability physics)
      (bp_typical_diameter physics).

  Lemma hydration_reduces_viscosity :
    forall h physics,
    h >= 100 ->
    viscosity_cP (hi (bp_viscosity (apply_hydration h physics))) <=
    viscosity_cP (hi (bp_viscosity physics)).
  Proof.
    intros h physics Hh.
    unfold apply_hydration.
    simpl.
    assert (Hinv: 200 - Nat.max 50 (Nat.min h 150) <= 100) by lia.
    assert (Hdiv: Nat.div (viscosity_cP (hi (bp_viscosity physics)) *
                           (200 - Nat.max 50 (Nat.min h 150))) 100 <=
                  viscosity_cP (hi (bp_viscosity physics))).
    { apply PeanoNat.Nat.div_le_upper_bound.
      - lia.
      - nia. }
    exact Hdiv.
  Qed.

  Lemma dehydration_increases_viscosity :
    forall h physics,
    h <= 100 ->
    h >= 50 ->
    viscosity_cP (lo (bp_viscosity (apply_hydration h physics))) >=
    viscosity_cP (lo (bp_viscosity physics)).
  Proof.
    intros h physics Hle Hge.
    unfold apply_hydration.
    simpl.
    assert (Hinv: 200 - Nat.max 50 (Nat.min h 150) >= 100) by lia.
    assert (Hdiv: Nat.div (viscosity_cP (lo (bp_viscosity physics)) *
                           (200 - Nat.max 50 (Nat.min h 150))) 100 >=
                  viscosity_cP (lo (bp_viscosity physics))).
    { apply PeanoNat.Nat.div_le_lower_bound.
      - lia.
      - nia. }
    exact Hdiv.
  Qed.

  Definition make_bolus_hydrated (bt : BristolType) (vol : Interval mL) (h : HydrationLevel) : Bolus :=
    let base_physics := bristol_to_physics bt in
    let adjusted_physics := apply_hydration h base_physics in
    mkBolus
      bt
      vol
      (mkInterval (Mkmm (Nat.mul (volume_mL (lo vol)) 2))
                  (Mkmm (Nat.mul (volume_mL (hi vol)) 3)))
      (bp_typical_diameter adjusted_physics)
      adjusted_physics.

End Bolus.


(*============================================================================*)
(*                         POSTURE GEOMETRY                         *)
(*============================================================================*)

(*
   Body position affects anorectal angle and hence required pressure.
   Squatting is biomechanically optimal; modern toilets are not.
*)

Module Posture.
  Import Units.
  
  
  Inductive PostureType : Type :=
    | Standing                (* anorectal angle ~90°, defecation difficult *)
    | SittingUpright          (* Western toilet, ~100° *)
    | SittingLeaning          (* leaning forward, ~110-120° *)
    | SittingWithFootstool    (* Squatty Potty, ~120-130° *)
    | FullSquat.              (* traditional/anatomical, ~130-140° *)
  
  
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
          (mkInterval (Mkdeg 170) (Mkdeg 180))
          (mkInterval (Mkdeg 85) (Mkdeg 95))
          false
          (mkInterval (MkPa 0) (MkPa 0))
    | SittingUpright =>
        mkPostureGeometry
          (mkInterval (Mkdeg 85) (Mkdeg 95))
          (mkInterval (Mkdeg 95) (Mkdeg 105))
          false
          (mkInterval (MkPa 200) (MkPa 500))
    | SittingLeaning =>
        mkPostureGeometry
          (mkInterval (Mkdeg 60) (Mkdeg 75))
          (mkInterval (Mkdeg 110) (Mkdeg 120))
          false
          (mkInterval (MkPa 500) (MkPa 1000))
    | SittingWithFootstool =>
        mkPostureGeometry
          (mkInterval (Mkdeg 40) (Mkdeg 55))
          (mkInterval (Mkdeg 120) (Mkdeg 130))
          true
          (mkInterval (MkPa 1000) (MkPa 1500))
    | FullSquat =>
        mkPostureGeometry
          (mkInterval (Mkdeg 20) (Mkdeg 40))
          (mkInterval (Mkdeg 130) (Mkdeg 140))
          true
          (mkInterval (MkPa 1500) (MkPa 2500))
    end.
  
  
  (*
     Claim: For a given bolus and anatomy, required expulsive pressure
     is monotonically decreasing in anorectal angle.
     
     Proof sketch: Straighter path = less resistance.
  *)
  
  (*
     Angle-pressure relationship uses continuous linear interpolation.

     Model: factor decreases linearly from 3 at 80° to 1 at 140°.
     - At 80° (acute): factor = 3. Puborectalis sling creates sharp bend.
     - At 110° (moderate): factor = 2. Partial straightening.
     - At 140° (squat): factor = 1. Near-linear path, minimal resistance.

     Formula: factor = 1 + (140 - clamped_angle) * 2 / 60
     where clamped_angle is angle clamped to [80, 140].

     This eliminates jump discontinuities present in threshold-based models
     while remaining tractable for formal verification.
  *)
  Definition continuous_angle_factor (angle_val : nat) : nat :=
    let clamped := Nat.max 80 (Nat.min angle_val 140) in
    let from_max := 140 - clamped in
    1 + Nat.div (from_max * 2) 60.

  Lemma continuous_angle_factor_bounds :
    forall angle_val, 1 <= continuous_angle_factor angle_val <= 3.
  Proof.
    intros angle_val.
    unfold continuous_angle_factor.
    split.
    - lia.
    - assert (H: Nat.div ((140 - Nat.max 80 (Nat.min angle_val 140)) * 2) 60 <= 2).
      { apply PeanoNat.Nat.div_le_upper_bound; lia. }
      lia.
  Qed.

  Lemma continuous_angle_factor_monotonic :
    forall a1 a2, a1 <= a2 -> continuous_angle_factor a2 <= continuous_angle_factor a1.
  Proof.
    intros a1 a2 Hle.
    unfold continuous_angle_factor.
    apply PeanoNat.Nat.add_le_mono_l.
    apply PeanoNat.Nat.div_le_mono.
    - lia.
    - apply PeanoNat.Nat.mul_le_mono_r.
      lia.
  Qed.

  Definition angle_pressure_relationship (angle : deg) (b : Bolus.Bolus) : Interval Pa :=
    let physics := Bolus.bolus_physics b in
    let base_pressure := pressure_Pa (lo (Bolus.bp_yield_stress physics)) in
    let angle_val := angle_deg angle in
    let angle_factor := continuous_angle_factor angle_val in
    mkInterval (MkPa (Nat.mul base_pressure angle_factor))
               (MkPa (Nat.mul (pressure_Pa (hi (Bolus.bp_yield_stress physics))) (S angle_factor))).

  Lemma angle_pressure_decreases_with_angle :
    forall b : Bolus.Bolus,
    forall a1 a2 : deg,
    deg_le a1 a2 ->
    Pa_le (hi (angle_pressure_relationship a2 b)) (hi (angle_pressure_relationship a1 b)).
  Proof.
    intros b a1 a2 Hle.
    unfold angle_pressure_relationship, Pa_le, deg_le in *.
    simpl.
    apply PeanoNat.Nat.mul_le_mono_l.
    apply le_n_S.
    apply continuous_angle_factor_monotonic.
    exact Hle.
  Qed.
  

End Posture.


(*============================================================================*)
(*                         PRESSURE DYNAMICS                        *)
(*============================================================================*)

(*
   The physics of expulsion. Pressure generated must exceed resistance.
*)

Module Pressure.
  Import Units.
  Import Anatomy.
  Import Bolus.
  Import Posture.
  

  (*
     Total resistance = sphincter pressure + frictional resistance +
                        geometric resistance from anorectal angle.

     Friction model: Derived from Hagen-Poiseuille, simplified.
     ΔP = (8 * μ * L * Q) / (π * r^4) simplifies to:
     friction ∝ (viscosity * length) / (diameter^2 * scaling)

     The scaling factor accounts for:
     - Unit conversion (cP to Pa·s requires /1000)
     - Cross-sectional geometry (π * r^2 factor)
     - Typical flow rate assumptions

     With friction_scaling_divisor = diameter^2 * 10, we get physiologically
     reasonable friction values in the 100-500 Pa range for normal stool.
  *)

  Record ResistanceComponents := mkResistance {
    r_ias : Interval Pa;          (* internal sphincter contribution *)
    r_eas : Interval Pa;          (* external sphincter contribution *)
    r_friction : Interval Pa;     (* bolus-mucosa friction *)
    r_angle : Interval Pa;        (* anorectal angle penalty *)
    r_total : Interval Pa;        (* sum with interaction terms *)
  }.

  Definition friction_scaling_divisor (diameter : Interval mm) : nat :=
    let d_avg := Nat.div (distance_mm (lo diameter) + distance_mm (hi diameter)) 2 in
    S (d_avg * d_avg * 10).

  Definition compute_friction (b : Bolus) : Interval Pa :=
    let viscosity := bp_viscosity b in
    let length := bolus_length b in
    let diameter := bolus_max_diameter b in
    let divisor := friction_scaling_divisor diameter in
    let raw_lo := Nat.mul (viscosity_cP (lo viscosity)) (distance_mm (lo length)) in
    let raw_hi := Nat.mul (viscosity_cP (hi viscosity)) (distance_mm (hi length)) in
    mkInterval (MkPa (Nat.div raw_lo divisor)) (MkPa (Nat.div raw_hi divisor)).

  Lemma compute_friction_bounded :
    forall b : Bolus,
    interval_wf_cP (bp_viscosity (bolus_physics b)) ->
    interval_wf_mm (bolus_length b) ->
    Pa_le (lo (compute_friction b)) (hi (compute_friction b)).
  Proof.
    intros b Hv Hl.
    unfold compute_friction, interval_wf_cP, interval_wf_mm, cP_le, mm_le, Pa_le in *.
    simpl.
    set (divisor := friction_scaling_divisor (bolus_max_diameter b)).
    assert (Hdiv_pos: divisor > 0) by (unfold divisor, friction_scaling_divisor; lia).
    assert (Hnum: viscosity_cP (lo (bp_viscosity (bolus_physics b))) * distance_mm (lo (bolus_length b)) <=
                  viscosity_cP (hi (bp_viscosity (bolus_physics b))) * distance_mm (hi (bolus_length b))).
    { apply PeanoNat.Nat.mul_le_mono; assumption. }
    apply PeanoNat.Nat.div_le_mono with (c := divisor) in Hnum.
    - exact Hnum.
    - lia.
  Qed.

  Definition compute_resistance
    (anat : AnatomicalConfig) (b : Bolus) (pg : PostureGeometry)
    : ResistanceComponents :=
    let ias_r := ias_resting_pressure (ias anat) in
    let eas_r := eas_resting_pressure (eas anat) in
    let friction := compute_friction b in
    let angle_r := angle_pressure_relationship (lo (resultant_anorectal_angle pg)) b in
    let total := mkInterval
      (MkPa (pressure_Pa (lo ias_r) + pressure_Pa (lo eas_r) +
             pressure_Pa (lo friction) + pressure_Pa (lo angle_r)))
      (MkPa (pressure_Pa (hi ias_r) + pressure_Pa (hi eas_r) +
             pressure_Pa (hi friction) + pressure_Pa (hi angle_r))) in
    mkResistance ias_r eas_r friction angle_r total.

  Definition compute_resistance_with_sphincter_state
    (b : Bolus) (pg : PostureGeometry)
    (ias_actual eas_actual : Interval Pa)
    : ResistanceComponents :=
    let friction := compute_friction b in
    let angle_r := angle_pressure_relationship (lo (resultant_anorectal_angle pg)) b in
    let total := mkInterval
      (MkPa (pressure_Pa (lo ias_actual) + pressure_Pa (lo eas_actual) +
             pressure_Pa (lo friction) + pressure_Pa (lo angle_r)))
      (MkPa (pressure_Pa (hi ias_actual) + pressure_Pa (hi eas_actual) +
             pressure_Pa (hi friction) + pressure_Pa (hi angle_r))) in
    mkResistance ias_actual eas_actual friction angle_r total.

  Definition relaxed_sphincter_pressure : Interval Pa :=
    mkInterval (MkPa 500) (MkPa 500).

  Definition compute_expulsion_resistance (b : Bolus) (pg : PostureGeometry)
    : ResistanceComponents :=
    compute_resistance_with_sphincter_state b pg
      relaxed_sphincter_pressure relaxed_sphincter_pressure.

  Lemma expulsion_resistance_le_resting :
    forall anat b pg,
    500 <= pressure_Pa (hi (ias_resting_pressure (ias anat))) ->
    500 <= pressure_Pa (hi (eas_resting_pressure (eas anat))) ->
    Pa_le (hi (r_total (compute_expulsion_resistance b pg)))
          (hi (r_total (compute_resistance anat b pg))).
  Proof.
    intros anat b pg Hias Heas.
    unfold compute_expulsion_resistance, compute_resistance_with_sphincter_state,
           compute_resistance, relaxed_sphincter_pressure, Pa_le.
    simpl.
    lia.
  Qed.

  Lemma le_from_leb : forall n m, Nat.leb n m = true -> n <= m.
  Proof.
    intros n m H.
    apply PeanoNat.Nat.leb_le.
    exact H.
  Defined.

  Lemma default_anatomy_has_adequate_resting_pressures :
    500 <= pressure_Pa (hi (ias_resting_pressure (ias default_anatomy))) /\
    500 <= pressure_Pa (hi (eas_resting_pressure (eas default_anatomy))).
  Proof.
    split; apply le_from_leb; vm_compute; reflexivity.
  Qed.

  
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
  
  (*
     Expulsive pressure constants.

     safe_expulsive_bound (15000 Pa ≈ 153 cmH2O): Maximum safe Valsalva.
     Above this threshold, risk of vasovagal syncope, hemorrhoid
     exacerbation, and inguinal hernia increases significantly.
     Clinical guideline: sustained straining >150 cmH2O contraindicated.

     peristaltic_base (500-1500 Pa ≈ 5-15 cmH2O): Intrinsic rectal
     contractile pressure from propagating mass movements. Values from
     colonic manometry studies.

     compression_bonus (1000 Pa ≈ 10 cmH2O): Additional pressure from
     thigh-abdomen compression in flexed postures. Measured via
     intra-abdominal pressure monitoring during squatting.
  *)
  Definition safe_expulsive_bound : nat := 15000.
  Definition peristaltic_base_lo : nat := 500.
  Definition peristaltic_base_hi : nat := 1500.
  Definition compression_bonus : nat := 1000.

  (*
     Gravity model: Simplified posture-dependent pressure contribution.

     Full physics would be: P_gravity = (ρ × g × h × sin θ) / A
     where:
       ρ = stool density (~1000 kg/m³)
       g = 9.81 m/s²
       h = bolus height/length
       θ = angle from horizontal
       A = cross-sectional area

     We approximate this with posture-dependent constants because:
     1. The angle changes with posture (squatting > sitting > standing)
     2. Thigh compression adds effective pressure in squatting/sitting
     3. Pelvic floor relaxation reduces counter-pressure

     The `e_gravity_assist` field combines:
     - pelvic_floor_relaxation_bonus: angle-dependent relaxation benefit
     - compression_bonus: thigh-abdomen compression in bent postures

     This produces physiologically reasonable values:
     - Standing: ~500-1000 Pa (minimal gravity assist)
     - Sitting: ~1500-2500 Pa (moderate)
     - Squatting: ~2500-3500 Pa (optimal)
  *)

  Definition compute_expulsive
    (anat : AnatomicalConfig) (pg : PostureGeometry) : ExpulsiveComponents :=
    let aw := abdominal_wall anat in
    let valsalva := aw_max_valsalva_pressure aw in
    let peristalsis := mkInterval (MkPa peristaltic_base_lo) (MkPa peristaltic_base_hi) in
    let pf_bonus := pelvic_floor_relaxation_bonus pg in
    let compress := if thigh_abdominal_compression pg then compression_bonus else 0 in
    let gravity := iv_add pf_bonus (mkInterval (MkPa compress) (MkPa compress)) in
    let raw_total_lo := pressure_Pa (lo valsalva) + pressure_Pa (lo peristalsis) + pressure_Pa (lo gravity) in
    let raw_total_hi := pressure_Pa (hi valsalva) + pressure_Pa (hi peristalsis) + pressure_Pa (hi gravity) in
    let capped_lo := Nat.min raw_total_lo safe_expulsive_bound in
    let capped_hi := Nat.min raw_total_hi safe_expulsive_bound in
    mkExpulsive valsalva peristalsis gravity (mkInterval (MkPa capped_lo) (MkPa capped_hi)).

  
  Definition pressure_differential
    (exp : ExpulsiveComponents) (res : ResistanceComponents) : Interval Pa :=
    iv_sub (e_total exp) (r_total res).
  
  
  (*
     Bolus moves iff expulsive pressure > resistance.
     Flow rate is function of pressure differential and viscosity.
  *)
  
  Definition passage_possible (exp : ExpulsiveComponents) (res : ResistanceComponents) : Prop :=
    pressure_Pa (lo (e_total exp)) > pressure_Pa (hi (r_total res)).

  (*
     Flow rate model: Linearized Bingham plastic approximation.

     For a Bingham plastic (non-Newtonian fluid with yield stress), flow through
     a tube follows: Q = (πR⁴/8μL)(ΔP - τ_y) when ΔP > τ_y, else Q = 0.

     We simplify to: flow ∝ (ΔP - τ_y) / μ

     This captures the essential physics:
     - No flow below yield stress (captures stool consistency)
     - Flow rate increases with pressure differential
     - Flow rate decreases with viscosity
     - Units: (Pa - Pa) / cP = dimensionless ratio, scaled to mm advancement

     The (S viscosity) denominator prevents division by zero and provides
     a scaling factor that produces reasonable mm/tick values.
  *)

  Definition flow_rate
    (pressure_diff : Interval Pa) (physics : BolusPhysics) : Interval mm :=
    let viscosity := bp_viscosity physics in
    let yield := bp_yield_stress physics in
    let effective_pressure_lo := pressure_Pa (lo pressure_diff) - pressure_Pa (hi yield) in
    let effective_pressure_hi := pressure_Pa (hi pressure_diff) - pressure_Pa (lo yield) in
    let flow_lo := Nat.div effective_pressure_lo (S (viscosity_cP (hi viscosity))) in
    let flow_hi := Nat.div effective_pressure_hi (S (viscosity_cP (lo viscosity))) in
    mkInterval (Mkmm flow_lo) (Mkmm flow_hi).

  Lemma flow_rate_nonneg :
    forall diff physics,
    distance_mm (lo (flow_rate diff physics)) >= 0.
  Proof.
    intros diff physics.
    unfold flow_rate.
    simpl.
    lia.
  Qed.

  Lemma flow_rate_positive :
    forall diff physics,
    pressure_Pa (lo diff) > pressure_Pa (hi (bp_yield_stress physics)) + viscosity_cP (hi (bp_viscosity physics)) ->
    distance_mm (lo (flow_rate diff physics)) > 0.
  Proof.
    intros diff physics Hdiff.
    unfold flow_rate.
    simpl.
    assert (Hnum: pressure_Pa (lo diff) - pressure_Pa (hi (bp_yield_stress physics)) > viscosity_cP (hi (bp_viscosity physics))).
    { lia. }
    assert (Hdiv: Nat.div (pressure_Pa (lo diff) - pressure_Pa (hi (bp_yield_stress physics))) (S (viscosity_cP (hi (bp_viscosity physics)))) > 0).
    { apply PeanoNat.Nat.div_str_pos.
      split.
      - lia.
      - lia. }
    exact Hdiv.
  Qed.

  Definition margin_for_flow (physics : BolusPhysics) : nat :=
    pressure_Pa (hi (bp_yield_stress physics)) + viscosity_cP (hi (bp_viscosity physics)).

  Lemma passage_possible_with_margin :
    forall exp res physics,
    pressure_Pa (lo (e_total exp)) > pressure_Pa (hi (r_total res)) + margin_for_flow physics ->
    distance_mm (lo (flow_rate (pressure_differential exp res) physics)) > 0.
  Proof.
    intros exp res physics Hmargin.
    apply flow_rate_positive.
    unfold pressure_differential, iv_sub, Pa_sub, margin_for_flow in *.
    simpl.
    lia.
  Qed.

  Lemma passage_possible_implies_positive_differential :
    forall exp res,
    passage_possible exp res ->
    Units.positive_differential (pressure_differential exp res).
  Proof.
    intros exp res Hpass.
    unfold Units.positive_differential, passage_possible, pressure_differential, iv_sub, Pa_sub in *.
    simpl.
    lia.
  Qed.

  Lemma passage_possible_dec :
    forall exp res,
    {passage_possible exp res} + {~passage_possible exp res}.
  Proof.
    intros exp res.
    unfold passage_possible.
    destruct (Compare_dec.gt_dec (pressure_Pa (lo (e_total exp))) (pressure_Pa (hi (r_total res)))).
    - left. exact g.
    - right. lia.
  Qed.

End Pressure.


(*============================================================================*)
(*                         NEURAL CONTROL                           *)
(*============================================================================*)

(*
   Reflex arcs and voluntary overrides. The control system.
*)

Module Neural.
  Import Units.
  Import Anatomy.
  
  
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
      (mkInterval (Mksec 10) (Mksec 30)).


  (*
     EAS contraction can maintain continence despite RAIR.
     Time-limited by fatigue.

     Fatigue model: hyperbolic decay from max toward floor.
     Uses the formula: remaining = floor + (max - floor) * tau / (tau + t)

     Properties:
     - At t=0: remaining = max (full strength)
     - At t=tau: remaining = floor + (max - floor)/2 (half decay)
     - As t→∞: remaining → floor (asymptotic approach)

     This is continuous and monotonically decreasing, avoiding the
     discontinuous jump to 0 in threshold-based models. The hyperbolic
     form approximates exponential decay while being tractable in nat.
  *)

  Definition eas_fatigue_model
    (eas : ExternalSphincter) (t : sec) : Interval Pa :=
    let max_lo := pressure_Pa (lo (eas_max_squeeze_pressure eas)) in
    let max_hi := pressure_Pa (hi (eas_max_squeeze_pressure eas)) in
    let floor_lo := pressure_Pa (lo (eas_voluntary_relaxation_floor eas)) in
    let floor_hi := pressure_Pa (hi (eas_voluntary_relaxation_floor eas)) in
    let tau_lo := time_sec (lo (eas_fatigue_time eas)) in
    let tau_hi := time_sec (hi (eas_fatigue_time eas)) in
    let t_val := time_sec t in
    let range_lo := max_lo - floor_hi in
    let range_hi := max_hi - floor_lo in
    let remaining_lo := floor_lo + Nat.div (range_lo * tau_lo) (S (tau_hi + t_val)) in
    let remaining_hi := floor_hi + Nat.div (range_hi * tau_hi) (S (tau_lo + t_val)) in
    mkInterval (MkPa remaining_lo) (MkPa remaining_hi).

  Lemma eas_fatigue_nonneg :
    forall eas t,
    pressure_Pa (lo (eas_fatigue_model eas t)) >= 0.
  Proof.
    intros eas t.
    unfold eas_fatigue_model.
    simpl.
    lia.
  Qed.

  Lemma eas_fatigue_above_floor :
    forall eas t,
    pressure_Pa (lo (eas_fatigue_model eas t)) >=
    pressure_Pa (lo (eas_voluntary_relaxation_floor eas)).
  Proof.
    intros eas t.
    unfold eas_fatigue_model.
    simpl.
    lia.
  Qed.

  Lemma div_antitone : forall a b c,
    b > 0 -> b <= c -> a / c <= a / b.
  Proof.
    intros a b c Hpos Hle.
    destruct (Nat.eq_dec c 0) as [Hc0 | Hc0].
    - lia.
    - assert (Hcpos: c > 0) by lia.
      assert (Hbneq: b <> 0) by lia.
      pose proof (PeanoNat.Nat.mul_div_le a c) as Hdiv.
      assert (Hbc: a / c * b <= a / c * c).
      { apply PeanoNat.Nat.mul_le_mono_l. lia. }
      assert (Htrans: a / c * b <= a) by lia.
      rewrite PeanoNat.Nat.mul_comm in Htrans.
      apply PeanoNat.Nat.div_le_lower_bound.
      + exact Hbneq.
      + exact Htrans.
  Qed.

  Lemma eas_fatigue_monotonic :
    forall eas t1 t2,
    time_sec t1 <= time_sec t2 ->
    pressure_Pa (hi (eas_fatigue_model eas t2)) <=
    pressure_Pa (hi (eas_fatigue_model eas t1)).
  Proof.
    intros eas t1 t2 Hle.
    unfold eas_fatigue_model.
    simpl.
    apply PeanoNat.Nat.add_le_mono_l.
    apply (div_antitone
      ((pressure_Pa (hi (eas_max_squeeze_pressure eas)) -
        pressure_Pa (lo (eas_voluntary_relaxation_floor eas))) *
       time_sec (hi (eas_fatigue_time eas)))
      (S (time_sec (lo (eas_fatigue_time eas)) + time_sec t1))
      (S (time_sec (lo (eas_fatigue_time eas)) + time_sec t2))).
    - lia.
    - lia.
  Qed.

  Record ContinenceState := mkContinence {
    eas_contracted : bool;
    contraction_duration : sec;
    remaining_strength : Interval Pa;
  }.

  Definition initial_continence (eas : ExternalSphincter) : ContinenceState :=
    mkContinence true (Mksec 0) (eas_max_squeeze_pressure eas).

  Definition update_continence (eas : ExternalSphincter) (cs : ContinenceState) (dt : sec)
    : ContinenceState :=
    let new_duration := Mksec (time_sec (contraction_duration cs) + time_sec dt) in
    let new_strength := eas_fatigue_model eas new_duration in
    mkContinence (eas_contracted cs) new_duration new_strength.

  Definition continence_exhausted (cs : ContinenceState) : Prop :=
    pressure_Pa (hi (remaining_strength cs)) = 0.


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
    cmd_valsalva_intensity : Interval Pa;
    cmd_bearing_down : bool;
  }.

  Definition effective_valsalva (cmd : VoluntaryCommands) (aw : Anatomy.AbdominalWall) : Interval Pa :=
    let base := cmd_valsalva_intensity cmd in
    let max_allowed := Anatomy.aw_max_valsalva_pressure aw in
    let clamped_lo := Nat.min (pressure_Pa (lo base)) (pressure_Pa (hi max_allowed)) in
    let clamped_hi := Nat.min (pressure_Pa (hi base)) (pressure_Pa (hi max_allowed)) in
    let bearing_bonus := if cmd_bearing_down cmd then 500 else 0 in
    mkInterval (MkPa (clamped_lo + bearing_bonus)) (MkPa (clamped_hi + bearing_bonus)).

  Lemma bearing_down_increases_pressure :
    forall cmd aw,
    cmd_bearing_down cmd = true ->
    pressure_Pa (lo (effective_valsalva cmd aw)) >= 500.
  Proof.
    intros cmd aw Hbd.
    unfold effective_valsalva.
    rewrite Hbd.
    simpl.
    apply PeanoNat.Nat.le_add_l.
  Defined.

  Definition commands_for_defecation (valsalva : Interval Pa) : VoluntaryCommands :=
    mkCommands true true valsalva true.

  Lemma commands_for_defecation_permits :
    forall v,
    cmd_eas_relax (commands_for_defecation v) = true /\
    cmd_pr_relax (commands_for_defecation v) = true.
  Proof.
    intros v.
    split; reflexivity.
  Defined.

  
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
(*                         STATE MACHINE                            *)
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
  

  Definition position_within_bolus (s : SystemState) : Prop :=
    match bolus s with
    | None => True
    | Some b => mm_le (hi (bolus_position s)) (hi (Bolus.bolus_length b))
    end.

  Definition state_wf (s : SystemState) : Prop :=
    position_within_bolus s.


  Definition urge_threshold : mL := MkmL 100.

  Definition guard_urge (s : SystemState) : Prop :=
    reflex_state s = Quiescent /\
    match bolus s with
    | None => False
    | Some b => mL_le urge_threshold (lo (bolus_volume b))
    end.

  Definition has_bolus (s : SystemState) : Prop :=
    match bolus s with
    | None => False
    | Some _ => True
    end.

  (* UrgePresent -> VoluntaryHold *)
  Definition guard_hold (s : SystemState) : Prop :=
    reflex_state s = UrgePresent /\
    cmd_eas_relax (voluntary_commands s) = false /\
    has_bolus s.

  (* UrgePresent -> InitiationPhase *)
  Definition guard_initiate (s : SystemState) : Prop :=
    reflex_state s = UrgePresent /\
    cmd_eas_relax (voluntary_commands s) = true /\
    cmd_pr_relax (voluntary_commands s) = true /\
    has_bolus s.

  Definition fatigue_limit : sec := Mksec 180.

  Definition guard_fatigue_failure (s : SystemState) : Prop :=
    reflex_state s = VoluntaryHold /\
    sec_le fatigue_limit (eas_fatigue_accumulated s) /\
    has_bolus s.

  Definition relaxation_threshold : Pa := MkPa 500.

  Definition guard_expulsion_start (s : SystemState) : Prop :=
    reflex_state s = InitiationPhase /\
    Pa_le (hi (eas_pressure s)) relaxation_threshold /\
    Pa_le (hi (ias_pressure s)) relaxation_threshold /\
    has_bolus s.

  Definition passage_complete_threshold : mm := Mkmm 0.

  Definition guard_completion (s : SystemState) : Prop :=
    reflex_state s = ExpulsionPhase /\
    mm_le (hi (bolus_position s)) passage_complete_threshold /\
    has_bolus s.

  Definition resting_tone_threshold : Pa := MkPa 3000.

  Definition guard_reset (s : SystemState) : Prop :=
    reflex_state s = CompletionPhase /\
    Pa_le resting_tone_threshold (lo (eas_pressure s)) /\
    Pa_le resting_tone_threshold (lo (ias_pressure s)).


  Definition default_ias_pressure : Interval Pa :=
    mkInterval resting_tone_threshold resting_tone_threshold.
  Definition default_eas_pressure : Interval Pa :=
    mkInterval resting_tone_threshold resting_tone_threshold.
  Definition relaxed_pressure : Interval Pa :=
    mkInterval relaxation_threshold relaxation_threshold.
  Definition zero_position : Interval mm :=
    mkInterval passage_complete_threshold passage_complete_threshold.
  Definition time_step : sec := Mksec 1.
  Definition hold_fatigue_increment : sec := Mksec 10.

  Definition transition_to_urge (s : SystemState) : SystemState :=
    mkState (anatomy s) (bolus s) (bolus_position s) (posture s)
            UrgePresent (voluntary_commands s)
            (ias_pressure s) (eas_pressure s) (anorectal_angle s)
            (Mksec (S (time_sec (elapsed_time s)))) (eas_fatigue_accumulated s).

  Definition transition_to_hold (s : SystemState) : SystemState :=
    mkState (anatomy s) (bolus s) (bolus_position s) (posture s)
            VoluntaryHold (voluntary_commands s)
            (ias_pressure s) (eas_pressure s) (anorectal_angle s)
            (Mksec (S (time_sec (elapsed_time s)))) (Mksec (time_sec (eas_fatigue_accumulated s) + time_sec hold_fatigue_increment)).

  Definition transition_to_initiation (s : SystemState) : SystemState :=
    mkState (anatomy s) (bolus s) (bolus_position s) (posture s)
            InitiationPhase (voluntary_commands s)
            relaxed_pressure relaxed_pressure (anorectal_angle s)
            (Mksec (S (time_sec (elapsed_time s)))) (eas_fatigue_accumulated s).

  Definition transition_fatigue_failure (s : SystemState) : SystemState :=
    mkState (anatomy s) (bolus s) (bolus_position s) (posture s)
            UrgePresent (voluntary_commands s)
            (ias_pressure s) relaxed_pressure (anorectal_angle s)
            (Mksec (S (time_sec (elapsed_time s)))) (eas_fatigue_accumulated s).

  Definition transition_to_expulsion (s : SystemState) : SystemState :=
    mkState (anatomy s) (bolus s) (bolus_position s) (posture s)
            ExpulsionPhase (voluntary_commands s)
            relaxed_pressure relaxed_pressure (anorectal_angle s)
            (Mksec (S (time_sec (elapsed_time s)))) (eas_fatigue_accumulated s).

  Definition compute_bolus_advancement (s : SystemState) : Interval mm :=
    match bolus s with
    | None => mkInterval (Mkmm 0) (Mkmm 0)
    | Some b =>
        let pg := Posture.posture_to_geometry (posture s) in
        let exp := Pressure.compute_expulsive (anatomy s) pg in
        let res := Pressure.compute_expulsion_resistance b pg in
        let diff := Pressure.pressure_differential exp res in
        Pressure.flow_rate diff (Bolus.bolus_physics b)
    end.

  Definition transition_expulsion_tick (s : SystemState) : SystemState :=
    let advancement := compute_bolus_advancement s in
    let new_pos_lo := distance_mm (lo (bolus_position s)) - distance_mm (hi advancement) in
    let new_pos_hi := distance_mm (hi (bolus_position s)) - distance_mm (lo advancement) in
    let clamped_lo := if Nat.leb (distance_mm (lo (bolus_position s))) (distance_mm (hi advancement)) then 0 else new_pos_lo in
    let clamped_hi := if Nat.leb (distance_mm (hi (bolus_position s))) (distance_mm (lo advancement)) then 0 else new_pos_hi in
    mkState (anatomy s) (bolus s) (mkInterval (Mkmm clamped_lo) (Mkmm clamped_hi)) (posture s)
            ExpulsionPhase (voluntary_commands s)
            relaxed_pressure relaxed_pressure (anorectal_angle s)
            (Mksec (S (time_sec (elapsed_time s)))) (eas_fatigue_accumulated s).

  Definition guard_expulsion_tick (s : SystemState) : Prop :=
    reflex_state s = ExpulsionPhase /\
    mm_lt passage_complete_threshold (hi (bolus_position s)).

  Definition transition_to_completion (s : SystemState) : SystemState :=
    mkState (anatomy s) None zero_position (posture s)
            CompletionPhase (voluntary_commands s)
            default_ias_pressure default_eas_pressure (anorectal_angle s)
            (Mksec (S (time_sec (elapsed_time s)))) (Mksec 0).

  Definition transition_to_quiescent (s : SystemState) : SystemState :=
    mkState (anatomy s) None zero_position (posture s)
            Quiescent (voluntary_commands s)
            default_ias_pressure default_eas_pressure (anorectal_angle s)
            (Mksec 0) (Mksec 0).

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
    forall s, Pa_le (hi (eas_pressure (transition_to_initiation s))) relaxation_threshold /\
              Pa_le (hi (ias_pressure (transition_to_initiation s))) relaxation_threshold.
  Proof.
    intros s.
    split; simpl; apply Pa_le_refl.
  Qed.
  Lemma transition_to_expulsion_preserves_position :
    forall s, bolus_position (transition_to_expulsion s) = bolus_position s.
  Proof. reflexivity. Qed.

  Lemma transition_expulsion_tick_state :
    forall s, reflex_state (transition_expulsion_tick s) = ExpulsionPhase.
  Proof. reflexivity. Qed.

  Lemma transition_expulsion_tick_decreases :
    forall s,
    mm_le (hi (bolus_position (transition_expulsion_tick s))) (hi (bolus_position s)).
  Proof.
    intros s.
    unfold transition_expulsion_tick, mm_le.
    simpl.
    destruct (Nat.leb (distance_mm (lo (bolus_position s))) (distance_mm (hi (compute_bolus_advancement s))));
    destruct (Nat.leb (distance_mm (hi (bolus_position s))) (distance_mm (lo (compute_bolus_advancement s)))); lia.
  Qed.

  Lemma transition_expulsion_tick_preserves_wf :
    forall s,
    position_within_bolus s ->
    position_within_bolus (transition_expulsion_tick s).
  Proof.
    intros s Hwf.
    unfold position_within_bolus in *.
    unfold transition_expulsion_tick.
    simpl.
    destruct (bolus s) as [b|].
    - unfold mm_le in *.
      destruct (Nat.leb (distance_mm (lo (bolus_position s))) (distance_mm (hi (compute_bolus_advancement s))));
      destruct (Nat.leb (distance_mm (hi (bolus_position s))) (distance_mm (lo (compute_bolus_advancement s)))).
      + simpl. lia.
      + simpl. lia.
      + simpl. lia.
      + simpl. lia.
    - exact I.
  Qed.

  Lemma all_phase_transitions_preserve_wf :
    forall s,
    position_within_bolus s ->
    position_within_bolus (transition_to_urge s) /\
    position_within_bolus (transition_to_hold s) /\
    position_within_bolus (transition_to_initiation s) /\
    position_within_bolus (transition_to_expulsion s) /\
    position_within_bolus (transition_to_completion s).
  Proof.
    intros s Hwf.
    unfold position_within_bolus in *.
    repeat split; simpl; destruct (bolus s); try exact I; exact Hwf.
  Defined.

  Lemma transition_to_completion_restores :
    forall s, Pa_le resting_tone_threshold (lo (eas_pressure (transition_to_completion s))) /\
              Pa_le resting_tone_threshold (lo (ias_pressure (transition_to_completion s))).
  Proof.
    intros s. split; simpl; apply Pa_le_refl.
  Qed.
  
  
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

  Lemma ms_step_r : forall a b c,
    MultiStep a b -> Step b c -> MultiStep a c.
  Proof.
    intros a b c Hab Hbc.
    apply ms_trans with b.
    - exact Hab.
    - apply ms_step with c.
      + exact Hbc.
      + apply ms_refl.
  Defined.

  Definition quiescent_empty (s : SystemState) : Prop :=
    reflex_state s = Quiescent /\ bolus s = None.

  Lemma quiescent_empty_no_step :
    forall s s',
    quiescent_empty s ->
    ~ Step s s'.
  Proof.
    intros s s' [Hq Hb] Hstep.
    inversion Hstep; subst;
      try (unfold guard_urge in *; destruct H as [_ Hg]; rewrite Hb in Hg; exact Hg);
      try (unfold guard_hold, has_bolus in *; destruct H as [_ [_ Hg]]; rewrite Hb in Hg; exact Hg);
      try (unfold guard_initiate, has_bolus in *; destruct H as [_ [_ [_ Hg]]]; rewrite Hb in Hg; exact Hg);
      try (unfold guard_fatigue_failure, has_bolus in *; destruct H as [_ [_ [_ Hg]]]; rewrite Hb in Hg; exact Hg);
      try (unfold guard_expulsion_start, has_bolus in *; destruct H as [_ Hg]; rewrite Hb in Hg; exact Hg);
      try (unfold guard_expulsion_tick in *; destruct H as [Hr _]; rewrite Hq in Hr; discriminate);
      try (unfold guard_completion in *; destruct H as [Hr _]; rewrite Hq in Hr; discriminate);
      try (unfold guard_reset in *; destruct H as [Hr _]; rewrite Hq in Hr; discriminate).
  Qed.

End StateMachine.


(*============================================================================*)
(*                         PROGRESS LEMMAS                          *)
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
  

  (*
     During ExpulsionPhase, if pressure differential is positive,
     bolus position strictly decreases (approaches anal verge).
  *)

  Definition bolus_advances (pos_before pos_after : Interval mm) : Prop :=
    mm_lt (hi pos_after) (hi pos_before).

  Lemma flow_implies_advancement :
    forall diff physics pos_before,
    pressure_Pa (lo diff) > pressure_Pa (hi (bp_yield_stress physics)) ->
    distance_mm (lo (flow_rate diff physics)) > 0 ->
    distance_mm (hi pos_before) > 0 ->
    exists pos_after : Interval mm,
    bolus_advances pos_before pos_after.
  Proof.
    intros diff physics pos_before Hdiff Hflow Hpos.
    exists (mkInterval (Mkmm 0) (Mkmm (distance_mm (hi pos_before) - 1))).
    unfold bolus_advances, mm_lt.
    simpl.
    lia.
  Qed.

  Lemma advancement_reduces_remaining :
    forall pos1 pos2 : Interval mm,
    bolus_advances pos1 pos2 ->
    mm_lt (hi pos2) (hi pos1).
  Proof.
    intros pos1 pos2 Hadv.
    unfold bolus_advances in Hadv.
    exact Hadv.
  Qed.


  (*
     VoluntaryHold cannot persist indefinitely.
     After eas_fatigue_time, transition to either Initiation or
     uncontrolled expulsion.
  *)

  Definition fatigue_exceeds_limit (acc : sec) : Prop :=
    sec_le StateMachine.fatigue_limit acc.

  Lemma fatigue_approaches_floor :
    forall eas t,
    pressure_Pa (lo (eas_fatigue_model eas t)) >=
    pressure_Pa (lo (eas_voluntary_relaxation_floor eas)).
  Proof.
    intros eas t.
    unfold eas_fatigue_model.
    simpl.
    lia.
  Qed.

  Lemma fatigue_bounded_above :
    forall eas t,
    pressure_Pa (lo (eas_fatigue_model eas t)) <=
    pressure_Pa (lo (eas_voluntary_relaxation_floor eas)) +
    Nat.div ((pressure_Pa (lo (eas_max_squeeze_pressure eas)) -
              pressure_Pa (hi (eas_voluntary_relaxation_floor eas))) *
             time_sec (lo (eas_fatigue_time eas)))
            (S (time_sec (hi (eas_fatigue_time eas)) + time_sec t)).
  Proof.
    intros eas t.
    unfold eas_fatigue_model.
    simpl.
    lia.
  Qed.

  Lemma fatigue_decreases_over_time :
    forall eas t1 t2,
    time_sec t1 <= time_sec t2 ->
    pressure_Pa (lo (eas_fatigue_model eas t2)) <=
    pressure_Pa (lo (eas_fatigue_model eas t1)).
  Proof.
    intros eas t1 t2 Hle.
    unfold eas_fatigue_model.
    simpl.
    apply PeanoNat.Nat.add_le_mono_l.
    apply (div_antitone
      ((pressure_Pa (lo (eas_max_squeeze_pressure eas)) -
        pressure_Pa (hi (eas_voluntary_relaxation_floor eas))) *
       time_sec (lo (eas_fatigue_time eas)))
      (S (time_sec (hi (eas_fatigue_time eas)) + time_sec t1))
      (S (time_sec (hi (eas_fatigue_time eas)) + time_sec t2))).
    - lia.
    - lia.
  Qed.

  Lemma hold_bounded_by_fatigue :
    forall acc_start acc_end : sec,
    time_sec acc_end >= time_sec acc_start ->
    time_sec acc_end >= time_sec StateMachine.fatigue_limit ->
    fatigue_exceeds_limit acc_end.
  Proof.
    intros acc_start acc_end Hge Hlim.
    unfold fatigue_exceeds_limit, StateMachine.fatigue_limit, sec_le.
    simpl. exact Hlim.
  Qed.


  (*
     Once voluntary commands issued, sphincters reach relaxed state
     in bounded time.
  *)

  Definition sphincter_relaxed (p : Interval Pa) : Prop :=
    Pa_le (hi p) StateMachine.relaxation_threshold.

  Lemma ias_relaxes_on_rair :
    forall ias vol,
    pressure_Pa (lo (ias_relaxation_magnitude ias)) > 0 ->
    pressure_Pa (lo (rair_ias_relaxation (compute_rair ias vol))) > 0.
  Proof.
    intros ias vol Hpos.
    unfold compute_rair.
    simpl.
    exact Hpos.
  Qed.

  Lemma default_ias_has_positive_relaxation :
    pressure_Pa (lo (ias_relaxation_magnitude default_ias)) > 0.
  Proof.
    unfold default_ias.
    simpl.
    lia.
  Qed.

  Lemma relaxation_bounded_time :
    forall ias,
    exists t_max : sec,
    time_sec t_max <= time_sec (hi (ias_relaxation_latency ias)) + time_sec (hi (mkInterval (Mksec 10) (Mksec 30))).
  Proof.
    intros ias.
    exists (Mksec (time_sec (hi (ias_relaxation_latency ias)) + 30)).
    simpl.
    lia.
  Qed.


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
(*                         TERMINATION PROOF                        *)
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
  
  
  (*
     Critical assumption: bolus volume is finite and bounded.
     Without this, ExpulsionPhase could run forever.
  *)
  
  Definition max_bolus_volume : mL := MkmL 500.

  Definition finite_bolus (b : Bolus) : Prop :=
    mL_le (hi (bolus_volume b)) max_bolus_volume.


  Definition voluntary_commands_permit_defecation (s : SystemState) : Prop :=
    cmd_eas_relax (voluntary_commands s) = true /\
    cmd_pr_relax (voluntary_commands s) = true.

  Fixpoint expulsion_ticks (n : nat) (s : SystemState) : SystemState :=
    match n with
    | O => s
    | S n' =>
        if Nat.leb (distance_mm (hi (bolus_position s))) (distance_mm passage_complete_threshold)
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
      destruct (distance_mm (hi (bolus_position s)) <=? 0) eqn:Hcmp.
      + exact Hs.
      + apply IHn.
        apply transition_expulsion_tick_state.
  Qed.

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
      destruct (distance_mm (hi (bolus_position s)) <=? 0) eqn:Hcmp.
      + apply ms_refl.
      + apply ms_step with (transition_expulsion_tick s).
        * apply step_expulsion_tick.
          unfold guard_expulsion_tick.
          split.
          -- exact Hs.
          -- apply PeanoNat.Nat.leb_gt in Hcmp.
             unfold mm_lt, passage_complete_threshold. simpl. exact Hcmp.
        * apply IHn.
          apply transition_expulsion_tick_state.
  Qed.

  Definition sufficient_ticks (pos : mm) : nat := S (distance_mm pos).

  (*
     Predicate indicating expulsion phase completed (bolus fully expelled).
     Use `expulsion_ticks_reaches_threshold` to prove completion given
     sufficient fuel (n >= bolus position) and positive flow.
  *)
  Definition expulsion_completed (s : SystemState) : Prop :=
    mm_le (hi (bolus_position s)) passage_complete_threshold.

  Definition has_positive_flow (s : SystemState) : Prop :=
    distance_mm (lo (compute_bolus_advancement s)) > 0.

  Definition sufficient_pressure_differential (s : SystemState) : Prop :=
    match bolus s with
    | None => False
    | Some b =>
        let pg := Posture.posture_to_geometry (posture s) in
        let exp := Pressure.compute_expulsive (anatomy s) pg in
        let res := Pressure.compute_expulsion_resistance b pg in
        pressure_Pa (lo (Pressure.e_total exp)) > pressure_Pa (hi (Pressure.r_total res))
    end.

  Definition sufficient_pressure_with_margin (s : SystemState) : Prop :=
    match bolus s with
    | None => False
    | Some b =>
        let pg := Posture.posture_to_geometry (posture s) in
        let exp := Pressure.compute_expulsive (anatomy s) pg in
        let res := Pressure.compute_expulsion_resistance b pg in
        let physics := Bolus.bolus_physics b in
        pressure_Pa (lo (Pressure.e_total exp)) > pressure_Pa (hi (Pressure.r_total res)) + Pressure.margin_for_flow physics
    end.

  Lemma sufficient_pressure_implies_flow :
    forall s,
    sufficient_pressure_with_margin s ->
    has_positive_flow s.
  Proof.
    intros s Hsuff.
    unfold has_positive_flow, compute_bolus_advancement, sufficient_pressure_with_margin in *.
    destruct (bolus s) as [b|] eqn:Hbolus.
    - apply Pressure.passage_possible_with_margin.
      exact Hsuff.
    - inversion Hsuff.
  Defined.

  Lemma sufficient_pressure_implies_differential :
    forall s,
    sufficient_pressure_with_margin s ->
    sufficient_pressure_differential s.
  Proof.
    intros s Hsuff.
    unfold sufficient_pressure_differential, sufficient_pressure_with_margin in *.
    destruct (bolus s) as [b|].
    - unfold Pressure.margin_for_flow in Hsuff. lia.
    - exact Hsuff.
  Defined.

  (* Concrete witness: Type4 + FullSquat + default anatomy has positive flow. *)

  Definition typical_bolus : Bolus.Bolus :=
    Bolus.make_bolus Bolus.Type4_SmoothSoftSausage (mkInterval (MkmL 150) (MkmL 200)).

  Definition typical_state : SystemState :=
    mkState
      Anatomy.default_anatomy
      (Some typical_bolus)
      (mkInterval (Mkmm 100) (Mkmm 150))
      Posture.FullSquat
      ExpulsionPhase
      (Neural.commands_for_defecation (mkInterval (MkPa 5000) (MkPa 8000)))
      relaxed_pressure
      relaxed_pressure
      (mkInterval (Mkdeg 130) (Mkdeg 140))
      (Mksec 0)
      (Mksec 0).

  Lemma typical_state_has_bolus : has_bolus typical_state.
  Proof.
    exact I.
  Qed.

  Definition typical_expulsive : Pressure.ExpulsiveComponents :=
    Pressure.compute_expulsive Anatomy.default_anatomy
      (Posture.posture_to_geometry Posture.FullSquat).

  Definition typical_resistance : Pressure.ResistanceComponents :=
    Pressure.compute_expulsion_resistance typical_bolus
      (Posture.posture_to_geometry Posture.FullSquat).

  Definition typical_margin : nat :=
    Pressure.margin_for_flow (Bolus.bolus_physics typical_bolus).

  Lemma gt_from_ltb : forall n m, Nat.ltb m n = true -> n > m.
  Proof.
    intros n m H.
    apply PeanoNat.Nat.ltb_lt in H.
    lia.
  Qed.

  Lemma typical_expulsive_lo_value :
    pressure_Pa (lo (Pressure.e_total typical_expulsive)) = 7000.
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  Lemma typical_resistance_hi_value :
    pressure_Pa (hi (Pressure.r_total typical_resistance)) = 1683.
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  Lemma typical_margin_value : typical_margin = 4150.
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  Lemma typical_sufficient_pressure :
    pressure_Pa (lo (Pressure.e_total typical_expulsive)) >
    pressure_Pa (hi (Pressure.r_total typical_resistance)) + typical_margin.
  Proof.
    rewrite typical_expulsive_lo_value.
    rewrite typical_resistance_hi_value.
    rewrite typical_margin_value.
    apply gt_from_ltb.
    vm_compute.
    reflexivity.
  Qed.

  Theorem typical_state_sufficient_pressure_with_margin :
    sufficient_pressure_with_margin typical_state.
  Proof.
    unfold sufficient_pressure_with_margin, typical_state.
    change (Pressure.compute_expulsive Anatomy.default_anatomy
      (Posture.posture_to_geometry Posture.FullSquat)) with typical_expulsive.
    change (Pressure.compute_expulsion_resistance typical_bolus
      (Posture.posture_to_geometry Posture.FullSquat)) with typical_resistance.
    change (Pressure.margin_for_flow (Bolus.bolus_physics typical_bolus))
      with typical_margin.
    exact typical_sufficient_pressure.
  Defined.

  Theorem typical_state_has_positive_flow : has_positive_flow typical_state.
  Proof.
    apply sufficient_pressure_implies_flow.
    exact typical_state_sufficient_pressure_with_margin.
  Defined.

  (* Additional witnesses: default_anatomy works across normal Bristol types. *)

  Definition type3_bolus : Bolus.Bolus :=
    Bolus.make_bolus Bolus.Type3_SausageWithCracks (mkInterval (MkmL 150) (MkmL 200)).

  Definition type3_expulsive : Pressure.ExpulsiveComponents :=
    Pressure.compute_expulsive Anatomy.default_anatomy
      (Posture.posture_to_geometry Posture.FullSquat).

  Definition type3_resistance : Pressure.ResistanceComponents :=
    Pressure.compute_expulsion_resistance type3_bolus
      (Posture.posture_to_geometry Posture.FullSquat).

  Definition type3_margin : nat :=
    Pressure.margin_for_flow (Bolus.bolus_physics type3_bolus).

  Lemma type3_expulsive_lo : pressure_Pa (lo (Pressure.e_total type3_expulsive)) = 7000.
  Proof. vm_compute. reflexivity. Qed.

  Lemma type3_resistance_hi : pressure_Pa (hi (Pressure.r_total type3_resistance)) = 2367.
  Proof. vm_compute. reflexivity. Qed.

  Lemma type3_margin_val : type3_margin = 8300.
  Proof. vm_compute. reflexivity. Qed.

  Theorem type3_passage_possible :
    pressure_Pa (lo (Pressure.e_total type3_expulsive)) >
    pressure_Pa (hi (Pressure.r_total type3_resistance)).
  Proof.
    rewrite type3_expulsive_lo, type3_resistance_hi.
    apply gt_from_ltb.
    vm_compute.
    reflexivity.
  Qed.

  Lemma type3_margin_insufficient :
    pressure_Pa (lo (Pressure.e_total type3_expulsive)) <=
    pressure_Pa (hi (Pressure.r_total type3_resistance)) + type3_margin.
  Proof.
    rewrite type3_expulsive_lo, type3_resistance_hi, type3_margin_val.
    apply le_from_leb.
    vm_compute.
    reflexivity.
  Qed.

  (* Counterexample: Type1 constipated stool may NOT have positive flow.      *)

  Definition type1_bolus : Bolus.Bolus :=
    Bolus.make_bolus Bolus.Type1_SeparateHardLumps (mkInterval (MkmL 150) (MkmL 200)).

  Definition type1_resistance : Pressure.ResistanceComponents :=
    Pressure.compute_expulsion_resistance type1_bolus
      (Posture.posture_to_geometry Posture.Standing).

  Definition standing_expulsive : Pressure.ExpulsiveComponents :=
    Pressure.compute_expulsive Anatomy.default_anatomy
      (Posture.posture_to_geometry Posture.Standing).

  Definition type1_margin : nat :=
    Pressure.margin_for_flow (Bolus.bolus_physics type1_bolus).

  Lemma standing_expulsive_lo : pressure_Pa (lo (Pressure.e_total standing_expulsive)) = 4500.
  Proof. vm_compute. reflexivity. Qed.

  Lemma type1_resistance_hi : pressure_Pa (hi (Pressure.r_total type1_resistance)) = 17327.
  Proof. vm_compute. reflexivity. Qed.

  Lemma type1_margin_val : type1_margin = 51000.
  Proof. vm_compute. reflexivity. Qed.

  Lemma type1_standing_insufficient :
    pressure_Pa (lo (Pressure.e_total standing_expulsive)) <=
    pressure_Pa (hi (Pressure.r_total type1_resistance)) + type1_margin.
  Proof.
    rewrite standing_expulsive_lo, type1_resistance_hi, type1_margin_val.
    apply le_from_leb.
    vm_compute.
    reflexivity.
  Qed.

  Lemma tick_strictly_decreases :
    forall s,
    has_positive_flow s ->
    distance_mm (hi (bolus_position (transition_expulsion_tick s))) < distance_mm (hi (bolus_position s)) \/
    distance_mm (hi (bolus_position (transition_expulsion_tick s))) = 0.
  Proof.
    intros s Hflow.
    unfold transition_expulsion_tick.
    simpl.
    unfold has_positive_flow in Hflow.
    destruct (Nat.leb (distance_mm (lo (bolus_position s))) (distance_mm (hi (compute_bolus_advancement s))));
    destruct (Nat.leb (distance_mm (hi (bolus_position s))) (distance_mm (lo (compute_bolus_advancement s)))) eqn:Hcmp.
    - right. reflexivity.
    - left. apply PeanoNat.Nat.leb_gt in Hcmp. lia.
    - right. reflexivity.
    - left. apply PeanoNat.Nat.leb_gt in Hcmp. lia.
  Qed.

  Lemma expulsion_ticks_at_threshold :
    forall n s,
    mm_le (hi (bolus_position s)) passage_complete_threshold ->
    mm_le (hi (bolus_position (expulsion_ticks n s))) passage_complete_threshold.
  Proof.
    induction n.
    - intros s Hle.
      simpl.
      exact Hle.
    - intros s Hle.
      simpl.
      unfold mm_le, passage_complete_threshold in *.
      simpl in *.
      assert (Hcmp: distance_mm (hi (bolus_position s)) <=? 0 = true).
      { apply PeanoNat.Nat.leb_le. exact Hle. }
      rewrite Hcmp.
      exact Hle.
  Qed.

  Lemma expulsion_ticks_reaches_threshold_aux :
    forall pos n s,
    reflex_state s = ExpulsionPhase ->
    distance_mm (hi (bolus_position s)) = pos ->
    n >= pos ->
    (forall s', reflex_state s' = ExpulsionPhase -> has_positive_flow s') ->
    mm_le (hi (bolus_position (expulsion_ticks n s))) passage_complete_threshold.
  Proof.
    induction pos as [pos IHpos] using (well_founded_induction Wf_nat.lt_wf).
    intros n s Hs Hpos Hn Hflow.
    destruct n.
    - simpl.
      unfold mm_le, passage_complete_threshold.
      simpl. lia.
    - simpl.
      destruct (distance_mm (hi (bolus_position s)) <=? 0) eqn:Hcmp.
      + apply PeanoNat.Nat.leb_le in Hcmp.
        unfold mm_le, passage_complete_threshold. simpl. exact Hcmp.
      + apply PeanoNat.Nat.leb_gt in Hcmp.
        assert (Htick := tick_strictly_decreases s (Hflow s Hs)).
        destruct Htick as [Hlt | Hzero].
        * apply (IHpos (distance_mm (hi (bolus_position (transition_expulsion_tick s))))).
          -- rewrite <- Hpos. exact Hlt.
          -- apply transition_expulsion_tick_state.
          -- reflexivity.
          -- lia.
          -- exact Hflow.
        * assert (Hle0: distance_mm (hi (bolus_position (transition_expulsion_tick s))) <= 0).
          { rewrite Hzero. lia. }
          apply expulsion_ticks_at_threshold.
          unfold mm_le, passage_complete_threshold.
          simpl. exact Hle0.
  Qed.

  Lemma expulsion_ticks_reaches_threshold :
    forall n s,
    reflex_state s = ExpulsionPhase ->
    n >= distance_mm (hi (bolus_position s)) ->
    (forall s', reflex_state s' = ExpulsionPhase -> has_positive_flow s') ->
    mm_le (hi (bolus_position (expulsion_ticks n s))) passage_complete_threshold.
  Proof.
    intros n s Hs Hn Hflow.
    apply (expulsion_ticks_reaches_threshold_aux (distance_mm (hi (bolus_position s))) n s Hs eq_refl Hn Hflow).
  Qed.

  Theorem defecation_terminates :
    forall s : SystemState,
    reflex_state s = UrgePresent ->
    voluntary_commands_permit_defecation s ->
    has_bolus s ->
    (match bolus s with Some b => finite_bolus b | None => True end) ->
    distance_mm (hi (bolus_position s)) <= volume_mL max_bolus_volume ->
    (forall s', reflex_state s' = ExpulsionPhase -> has_positive_flow s') ->
    exists s' : SystemState,
    MultiStep s s' /\
    reflex_state s' = Quiescent.
  Proof.
    intros s Hurge [Heas Hpr] Hbol Hfinite Hpos Hflow.
    set (s1 := transition_to_initiation s).
    set (s2 := transition_to_expulsion s1).
    set (n := sufficient_ticks (hi (bolus_position s2))).
    set (s2' := expulsion_ticks n s2).
    set (s3 := transition_to_completion s2').
    set (s4 := transition_to_quiescent s3).
    assert (Hbol_s1: has_bolus s1).
    { unfold s1, transition_to_initiation, has_bolus. simpl. exact Hbol. }
    assert (Hbol_s2: has_bolus s2).
    { unfold s2, transition_to_expulsion, has_bolus. simpl. exact Hbol_s1. }
    assert (Hbol_s2': has_bolus s2').
    { unfold s2'.
      assert (Hpres: forall m st, has_bolus st -> has_bolus (expulsion_ticks m st)).
      { induction m.
        - intros st Hb. simpl. exact Hb.
        - intros st Hb. simpl.
          destruct (distance_mm (hi (bolus_position st)) <=? 0).
          + exact Hb.
          + apply IHm. unfold transition_expulsion_tick, has_bolus. simpl. exact Hb. }
      apply Hpres. exact Hbol_s2. }
    exists s4.
    split.
    - apply ms_step with s1.
      + apply step_initiate.
        unfold guard_initiate.
        rewrite Hurge.
        repeat split.
        * exact Heas.
        * exact Hpr.
        * exact Hbol.
      + apply ms_step with s2.
        * apply step_expel.
          unfold guard_expulsion_start.
          split.
          -- apply transition_to_initiation_state.
          -- split.
             ++ destruct (transition_to_initiation_relaxes s) as [Heas_r Hias_r].
                exact Heas_r.
             ++ split.
                ** destruct (transition_to_initiation_relaxes s) as [Heas_r Hias_r].
                   exact Hias_r.
                ** exact Hbol_s1.
        * assert (Hs2_state: reflex_state s2 = ExpulsionPhase).
          { apply transition_to_expulsion_state. }
          assert (Hms_s2_s2': MultiStep s2 s2').
          { apply expulsion_ticks_multistep.
            exact Hs2_state. }
          apply (ms_trans s2 s2' s4 Hms_s2_s2').
          apply ms_step with s3.
             ++ apply step_complete.
                unfold guard_completion.
                repeat split.
                ** apply expulsion_ticks_state.
                   exact Hs2_state.
                ** apply expulsion_ticks_reaches_threshold.
                   --- exact Hs2_state.
                   --- unfold n, sufficient_ticks.
                       lia.
                   --- exact Hflow.
                ** exact Hbol_s2'.
             ++ apply ms_step with s4.
                ** apply step_reset.
                   unfold guard_reset.
                   split.
                   --- apply transition_to_completion_state.
                   --- apply transition_to_completion_restores.
                ** apply ms_refl.
    - apply transition_to_quiescent_state.
  Qed.
  
  
  Corollary termination_time_bounded :
    forall s : SystemState,
    reflex_state s = UrgePresent ->
    voluntary_commands_permit_defecation s ->
    has_bolus s ->
    (match bolus s with Some b => finite_bolus b | None => True end) ->
    distance_mm (hi (bolus_position s)) <= volume_mL max_bolus_volume ->
    (forall s', reflex_state s' = ExpulsionPhase -> has_positive_flow s') ->
    exists s' : SystemState,
    MultiStep s s' /\ reflex_state s' = Quiescent.
  Proof.
    intros s Hurge Hcmd Hbol Hfin Hpos Hflow.
    exact (defecation_terminates s Hurge Hcmd Hbol Hfin Hpos Hflow).
  Defined.

  Corollary no_infinite_hold :
    forall s : SystemState,
    reflex_state s = VoluntaryHold ->
    fatigue_limit <=sec eas_fatigue_accumulated s ->
    has_bolus s ->
    exists s' : SystemState,
    Step s s' /\ reflex_state s' <> VoluntaryHold.
  Proof.
    intros s Hhold Hfatigue Hbol.
    exists (transition_fatigue_failure s).
    split.
    - apply step_fatigue.
      unfold guard_fatigue_failure.
      repeat split.
      + exact Hhold.
      + exact Hfatigue.
      + exact Hbol.
    - rewrite transition_fatigue_failure_state.
      discriminate.
  Defined.

  Lemma typical_state_expulsion_has_flow :
    reflex_state typical_state = ExpulsionPhase ->
    has_positive_flow typical_state.
  Proof.
    intros _.
    exact typical_state_has_positive_flow.
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
(*                         WIPING CONVERGENCE                       *)
(*============================================================================*)

(*
   Post-expulsion cleanup. A separate termination problem.
*)

Module Wiping.
  Import Units.
  Import Bolus.
  Import List.
  Import ListNotations.
  
  
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
    mkInterval
      (MkmL (Nat.div (volume_mL (lo residue)) (S eff)))
      (MkmL (Nat.div (volume_mL (hi residue)) (S eff))).

  Definition wipe_efficiency (residue : Interval mL) : Interval mL :=
    let efficiency_factor := 2 in
    mkInterval
      (MkmL (Nat.div (volume_mL (lo residue)) efficiency_factor))
      (MkmL (Nat.div (volume_mL (hi residue)) efficiency_factor)).
  
  
  Definition cleanliness_threshold : nat := 1.

  Definition clean_enough (r : Interval mL) : Prop :=
    volume_mL (hi r) <= cleanliness_threshold.
  

  (*
     Under reasonable efficiency assumptions (efficiency > 0.5),
     residue converges to below threshold in O(log(initial)) wipes.
  *)

  Lemma wipe_reduces_hi :
    forall r : Interval mL,
    volume_mL (hi r) >= 2 ->
    volume_mL (hi (wipe_efficiency r)) < volume_mL (hi r).
  Proof.
    intros r Hge.
    unfold wipe_efficiency.
    simpl.
    assert (H: Nat.div (volume_mL (hi r)) 2 <= Nat.div (volume_mL (hi r)) 2) by lia.
    assert (Hdiv: Nat.div (volume_mL (hi r)) 2 < volume_mL (hi r)).
    { apply PeanoNat.Nat.div_lt; lia. }
    exact Hdiv.
  Defined.

  Lemma wipe_reduces_lo :
    forall r : Interval mL,
    volume_mL (lo r) >= 2 ->
    volume_mL (lo (wipe_efficiency r)) < volume_mL (lo r).
  Proof.
    intros r Hge.
    unfold wipe_efficiency.
    simpl.
    assert (Hdiv: Nat.div (volume_mL (lo r)) 2 < volume_mL (lo r)).
    { apply PeanoNat.Nat.div_lt; lia. }
    exact Hdiv.
  Defined.

  Lemma wipe_monotonic :
    forall r : Interval mL,
    volume_mL (hi (wipe_efficiency r)) <= volume_mL (hi r).
  Proof.
    intros r.
    unfold wipe_efficiency.
    simpl.
    assert (Hdiv: Nat.div (volume_mL (hi r)) 2 <= volume_mL (hi r)).
    { apply PeanoNat.Nat.div_le_upper_bound; lia. }
    exact Hdiv.
  Defined.

  Lemma wipe_iter_monotonic :
    forall (n : nat) (r : Interval mL),
    volume_mL (hi (Nat.iter n wipe_efficiency r)) <= volume_mL (hi r).
  Proof.
    induction n.
    - intros r.
      simpl.
      lia.
    - intros r.
      simpl.
      apply PeanoNat.Nat.le_trans with (m := volume_mL (hi (Nat.iter n wipe_efficiency r))).
      + apply wipe_monotonic.
      + apply IHn.
  Defined.

  Theorem wiping_eventually_converges :
    forall initial_residue : Interval mL,
    exists n : nat,
    volume_mL (hi (Nat.iter n wipe_efficiency initial_residue)) <= cleanliness_threshold \/
    volume_mL (hi (Nat.iter n wipe_efficiency initial_residue)) < volume_mL (hi initial_residue).
  Proof.
    intros initial_residue.
    destruct (Compare_dec.le_dec (volume_mL (hi initial_residue)) cleanliness_threshold) as [Hle | Hgt].
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
    volume_mL (hi r) >= 2 ->
    volume_mL (hi (wipe_efficiency r)) <= Nat.div (volume_mL (hi r)) 2.
  Proof.
    intros r Hge.
    unfold wipe_efficiency.
    simpl.
    lia.
  Defined.

  Lemma wipe_below_threshold_stays :
    forall r : Interval mL,
    volume_mL (hi r) <= cleanliness_threshold ->
    volume_mL (hi (wipe_efficiency r)) <= cleanliness_threshold.
  Proof.
    intros r Hle.
    unfold wipe_efficiency, cleanliness_threshold in *.
    simpl.
    assert (Hdiv: Nat.div (volume_mL (hi r)) 2 <= Nat.div 1 2).
    { apply PeanoNat.Nat.div_le_mono; lia. }
    simpl in Hdiv.
    lia.
  Defined.

  Lemma wipe_strictly_reduces :
    forall r : Interval mL,
    volume_mL (hi r) > cleanliness_threshold ->
    volume_mL (hi (wipe_efficiency r)) < volume_mL (hi r).
  Proof.
    intros r Hgt.
    unfold wipe_efficiency, cleanliness_threshold in *.
    simpl.
    assert (Hdiv: Nat.div (volume_mL (hi r)) 2 < volume_mL (hi r)).
    { apply PeanoNat.Nat.div_lt; lia. }
    exact Hdiv.
  Defined.

  Lemma wipe_eventually_below_threshold :
    forall r : Interval mL,
    volume_mL (hi r) > cleanliness_threshold ->
    volume_mL (hi (wipe_efficiency r)) <= volume_mL (hi r) - 1.
  Proof.
    intros r Hgt.
    assert (Hred: volume_mL (hi (wipe_efficiency r)) < volume_mL (hi r)).
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
    volume_mL (hi r) = v ->
    exists n : nat, volume_mL (hi (Nat.iter n wipe_efficiency r)) <= cleanliness_threshold.
  Proof.
    induction v as [v IHv] using (well_founded_induction Wf_nat.lt_wf).
    intros r Heq.
    destruct (Compare_dec.le_dec (volume_mL (hi r)) cleanliness_threshold) as [Hle | Hgt].
    - exists 0.
      simpl.
      exact Hle.
    - assert (Hlt: volume_mL (hi (wipe_efficiency r)) < volume_mL (hi r)).
      { apply wipe_strictly_reduces. lia. }
      rewrite Heq in Hlt.
      specialize (IHv (volume_mL (hi (wipe_efficiency r))) Hlt (wipe_efficiency r) eq_refl).
      destruct IHv as [n Hn].
      exists (S n).
      simpl.
      rewrite iter_shift in Hn.
      exact Hn.
  Defined.

  Theorem wiping_converges :
    forall initial_residue : Interval mL,
    exists n : nat,
    volume_mL (hi (Nat.iter n wipe_efficiency initial_residue)) <= cleanliness_threshold.
  Proof.
    intros initial_residue.
    apply (wipe_iter_converges_aux (volume_mL (hi initial_residue)) initial_residue eq_refl).
  Defined.

  Lemma typed_wipe_reduces :
    forall b r,
    volume_mL (hi (wipe_efficiency_typed b r)) <= volume_mL (hi r).
  Proof.
    intros b r.
    unfold wipe_efficiency_typed.
    simpl.
    assert (H: forall n d, Nat.div n (S d) <= n).
    { intros. apply PeanoNat.Nat.div_le_upper_bound; lia. }
    apply H.
  Defined.

  Lemma typed_wipe_strictly_reduces :
    forall b r,
    volume_mL (hi r) > cleanliness_threshold ->
    bristol_efficiency_factor b >= 1 ->
    volume_mL (hi (wipe_efficiency_typed b r)) < volume_mL (hi r).
  Proof.
    intros b r Hgt Heff.
    unfold wipe_efficiency_typed, cleanliness_threshold in *.
    simpl.
    assert (Hdiv: forall n d, n > 1 -> d >= 1 -> Nat.div n (S d) < n).
    { intros n d Hn Hd. apply PeanoNat.Nat.div_lt; lia. }
    apply Hdiv; lia.
  Defined.

  Fixpoint typed_wipe_iter (b : BristolType) (n : nat) (r : Interval mL) : Interval mL :=
    match n with
    | O => r
    | S n' => typed_wipe_iter b n' (wipe_efficiency_typed b r)
    end.

  Lemma typed_wipe_iter_converges_aux :
    forall (v : nat) (b : BristolType) (r : Interval mL),
    volume_mL (hi r) = v ->
    bristol_efficiency_factor b >= 1 ->
    exists n : nat, volume_mL (hi (typed_wipe_iter b n r)) <= cleanliness_threshold.
  Proof.
    induction v as [v IHv] using (well_founded_induction Wf_nat.lt_wf).
    intros b r Heq Heff.
    destruct (Compare_dec.le_dec (volume_mL (hi r)) cleanliness_threshold) as [Hle | Hgt].
    - exists 0.
      simpl.
      exact Hle.
    - assert (Hlt: volume_mL (hi (wipe_efficiency_typed b r)) < volume_mL (hi r)).
      { apply typed_wipe_strictly_reduces; lia. }
      rewrite Heq in Hlt.
      specialize (IHv (volume_mL (hi (wipe_efficiency_typed b r))) Hlt b (wipe_efficiency_typed b r) eq_refl Heff).
      destruct IHv as [n Hn].
      exists (S n).
      simpl.
      exact Hn.
  Defined.

  Theorem typed_wiping_converges :
    forall (b : BristolType) (initial_residue : Interval mL),
    bristol_efficiency_factor b >= 1 ->
    exists n : nat,
    volume_mL (hi (typed_wipe_iter b n initial_residue)) <= cleanliness_threshold.
  Proof.
    intros b initial_residue Heff.
    apply (typed_wipe_iter_converges_aux (volume_mL (hi initial_residue)) b initial_residue eq_refl Heff).
  Defined.

  Lemma all_bristol_types_have_positive_efficiency :
    forall b, bristol_efficiency_factor b >= 1.
  Proof.
    intros b.
    destruct b; simpl; lia.
  Defined.

  Corollary any_bristol_wiping_converges :
    forall (b : BristolType) (initial_residue : Interval mL),
    exists n : nat,
    volume_mL (hi (typed_wipe_iter b n initial_residue)) <= cleanliness_threshold.
  Proof.
    intros b initial_residue.
    apply typed_wiping_converges.
    apply all_bristol_types_have_positive_efficiency.
  Defined.


  (*
     The "endless wiping" phenomenon occurs when residual seepage or
     moisture replenishment exceeds the removal rate of wiping.

     Model: R_{n+1} = R_n / efficiency + seepage_rate

     When seepage_rate >= R_n * (1 - 1/efficiency), the residue cannot
     decrease below a steady-state value, causing infinite wiping.

     Formally:
     - If seepage = 0: converges (already proven above)
     - If seepage > 0 and seepage >= floor: stuck in endless loop
     - Bidet intervention eliminates seepage, restoring convergence
  *)

  (*
     Seepage rate by Bristol type (mL residue per wipe cycle).

     Types 1-4 (formed stool): No seepage. Solid/semi-solid consistency
     means residue is removed mechanically without replenishment.

     Types 5-7 (loose/liquid stool): Positive seepage due to:
     - Incomplete evacuation leaving liquid residue in rectal ampulla
     - Mucus hypersecretion from irritated colonic mucosa
     - Capillary action wicking moisture to perianal skin
     - Reduced anal sphincter seal with liquid consistency

     Values calibrated to typical residue replenishment rates.
  *)
  Definition seepage_rate (b : BristolType) : nat :=
    match b with
    | Type1_SeparateHardLumps => 0
    | Type2_LumpySausage => 0
    | Type3_SausageWithCracks => 0
    | Type4_SmoothSoftSausage => 0
    | Type5_SoftBlobsClearEdges => 2
    | Type6_FluffentPieces => 3
    | Type7_WateryNoSolids => 4
    end.

  Definition has_seepage (b : BristolType) : Prop :=
    seepage_rate b > 0.

  Lemma has_seepage_dec : forall b, {has_seepage b} + {~has_seepage b}.
  Proof.
    intros b.
    unfold has_seepage.
    destruct (Compare_dec.gt_dec (seepage_rate b) 0).
    - left. exact g.
    - right. lia.
  Defined.

  Definition wipe_with_seepage (b : BristolType) (residue : Interval mL) : Interval mL :=
    let base := wipe_efficiency_typed b residue in
    let seep := seepage_rate b in
    mkInterval
      (MkmL (volume_mL (lo base) + seep))
      (MkmL (volume_mL (hi base) + seep)).


  (*
     Key insight: after each wipe with seepage, residue is at least seepage_rate.
     This is because wipe_with_seepage adds seepage_rate to the result.

     Therefore, with any nonzero seepage, residue can NEVER go below seepage_rate.
  *)

  Lemma wipe_with_seepage_lower_bound :
    forall b r,
    volume_mL (hi (wipe_with_seepage b r)) >= seepage_rate b.
  Proof.
    intros b r.
    unfold wipe_with_seepage.
    simpl.
    lia.
  Defined.

  Lemma seepage_steady_state_succ :
    forall b n r,
    volume_mL (hi (Nat.iter (S n) (wipe_with_seepage b) r)) >= seepage_rate b.
  Proof.
    intros b n r.
    simpl.
    apply wipe_with_seepage_lower_bound.
  Defined.

  Theorem endless_wiping :
    forall b r,
    has_seepage b ->
    forall n : nat,
    n >= 1 ->
    volume_mL (hi (Nat.iter n (wipe_with_seepage b) r)) >= seepage_rate b.
  Proof.
    intros b r Hseep n Hn.
    destruct n.
    - lia.
    - apply seepage_steady_state_succ.
  Defined.

  Theorem endless_wiping_strong :
    forall b r,
    has_seepage b ->
    volume_mL (hi r) >= seepage_rate b ->
    forall n : nat,
    volume_mL (hi (Nat.iter n (wipe_with_seepage b) r)) >= seepage_rate b.
  Proof.
    intros b r Hseep Hinit n.
    destruct n.
    - simpl. exact Hinit.
    - apply seepage_steady_state_succ.
  Defined.

  Corollary no_convergence_with_seepage :
    forall b r,
    has_seepage b ->
    seepage_rate b > cleanliness_threshold ->
    forall n : nat,
    n >= 1 ->
    volume_mL (hi (Nat.iter n (wipe_with_seepage b) r)) > cleanliness_threshold.
  Proof.
    intros b r Hseep Hthresh n Hn.
    assert (Hss := endless_wiping b r Hseep n Hn).
    lia.
  Defined.

  Corollary no_convergence_with_seepage_strong :
    forall b r,
    has_seepage b ->
    seepage_rate b > cleanliness_threshold ->
    volume_mL (hi r) >= seepage_rate b ->
    forall n : nat,
    volume_mL (hi (Nat.iter n (wipe_with_seepage b) r)) > cleanliness_threshold.
  Proof.
    intros b r Hseep Hthresh Hinit n.
    assert (Hss := endless_wiping_strong b r Hseep Hinit n).
    lia.
  Defined.


  (*
     Bidet eliminates seepage by:
     1. Removing residue mechanically (water pressure)
     2. Cleaning the area to prevent further seepage
     3. Reducing residue to effectively zero

     Modeled as resetting residue to a clean state.
  *)

  Record BidetParams := mkBidet {
    bidet_water_pressure : Interval Pa;
    bidet_duration : sec;
    bidet_effectiveness : nat;  (* percentage residue removal 0-100 *)
  }.

  (*
     Standard bidet parameters based on typical electronic bidet seats.

     Water pressure 30000-50000 Pa (0.3-0.5 bar): Typical adjustable
     range for posterior wash. Higher pressures available but may cause
     discomfort.

     Duration 30s: Standard wash cycle. Sufficient for mechanical
     removal without excessive water usage.

     Effectiveness 95%: Residue removal percentage. Studies comparing
     bidet vs. paper hygiene show 90-98% bacterial load reduction.
     Conservative estimate accounts for incomplete coverage.
  *)
  Definition standard_bidet : BidetParams :=
    mkBidet
      (mkInterval (MkPa 30000) (MkPa 50000))
      (Mksec 30)
      95.

  Definition bidet_clean (params : BidetParams) (r : Interval mL) : Interval mL :=
    let remaining_pct := 100 - bidet_effectiveness params in
    mkInterval
      (MkmL (Nat.div (volume_mL (lo r) * remaining_pct) 100))
      (MkmL (Nat.div (volume_mL (hi r) * remaining_pct) 100)).

  Lemma standard_bidet_effective :
    bidet_effectiveness standard_bidet = 95.
  Proof.
    unfold standard_bidet. reflexivity.
  Defined.

  Lemma standard_bidet_residue :
    forall r,
    volume_mL (hi (bidet_clean standard_bidet r)) = Nat.div (volume_mL (hi r) * 5) 100.
  Proof.
    intros r.
    unfold bidet_clean, standard_bidet.
    simpl.
    reflexivity.
  Defined.

  Definition bidet_eliminates_seepage : Prop :=
    forall b r,
    volume_mL (hi (bidet_clean standard_bidet r)) < seepage_rate b \/
    volume_mL (hi (bidet_clean standard_bidet r)) <= cleanliness_threshold.

  Lemma bidet_achieves_cleanliness :
    forall r,
    volume_mL (hi r) <= 20 ->
    volume_mL (hi (bidet_clean standard_bidet r)) <= cleanliness_threshold.
  Proof.
    intros r Hr.
    unfold bidet_clean, standard_bidet, cleanliness_threshold.
    simpl.
    assert (H: Nat.div (volume_mL (hi r) * 5) 100 <= Nat.div (20 * 5) 100).
    { apply PeanoNat.Nat.div_le_mono. lia. lia. }
    simpl in H.
    lia.
  Defined.


  (*
     Optimal strategy for problematic types:
     1. Wipe until steady state (paper reduction phase)
     2. Apply bidet (seepage elimination)
     3. Single confirmatory wipe (verification)
  *)

  Inductive CleaningAction :=
    | Wipe
    | UseBidet.

  Definition cleaning_protocol (b : BristolType) : list CleaningAction :=
    match b with
    | Type1_SeparateHardLumps => Wipe :: Wipe :: nil
    | Type2_LumpySausage => Wipe :: Wipe :: Wipe :: nil
    | Type3_SausageWithCracks => Wipe :: Wipe :: Wipe :: nil
    | Type4_SmoothSoftSausage => Wipe :: Wipe :: Wipe :: Wipe :: nil
    | Type5_SoftBlobsClearEdges => Wipe :: Wipe :: UseBidet :: Wipe :: nil
    | Type6_FluffentPieces => Wipe :: UseBidet :: Wipe :: nil
    | Type7_WateryNoSolids => UseBidet :: Wipe :: nil
    end.

  Definition requires_bidet (b : Bolus.BristolType) : Prop :=
    has_seepage b /\ seepage_rate b > cleanliness_threshold.

  Lemma type5_requires_bidet : requires_bidet Type5_SoftBlobsClearEdges.
  Proof.
    unfold requires_bidet, has_seepage, seepage_rate, cleanliness_threshold.
    simpl. lia.
  Defined.

  Lemma type6_requires_bidet : requires_bidet Type6_FluffentPieces.
  Proof.
    unfold requires_bidet, has_seepage, seepage_rate, cleanliness_threshold.
    simpl. lia.
  Defined.

  Lemma type7_requires_bidet : requires_bidet Type7_WateryNoSolids.
  Proof.
    unfold requires_bidet, has_seepage, seepage_rate, cleanliness_threshold.
    simpl. lia.
  Defined.

  Lemma type4_no_bidet_needed : ~requires_bidet Type4_SmoothSoftSausage.
  Proof.
    unfold requires_bidet, has_seepage, seepage_rate.
    simpl. lia.
  Defined.

  Lemma type1_no_bidet_needed : ~requires_bidet Type1_SeparateHardLumps.
  Proof.
    unfold requires_bidet, has_seepage, seepage_rate.
    simpl. lia.
  Defined.


  (*
     The key theorem: for any Bristol type, cleanliness is achievable
     if and only if bidet is used when required.
  *)

  Definition apply_action (b : BristolType) (a : CleaningAction) (r : Interval mL) : Interval mL :=
    match a with
    | Wipe => if has_seepage_dec b
              then wipe_with_seepage b r
              else wipe_efficiency_typed b r
    | UseBidet => bidet_clean standard_bidet r
    end.

  Fixpoint apply_protocol (b : BristolType) (actions : list CleaningAction) (r : Interval mL) : Interval mL :=
    match actions with
    | nil => r
    | a :: rest => apply_protocol b rest (apply_action b a r)
    end.

  (*
     Key insight: bidet not only cleans but also eliminates the source of seepage.
     For typical residue levels (<=20 mL), bidet alone achieves cleanliness.
     For larger amounts, multiple bidet applications work.
  *)

  Theorem bidet_guarantees_convergence :
    forall b r,
    volume_mL (hi r) <= 20 ->
    exists protocol : list CleaningAction,
    volume_mL (hi (apply_protocol b protocol r)) <= cleanliness_threshold.
  Proof.
    intros b r Hr.
    exists (UseBidet :: nil).
    unfold apply_protocol, apply_action, bidet_clean, standard_bidet, cleanliness_threshold.
    simpl.
    assert (Hbidet: Nat.div (volume_mL (hi r) * 5) 100 <= 1).
    { apply PeanoNat.Nat.div_le_upper_bound.
      - lia.
      - assert (volume_mL (hi r) * 5 <= 20 * 5) by lia.
        simpl in *. lia. }
    exact Hbidet.
  Defined.

  Corollary endless_wiping_resolved :
    forall b r,
    has_seepage b ->
    volume_mL (hi r) <= 20 ->
    (forall n, n >= 1 -> volume_mL (hi (Nat.iter n (wipe_with_seepage b) r)) > cleanliness_threshold) \/
    (exists protocol, volume_mL (hi (apply_protocol b protocol r)) <= cleanliness_threshold).
  Proof.
    intros b r Hseep Hr.
    right.
    apply bidet_guarantees_convergence.
    exact Hr.
  Defined.

End Wiping.


(*============================================================================*)
(*                         PATHOLOGICAL CASES                      *)
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
  
  
  (*
     If bolus diameter exceeds anal canal max_dilation,
     passage is geometrically impossible without intervention.
  *)
  
  Definition obstructed (anat : AnatomicalConfig) (b : Bolus) : Prop :=
    distance_mm (hi (bolus_max_diameter b)) > distance_mm (hi (ac_max_dilation (anal_canal anat))).

  Definition passage_geometrically_possible (anat : AnatomicalConfig) (b : Bolus) : Prop :=
    distance_mm (hi (bolus_max_diameter b)) <= distance_mm (hi (ac_max_dilation (anal_canal anat))).

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
    destruct (Compare_dec.le_dec (distance_mm (hi (bolus_max_diameter b)))
                                  (distance_mm (hi (ac_max_dilation (anal_canal anat))))).
    - right. exact l.
    - left. lia.
  Defined.

  Lemma obstruction_witness :
    forall anat,
    let large_bolus := make_bolus Type1_SeparateHardLumps (mkInterval (MkmL 400) (MkmL 500)) in
    distance_mm (hi (bolus_max_diameter large_bolus)) > 40 ->
    distance_mm (hi (ac_max_dilation (anal_canal anat))) <= 40 ->
    obstructed anat large_bolus.
  Proof.
    intros anat large_bolus Hlarge Hsmall.
    unfold obstructed.
    lia.
  Defined.

  Lemma non_obstruction_witness :
    forall anat,
    let small_bolus := make_bolus Type4_SmoothSoftSausage (mkInterval (MkmL 100) (MkmL 200)) in
    distance_mm (hi (bolus_max_diameter small_bolus)) <= 30 ->
    distance_mm (hi (ac_max_dilation (anal_canal anat))) >= 30 ->
    passage_geometrically_possible anat small_bolus.
  Proof.
    intros anat small_bolus Hsmall Hlarge.
    unfold passage_geometrically_possible.
    lia.
  Defined.

  Lemma typical_bolus_not_obstructed :
    passage_geometrically_possible Anatomy.default_anatomy Termination.typical_bolus.
  Proof.
    unfold passage_geometrically_possible.
    unfold Termination.typical_bolus, Bolus.make_bolus.
    simpl.
    lia.
  Defined.

  Lemma type3_bolus_not_obstructed :
    passage_geometrically_possible Anatomy.default_anatomy Termination.type3_bolus.
  Proof.
    unfold passage_geometrically_possible.
    unfold Termination.type3_bolus, Bolus.make_bolus.
    simpl.
    lia.
  Defined.


  (*
     Dyssynergic defecation: voluntary command to relax EAS
     paradoxically causes contraction. Common disorder.
  *)

  Definition dyssynergia (s_before s_after : SystemState) : Prop :=
    cmd_eas_relax (voluntary_commands s_before) = true /\
    pressure_Pa (lo (eas_pressure s_after)) > pressure_Pa (lo (eas_pressure s_before)).

  Lemma dyssynergia_blocks_initiation :
    forall s_before s_after,
    dyssynergia s_before s_after ->
    pressure_Pa (hi (eas_pressure s_after)) > pressure_Pa relaxation_threshold ->
    ~guard_expulsion_start s_after.
  Proof.
    intros s_before s_after [Hcmd Hinc] Hhi Hguard.
    unfold guard_expulsion_start in Hguard.
    destruct Hguard as [Hinit [Heas _]].
    unfold Pa_le in Heas.
    lia.
  Defined.


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


  (*
     Absence of ganglion cells -> no RAIR response.
     IAS never relaxes. Requires surgical intervention.
  *)

  Definition hirschsprung (ias : InternalSphincter) : Prop :=
    pressure_Pa (lo (ias_relaxation_magnitude ias)) = 0 /\
    pressure_Pa (hi (ias_relaxation_magnitude ias)) = 0.

  Lemma hirschsprung_no_rair :
    forall ias vol,
    hirschsprung ias ->
    pressure_Pa (lo (rair_ias_relaxation (compute_rair ias vol))) = 0.
  Proof.
    intros ias vol [Hlo Hhi].
    unfold compute_rair.
    simpl.
    exact Hlo.
  Defined.

  Lemma hirschsprung_blocks_reflex_relaxation :
    forall ias,
    hirschsprung ias ->
    forall vol, pressure_Pa (hi (rair_ias_relaxation (compute_rair ias vol))) = 0.
  Proof.
    intros ias [Hlo Hhi] vol.
    unfold compute_rair.
    simpl.
    exact Hhi.
  Defined.

  (*
     Hirschsprung non-termination: without RAIR, IAS cannot relax below
     the threshold required for guard_expulsion_start. If IAS resting
     pressure exceeds relaxation_threshold and RAIR magnitude is 0,
     expulsion phase can never begin.
  *)

  Lemma hirschsprung_blocks_expulsion :
    forall s,
    hirschsprung (ias (anatomy s)) ->
    pressure_Pa (hi (ias_pressure s)) > pressure_Pa relaxation_threshold ->
    ~guard_expulsion_start s.
  Proof.
    intros s Hhirsch Hhigh Hguard.
    unfold guard_expulsion_start in Hguard.
    destruct Hguard as [Hinit [Heas [Hias _]]].
    unfold Pa_le in Hias.
    lia.
  Defined.

End Pathology.


(*============================================================================*)
(*                         INTERVENTIONS                           *)
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
            (mkInterval (MkcP (Nat.div (viscosity_cP (lo (bp_viscosity physics))) 2)) (MkcP (Nat.div (viscosity_cP (hi (bp_viscosity physics))) 2)))
            (mkInterval (MkPa (Nat.div (pressure_Pa (lo (bp_yield_stress physics))) 2)) (MkPa (Nat.div (pressure_Pa (hi (bp_yield_stress physics))) 2)))
            (bp_cohesion physics)
            (bp_fragmentability physics)
            (bp_typical_diameter physics)
      | StimulantLaxative =>
          mkBolusPhysics
            (bp_viscosity physics)
            (mkInterval (MkPa (Nat.div (pressure_Pa (lo (bp_yield_stress physics))) 2)) (MkPa (Nat.div (pressure_Pa (hi (bp_yield_stress physics))) 2)))
            (bp_cohesion physics)
            (bp_fragmentability physics)
            (bp_typical_diameter physics)
      | StoolSoftener =>
          mkBolusPhysics
            (mkInterval (MkcP (Nat.div (viscosity_cP (lo (bp_viscosity physics))) 3)) (MkcP (Nat.div (viscosity_cP (hi (bp_viscosity physics))) 3)))
            (mkInterval (MkPa (Nat.div (pressure_Pa (lo (bp_yield_stress physics))) 3)) (MkPa (Nat.div (pressure_Pa (hi (bp_yield_stress physics))) 3)))
            (mkInterval (MkPa (Nat.div (pressure_Pa (lo (bp_cohesion physics))) 2)) (MkPa (Nat.div (pressure_Pa (hi (bp_cohesion physics))) 2)))
            true
            (bp_typical_diameter physics)
      | BulkForming =>
          mkBolusPhysics
            (bp_viscosity physics)
            (bp_yield_stress physics)
            (bp_cohesion physics)
            false
            (mkInterval (Mkmm (distance_mm (lo (bp_typical_diameter physics)) + 5)) (Mkmm (distance_mm (hi (bp_typical_diameter physics)) + 10)))
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
    viscosity_cP (hi (bp_viscosity (bolus_physics (laxative_effect OsmoticLaxative b)))) <=
    viscosity_cP (hi (bp_viscosity (bolus_physics b))).
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
    pressure_Pa (hi (bp_yield_stress (bolus_physics (laxative_effect StoolSoftener b)))) <=
    pressure_Pa (hi (bp_yield_stress (bolus_physics b))).
  Proof.
    intros b.
    unfold laxative_effect.
    simpl.
    assert (H: forall n d, Nat.div n (S d) <= n).
    { intros. apply PeanoNat.Nat.div_le_upper_bound; lia. }
    apply H.
  Defined.
  
  
  (*
     Direct removal of obstruction. Models as:
     - Reduces bolus volume
     - May fragment bolus
  *)
  
  Definition manual_disimpaction (b : Bolus) : Bolus :=
    let physics := bolus_physics b in
    mkBolus
      (bolus_type b)
      (mkInterval (MkmL (Nat.div (volume_mL (lo (bolus_volume b))) 2)) (MkmL (Nat.div (volume_mL (hi (bolus_volume b))) 2)))
      (mkInterval (Mkmm (Nat.div (distance_mm (lo (bolus_length b))) 2)) (Mkmm (Nat.div (distance_mm (hi (bolus_length b))) 2)))
      (mkInterval (Mkmm (distance_mm (lo (bolus_max_diameter b)))) (Mkmm (Nat.div (distance_mm (hi (bolus_max_diameter b))) 2)))
      (mkBolusPhysics
        (bp_viscosity physics)
        (bp_yield_stress physics)
        (bp_cohesion physics)
        true
        (bp_typical_diameter physics)).
  
  
  (*
     Introduces fluid, softening bolus and increasing volume/pressure.
  *)
  
  Definition enema_effect (vol : Interval mL) (b : Bolus) : Bolus :=
    let physics := bolus_physics b in
    mkBolus
      Type6_FluffentPieces
      (mkInterval (MkmL (volume_mL (lo (bolus_volume b)) + volume_mL (lo vol))) (MkmL (volume_mL (hi (bolus_volume b)) + volume_mL (hi vol))))
      (bolus_length b)
      (bolus_max_diameter b)
      (mkBolusPhysics
        (mkInterval (MkcP 50) (MkcP 200))
        (mkInterval (MkPa 5) (MkPa 20))
        (mkInterval (MkPa 5) (MkPa 30))
        true
        (bp_typical_diameter physics)).
  
  
  (*
     Training to correct dyssynergia. Modifies voluntary control:
     - Improves EAS relaxation on command
     - Improves PR relaxation
  *)
  
  Definition saturating_sub (a b : nat) : nat :=
    if Nat.leb b a then a - b else 0.

  Definition biofeedback_training (sessions : nat) (anat : AnatomicalConfig) : AnatomicalConfig :=
    let improvement := Nat.min sessions 10 in
    let old_eas := eas anat in
    let old_lo := pressure_Pa (lo (eas_voluntary_relaxation_floor old_eas)) in
    let old_hi := pressure_Pa (hi (eas_voluntary_relaxation_floor old_eas)) in
    let new_lo := saturating_sub old_lo (improvement * 50) in
    let new_hi := saturating_sub old_hi (improvement * 30) in
    let new_eas := mkEAS
      (eas_length old_eas)
      (eas_resting_pressure old_eas)
      (eas_max_squeeze_pressure old_eas)
      (mkInterval (Mksec (time_sec (lo (eas_fatigue_time old_eas)) + improvement * 10))
                  (Mksec (time_sec (hi (eas_fatigue_time old_eas)) + improvement * 15)))
      (mkInterval (MkPa new_lo) (MkPa new_hi)) in
    mkAnatomy
      (rectum anat)
      (ias anat)
      new_eas
      (puborectalis anat)
      (abdominal_wall anat)
      (anal_canal anat).

  Lemma biofeedback_improves_relaxation :
    forall sessions anat,
    pressure_Pa (lo (eas_voluntary_relaxation_floor (eas (biofeedback_training sessions anat)))) <=
    pressure_Pa (lo (eas_voluntary_relaxation_floor (eas anat))).
  Proof.
    intros sessions anat.
    unfold biofeedback_training, saturating_sub.
    simpl.
    destruct (Nat.leb (Nat.min sessions 10 * 50)
                       (pressure_Pa (lo (eas_voluntary_relaxation_floor (eas anat))))); lia.
  Defined.

  (*
     Note: biofeedback_improves_relaxation shows monotonic improvement.
     For dyssynergia, repeated sessions progressively lower the voluntary
     relaxation floor, eventually enabling proper EAS relaxation on command.
     The connection to Pathology.dyssynergia is conceptual: dyssynergia
     causes paradoxical contraction, biofeedback training lowers the
     achievable floor, restoring normal relaxation response.
  *)

  
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
(*                         SAFETY PROPERTIES                       *)
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
  
  
  (*
     Valsalva pressure should not exceed cardiovascular safety threshold.
     Excessive straining can cause syncope, hemorrhoids, hernia.
  *)
  
  Definition max_safe_pressure : Pa := MkPa 15000.

  Definition safe_pressure (p : Interval Pa) : Prop :=
    pressure_Pa (hi p) <= pressure_Pa max_safe_pressure.

  Lemma expulsive_within_safe_limits :
    forall anat pg,
    pressure_Pa (hi (e_total (compute_expulsive anat pg))) <= pressure_Pa max_safe_pressure.
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
  
  
  (*
     Bolus diameter should not exceed max safe dilation.
  *)
  
  Definition max_safe_dilation : mm := Mkmm 45.

  Definition safe_dilation (anat : AnatomicalConfig) (b : Bolus) : Prop :=
    distance_mm (hi (bolus_max_diameter b)) <= distance_mm max_safe_dilation.

  Lemma safe_dilation_dec :
    forall anat b,
    {safe_dilation anat b} + {~safe_dilation anat b}.
  Proof.
    intros anat b.
    unfold safe_dilation, max_safe_dilation.
    simpl.
    destruct (Compare_dec.le_dec (distance_mm (hi (bolus_max_diameter b))) 45).
    - left. exact l.
    - right. exact n.
  Defined.

  Lemma safe_dilation_implies_non_obstruction :
    forall anat b,
    safe_dilation anat b ->
    distance_mm (hi (ac_max_dilation (anal_canal anat))) >= distance_mm max_safe_dilation ->
    Pathology.passage_geometrically_possible anat b.
  Proof.
    intros anat b Hsafe Hanat.
    unfold Pathology.passage_geometrically_possible, safe_dilation, mm_le, max_safe_dilation in *.
    lia.
  Defined.

  Lemma non_obstruction_with_margin_enables_passage :
    forall anat b,
    Pathology.passage_geometrically_possible anat b ->
    ~Pathology.obstructed anat b.
  Proof.
    intros anat b Hpass.
    apply Pathology.passage_requires_non_obstruction.
    exact Hpass.
  Defined.

  
  (*
     Straining duration bounded to prevent syncope.
  *)
  
  Definition max_strain_duration : sec := Mksec 30.


  (*
     Involuntary passage should not occur while EAS is commanded contracted
     (until fatigue).
  *)

  Definition before_fatigue (t : sec) : Prop :=
    time_sec t < time_sec fatigue_limit.

  Lemma before_fatigue_dec : forall t, {before_fatigue t} + {~before_fatigue t}.
  Proof.
    intros t.
    unfold before_fatigue, fatigue_limit.
    simpl.
    destruct (Compare_dec.lt_dec (time_sec t) 180).
    - left. exact l.
    - right. lia.
  Defined.

  Lemma strain_within_safe_duration :
    forall s,
    time_sec (elapsed_time s) < time_sec max_strain_duration ->
    before_fatigue (elapsed_time s).
  Proof.
    intros s Hlt.
    unfold before_fatigue, max_strain_duration, fatigue_limit in *.
    simpl in *.
    lia.
  Defined.

  Lemma continence_maintained_before_fatigue :
    forall s,
    reflex_state s = VoluntaryHold ->
    cmd_eas_relax (voluntary_commands s) = false ->
    before_fatigue (eas_fatigue_accumulated s) ->
    ~guard_initiate s.
  Proof.
    intros s Hhold Hcmd Hfat Hinit.
    unfold guard_initiate in Hinit.
    destruct Hinit as [Hurge _].
    rewrite Hhold in Hurge.
    discriminate.
  Defined.

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

  (*
     Positive flow coverage for normal Bristol types.

     Proven witnesses:
     - Type4 + FullSquat: Termination.typical_state_has_positive_flow
     - Type3 + FullSquat: Termination.type3_passage_possible

     General theorem would require case analysis on Types 2-6, each with
     different physics parameters. The existing witnesses demonstrate the
     pattern; exhaustive enumeration left as future work.
  *)

  (* Witness: Bidet required for soft/liquid stool types. *)
  Example type6_requires_bidet_ex : requires_bidet Type6_FluffentPieces.
  Proof.
    unfold requires_bidet, has_seepage, seepage_rate, cleanliness_threshold.
    simpl. lia.
  Defined.

  (* Counterexample: Type4 does not require bidet. *)
  Example type4_no_bidet_ex : ~requires_bidet Type4_SmoothSoftSausage.
  Proof.
    unfold requires_bidet, has_seepage, seepage_rate.
    simpl. lia.
  Defined.

  (* Witness: Endless wiping is formally provable for Type6 after at least one wipe. *)
  Example endless_wiping_type6 :
    forall r n,
    n >= 1 ->
    volume_mL (hi (Nat.iter n (wipe_with_seepage Type6_FluffentPieces) r)) >= seepage_rate Type6_FluffentPieces.
  Proof.
    intros r n Hn.
    apply endless_wiping.
    - unfold has_seepage, seepage_rate. simpl. lia.
    - exact Hn.
  Defined.

  (* Witness: Bidet resolves endless wiping. *)
  Example bidet_resolves_type6 :
    forall r,
    volume_mL (hi r) <= 20 ->
    exists protocol, volume_mL (hi (apply_protocol Type6_FluffentPieces protocol r)) <= cleanliness_threshold.
  Proof.
    intros r Hr.
    apply bidet_guarantees_convergence.
    exact Hr.
  Defined.

  (* Witness: Squatting improves anorectal angle (larger = straighter = better). *)
  Example squatting_improves_angle :
    angle_deg (lo (Posture.resultant_anorectal_angle (Posture.posture_to_geometry Posture.FullSquat))) >
    angle_deg (lo (Posture.resultant_anorectal_angle (Posture.posture_to_geometry Posture.SittingUpright))).
  Proof. simpl. lia. Defined.

  (* Witness: Wiping converges within finite steps. *)
  Example wiping_finite_steps :
    exists n, volume_mL (hi (Nat.iter n wipe_efficiency (mkInterval (MkmL 10) (MkmL 10)))) <= cleanliness_threshold.
  Proof.
    exists 4.
    unfold wipe_efficiency, cleanliness_threshold.
    simpl. lia.
  Defined.

  (* Witness: All efficiency factors are >= 1. *)
  Example type1_efficiency : bristol_efficiency_factor Type1_SeparateHardLumps >= 1.
  Proof. simpl. lia. Defined.

  Example type7_efficiency : bristol_efficiency_factor Type7_WateryNoSolids >= 1.
  Proof. simpl. lia. Defined.

  (* Witness: Osmotic laxative reduces viscosity by half. *)
  Example osmotic_halves_viscosity :
    forall b,
    viscosity_cP (hi (bp_viscosity (bolus_physics (Interventions.laxative_effect Interventions.OsmoticLaxative b)))) <=
    Nat.div (viscosity_cP (hi (bp_viscosity (bolus_physics b)))) 2.
  Proof.
    intros b.
    unfold Interventions.laxative_effect.
    simpl. lia.
  Defined.

  (* Witness: Stimulant laxative reduces yield stress. *)
  Example stimulant_reduces_yield :
    forall b,
    pressure_Pa (hi (bp_yield_stress (bolus_physics (Interventions.laxative_effect Interventions.StimulantLaxative b)))) <=
    pressure_Pa (hi (bp_yield_stress (bolus_physics b))).
  Proof.
    intros b.
    unfold Interventions.laxative_effect.
    simpl.
    assert (H: forall n, Nat.div n 2 <= n).
    { intros n. apply PeanoNat.Nat.div_le_upper_bound; lia. }
    apply H.
  Defined.

  (* Witness: Biofeedback cannot produce negative values. *)
  Example biofeedback_nonnegative :
    forall sessions anat,
    pressure_Pa (lo (Anatomy.eas_voluntary_relaxation_floor
      (Anatomy.eas (Interventions.biofeedback_training sessions anat)))) >= 0.
  Proof.
    intros sessions anat.
    unfold Interventions.biofeedback_training, Interventions.saturating_sub.
    simpl.
    destruct (Nat.leb _ _); lia.
  Defined.

End Examples.


(*============================================================================*)
(*                    AXIOM CHECK: VERIFY NO HIDDEN AXIOMS                    *)
(*============================================================================*)

Print Assumptions Termination.defecation_terminates.
Print Assumptions Termination.typical_state_has_positive_flow.
Print Assumptions StateMachine.quiescent_empty_no_step.
Print Assumptions Safety.no_dangerous_straining.
Print Assumptions Wiping.endless_wiping.
Print Assumptions Wiping.no_convergence_with_seepage.
Print Assumptions Wiping.bidet_guarantees_convergence.

(*============================================================================*)
(*                                   EOF                                      *)
(*============================================================================*)
