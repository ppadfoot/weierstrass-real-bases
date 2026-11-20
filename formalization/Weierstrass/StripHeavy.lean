module

public import Weierstrass.StripGeometry
public import Weierstrass.SeedOverlap

/-! # Averaging actual reanchored full occupations after simultaneous physical and stable retention -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Weierstrass.StripProof
open CriticalRay

local instance heavyPhaseMeasurable (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance heavyPhaseBorel (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

theorem real_prod_sections {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {S : Set (X × Y)} (mS : MeasurableSet S) :
    (μ.prod ν).real S = ∫ x, ν.real (Prod.mk x ⁻¹' S) ∂μ := by
  simp only [measureReal_def]
  rw [Measure.prod_apply mS,integral_toReal (measurable_measure_prodMk_left mS).aemeasurable
    (ae_of_all _ fun _ => measure_lt_top _ _)]

def centeredHeavy (b g : ℝ) (p : RayParameters) (z : PhaseTorus) (T A r h : ℝ) :=
  stableLaw.real {x | ENNReal.ofReal (r^h) < rayOccupation b g p (z+transverseOrbit b p.2 x) T A r}

theorem measurable_centeredHeavy (b g : ℝ) (p : RayParameters) (T A r h : ℝ) :
    Measurable (fun z => centeredHeavy b g p z T A r h) := by
  let E := {v : PhaseTorus × ℝ | ENNReal.ofReal (r^h) <
    rayOccupation b g p (v.1+transverseOrbit b p.2 v.2) T A r}
  have mE : MeasurableSet E := measurableSet_lt measurable_const ((measurable_rayOccupation _ _ _ _ _ _).comp
    (measurable_fst.add ((measurable_transverseOrbit _ _).comp measurable_snd)))
  exact ENNReal.measurable_toReal.comp (measurable_measure_prodMk_left (ν := stableLaw) mE)

theorem haar_centeredHeavy {B : ℂ} (g : ℝ) (p : RayParameters) (e : ℤ → ℝ)
    (ρ q T A r h : ℝ) (ω : PhaseTorus) (tp : ∀ x, transverseOrbit ‖B‖ p.2 x ∈ complexPhaseGroup B)
    (te : ∀ x, transverseOrbit ρ e x ∈ complexPhaseGroup B) :
    (complexPhaseHaar B).real {z : complexPhaseGroup B | ENNReal.ofReal (r^h) <
      rayOccupation ‖B‖ g p (ω+z.val) T A r} =
    ∫ z : complexPhaseGroup B, ∫ u, centeredHeavy ‖B‖ g p ((ω+z.val)+transverseOrbit ρ e (q*u)) T A r h
      ∂stableLaw ∂complexPhaseHaar B := by
  let H := fun v : complexPhaseGroup B × ℝ =>
    centeredHeavy ‖B‖ g p ((ω+v.1.val)+transverseOrbit ρ e (q*v.2)) T A r h
  have mH : Measurable H := (measurable_centeredHeavy _ _ _ _ _ _ _).comp
    ((measurable_const.add (continuous_subtype_val.measurable.comp measurable_fst)).add
    ((measurable_transverseOrbit _ _).comp (measurable_const.mul measurable_snd)))
  have hi : Integrable H ((complexPhaseHaar B).prod stableLaw) :=
    (integrable_const (1:ℝ)).mono' mH.aestronglyMeasurable (ae_of_all _ fun v => by
      rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ H v from measureReal_nonneg)]
      exact (measureReal_mono (μ := stableLaw) (subset_univ _)).trans (by simp))
  change _ = ∫ z, ∫ u, H (z,u) ∂stableLaw ∂complexPhaseHaar B
  rw [← integral_prod H hi,integral_prod_symm H hi]
  have each (u : ℝ) : (∫ z, H (z,u) ∂complexPhaseHaar B) =
      (complexPhaseHaar B).real {z : complexPhaseGroup B | ENNReal.ofReal (r^h) <
      rayOccupation ‖B‖ g p (ω+z.val) T A r} := by
    have hh := congrArg ENNReal.toReal (RaySeed.heavyAt_mass (complexPhaseHaar B) g ρ p e ω T A r h
      (q*u) tp (te _))
    rw [← measureReal_def,real_prod_sections _ _ (RaySeed.heavyAt_meas _ _ _ _ _ _ _ _ _ _)] at hh
    exact hh
  simp_rw [each]
  simp

private theorem heavy_target_meas (μ : Measure ℝ) [IsFiniteMeasure μ] (R τ₀ : ℝ) :
    MeasurableSet {x | τ₀ < μ.real (Icc (x-R) (x+R))} := by
  let E := {v : ℝ × ℝ | v.1-R ≤ v.2 ∧ v.2 ≤ v.1+R}
  have mE : MeasurableSet E := (measurableSet_le (measurable_fst.sub_const _) measurable_snd).inter
    (measurableSet_le measurable_snd (measurable_fst.add_const _))
  exact measurableSet_lt measurable_const (ENNReal.measurable_toReal.comp (measurable_measure_prodMk_left (ν := μ) mE))

set_option maxHeartbeats 1100000 in
theorem centeredHeavy_le {b g T A r h : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1)
    (hbg : 1 < b*g) (hT : 0 < T) (hr : 0 < r) {p : RayParameters}
    (hc : ∀ j, |p.1 j| ≤ 1) (hd : ∀ j, |p.2 j| ≤ 1) (z : PhaseTorus) :
    centeredHeavy b g p z T A r h ≤ (1+2*T)*heavyMass ((physicalLaw T).map (circleRay b g p.1 p.2 z))
      (A*r) (r^h/(1+2*T)) := by
  let := physicalLaw_probability hT
  let F := circleRay b g p.1 p.2 z
  let ν := (physicalLaw T).map F
  let E := {x | ENNReal.ofReal (r^h) < rayOccupation b g p (z+transverseOrbit b p.2 x) T A r}
  let G := {y | r^h/(1+2*T) < ν.real (Icc (y-A*r) (y+A*r))}
  have mF : Measurable F := measurable_ray_time b g p z
  have mG : MeasurableSet G := heavy_target_meas ν _ _
  have P : 0 < 1+2*T := by linarith
  have cover : E ∩ Icc 0 1 ⊆ (F ⁻¹' G) ∩ RaySeed.sampleInterval T := by
    rintro x ⟨hx,hI⟩
    refine ⟨?_,⟨by linarith [hI.1],by linarith [hI.2]⟩⟩
    have hh := lt_of_lt_of_le hx (RaySeed.reanchor_dominates hb hg hg1 hbg hc hd z T A r x hI)
    rw [physical_full_mass hT] at hh
    change ENNReal.ofReal (r^h) < ENNReal.ofReal (1+2*T)*ν (Icc (F x-A*r) (F x+A*r)) at hh
    rw [← ofReal_measureReal (measure_ne_top _ _),← ENNReal.ofReal_mul P.le] at hh
    apply (div_lt_iff₀ P).mpr
    simpa only [mul_comm] using (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.rpow_pos_of_pos hr h).le).mp hh
  have mon := measure_mono (μ := volume) cover
  rw [← Measure.restrict_apply' (show MeasurableSet (RaySeed.sampleInterval T) from measurableSet_Icc),
    ← Measure.map_apply mF mG] at mon
  change volume (E ∩ Icc 0 1) ≤ RaySeed.sampledLaw F T G at mon
  rw [physical_full_mass hT] at mon
  change stableLaw.real E ≤ _
  change (volume.restrict (Icc 0 1) E).toReal ≤ _
  rw [Measure.restrict_apply' measurableSet_Icc]
  have rbound := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) mon
  change _ ≤ (1+2*T)*(((physicalLaw T).map F) G).toReal
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal P.le] using rbound


theorem measurable_raw_collision {κ : Measure ℝ} [IsFiniteMeasure κ] {F : ℝ → ℝ → ℝ}
    (mF : Measurable (fun p : ℝ × ℝ => F p.1 p.2)) (R : ℝ) :
    Measurable (fun u => Weierstrass.collision (κ.map (F u)) R) := by
  let E := {v : ℝ × (ℝ × ℝ) | |F v.1 v.2.1-F v.1 v.2.2| ≤ R}
  have mE : MeasurableSet E := measurableSet_le ((mF.comp (measurable_fst.prodMk
    (measurable_fst.comp measurable_snd))).sub (mF.comp (measurable_fst.prodMk
    (measurable_snd.comp measurable_snd)))).abs measurable_const
  have mS : MeasurableSet {p : ℝ × ℝ | |p.1-p.2| ≤ R} :=
    measurableSet_le (measurable_fst.sub measurable_snd).abs measurable_const
  have eq (u : ℝ) : Weierstrass.collision (κ.map (F u)) R = (κ.prod κ).real (Prod.mk u ⁻¹' E) := by
    have mu : Measurable (F u) := measurable_time_slice F mF u
    unfold Weierstrass.collision
    rw [Measure.map_prod_map _ _ mu mu,map_measureReal_apply (mu.prodMap mu) mS]
    rfl
  simp_rw [eq]
  exact ENNReal.measurable_toReal.comp (measurable_measure_prodMk_left mE)

private theorem measurable_family {X Y Z G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [MeasurableSpace G] (F : Z → Y → G)
    (hf : Measurable (fun v : Z × Y => F v.1 v.2)) (W : X → Z) (mW : Measurable W) :
    Measurable (fun v : X × Y => F (W v.1) v.2) :=
  hf.comp ((mW.comp measurable_fst).prodMk measurable_snd)

set_option maxHeartbeats 1200000 in
theorem integrated_retention {b g T A r h q ρ : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1)
    (hbg : 1 < b*g) (hT : 0 < T) (hA : 0 < A) (hr : 0 < r) {p : RayParameters}
    (hc : ∀ j, |p.1 j| ≤ 1) (hd : ∀ j, |p.2 j| ≤ 1) (e : ℤ → ℝ) (z : PhaseTorus)
    (Q U : Set ℝ) (mU : MeasurableSet U) {M cost : ℝ} (hM : 1 < M)
    (est : ∫ u in U, Weierstrass.collision (((physicalLaw T).restrict Q).map
      (circleRay b g p.1 p.2 (z+transverseOrbit ρ e (q*u)))) (A*r) ∂stableLaw ≤ cost) :
    (∫ u, centeredHeavy b g p (z+transverseOrbit ρ e (q*u)) T A r h ∂stableLaw) ≤
      stableLaw.real Uᶜ+(1+2*T)*((1-(physicalLaw T).real Q)+3/M+
        (M/(r^h/(1+2*T)))*cost) := by
  let := physicalLaw_probability hT
  let W := fun u => z+transverseOrbit ρ e (q*u)
  let F := fun u => circleRay b g p.1 p.2 (W u)
  let H := fun u => centeredHeavy b g p (W u) T A r h
  let κ := physicalLaw T
  let C := fun u => Weierstrass.collision ((κ.restrict Q).map (F u)) (A*r)
  let D := 1-κ.real Q+3/M
  let K := M/(r^h/(1+2*T))
  have P : 0 < 1+2*T := by linarith
  have KP : 0 ≤ K := (div_pos (zero_lt_one.trans hM) (div_pos (Real.rpow_pos_of_pos hr _) P)).le
  have mW : Measurable W := (measurable_const (a := z)).add ((measurable_transverseOrbit ρ e).comp ((measurable_const (a := q)).mul measurable_id))
  have mF : Measurable (fun v : ℝ × ℝ => F v.1 v.2) :=
    measurable_family (circleRay b g p.1 p.2) (measurable_circleRay b g p.1 p.2) W mW
  have mFu (u : ℝ) : Measurable (F u) := measurable_ray_time b g p (W u)
  have mH : Measurable H := (measurable_centeredHeavy b g p T A r h).comp mW
  have bH (u : ℝ) : 0 ≤ H u ∧ H u ≤ 1 := ⟨measureReal_nonneg,measureReal_le_one⟩
  have hi : Integrable H stableLaw := (integrable_const (1:ℝ)).mono' mH.aestronglyMeasurable
    (ae_of_all _ fun u => by rw [Real.norm_eq_abs,abs_of_nonneg (bH _).1]; exact (bH u).2)
  have Cint : Integrable C (stableLaw.restrict U) := by
    apply (integrable_const (1:ℝ)).mono' (measurable_raw_collision (κ := κ.restrict Q) mF (A*r)).aestronglyMeasurable
    filter_upwards [] with u
    let η := (κ.restrict Q).map (F u)
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ C u from measureReal_nonneg)]
    apply (measureReal_mono (μ := η.prod η) (subset_univ _)).trans
    rw [← univ_prod_univ,measureReal_prod_prod]
    have bd : η.real univ ≤ 1 := by
      rw [map_measureReal_apply (mFu u) MeasurableSet.univ,preimage_univ,measureReal_restrict_apply_univ]
      exact measureReal_le_one
    simpa using mul_le_mul bd bd measureReal_nonneg zero_le_one
  have point (u : ℝ) : H u ≤ (1+2*T)*(D+K*C u) := by
    let ν := κ.map (F u)
    let η := (κ.restrict Q).map (F u)
    let : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (mFu u).aemeasurable
    have cmp : η ≤ ν := Measure.map_mono Measure.restrict_le_self (mFu u)
    have hfull := fullBallFromRetainedCollisions ν η cmp (mul_pos hA hr) (div_pos (Real.rpow_pos_of_pos hr h) P) hM
    have mass : η.real univ = κ.real Q := by
      rw [map_measureReal_apply (mFu u) MeasurableSet.univ,preimage_univ,measureReal_restrict_apply_univ]
    rw [mass] at hfull
    exact (centeredHeavy_le hb hg hg1 hbg hT hr hc hd (W u)).trans (mul_le_mul_of_nonneg_left hfull P.le)
  have hcst : 0 ≤ D := add_nonneg (sub_nonneg.mpr measureReal_le_one) (div_nonneg (by norm_num) (zero_lt_one.trans hM).le)
  have main : (∫ u in U, H u ∂stableLaw) ≤ (1+2*T)*(D+K*cost) := by
    apply (integral_mono hi.integrableOn (((integrable_const D).add (Cint.const_mul K)).const_mul _) point).trans
    simp only [Pi.add_apply]
    rw [integral_const_mul,integral_add (integrable_const D) (Cint.const_mul K),integral_const_mul,setIntegral_const,smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_of_le_one_left hcst measureReal_le_one)
      (mul_le_mul_of_nonneg_left est KP)) P.le
  have other : (∫ u in Uᶜ, H u ∂stableLaw) ≤ stableLaw.real Uᶜ := by
    convert! integral_mono hi.integrableOn (integrable_const (μ := stableLaw.restrict Uᶜ) (1:ℝ)) (fun u => (bH u).2) using 1
    simp
  change (∫ u, H u ∂stableLaw) ≤ _
  rw [← integral_add_compl mU hi]
  exact (add_le_add main other).trans_eq (add_comm _ _)


theorem haar_retention_bound {B : ℂ} {g T A r h q ρ : ℝ} (hb : 0 < ‖B‖) (hg : 0 < g) (hg1 : g < 1)
    (hbg : 1 < ‖B‖*g) (hT : 0 < T) (hA : 0 < A) (hr : 0 < r) {p : RayParameters}
    (hc : ∀ j, |p.1 j| ≤ 1) (hd : ∀ j, |p.2 j| ≤ 1) (e : ℤ → ℝ) (ω : PhaseTorus)
    (tp : ∀ x, transverseOrbit ‖B‖ p.2 x ∈ complexPhaseGroup B)
    (te : ∀ x, transverseOrbit ρ e x ∈ complexPhaseGroup B)
    (Q U : Set (complexPhaseGroup B × ℝ)) (mQ : MeasurableSet Q) (mU : MeasurableSet U)
    {M cost : ℝ} (hM : 1 < M)
    (est : ∀ z : complexPhaseGroup B, ∫ u in Prod.mk z ⁻¹' U, Weierstrass.collision
      (((physicalLaw T).restrict (Prod.mk z ⁻¹' Q)).map
        (circleRay ‖B‖ g p.1 p.2 ((ω+z.val)+transverseOrbit ρ e (q*u)))) (A*r) ∂stableLaw ≤ cost) :
    (complexPhaseHaar B).real {z : complexPhaseGroup B | ENNReal.ofReal (r^h) <
      rayOccupation ‖B‖ g p (ω+z.val) T A r} ≤
      ((complexPhaseHaar B).prod stableLaw).real Uᶜ+(1+2*T)*
        (((complexPhaseHaar B).prod (physicalLaw T)).real Qᶜ+3/M+(M/(r^h/(1+2*T)))*cost) := by
  let := physicalLaw_probability hT
  let μ := complexPhaseHaar B
  let pU := fun z => stableLaw.real (Prod.mk z ⁻¹' Uᶜ)
  let pQ := fun z => (physicalLaw T).real (Prod.mk z ⁻¹' Qᶜ)
  have iU : Integrable pU μ := (integrable_const (1:ℝ)).mono'
    (ENNReal.measurable_toReal.comp (measurable_measure_prodMk_left mU.compl)).aestronglyMeasurable
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ pU z from measureReal_nonneg)]; exact measureReal_le_one)
  have iQ : Integrable pQ μ := (integrable_const (1:ℝ)).mono'
    (ENNReal.measurable_toReal.comp (measurable_measure_prodMk_left mQ.compl)).aestronglyMeasurable
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ pQ z from measureReal_nonneg)]; exact measureReal_le_one)
  rw [haar_centeredHeavy g p e ρ q T A r h ω tp te,real_prod_sections _ _ mU.compl,real_prod_sections _ _ mQ.compl]
  let k := (M/(r^h/(1+2*T)))*cost
  calc
    _ ≤ ∫ z, pU z+(1+2*T)*(pQ z+3/M+k) ∂μ := by
      apply integral_mono_of_nonneg (ae_of_all _ fun z => integral_nonneg fun _ => measureReal_nonneg)
        (iU.add (((iQ.add (integrable_const _)).add (integrable_const _)).const_mul _))
      apply ae_of_all
      intro z
      have cut := integrated_retention (h:=h) hb hg hg1 hbg hT hA hr hc hd e (ω+z.val)
        (Prod.mk z ⁻¹' Q) (Prod.mk z ⁻¹' U) (mU.preimage (measurable_prodMk_left (x:=z))) hM (est z)
      have qeq : pQ z = 1-(physicalLaw T).real (Prod.mk z ⁻¹' Q) := by
        change (physicalLaw T).real (Prod.mk z ⁻¹' Q)ᶜ = _
        rw [measureReal_compl (mQ.preimage (measurable_prodMk_left (x:=z)))]
        simp
      rw [← qeq] at cut
      exact cut
    _ = _ := by
      rw [integral_add (f := pU) (g := fun z => (1+2*T)*(pQ z+3/M+k)) iU
          (((iQ.add (integrable_const (3/M))).add (integrable_const k)).const_mul (1+2*T)),
        integral_const_mul,integral_add (f := fun z => pQ z+3/M) (g := fun _ => k)
          (iQ.add (integrable_const _)) (integrable_const _), integral_add iQ (integrable_const (3/M))]
      simp [k,pQ,pU,μ]

end Weierstrass.StripProof
