module

public import Weierstrass.Anchored
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! A uniform first-moment criterion for the actual coset-anchored statement. -/
@[expose] public noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Weierstrass

def occupation (b lam T A r : ℝ) (z : PhaseTorus) : ℝ≥0∞ :=
  volume {u : ℝ | u ∈ Icc (-T) T ∧ |circleIncrement b lam z u| ≤ A*r}

theorem measurable_circleIncrement (b lam : ℝ) :
    Measurable (fun p : PhaseTorus × ℝ => circleIncrement b lam p.1 p.2) := by
  unfold circleIncrement bilateralIncrement
  apply Measurable.tsum
  intro j
  have coord : Measurable (fun p : PhaseTorus × ℝ => p.1 j) :=
    (measurable_pi_apply j).comp measurable_fst
  have lift : Measurable (fun p : PhaseTorus × ℝ =>
      (AddCircle.equivIco (1:ℝ) 0 (p.1 j) : ℝ)) :=
    measurable_subtype_coe.comp ((AddCircle.measurableEquivIco (1:ℝ) 0).measurable.comp coord)
  unfold incrementTerm
  fun_prop

theorem measurable_occupation (b lam T A r : ℝ) : Measurable (occupation b lam T A r) := by
  apply measurable_measure_prodMk_left (ν := volume)
    (s := {p : PhaseTorus × ℝ | p.2 ∈ Icc (-T) T ∧ |circleIncrement b lam p.1 p.2| ≤ A*r})
  exact (measurable_snd measurableSet_Icc).inter
    (measurableSet_le (continuous_abs.measurable.comp (measurable_circleIncrement b lam)) measurable_const)

private theorem coset_add_measurable (b : ℝ) (ω : PhaseTorus) :
    @Measurable _ _ (borel (phaseGroup b)) _ (fun z : phaseGroup b => ω + z.val) := by
  let _ : MeasurableSpace (phaseGroup b) := borel _
  let _ : BorelSpace (phaseGroup b) := ⟨rfl⟩
  exact (continuous_const.add continuous_subtype_val).measurable

local instance phaseGroupBorel (b : ℝ) : MeasurableSpace (phaseGroup b) := borel _

set_option maxHeartbeats 350000 in
/-- The constants, the exponent gain, and the cutoff in r are uniform over cosets. -/
theorem anchored_of_first_moment (b lam s : ℝ)
    (estimate : ∀ h : ℝ, 0 < h → h < s → ∀ T A : ℝ, 0 < T → 0 < A →
      ∃ k C : ℝ, h < k ∧ 0 ≤ C ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ ω : PhaseTorus,
        (∫⁻ z : phaseGroup b, occupation b lam T A r (ω + z.val) ∂phaseHaar b) ≤
          ENNReal.ofReal (C * r ^ k)) : AnchoredEstimate b lam s := by
  intro h hh hs T A hT hA
  obtain ⟨k,C,hk,hC,hm⟩ := estimate h hh hs T A hT hA
  have lim : Tendsto (fun r : ℝ => ENNReal.ofReal (C * r ^ (k-h))) (𝓝[>] 0) (𝓝 0) := by
    have e : 0 < k-h := sub_pos.mpr hk
    have cont : Continuous (fun r : ℝ => ENNReal.ofReal (C * r ^ (k-h))) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul (Real.continuous_rpow_const e.le))
    simpa [Real.zero_rpow e.ne'] using (cont.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  change Tendsto (fun r : ℝ ↦ ⨆ ω : PhaseTorus,
    phaseHaar b {z : phaseGroup b | ENNReal.ofReal (r^h) < occupation b lam T A r (ω+z.val)})
    (𝓝[>] 0) (𝓝 0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℝ ↦ (0 : ℝ≥0∞))
    tendsto_const_nhds lim
  · exact Eventually.of_forall fun _ => bot_le
  filter_upwards [self_mem_nhdsWithin, hm] with r hr hmean
  have hr0 : 0 < r := hr
  apply iSup_le
  intro ω
  let f (z : phaseGroup b) := occupation b lam T A r (ω+z.val)
  let μ := phaseHaar b
  have hmeas : Measurable f :=
    (measurable_occupation b lam T A r).comp (coset_add_measurable b ω)
  have hp := Real.rpow_pos_of_pos hr0 h
  have he := ENNReal.ofReal_ne_zero_iff.mpr hp
  have markov := meas_ge_le_lintegral_div (μ := μ) (f := f) hmeas.aemeasurable he
    ENNReal.ofReal_ne_top
  have hm' : (∫⁻ z, f z ∂μ) ≤ ENNReal.ofReal (C * r^k) := hmean ω
  change μ {z | ENNReal.ofReal (r^h) < f z} ≤ _
  calc
    μ {z | ENNReal.ofReal (r^h) < f z} ≤ μ {z | ENNReal.ofReal (r^h) ≤ f z} :=
      measure_mono (fun z (hz : ENNReal.ofReal (r^h) < f z) ↦ (le_of_lt hz : ENNReal.ofReal (r^h) ≤ f z))
    _ ≤ (∫⁻ z, f z ∂μ) / ENNReal.ofReal (r^h) := markov
    _ ≤ ENNReal.ofReal (C*r^k) / ENNReal.ofReal (r^h) := ENNReal.div_le_div_right hm' _
    _ = ENNReal.ofReal (C * r ^ (k-h)) := by
      rw [← ENNReal.ofReal_div_of_pos hp, Real.rpow_sub hr0, mul_div_assoc]

end Weierstrass
