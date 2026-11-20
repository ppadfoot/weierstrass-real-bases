module

public import Weierstrass.HarmonicArcs
public import Weierstrass.ProductSmallBall
public import Weierstrass.PhaseDensity

/-! A concentration bound for finite sums of the independent harmonic coordinates.
The real coefficients can have either sign. The estimate is uniform in the center. -/

public noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Weierstrass

theorem harmonic_sum_band {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) {a δ r : ℝ} (ha : 0 < a) (hw : ∀ i, a ≤ |w i|)
    (hδ : 0 < δ) (hr : 0 ≤ r) (y : ℝ) :
    (Measure.pi fun _ : ι ↦ circleUniform)
      {z | |(∑ j, w j * harmonicCos (z j)) - y| ≤ r} ≤
      ENNReal.ofReal (4 * δ) ^ Fintype.card ι +
        Fintype.card ι • ENNReal.ofReal ((r / a) / (4 * δ)) := by
  classical
  let E : Set (ι → AddCircle (1 : ℝ)) :=
    {z | |(∑ j, w j * harmonicCos (z j)) - y| ≤ r}
  have hsum : Measurable (fun z : ι → AddCircle (1 : ℝ) ↦ ∑ j, w j * harmonicCos (z j)) :=
    Finset.measurable_fun_sum _ (fun j _ ↦ measurable_const.mul
      (measurable_harmonicCos.comp (measurable_pi_apply j)))
  have hE : MeasurableSet E := measurableSet_le (continuous_abs.measurable.comp (hsum.sub measurable_const)) measurable_const
  apply ProductSmallBall.product_small_ball (fun _ : ι ↦ circleUniform)
    (fun _ ↦ (regularPhase δ)ᶜ) E hE (fun _ ↦ (measurableSet_regularPhase δ).compl)
    (fun _ ↦ harmonic_bad_mass δ hδ.le)
  intro i x
  let S := ∑ j ∈ Finset.univ.erase i, w j * harmonicCos (x j)
  have hwi : w i ≠ 0 := abs_pos.mp (ha.trans_le (hw i))
  apply le_trans (measure_mono (t :=
    {t | t ∈ regularPhase δ ∧ |harmonicCos t - (y-S)/w i| ≤ r/a}) ?_)
    (harmonic_good_band hδ _ _ (div_nonneg hr ha.le))
  rintro t ⟨ht, h⟩
  refine ⟨not_not.mp ht, ?_⟩
  have hsplit : (∑ j, w j * harmonicCos (Function.update x i t j)) = S + w i * harmonicCos t := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    exact Finset.sum_congr rfl (fun j hj ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  change |(∑ j, w j * harmonicCos (Function.update x i t j)) - y| ≤ r at h
  rw [hsplit] at h
  have hid : harmonicCos t - (y-S)/w i = (S + w i * harmonicCos t - y)/w i := by
    field_simp
    ring
  rw [hid, abs_div]
  exact (div_le_div_of_nonneg_right h (abs_nonneg _)).trans
    (div_le_div_of_nonneg_left hr ha (hw i))

end Weierstrass
