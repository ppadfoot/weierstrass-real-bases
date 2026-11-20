module

public import Weierstrass.BranchGraphLower
public import Weierstrass.SlopeDimensionUpper

/-! Theorem B.2 with its pointwise lower local dimension hypothesis. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Weierstrass.Predecessor
open scoped ENNReal Topology
namespace Weierstrass.Branch

/-- The assumed lower exponent cannot exceed the per-state upper exponent.
The latter comes from the uniform prefix probabilities and the ambient line. -/
theorem slope_threshold_le {p : ℕ} (hp : 2≤p) (d : ℕ) (a : ℕ → ℤ) (η : ℕ → ℝ) {g s : ℝ} (hg : 0<g) (hg1 : g<1)
    (H : ∀ᵐ w : Fin d → UnitAddCircle, let μ := baseSlopeLaw (by omega : 0<p) d a (centralLift w) η g
        ∀ᵐ y ∂μ, ∀ t : ℝ, t<s → ∀ᶠ r : ℝ in 𝓝[>] 0, t ≤ Real.log (μ.real (Icc (y-r) (y+r)))/Real.log r) :
    s ≤ slopeExponent p g := by
  by_contra! gap
  obtain ⟨lo,slow,los⟩ := exists_between gap
  obtain ⟨hi,lh,his⟩ := exists_between los
  let _ : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  obtain ⟨w,mw⟩ := H.exists
  let μ := baseSlopeLaw (by omega : 0<p) d a (centralLift w) η g
  have _ : IsProbabilityMeasure μ := ⟨baseSlopeLaw_univ (by omega : 0<p) d a (centralLift w) η g⟩
  have both := mw.and (slope_upper_local_dimension hp d a (centralLift w) η hg hg1)
  change ∀ᵐ y ∂μ, _ at both
  obtain ⟨y,bottom,top⟩ := both.exists
  obtain ⟨r,left,right⟩ := ((bottom hi his).and (top lo slow)).exists
  exact lh.not_ge (left.trans right)

/-- Graph lower bound on each interval with nonempty interior, and the
full graph and normalized-measure conclusion at exponent one. Arbitrary
prescribed graph phases are allowed, including the zero phases of Theorem B.2. -/
theorem conditional_slopes_graph {b l s : ℝ} (hb : 1<b) (hl : b⁻¹<l) (hl1 : l<1) (E : PrimitiveEquation b)
    (digits : 2≤E.p) (_hs : 0<s) (η : ℕ → ℝ)
    (H : ∀ᵐ w : Fin (E.d+1) → UnitAddCircle, let μ := baseSlopeLaw (positive_digits E) (E.d+1) E.a (centralLift w) η (b*l)⁻¹
        ∀ᵐ y ∂μ, ∀ t : ℝ, t<s → ∀ᶠ r : ℝ in 𝓝[>] 0, t ≤ Real.log (μ.real (Icc (y-r) (y+r)))/Real.log r)
    (phase : ℕ → ℝ) {I : Set ℝ} (conn : I.OrdConnected) (hi : (interior I).Nonempty) :
    ENNReal.ofReal (1+s*(1-alpha b l)) ≤ dimH (graph b l phase I) ∧
    (s=1 → dimH (graph b l phase I) = ENNReal.ofReal (2-alpha b l) ∧
      (Bornology.IsBounded I → ExactDimensional (graphMeasure b l phase I) (2-alpha b l))) := by
  have bp := zero_lt_one.trans hb
  have gp := inv_pos.mpr (mul_pos bp ((inv_pos.mpr bp).trans hl))
  have g1 := inv_lt_one_of_one_lt₀ ((inv_lt_iff_one_lt_mul₀' bp).mp hl)
  have le : s≤slopeExponent E.p (b*l)⁻¹ := slope_threshold_le digits _ _ η gp g1 H
  constructor
  · apply (ENNReal.ofReal_le_ofReal (add_le_add_right (a:=1) ?_)).trans (predecessor_graph_lower hb hl hl1 E digits phase hi)
    exact mul_le_mul_of_nonneg_right le (sub_nonneg.mpr (alpha_mem_Ioo hb hl hl1).2.le)
  · intro eq
    have one : slopeExponent E.p (b*l)⁻¹ = 1 := le_antisymm (min_le_left ..) (eq ▸ le)
    exact graph_of_anchored_estimate hb hl hl1 (one ▸ predecessor_anchored hb hl hl1 E digits) phase I conn hi

end Weierstrass.Branch
