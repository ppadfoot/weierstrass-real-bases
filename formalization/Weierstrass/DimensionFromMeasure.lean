module

public import Weierstrass.UpperBound
public import Weierstrass.LocalDimension
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # From graph-measure dimension to Hausdorff dimension

Exact dimension is expressed using the logarithm of the mass of an open ball.
The mass-distribution argument uses closed balls and includes radius zero.
Taking limits from above preserves the same exponent and handles singleton covers.
-/

public noncomputable section

open Filter MeasureTheory Set
open scoped Topology ENNReal NNReal

namespace Weierstrass

private theorem open_ball_mass_eventually {μ : Measure ℂ} {x : ℂ} {s d : ℝ}
    (hd : Tendsto (fun r : ℝ => Real.log (μ (Metric.ball x r)).toReal / Real.log r)
      (𝓝[>] 0) (𝓝 d)) (hs : s < d) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, (μ (Metric.ball x r)).toReal ≤ r ^ s := by
  filter_upwards [hd.eventually (eventually_gt_nhds hs), Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)]
    with r hr hr01
  by_cases hm : (μ (Metric.ball x r)).toReal = 0
  · rw [hm]
    exact Real.rpow_nonneg hr01.1.le _
  · have hpos := (ENNReal.toReal_nonneg (a := μ (Metric.ball x r))).lt_of_ne' hm
    apply (Real.log_le_log_iff hpos (Real.rpow_pos_of_pos hr01.1 _)).mp
    rw [Real.log_rpow hr01.1]
    exact ((lt_div_iff_of_neg (Real.log_neg hr01.1 hr01.2)).mp hr).le

private theorem closed_ball_mass_of_open_bounds (μ : Measure ℂ) [IsFiniteMeasure μ]
    (x : ℂ) {s δ r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) (hrδ : r < δ)
    (hb : ∀ a ∈ Ioo 0 δ, (μ (Metric.ball x a)).toReal ≤ a ^ s) :
    μ (Metric.closedEBall x (ENNReal.ofReal r)) ≤ ENNReal.ofReal r ^ s := by
  rw [Metric.closedEBall_ofReal hr, ENNReal.ofReal_rpow_of_nonneg hr hs]
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ (Metric.closedBall x r))]
  apply ENNReal.ofReal_le_ofReal
  apply le_of_tendsto_of_tendsto (f := fun _ : ℝ => (μ (Metric.closedBall x r)).toReal)
    (b := 𝓝[>] r) tendsto_const_nhds
    ((Real.continuous_rpow_const hs).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [Ioo_mem_nhdsGT hrδ] with a ha
  exact (ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (Metric.closedBall_subset_ball ha.1))).trans (hb a ⟨hr.trans_lt ha.1, ha.2⟩)

/-- For a finite Borel measure on the plane, every set with positive outer mass
has Hausdorff dimension at least the exact dimension of the measure. -/
theorem le_dimH_of_lower_ball_law {μ : Measure ℂ} [IsFiniteMeasure μ] {d : ℝ}
    (hd : ∀ s : ℝ, 0 ≤ s → s < d → ∀ᵐ x ∂μ, ∀ᶠ r : ℝ in 𝓝[>] 0,
      (μ (Metric.ball x r)).toReal ≤ r^s) {G : Set ℂ} (hG : μ G ≠ 0) : ENNReal.ofReal d ≤ dimH G := by
  by_contra! h
  obtain ⟨v, h₁, h₂⟩ := exists_between h
  lift v to ℝ≥0 using h₂.ne_top
  have hvd : (v : ℝ) < d := ENNReal.coe_lt_ofReal.mp h₂
  have hv : (v : ℝ≥0∞) ≤ dimH G := by
    let q : ℝ := 1/2
    have hq : 0 < q := by norm_num [q]
    have hq' : q < 1 := by norm_num [q]
    apply le_dimH_from_ae_eventual_mass μ hG v (fun n => ENNReal.ofReal (q^n))
      (fun n => ENNReal.ofReal_pos.mpr (pow_pos hq _))
    filter_upwards [hd v v.2 hvd] with x hh
    intro _
    obtain ⟨δ, hδ, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hh
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hq'
    refine ⟨n, ?_⟩
    intro R hR
    have hRfin := (hR.trans_lt ENNReal.ofReal_lt_top).ne
    have hR' : R.toReal < δ :=
      ((ENNReal.toReal_le_toReal hRfin ENNReal.ofReal_ne_top).mpr hR).trans_lt
        (by simpa only [ENNReal.toReal_ofReal (pow_pos hq n).le] using hn)
    have res := closed_ball_mass_of_open_bounds μ x v.2 ENNReal.toReal_nonneg hR'
      (fun a ha => hb ha)
    rwa [ENNReal.ofReal_toReal hRfin] at res
  exact (not_lt_of_ge hv) h₁

theorem ExactDimensional.le_dimH_of_positive_mass {μ : Measure ℂ} [IsFiniteMeasure μ]
    {d : ℝ} (hd : ExactDimensional μ d) {G : Set ℂ} (hG : μ G ≠ 0) :
    ENNReal.ofReal d ≤ dimH G :=
  le_dimH_of_lower_ball_law (fun _ _ hs ↦ hd.mono (fun _ h ↦ open_ball_mass_eventually h hs)) hG

/-- The normalized pushforward gives the graph outer mass one on every
bounded parameter set having nonempty interior. -/
theorem graphMeasure_self {b lam : ℝ} (hl : 0 ≤ lam) (h1 : lam < 1)
    (phase : ℕ → ℝ) {I : Set ℝ} (hi : (interior I).Nonempty) (hbd : Bornology.IsBounded I) :
    graphMeasure b lam phase I (graph b lam phase I) = 1 := by
  let := graphMeasure_probability hl h1 b phase hi hbd
  refine le_antisymm ((measure_mono (subset_univ _)).trans (measure_univ.le)) ?_
  have h := Measure.le_map_apply_image (μ := (volume I)⁻¹ • volume.restrict I)
    (continuous_graphMap hl h1 b phase).measurable.aemeasurable I
  rw [Measure.smul_apply, Measure.restrict_apply_self, smul_eq_mul,
    ENNReal.inv_mul_cancel (Measure.measure_pos_of_nonempty_interior volume hi).ne'
      (hbd.measure_lt_top (μ := volume)).ne] at h
  exact h

/-- The exact-dimensionality clause of the main theorem on all bounded
intervals with nonempty interior, for every base, amplitude, and phase. -/
@[expose] def ExactDimensionOnBoundedIntervals : Prop :=
  ∀ b lam : ℝ, 1 < b → b⁻¹ < lam → lam < 1 →
    ∀ (phase : ℕ → ℝ) (I : Set ℝ), I.OrdConnected → (interior I).Nonempty →
      Bornology.IsBounded I → ExactDimensional (graphMeasure b lam phase I) (2 - alpha b lam)

/-- The graph upper bound and mass-distribution theorem make the graph
dimension formula a consequence of the bounded-interval measure clause.
An arbitrary interval, including an unbounded one, contains a compact
subinterval with nonempty interior. -/
theorem mainStatement_iff_exactDimensionOnBoundedIntervals :
    MainStatement ↔ ExactDimensionOnBoundedIntervals := by
  constructor
  · intro h b lam hb hl h1 phase I hc hi
    exact (h b lam hb hl h1 phase I hc hi).2
  · intro h b lam hb hl h1 phase I hc hi
    refine ⟨le_antisymm (graph_dim_le_formula hb hl h1 phase I) ?_,
      h b lam hb hl h1 phase I hc hi⟩
    obtain ⟨x, hx⟩ := hi
    obtain ⟨a, z, _, hnhds, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx)
    have hj : (interior (Icc a z)).Nonempty := ⟨x, mem_interior_iff_mem_nhds.mpr hnhds⟩
    have hbd := (isCompact_Icc (a := a) (b := z)).isBounded
    have hl₀ := ((inv_pos.mpr (zero_lt_one.trans hb)).trans hl).le
    let := graphMeasure_probability hl₀ h1 b phase hj hbd
    have hed := h b lam hb hl h1 phase _ ordConnected_Icc hj hbd
    have hmass := graphMeasure_self (b := b) hl₀ h1 phase hj hbd
    exact (hed.le_dimH_of_positive_mass (hmass ▸ one_ne_zero)).trans
      (dimH_mono (image_mono hsub))

end Weierstrass
