module

public import Mathlib.Topology.MetricSpace.HausdorffDimension

/-! The mass-distribution step from Appendix A. The scale from which the ball
estimate holds may depend on the center. Even the set to which we restrict the
measure need not be Borel. -/
public noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal

namespace Weierstrass

/-- A common small-scale ball bound on a positive-mass subset implies the
Hausdorff lower bound. The extended radii include zero, for singleton covers. -/
theorem le_dimH_from_uniform_mass {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    {E : Set X} (hE : μ E ≠ 0) (s : ℝ≥0) {ε : ℝ≥0∞} (hε : 0 < ε)
    (hmass : ∀ x ∈ E, ∀ r : ℝ≥0∞, r ≤ ε →
      μ (Metric.closedEBall x r) ≤ r ^ (s : ℝ)) : (s : ℝ≥0∞) ≤ dimH E := by
  have dominated : μ.restrict E ≤ μH[(s:ℝ)] := by
    apply Measure.le_hausdorffMeasure _ _ ε hε
    intro A hA
    calc
      μ.restrict E A ≤ μ.restrict E (closure A) := measure_mono subset_closure
      _ = μ (closure A ∩ E) := Measure.restrict_apply isClosed_closure.measurableSet
      _ ≤ (Metric.ediam A) ^ (s:ℝ) := by
        by_cases h : (closure A ∩ E).Nonempty
        · obtain ⟨x,hx,hxE⟩ := h
          apply le_trans (measure_mono (t := Metric.closedEBall x (Metric.ediam A)) ?_)
            (hmass x hxE _ hA)
          intro y hy
          change edist y x ≤ Metric.ediam A
          rw [← Metric.ediam_closure]
          exact Metric.edist_le_ediam_of_mem hy.1 hx
        · simp [Set.not_nonempty_iff_eq_empty.mp h]
  apply le_dimH_of_hausdorffMeasure_ne_zero
  have hd := dominated E
  rw [Measure.restrict_apply_self] at hd
  exact ne_of_gt ((pos_iff_ne_zero.mpr hE).trans_le hd)

/-- Applying the preceding argument on one of countably many scales allows
the starting threshold to depend on the center. -/
theorem le_dimH_from_ae_eventual_mass {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    {G : Set X} (hG : μ G ≠ 0) (s : ℝ≥0)
    (eps : ℕ → ℝ≥0∞) (hpos : ∀ n, 0 < eps n)
    (hmass : ∀ᵐ x ∂μ, x ∈ G → ∃ n, ∀ r : ℝ≥0∞, r ≤ eps n →
      μ (Metric.closedEBall x r) ≤ r ^ (s : ℝ)) :
    (s : ℝ≥0∞) ≤ dimH G := by
  let E (n : ℕ) := {x ∈ G | ∀ r : ℝ≥0∞, r ≤ eps n →
    μ (Metric.closedEBall x r) ≤ r ^ (s : ℝ)}
  have cover : G ≤ᵐ[μ] (⋃ n, E n) := by
    filter_upwards [hmass] with x hx
    intro hxG
    obtain ⟨n,hn⟩ := hx hxG
    exact mem_iUnion.mpr ⟨n, hxG, hn⟩
  have hu : μ (⋃ n, E n) ≠ 0 := ne_of_gt ((pos_iff_ne_zero.mpr hG).trans_le (measure_mono_ae cover))
  obtain ⟨n,hn⟩ : ∃ n, μ (E n) ≠ 0 := by
    by_contra! h
    exact hu (measure_iUnion_null h)
  exact (le_dimH_from_uniform_mass μ hn s (hpos n) fun _ hx => hx.2).trans
    (dimH_mono fun _ hx => hx.1)

end Weierstrass
