module

public import Mathlib.MeasureTheory.Integral.Marginal

/-! Small-ball estimates obtained by conditioning on one independent coordinate. -/

public noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Weierstrass.ProductSmallBall

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- A uniform bound for every section in coordinate `i` controls the measure of the event. -/
theorem measure_le_of_slice (i : ι) {E : Set (∀ j, X j)} (hE : MeasurableSet E)
    {ε : ℝ≥0∞} (slice : ∀ x, μ i ((Function.update x i) ⁻¹' E) ≤ ε) :
    Measure.pi μ E ≤ ε := by
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure (Measure.pi μ)
  let f : (∀ j, X j) → ℝ≥0∞ := E.indicator 1
  have hf : Measurable f := measurable_const.indicator hE
  have inner (x : ∀ j, X j) : (∫⁻ t, f (Function.update x i t) ∂μ i) ≤ ε := by
    have idf : (fun t => f (Function.update x i t)) =
        ((Function.update x i) ⁻¹' E).indicator 1 := by
      funext t
      by_cases h : Function.update x i t ∈ E <;> simp [f, h]
    rw [idf]
    exact (lintegral_indicator_one_le _).trans (slice x)
  calc
    Measure.pi μ E = ∫⁻ x, f x ∂Measure.pi μ := (lintegral_indicator_one hE).symm
    _ = lmarginal μ Finset.univ f x₀ := lintegral_eq_lmarginal_univ x₀
    _ = lmarginal μ (Finset.univ.erase i) (fun x => ∫⁻ t, f (Function.update x i t) ∂μ i) x₀ := by
      rw [lmarginal_erase' f hf (Finset.mem_univ i)]
    _ ≤ lmarginal μ (Finset.univ.erase i) (fun _ => ε) x₀ := lmarginal_mono inner x₀
    _ = ε := by simp [lmarginal]

/-- If each bad-coordinate set has mass at most `β`, and each good-coordinate
section of a measurable event has mass at most `ε`, then either all the coordinates
are bad, or there is a good coordinate on which to condition. -/
theorem product_small_ball (bad : ∀ i, Set (X i)) (E : Set (∀ i, X i))
    (hE : MeasurableSet E) (hm : ∀ i, MeasurableSet (bad i)) {β ε : ℝ≥0∞}
    (hbad : ∀ i, μ i (bad i) ≤ β)
    (hslice : ∀ i (x : ∀ j, X j), μ i {t | t ∉ bad i ∧ Function.update x i t ∈ E} ≤ ε) :
    Measure.pi μ E ≤ β ^ Fintype.card ι + Fintype.card ι • ε := by
  classical
  let G (i : ι) : Set (∀ j, X j) := {x | x i ∉ bad i ∧ x ∈ E}
  have good (i : ι) : Measure.pi μ (G i) ≤ ε := by
    apply measure_le_of_slice μ i (((hm i).compl.preimage (measurable_pi_apply i)).inter hE)
    intro x
    simpa [G, Set.preimage] using hslice i x
  have allbad : Measure.pi μ (univ.pi bad) ≤ β ^ Fintype.card ι := by
    rw [Measure.pi_pi]
    simpa using Finset.prod_le_prod' (s := Finset.univ) (g := fun _ => β) (fun i _ => hbad i)
  have cover : E ⊆ (univ.pi bad) ∪ ⋃ i, G i := by
    intro x hx
    by_cases h : ∀ i, x i ∈ bad i
    · exact Or.inl (fun i _ => h i)
    · obtain ⟨i,hi⟩ := not_forall.mp h
      exact Or.inr (mem_iUnion.mpr ⟨i,hi,hx⟩)
  apply (measure_mono cover).trans
  apply (measure_union_le _ _).trans
  exact add_le_add allbad ((measure_iUnion_fintype_le _ _).trans
    ((Finset.sum_le_card_nsmul _ _ _ (fun i _ => good i)).trans_eq (by rw [Finset.card_univ])))

end Weierstrass.ProductSmallBall
