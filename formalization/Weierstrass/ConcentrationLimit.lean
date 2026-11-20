module

public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Vanishing concentration at shrinking widths, uniformly in moving centers. -/
public noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Weierstrass.CriticalRay

/-- Weak convergence towards an atomless law excludes positive mass in
intervals of shrinking widths even when their centers depend on the index.
The proof controls the difference of two independent samples. -/
theorem shrinking_band_of_weak {ν : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (weak : Tendsto ν atTop (𝓝 μ)) (atomless : ∀ x : ℝ, (μ : Measure ℝ) {x} = 0)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      (ν n : Measure ℝ).real (Icc (t-r n) (t+r n)) < ε := by
  let M := (μ : Measure ℝ).prod (μ : Measure ℝ)
  let D (a : ℝ) := {z : ℝ × ℝ | |z.1-z.2| ≤ a}
  have closed (a : ℝ) : IsClosed (D a) :=
    isClosed_le (continuous_fst.sub continuous_snd |>.abs) continuous_const
  let rad (k : ℕ) := 1/((k:ℝ)+1)
  have decreases : Antitone (fun k : ℕ ↦ D (rad k)) := by
    intro k j h z hz
    change |z.1-z.2| ≤ rad j at hz
    change |z.1-z.2| ≤ rad k
    apply le_trans hz
    dsimp [rad]
    gcongr
  have diag : (⋂ k : ℕ, D (rad k)) = D 0 := by
    ext z
    simp only [mem_iInter]
    constructor
    · intro h
      exact le_of_tendsto_of_tendsto' tendsto_const_nhds
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)) h
    · intro h k
      exact (show |z.1-z.2| ≤ 0 from h).trans (by dsimp [rad]; positivity)
  have null : M (D 0) = 0 := by
    rw [show M (D 0) = ∫⁻ x, (μ : Measure ℝ) (Prod.mk x ⁻¹' D 0) ∂(μ : Measure ℝ)
      from Measure.prod_apply (closed 0).measurableSet]
    apply lintegral_eq_zero_of_ae_eq_zero
    apply Eventually.of_forall
    intro x
    have eq : Prod.mk x ⁻¹' D 0 = {x} := by
      ext y
      simp [D,sub_eq_zero,eq_comm]
    change (μ : Measure ℝ) (Prod.mk x ⁻¹' D 0) = 0
    rw [eq,atomless]
  have dec := tendsto_measure_iInter_atTop (μ:=M) (fun k : ℕ ↦ (closed (rad k)).measurableSet.nullMeasurableSet)
    decreases ⟨0,measure_ne_top _ _⟩
  rw [diag,null] at dec
  have both : Tendsto (fun n ↦ (ν n).prod (ν n)) atTop (𝓝 (μ.prod μ)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp (weak.prodMk_nhds weak)
  intro ε hε
  let E := ENNReal.ofReal (ε^2)
  have ep : 0 < E := ENNReal.ofReal_pos.mpr (sq_pos_of_pos hε)
  obtain ⟨k,hk⟩ := (dec.eventually (eventually_lt_nhds ep)).exists
  have p := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto both (closed (rad k))
  have p' := eventually_lt_of_limsup_lt (p.trans_lt hk)
  have rsmall := (hr.const_mul 2).eventually_lt_const
    (show (2:ℝ)*0 < rad k by rw [mul_zero]; dsimp [rad]; positivity)
  filter_upwards [p',rsmall] with n hn small
  intro t
  let B := Icc (t-r n) (t+r n)
  have sub : B ×ˢ B ⊆ D (rad k) := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    change |x-y| ≤ rad k
    change t-r n ≤ x ∧ x ≤ t+r n at hx
    change t-r n ≤ y ∧ y ≤ t+r n at hy
    apply abs_le.mpr
    constructor <;> linarith only [hx.1,hx.2,hy.1,hy.2,small]
  have m := (measure_mono (μ:=(ν n : Measure ℝ).prod (ν n : Measure ℝ)) sub).trans_lt hn
  rw [Measure.prod_prod] at m
  have r := (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))
    (by exact ENNReal.ofReal_ne_top)).mpr m
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg ε)] at r
  change ((ν n : Measure ℝ) B).toReal < ε
  nlinarith only [r,ENNReal.toReal_nonneg (a:=(ν n : Measure ℝ) B),hε]

end Weierstrass.CriticalRay
