module

public import Weierstrass.RaySeedSlope

/-! An explicit summable modulus for the physical derivative, uniform in all
phases and weights. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology ENNReal ComplexConjugate
namespace Weierstrass.RaySeed

def slopeModulus (b q ρ s t : ℝ) : ℝ :=
  ∑' j : ℤ, 2*physicalEnvelope q ρ s j * min 2 ((2*Real.pi)*b^j*|t|)

private theorem nonneg_env {q ρ : ℝ} (hq : 0 < q) (hρ : 0 < ρ) (s : ℝ) (j : ℤ) :
    0 ≤ physicalEnvelope q ρ s j := by unfold physicalEnvelope;split <;> positivity

theorem slopeModulus_tendsto {b q ρ : ℝ} (hb : 0 < b) (hq : 1 < q) (hρ : 0 < ρ)
    (hQ : q*ρ < 1) (s : ℝ) : Tendsto (slopeModulus b q ρ s) (𝓝 0) (𝓝 0) := by
  let W := physicalEnvelope q ρ s
  have sw : Summable W := summable_physicalEnvelope hq hρ hQ s
  have ew (j : ℤ) : 0 ≤ W j := nonneg_env (zero_lt_one.trans hq) hρ s j
  have pt (j : ℤ) : Tendsto (fun t : ℝ ↦ 2*W j*min 2 ((2*Real.pi)*b^j*|t|)) (𝓝 0) (𝓝 0) := by
    have c : Continuous (fun t : ℝ ↦ 2*W j*min 2 ((2*Real.pi)*b^j*|t|)) := by fun_prop
    simpa using (c.continuousAt (x:=0)).tendsto
  have bound (t : ℝ) (j : ℤ) :
      ‖2*W j*min 2 ((2*Real.pi)*b^j*|t|)‖ ≤ 4*W j := by
    have wj : 0 ≤ 2*W j := mul_nonneg zero_le_two (ew j)
    rw [Real.norm_of_nonneg (mul_nonneg wj (le_min (by norm_num) (by positivity)))]
    exact (mul_le_mul_of_nonneg_left (min_le_left _ _) wj).trans_eq (by ring)
  have hc := tendsto_tsum_of_dominated_convergence (sw.mul_left 4) pt (.of_forall bound)
  change Tendsto (fun t : ℝ ↦ ∑' j : ℤ, 2*W j*min 2 ((2*Real.pi)*b^j*|t|)) _ _
  simpa only [tsum_zero] using hc

theorem slopeTerm_difference {b g ρ : ℝ} (hb : 0 < b) (hg : 0 < g) (hρ : 0 < ρ)
    {c d e : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (ω z : PhaseTorus) (h₁ h₀ t v : ℝ) (j : ℤ) :
    ‖slopeTerm b g ρ c d e ω z h₁ h₀ t j-slopeTerm b g ρ c d e ω z h₁ h₀ v j‖ ≤
      2*physicalEnvelope (b*g) ρ (h₁-h₀) j * min 2 ((2*Real.pi)*b^j*|t-v|) := by
  let X u := derivativeCoeff (b*g) ρ (h₁-h₀) (fun i ↦ c i*d i) e (phaseAt b ρ h₀ d e ω u) j * coord z j
  let y := b^j*d j*(t-v)
  have phaseEq : phaseAt b ρ h₀ d e ω t j = phaseAt b ρ h₀ d e ω v j + ↑y := by
    unfold phaseAt
    rw [add_assoc,←AddCircle.coe_add]
    congr 2
    dsimp [y];ring
  have diff : X t-X v = X v*circleJump y := by
    dsimp only [X,derivativeCoeff,coord]
    rw [phaseEq,turn_add];simp only [circleJump];ring
  have yabs : |y| ≤ b^j*|t-v| := by
    simp only [y,abs_mul,abs_of_pos (zpow_pos hb j)]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (zpow_pos hb _).le (hd j)) (abs_nonneg _)
  have hj := circleJump_bounds y
  have bj : ‖circleJump y‖ ≤ min 2 ((2*Real.pi)*b^j*|t-v|) :=
    le_min hj.1 (hj.2.trans ((mul_le_mul_of_nonneg_left yabs (by positivity)).trans_eq (by ring)))
  have hu j : |c j*d j| ≤ 1 := by rw [abs_mul];exact (mul_le_of_le_one_right (abs_nonneg _) (hd j)).trans (hc j)
  have ph := physical_bounds (mul_pos hb hg) hρ (h₁-h₀) hu he (phaseAt b ρ h₀ d e ω v) j
  have wx : ‖X v‖ ≤ physicalEnvelope (b*g) ρ (h₁-h₀) j := by
    dsimp only [X]
    rw [norm_mul,norm_coord,mul_one,physicalEnvelope]
    split <;> first | exact ph.1 | exact ph.2
  change ‖2*(X t).re-2*(X v).re‖ ≤ _
  rw [←mul_sub,←Complex.sub_re,norm_mul,Real.norm_of_nonneg (by norm_num : 0 ≤ (2:ℝ))]
  apply (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) zero_le_two).trans
  rw [diff,norm_mul]
  exact (mul_le_mul_of_nonneg_left (mul_le_mul wx bj (norm_nonneg _) (nonneg_env (mul_pos hb hg) hρ _ _)) zero_le_two).trans_eq (by ring)

theorem uniform_slope_modulus {b g ρ : ℝ} (hb : 0 < b) (hg : 0 < g) (hq : 1 < b*g)
    (hρ : 0 < ρ) (hQ : (b*g)*ρ < 1) (h₁ h₀ : ℝ) {κ : ℝ} (hk : 0 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (c d e : ℤ → ℝ), (∀ j, |c j| ≤ 1) → (∀ j, |d j| ≤ 1) →
      (∀ j, |e j| ≤ 1) → ∀ (ω z : PhaseTorus) (t v : ℝ), |t-v| ≤ δ →
      |slope b g ρ c d e ω z h₁ h₀ t - slope b g ρ c d e ω z h₁ h₀ v| ≤ κ := by
  have ev := (slopeModulus_tendsto hb hq hρ hQ (h₁-h₀)).eventually_lt_const hk
  obtain ⟨δ,hδ,inc⟩ := Metric.mem_nhds_iff.mp ev
  refine ⟨δ/2,by positivity,?_⟩
  intro c d e hc hd he ω z t v dist
  have close : t-v ∈ Metric.ball (0:ℝ) δ := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using dist.trans_lt (half_lt_self hδ)
  have sm := (show slopeModulus b (b*g) ρ (h₁-h₀) (t-v) < κ from inc close).le
  let W := physicalEnvelope (b*g) ρ (h₁-h₀)
  have sw : Summable W := summable_physicalEnvelope hq hρ hQ _
  have sb x : Summable (slopeTerm b g ρ c d e ω z h₁ h₀ x) :=
    (sw.mul_left 2).of_norm_bounded (bound_slopeTerm hb hg hρ hc hd he _ _ _ _ x)
  rw [slope,slope,←(sb t).tsum_sub (sb v)]
  apply le_trans _ sm
  apply tsum_of_norm_bounded _ (slopeTerm_difference hb hg hρ hc hd he _ _ _ _ _ _)
  apply Summable.hasSum
  apply (sw.mul_left 4).of_nonneg_of_le
  · intro j
    exact mul_nonneg (mul_nonneg (by norm_num) (nonneg_env (mul_pos hb hg) hρ _ _))
      (le_min (by norm_num) (by positivity))
  · intro j
    exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (mul_nonneg zero_le_two (nonneg_env (mul_pos hb hg) hρ _ _))).trans_eq (by ring)

end Weierstrass.RaySeed
