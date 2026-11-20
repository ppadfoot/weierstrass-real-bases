module

public import Weierstrass.StripMaximal

/-! # Sharp planar Fourier energy at one physical mesh -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Weierstrass.StripProof

theorem fourier_bound (μ : Measure Plane) [IsFiniteMeasure μ] (ξ : Plane) :
    ‖fourier μ ξ‖ ≤ μ.real univ := by
  simpa [fourier] using norm_integral_le_of_norm_le_const (μ := μ)
    (ae_of_all _ fun p : Plane => (norm_character (dot p ξ)).le)

theorem measurable_bell (a : ℝ) (c : Plane) : Measurable (bell a c) := by
  unfold bell; fun_prop

theorem physical_gaussian_energy (μ : Measure Plane) [IsFiniteMeasure μ] {R B : ℝ}
    (hR : 0 < R) (hbox : ∀ z, μ.real (box z R⁻¹) ≤ B) (c : Plane) :
    ∫ v, ‖fourier μ (c+R • v)‖^2 ∂gaussian ≤ Real.exp 1 * Real.pi * B * μ.real univ := by
  have localBound (p : Plane) : ∫ q, bell (R^2/2) p q ∂μ ≤ Real.exp 1 * Real.pi * B := by
    have H := gaussian_of_box_bound μ (inv_pos.mpr hR) (by positivity : 0 < R^2/2) hbox p
    have he : 2*(R^2/2)*(R⁻¹)^2 = 1 := by field_simp
    rw [he] at H
    field_simp [hR.ne'] at H
    nlinarith
  refine (gaussian_energy_le μ c R).trans ?_
  let K (p : Plane × Plane) := bell (R^2/2) p.1 p.2
  have mK : Measurable K := by unfold K bell; fun_prop
  have iK : Integrable K (μ.prod μ) := by
    apply (integrable_const (1:ℝ)).mono' mK.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    dsimp [K]; rw [abs_of_pos (bell_pos _ _ _)]
    have small (x : ℝ) : Real.exp (-(R^2/2)*x^2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg _))
    exact mul_le_one₀ (small _) (Real.exp_pos _).le (small _)
  have hK (p : Plane × Plane) : Real.exp
      (-((R*(p.1.1-p.2.1))^2+(R*(p.1.2-p.2.2))^2)/2) = K p := by
    unfold K bell; rw [← Real.exp_add]; congr 1; ring
  simp_rw [hK]
  rw [integral_prod _ iK]
  calc
    _ ≤ ∫ _ : Plane, Real.exp 1 * Real.pi * B ∂μ :=
      integral_mono iK.integral_prod_left (integrable_const _) localBound
    _ = _ := by rw [integral_const,smul_eq_mul,mul_comm]

/-- The normalized planar Gaussian integral written with Lebesgue density. -/
theorem integral_gaussian_density (F : Plane → ℝ) :
    ∫ v, F v ∂gaussian = (2*Real.pi)⁻¹ * ∫ v, bell (1/2) 0 v * F v := by
  rw [gaussian,gaussianReal_of_var_ne_zero 0 one_ne_zero,
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _)]
  have md : Measurable (fun z : Plane => gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2) := ((measurable_gaussianPDF 0 1).comp measurable_fst).mul
    ((measurable_gaussianPDF 0 1).comp measurable_snd)
  rw [integral_withDensity_eq_integral_toReal_smul md (ae_of_all _ fun _ =>
    ENNReal.mul_lt_top gaussianPDF_lt_top gaussianPDF_lt_top), ← integral_const_mul]
  apply integral_congr_ae (ae_of_all _ fun p => ?_)
  rw [smul_eq_mul,ENNReal.toReal_mul,gaussianPDF,gaussianPDF,
    ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),
    ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  simp only [gaussianPDFReal,bell,NNReal.coe_one,mul_one,Prod.fst_zero,Prod.snd_zero,sub_zero]
  have hπ : 0 < 2*Real.pi := by positivity
  have hs := Real.sq_sqrt hπ.le
  rw [show -(p.1^2)/2 = -(1/2:ℝ)*p.1^2 by ring,
    show -(p.2^2)/2 = -(1/2:ℝ)*p.2^2 by ring]
  field_simp [hπ.ne', (Real.sqrt_pos.mpr hπ).ne']
  rw [hs]

/-- Change of center and scale of the Gaussian density on the frequency plane. -/
theorem integral_gaussian_scaled (F : Plane → ℝ) (c : Plane) {R : ℝ} (hR : 0 < R) :
    ∫ v, F (c+R • v) ∂gaussian =
      (2*Real.pi*R^2)⁻¹ * ∫ v, bell (1/(2*R^2)) c v * F v := by
  rw [integral_gaussian_density]
  let G := fun z : Plane => bell (1/(2*R^2)) c z * F z
  have eqn (v : Plane) : bell (1/2) 0 v * F (c+R • v) = G (c+R • v) := by
    unfold G bell
    congr 2 <;> simp <;> field_simp [hR.ne']
  simp_rw [eqn]
  rw [Measure.integral_comp_smul_of_nonneg volume (fun z : Plane => G (c+z)) R (hR := hR.le),
    integral_add_left_eq_self]
  simp [Module.finrank_prod,smul_eq_mul,G]
  ring

/-- Uniform translated frequency-square estimate with the full single-strip mass factor. -/
theorem fourier_square_energy (μ : Measure Plane) [IsFiniteMeasure μ] {R B : ℝ}
    (hR : 0 < R) (hbox : ∀ z, μ.real (box z R⁻¹) ≤ B) (c : Plane) :
    ∫ v in box c R, ‖fourier μ v‖^2 ≤
      2 * Real.exp 2 * Real.pi^2 * R^2 * B * μ.real univ := by
  let F := fun v => ‖fourier μ v‖^2
  have hi : Integrable (fun v => bell (1/(2*R^2)) c v * F v) := by
    apply ((integrable_bell (show 0 < 1/(2*R^2) by positivity) c).mul_const ((μ.real univ)^2)).mono'
      (((measurable_bell _ _).mul ((measurable_fourier μ).norm.pow_const 2)).aestronglyMeasurable)
      (ae_of_all _ fun v => ?_)
    change ‖bell (1/(2*R^2)) c v * ‖fourier μ v‖^2‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (bell_pos _ _ _).le (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (fourier_bound μ v) _) (bell_pos _ _ _).le
  have hmono : ∫ v in box c R, F v ≤ Real.exp 1 * ∫ v, bell (1/(2*R^2)) c v * F v := by
    rw [← integral_indicator (measurable_box _ _),← integral_const_mul]
    apply integral_mono_of_nonneg (ae_of_all _ fun v => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
      (hi.const_mul _) (ae_of_all _ fun v => ?_)
    by_cases hv : v ∈ box c R
    · rw [Set.indicator_of_mem hv]
      apply le_of_sub_nonneg
      have coord (x y : ℝ) (h : x ∈ Icc (y-R) (y+R)) : (x-y)^2 ≤ R^2 := by
        rcases h with ⟨h1,h2⟩
        nlinarith [mul_nonneg (by linarith : 0 ≤ R-(x-y)) (by linarith : 0 ≤ R+(x-y))]
      have he : 1 ≤ Real.exp 1 * bell (1/(2*R^2)) c v := by
        rw [bell,← Real.exp_add,← Real.exp_add,Real.one_le_exp_iff]
        field_simp [hR.ne']
        linarith [coord _ _ hv.1, coord _ _ hv.2]
      nlinarith [mul_le_mul_of_nonneg_right he (show 0 ≤ F v from sq_nonneg _)]
    · rw [Set.indicator_of_notMem hv]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (bell_pos _ _ _).le (sq_nonneg _))
  have H := physical_gaussian_energy μ hR hbox c
  rw [integral_gaussian_scaled F c hR] at H
  have hπ : 0 < 2*Real.pi*R^2 := by positivity
  have M := mul_le_mul_of_nonneg_left H hπ.le
  rw [← mul_assoc,mul_inv_cancel₀ hπ.ne',one_mul] at M
  apply hmono.trans
  have HH := mul_le_mul_of_nonneg_left M (Real.exp_pos 1).le
  convert HH using 1
  rw [show (2:ℝ)=1+1 by norm_num,Real.exp_add]
  ring

end Weierstrass.StripProof
