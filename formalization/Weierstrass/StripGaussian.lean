module

public import Weierstrass.StripProof
public import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Gaussian Fourier energy for planar strip measures -/

@[expose] public noncomputable section
open Set MeasureTheory Complex ProbabilityTheory
open scoped BigOperators ComplexConjugate

namespace Weierstrass.StripProof

abbrev Plane := ℝ × ℝ

/-- Planar Fourier transform in radian normalization. -/
def dot (p q : Plane) : ℝ := p.1*q.1 + p.2*q.2

def fourier (μ : Measure Plane) (ξ : Plane) : ℂ := ∫ p, character (dot p ξ) ∂μ

/-- Independent standard Gaussian frequencies in the two coordinates. -/
def gaussian : Measure Plane := (gaussianReal 0 1).prod (gaussianReal 0 1)

instance : IsProbabilityMeasure gaussian := by unfold gaussian; infer_instance

theorem character_add (s t : ℝ) : character (s+t) = character s * character t := by
  simp only [character,Complex.ofReal_add,add_mul,Complex.exp_add]

private theorem integral_gaussian_character (t : ℝ) :
    ∫ v, character (t*v) ∂gaussianReal 0 1 = (Real.exp (-(t^2)/2) : ℂ) := by
  have H := charFun_gaussianReal (μ := 0) (v := 1) t
  rw [charFun_apply_real] at H
  simpa [character, Complex.ofReal_exp, neg_div] using H

/-- The Fourier multiplier of the product Gaussian. -/
theorem gaussian_character (t : Plane) :
    ∫ v, character (dot t v) ∂gaussian =
      (Real.exp (-(t.1^2+t.2^2)/2) : ℂ) := by
  simp only [gaussian,dot,character_add]
  rw [integral_prod_mul (fun u => character (t.1*u)) (fun v => character (t.2*v))]
  rw [integral_gaussian_character,integral_gaussian_character,← Complex.ofReal_mul,
    ← Real.exp_add]
  congr 2; ring

private theorem continuous_dot : Continuous (fun p : Plane × Plane => dot p.1 p.2) := by
  unfold dot; fun_prop

theorem measurable_fourier (μ : Measure Plane) [IsFiniteMeasure μ] : Measurable (fourier μ) :=
  ((continuous_character.comp (continuous_dot.comp continuous_swap)).stronglyMeasurable
    |>.integral_prod_right' (ν := μ)).measurable

private theorem corr (μ : Measure Plane) [IsFiniteMeasure μ] (ξ : Plane) :
    ((‖fourier μ ξ‖^2 : ℝ) : ℂ) =
      ∫ p : Plane × Plane, character (dot (p.1-p.2) ξ) ∂μ.prod μ := by
  rw [Complex.ofReal_pow,← Complex.mul_conj']
  unfold fourier
  rw [← integral_conj, ← integral_prod_mul]
  apply integral_congr_ae (ae_of_all _ fun p => ?_)
  have H : dot (p.1-p.2) ξ = dot p.1 ξ - dot p.2 ξ := by simp [dot]; ring
  rw [H,character_sub]

/-- The Gaussian-weighted Fourier energy at an arbitrary frequency center is exactly the
physical double integral with a Gaussian difference kernel and the center modulation. -/
theorem gaussian_energy_identity (μ : Measure Plane) [IsFiniteMeasure μ] (c : Plane) (R : ℝ) :
    ((∫ v, ‖fourier μ (c+R • v)‖^2 ∂gaussian : ℝ) : ℂ) =
      ∫ p : Plane × Plane, character (dot (p.1-p.2) c) *
        (Real.exp (-( (R*(p.1.1-p.2.1))^2+(R*(p.1.2-p.2.2))^2 )/2) : ℂ) ∂μ.prod μ := by
  let F (v : Plane) (p : Plane × Plane) := character (dot (p.1-p.2) (c+R • v))
  have hF : Continuous (Function.uncurry F) := by
    unfold F Function.uncurry; apply continuous_character.comp
    unfold dot; fun_prop
  have hi : Integrable (Function.uncurry F) (gaussian.prod (μ.prod μ)) :=
    (integrable_const (1:ℝ)).mono' hF.aestronglyMeasurable (ae_of_all _ fun _ => (norm_character _).le)
  rw [← integral_complex_ofReal]
  simp_rw [corr]
  change (∫ v, ∫ p, F v p ∂μ.prod μ ∂gaussian) = _
  rw [integral_integral_swap hi]
  apply integral_congr_ae (ae_of_all _ fun p => ?_)
  have hsplit (v : Plane) : F v p = character (dot (p.1-p.2) c) *
      character (dot (R • (p.1-p.2)) v) := by
    unfold F; rw [← character_add]; congr 1
    simp [dot]; ring
  simp_rw [hsplit,integral_const_mul,gaussian_character]
  rfl

/-- Uniform Gaussian energy bound, keeping the original strip measure in both factors. -/
theorem gaussian_energy_le (μ : Measure Plane) [IsFiniteMeasure μ] (c : Plane) (R : ℝ) :
    ∫ v, ‖fourier μ (c+R • v)‖^2 ∂gaussian ≤
      ∫ p : Plane × Plane, Real.exp (-( (R*(p.1.1-p.2.1))^2+(R*(p.1.2-p.2.2))^2 )/2) ∂μ.prod μ := by
  have H := congrArg norm (gaussian_energy_identity μ c R)
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)] at H
  rw [H]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae (ae_of_all _ fun p => ?_)
  rw [norm_mul,norm_character,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

end Weierstrass.StripProof
