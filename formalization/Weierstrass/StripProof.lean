module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Fourier estimates for collisions of strip projections

A finite Fejér majorant permits real projections of arbitrary finite Borel measures,
including projections of two different strips translated by their strip indices. -/

@[expose] public noncomputable section
open Set MeasureTheory Complex
open scoped BigOperators ComplexConjugate

namespace Weierstrass.StripProof

/-- The additive character in radian normalization. -/
def character (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * I)

@[simp] theorem norm_character (t : ℝ) : ‖character t‖ = 1 := by
  simp [character, Complex.norm_exp, Complex.mul_re]

theorem character_sub (s t : ℝ) : character (s - t) = character s * conj (character t) := by
  unfold character
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub]
  ring

theorem continuous_character : Continuous character := by unfold character; fun_prop

/-- The unnormalized Dirichlet sum, whose squared modulus is a positive Fejér kernel. -/
def dirichlet (N : ℕ) (t : ℝ) : ℂ := ∑ k ∈ Finset.range N, character (k*t)

theorem fejer_lower {N : ℕ} {t : ℝ} (ht : (N : ℝ)*|t| ≤ 1) :
    (N : ℝ)^2 / 4 ≤ ‖dirichlet N t‖^2 := by
  have half (k : ℕ) (hk : k ∈ Finset.range N) : 1/2 ≤ (character (k*t)).re := by
    have hk' : (k : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hk).le
    have ha : |(k : ℝ) * t| ≤ 1 := by
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
      exact (mul_le_mul_of_nonneg_right hk' (abs_nonneg _)).trans ht
    have c := Real.one_sub_sq_div_two_le_cos (x := (k : ℝ)*t)
    rw [← sq_abs] at c
    simp only [character, Complex.exp_ofReal_mul_I_re]
    nlinarith [sq_nonneg (1 - |(k:ℝ)*t|), mul_nonneg (sub_nonneg.mpr ha)
      (show 0 ≤ 1 + |(k:ℝ)*t| by positivity)]
  have h : (N : ℝ)/2 ≤ (dirichlet N t).re := by
    simpa [dirichlet, Complex.re_sum, div_eq_mul_inv] using Finset.sum_le_sum half
  have h' := h.trans (Complex.re_le_norm _)
  nlinarith [mul_nonneg (sub_nonneg.mpr h') (by positivity : 0 ≤ ‖dirichlet N t‖ + (N:ℝ)/2)]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Characteristic coefficient of a real projection of a finite measure. -/
def coefficient (μ : Measure X) (f : X → ℝ) (k : ℝ) : ℂ := ∫ x, character (k*f x) ∂μ

private theorem char_int (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Measurable f) (k : ℝ) : Integrable (fun x => character (k*f x)) μ :=
  (integrable_const (1:ℝ)).mono' ((continuous_character.measurable.comp
    (measurable_const.mul hf)).aestronglyMeasurable) (ae_of_all _ fun _ => (norm_character _).le)

private theorem fejer_expand (N : ℕ) (s t : ℝ) :
    ((‖dirichlet N (s - t)‖^2 : ℝ) : ℂ) =
      ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
        character (((a:ℝ)-b)*s) * conj (character (((a:ℝ)-b)*t)) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [dirichlet, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  rw [← character_sub, ← character_sub]
  congr 1; ring

/-- Exact finite-frequency energy formula for a mixed collision kernel. -/
theorem fejer_energy_identity (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {f : X → ℝ} {g : Y → ℝ} (hf : Measurable f) (hg : Measurable g) (N : ℕ) :
    ∫ p, ‖dirichlet N (f p.1 - g p.2)‖^2 ∂μ.prod ν =
      (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
        coefficient μ f ((a:ℝ)-b) * conj (coefficient ν g ((a:ℝ)-b))).re := by
  let A (a b : ℕ) (p : X × Y) := character (((a:ℝ)-b)*f p.1) *
    conj (character (((a:ℝ)-b)*g p.2))
  have hA (a b : ℕ) : Integrable (A a b) (μ.prod ν) := by
    exact (char_int μ hf _).mul_prod ((integrable_const (1:ℝ)).mono'
      ((Complex.continuous_conj.comp continuous_character).measurable.comp
        (measurable_const.mul hg)).aestronglyMeasurable (ae_of_all _ fun _ => by simp))
  have hId (a b : ℕ) : ∫ p, A a b p ∂μ.prod ν =
      coefficient μ f ((a:ℝ)-b) * conj (coefficient ν g ((a:ℝ)-b)) := by
    unfold A coefficient
    rw [integral_prod_mul (fun x => character (((a:ℝ)-b)*f x))
      (fun y => conj (character (((a:ℝ)-b)*g y))), integral_conj]
  apply Complex.ofReal_injective
  have H : ((∫ p, ‖dirichlet N (f p.1 - g p.2)‖^2 ∂μ.prod ν : ℝ) : ℂ) =
      ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
        coefficient μ f ((a:ℝ)-b) * conj (coefficient ν g ((a:ℝ)-b)) := by
    rw [← integral_complex_ofReal]
    simp_rw [fejer_expand]
    change (∫ p, ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, A a b p ∂μ.prod ν) = _
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hA a b))]
    simp_rw [integral_finsetSum _ (fun b _ => hA _ b),hId]
  exact_mod_cast congrArg Complex.re H

/-- Mixed collision probability is controlled by the two individual Fourier energies.
The support or absolute position of the two projections is arbitrary. -/
theorem projected_collision_le (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {f : X → ℝ} {g : Y → ℝ} (hf : Measurable f) (hg : Measurable g)
    {N : ℕ} {r : ℝ} (hNr : (N:ℝ)*r ≤ 1) :
    ((N:ℝ)^2/4) * (μ.prod ν).real {p | |f p.1 - g p.2| ≤ r} ≤
      ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
        (‖coefficient μ f ((a:ℝ)-b)‖^2 + ‖coefficient ν g ((a:ℝ)-b)‖^2)/2 := by
  let S : Set (X × Y) := {p | |f p.1 - g p.2| ≤ r}
  have md : Measurable (fun p : X × Y => f p.1 - g p.2) := (hf.comp measurable_fst).sub
    (hg.comp measurable_snd)
  have mS : MeasurableSet S := measurableSet_le (continuous_abs.measurable.comp md) measurable_const
  have bound (t : ℝ) : ‖dirichlet N t‖ ≤ N := by
    simpa [dirichlet] using (norm_sum_le (Finset.range N) (fun k : ℕ => character (k*t)))
  have cont : Continuous (dirichlet N) := continuous_finsetSum _ fun k _ =>
    continuous_character.comp (continuous_const.mul continuous_id)
  have hint : Integrable (fun p : X × Y => ‖dirichlet N (f p.1 - g p.2)‖^2) (μ.prod ν) :=
    (integrable_const ((N:ℝ)^2)).mono' ((cont.measurable.comp md).norm.pow_const
      2).aestronglyMeasurable (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (bound _) _)
  calc
    _ = ∫ p, S.indicator (fun _ => (N:ℝ)^2/4) p ∂μ.prod ν := by
      rw [integral_indicator_const _ mS,smul_eq_mul,mul_comm]
    _ ≤ ∫ p, ‖dirichlet N (f p.1 - g p.2)‖^2 ∂μ.prod ν := by
      apply integral_mono ((integrable_const _).indicator mS) hint
      intro p
      by_cases hp : p ∈ S
      · rw [Set.indicator_of_mem hp]; apply fejer_lower
        exact (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg N)).trans hNr
      · simp [Set.indicator_of_notMem hp]
    _ = _ := fejer_energy_identity μ ν hf hg N
    _ ≤ _ := by
      simp only [Complex.re_sum]
      apply Finset.sum_le_sum; intro a _
      apply Finset.sum_le_sum; intro b _
      apply (Complex.re_le_norm _).trans
      rw [norm_mul,Complex.norm_conj]
      nlinarith [sq_nonneg (‖coefficient μ f ((a:ℝ)-b)‖ - ‖coefficient ν g ((a:ℝ)-b)‖)]

end Weierstrass.StripProof
