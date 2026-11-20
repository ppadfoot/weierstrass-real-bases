module

public import Weierstrass.Graph

/-! Uniform choice of consecutive active harmonics at every nonzero displacement. -/

public noncomputable section
open Set

namespace Weierstrass

private theorem base_neg_alpha {b lam : ℝ} (hb : 1 < b) (hlam : 0 < lam) :
    b ^ (-alpha b lam) = lam := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hb), alpha]
  rw [show Real.log b * -(-Real.log lam / Real.log b) = Real.log lam by
    field_simp [(Real.log_pos hb).ne']]
  exact Real.exp_log hlam

/-- At time u, m consecutive Fourier coordinates of the bilateral cosine increment
have magnitude at least a fixed positive multiple of |u|^α. The first
frequency may have a negative index. The inequalities hold for either sign of u. -/
theorem exists_active_harmonics {b l : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl' : l < 1)
    (m : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, u ≠ 0 → ∃ k : ℤ, ∀ d : ℕ, d ≤ m →
      C * |u| ^ alpha b l ≤ |2 * l ^ (k - (d : ℤ)) *
        Real.sin (Real.pi * (b ^ (k - (d : ℤ)) * u))| := by
  have hb₀ := zero_lt_one.trans hb
  have hl₀ := (inv_pos.mpr hb₀).trans hl
  have hα := (alpha_mem_Ioo hb hl hl').1
  let c := 1 / (4 * b ^ (m+1))
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨4*c, by positivity, ?_⟩
  intro u hu
  have hu' := abs_pos.mpr hu
  obtain ⟨k, hkl, hku⟩ := exists_mem_Ico_zpow (x := 1/(4*|u|)) (by positivity) hb
  have hlow : 1/(4*b) ≤ b ^ k * |u| := by
    rw [zpow_add_one₀ hb₀.ne'] at hku
    apply (div_le_iff₀ (by positivity : 0 < 4*b)).mpr
    have key := (div_lt_iff₀ (by positivity : 0 < 4*|u|)).mp hku
    linarith only [key]
  have hhigh : b ^ k * |u| ≤ 1/4 := by
    have := (le_div_iff₀ (by positivity : 0 < 4*|u|)).mp hkl
    linarith
  refine ⟨k, ?_⟩
  intro d hd
  let j := k-(d:ℤ)
  have hratio : b ^ j * |u| = (b ^ k * |u|) / b ^ d := by
    simp only [j,zpow_sub₀ hb₀.ne', zpow_natCast]; ring
  have hdl : 1 ≤ b ^ d := one_le_pow₀ hb.le
  have hdu : b ^ d ≤ b ^ m := pow_le_pow_right₀ hb.le hd
  have hx₀ : c ≤ b ^ j * |u| := by
    rw [hratio, le_div_iff₀ (pow_pos hb₀ d)]
    refine (mul_le_mul_of_nonneg_left hdu hc.le).trans ?_
    dsimp [c]
    rw [pow_succ]
    field_simp
    nlinarith [(div_le_iff₀ (show 0 < 4*b by positivity)).mp hlow]
  have hx₁ : b ^ j * |u| ≤ 1/4 := by
    rw [hratio, div_le_iff₀ (pow_pos hb₀ d)]
    linarith
  have hs : 2*(b ^ j * |u|) ≤ |Real.sin (Real.pi*(b^j*u))| := by
    have hπ := Real.mul_abs_le_abs_sin (x := Real.pi*(b^j*u)) (by
      rw [abs_mul, abs_of_pos Real.pi_pos, abs_mul, abs_of_pos (zpow_pos hb₀ j)]
      exact (mul_le_mul_of_nonneg_left hx₁ Real.pi_pos.le).trans (by linarith [Real.pi_pos]))
    rw [abs_mul, abs_of_pos Real.pi_pos, abs_mul, abs_of_pos (zpow_pos hb₀ j),
      ← mul_assoc, div_mul_cancel₀ _ Real.pi_pos.ne'] at hπ
    exact hπ
  have hpow : |u| ^ alpha b l ≤ l ^ j := by
    have hsmall : |u| ≤ (b ^ j)⁻¹ := by
      rw [← one_div, le_div_iff₀ (zpow_pos hb₀ j)]
      linarith only [hx₁]
    calc
      _ ≤ ((b ^ j)⁻¹) ^ alpha b l := Real.rpow_le_rpow (abs_nonneg _) hsmall hα.le
      _ = l ^ j := by rw [← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_zpow_comm hb₀.le,
        base_neg_alpha hb hl₀]
  change 4*c * |u| ^ alpha b l ≤ |2 * l ^ j * Real.sin (Real.pi*(b^j*u))|
  rw [abs_mul, abs_of_pos (show 0 < 2*l^j by positivity)]
  calc
    _ ≤ 4*c * l ^ j := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (2*l^j)*(2*c) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ((by linarith : 2*c ≤ 2*(b^j*|u|)).trans hs) (by positivity)

end Weierstrass
