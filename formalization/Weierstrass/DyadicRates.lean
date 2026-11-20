module

public import Weierstrass.PhysicalEntropy

/-! The horizontal and vertical physical scales and the last numerical
limit of the entropy gain in Appendix A. -/
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace Weierstrass.GraphWindow

def horizontalRate (b : ℝ) := Real.log b/Real.log 2
def verticalRate (l : ℝ) := -Real.log l/Real.log 2

theorem rates_admissible {b l : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl' : l < 1) :
    0 < verticalRate l ∧ verticalRate l < horizontalRate b := by
  have b₀ := zero_lt_one.trans hb
  have l₀ := (inv_pos.mpr b₀).trans hl
  have logTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have H := Real.log_lt_log (inv_pos.mpr b₀) hl
  rw [Real.log_inv] at H
  exact ⟨div_pos (neg_pos.mpr (Real.log_neg l₀ hl')) logTwo,
    (div_lt_div_iff_of_pos_right logTwo).mpr (by linarith only [H])⟩

private theorem two_pow_logscale {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (2:ℝ)^(horizontalRate x*n) = x^n := by
  have logTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
  rw [Real.rpow_def_of_pos (by norm_num)]
  change Real.exp (Real.log 2*(Real.log x/Real.log 2*n)) = _
  rw [show Real.log 2*(Real.log x/Real.log 2*n) = n*Real.log x by field_simp]
  rw [← Real.log_pow,Real.exp_log (pow_pos hx n)]

theorem horizontal_width {b : ℝ} (hb : 1 < b) (n : ℕ) :
    (b^n)⁻¹/2 ≤ ((2:ℝ)^⌈horizontalRate b*n⌉₊)⁻¹ ∧
      ((2:ℝ)^⌈horizontalRate b*n⌉₊)⁻¹ ≤ (b^n)⁻¹ := by
  let d := horizontalRate b
  have b₀ := zero_lt_one.trans hb
  have dpos : 0 < d := div_pos (Real.log_pos hb) (Real.log_pos (by norm_num))
  have lo := Nat.le_ceil (d*n)
  have hi := (Nat.ceil_lt_add_one (mul_nonneg dpos.le (Nat.cast_nonneg n))).le
  have low := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) lo
  have high := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hi
  rw [Real.rpow_natCast,two_pow_logscale b₀] at low
  rw [Real.rpow_natCast,Real.rpow_add_one (by norm_num : (2:ℝ) ≠ 0),two_pow_logscale b₀] at high
  constructor
  · calc
      _ = (b^n*2)⁻¹ := by ring
      _ ≤ _ := inv_anti₀ (by positivity) high
  · exact inv_anti₀ (pow_pos b₀ n) low

theorem vertical_width {l : ℝ} (hl : 0 < l) (hl' : l < 1) (n : ℕ) :
    l^n ≤ ((2:ℝ)^⌊verticalRate l*n⌋₊)⁻¹ ∧
      ((2:ℝ)^⌊verticalRate l*n⌋₊)⁻¹ ≤ 2*l^n := by
  let a := verticalRate l
  have eqa : a = horizontalRate l⁻¹ := by simp [a,verticalRate,horizontalRate,Real.log_inv]
  have apos : 0 < a := div_pos (neg_pos.mpr (Real.log_neg hl hl')) (Real.log_pos (by norm_num))
  have lo := Nat.floor_le (mul_nonneg apos.le (Nat.cast_nonneg n))
  have hi := (Nat.lt_floor_add_one (a*n)).le
  have low := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) lo
  have high := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hi
  have eqpow : (2:ℝ)^(a*n) = (l^n)⁻¹ := by rw [eqa,two_pow_logscale (inv_pos.mpr hl),inv_pow]
  rw [Real.rpow_natCast,eqpow] at low
  rw [eqpow,Real.rpow_add_one (by norm_num : (2:ℝ) ≠ 0),Real.rpow_natCast] at high
  have step := inv_anti₀ (by positivity) low
  rw [inv_inv] at step
  refine ⟨step,?_⟩
  change ((2:ℝ)^⌊a*n⌋₊)⁻¹ ≤ _
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  have ht := (inv_le_iff_one_le_mul₀ (pow_pos hl n)).mp high
  linarith only [ht]

theorem holder_scale {b l : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl' : l < 1) (n : ℕ) :
    (((2:ℝ)^⌈horizontalRate b*n⌉₊)⁻¹)^alpha b l ≤ ((2:ℝ)^⌊verticalRate l*n⌋₊)⁻¹ := by
  have l₀ := (inv_pos.mpr (zero_lt_one.trans hb)).trans hl
  have hr := (horizontal_width hb n).2
  have h := Real.rpow_le_rpow (by positivity) hr (alpha_mem_Ioo hb hl hl').1.le
  have hp := pow_pos (zero_lt_one.trans hb) n
  have logB := (Real.log_pos hb).ne'
  rw [Real.rpow_def_of_pos (inv_pos.mpr hp),Real.log_inv,Real.log_pow,alpha] at h
  have e : -(n*Real.log b)*(-Real.log l/Real.log b) = n*Real.log l := by field_simp
  rw [e,← Real.log_pow,Real.exp_log (pow_pos l₀ n)] at h
  exact h.trans (vertical_width l₀ hl' n).1

/-- The positive rate obtained from the physical entropy, before the two
arbitrarily small exponent losses are removed. Boundary constants of order
one per block and square-root boundary losses disappear in this limit. -/
theorem entropy_rate_limit {b l h : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl' : l < 1)
    (hh : 0 < h) (δ C A : ℝ) :
    let a := verticalRate l
    let d := horizontalRate b
    let w (q : ℕ) := ((q:ℝ)*a)⁻¹-((q:ℝ)*d)⁻¹
    Tendsto (fun q ↦ (w q*((1-δ)*max 0 ((q:ℝ)*h*(-Real.log l)-Real.log 2))
      - C*w q - A*Real.sqrt (w q))/Real.log 2)
      atTop (𝓝 ((1-δ)*h*(1-alpha b l))) := by
  let a := verticalRate l
  let d := horizontalRate b
  let V := a⁻¹-d⁻¹
  let w (q : ℕ) := ((q:ℝ)*a)⁻¹-((q:ℝ)*d)⁻¹
  dsimp only
  change Tendsto (fun q ↦ (w q*((1-δ)*max 0 ((q:ℝ)*h*(-Real.log l)-Real.log 2))
    - C*w q - A*Real.sqrt (w q))/Real.log 2) atTop _
  have logB := (Real.log_pos hb).ne'
  have logTwo := (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
  have logL := (Real.log_neg ((inv_pos.mpr (zero_lt_one.trans hb)).trans hl) hl').ne
  have hpos := mul_pos hh (neg_pos.mpr (lt_of_le_of_ne (Real.log_nonpos
    ((inv_pos.mpr (zero_lt_one.trans hb)).trans hl).le hl'.le) logL))
  have asprod (q : ℕ) : w q = V*(q:ℝ)⁻¹ := by simp [w,V,mul_inv_rev]; ring
  have inv0 : Tendsto (fun q : ℕ ↦ (q:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have w0 : Tendsto w atTop (𝓝 0) := by
    rw [funext asprod]
    simpa only [mul_zero] using inv0.const_mul V
  have gain (q : ℕ) (hq : q ≠ 0) (hq' : Real.log 2 ≤ (q:ℝ)*h*(-Real.log l)) :
      w q*((1-δ)*max 0 ((q:ℝ)*h*(-Real.log l)-Real.log 2)) =
        V*((1-δ)*(h*(-Real.log l))) - (V*((1-δ)*Real.log 2))*(q:ℝ)⁻¹ := by
    rw [asprod,max_eq_right (sub_nonneg.mpr hq')]
    field_simp
  have grow : Tendsto (fun q : ℕ ↦ (q:ℝ)*h*(-Real.log l)) atTop atTop := by
    simpa only [mul_assoc] using (tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_mul_const hpos
  have numerical : V*((1-δ)*(h*(-Real.log l)))/Real.log 2 = (1-δ)*h*(1-alpha b l) := by
    dsimp [V,a,d,alpha,verticalRate,horizontalRate]
    field_simp
    ring
  rw [← numerical]
  have T := ((((tendsto_const_nhds (x:=V*((1-δ)*(h*(-Real.log l))))).sub (inv0.const_mul (V*((1-δ)*Real.log 2)))).sub
    (w0.const_mul C)).sub ((Real.continuous_sqrt.continuousAt.tendsto.comp w0).const_mul A)).div_const (Real.log 2)
  simp only [mul_zero,Real.sqrt_zero,sub_zero] at T
  apply T.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ), grow.eventually_ge_atTop (Real.log 2)] with q hq hq'
  simp only [gain q hq.ne' hq', Function.comp_apply]

end Weierstrass.GraphWindow
