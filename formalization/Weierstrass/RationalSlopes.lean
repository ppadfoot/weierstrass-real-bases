module

public import Weierstrass.ConditionalDimension

/-! The rational-base specialization following Theorem B.1. For a reduced
base P/Q the primitive polynomial is P−QX. The calculation works directly
for any such linear recurrence without requiring a coprimality assumption. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Real
open scoped ENNReal Topology
namespace Weierstrass.Predecessor

theorem rational_conditional_slope_dimension {P Q : ℕ} (q0 : 0<Q) (pq : Q<P)
    {b l : ℝ} (ratio : b=(P:ℝ)/Q) (hl : b⁻¹<l) (hl1 : l<1) (η : ℕ → ℝ) :
    let ν (w : Fin 1 → UnitAddCircle) := baseSlopeLaw (by omega : 0<P) 1 (fun _ ↦ -(Q:ℤ)) (centralLift w) η (b*l)⁻¹
    ∀ᵐ w, ∀ᵐ y ∂ν w, Tendsto (fun r : ℝ ↦ log ((ν w).real (Icc (y-r) (y+r))) / log r) (𝓝[>] 0) (𝓝 1) := by
  intro ν
  have qr : 0<(Q:ℝ) := by exact_mod_cast q0
  have one : (1:ℝ)≤Q := by exact_mod_cast q0
  have bp : 1<b := by rw [ratio];exact (one_lt_div qr).mpr (by exact_mod_cast pq)
  have b0 := zero_lt_one.trans bp
  have lp := (inv_pos.mpr b0).trans hl
  have bg := (inv_lt_iff_one_lt_mul₀' b0).mp hl
  have eqb : b*Q=P := by rw [ratio];field_simp
  have poly : (P:ℝ)+b*∑ k ∈ Finset.range 1, ((-(Q:ℤ):ℤ):ℝ)*b^k = 0 := by simp;linarith only [eqb]
  have room : b*l ≤ P := by
    rw [←eqb]
    exact mul_le_mul_of_nonneg_left (hl1.le.trans one) b0.le
  have eq : min 1 (log P/log (1/(b*l)⁻¹))=1 := by
    rw [one_div,inv_inv,min_eq_left]
    exact (one_le_div (Real.log_pos bg)).mpr (Real.log_le_log (zero_lt_one.trans bg) room)
  have h := conditional_slope_exact_dimension (p:=P) (d:=0) (by omega) (fun _ ↦ -(Q:ℤ)) (by exact neg_ne_zero.mpr (by exact_mod_cast q0.ne'))
    (inv_pos.mpr b0) (inv_lt_one_of_one_lt₀ bp) (inv_pos.mpr (mul_pos b0 lp)) (inv_lt_one_of_one_lt₀ bg)
    (mul_inv_cancel₀ b0.ne') poly 0 η
  simpa only [pow_zero,mul_one,eq] using h

end Weierstrass.Predecessor
