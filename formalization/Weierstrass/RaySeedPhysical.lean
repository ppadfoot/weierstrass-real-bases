module

public import Weierstrass.RayUniform

/-! Actual derivative harmonics in the initial exponent argument, for a pair
of distinct transverse translations separated by s. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology ENNReal ComplexConjugate
namespace Weierstrass.RaySeed

local instance (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

def circleJump (x : ℝ) := turn (↑x) - 1

theorem circleJump_large (x : ℝ) (hx : |x| ≤ 1/2) : 4*|x| ≤ ‖circleJump x‖ := by
  rw [circleJump,turn_exp,Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2*Real.pi*x/2 = Real.pi*x by ring]
  have hp := Real.pi_pos
  have h : |Real.pi*x| ≤ Real.pi/2 := by
    rw [abs_mul,abs_of_pos hp]
    linarith only [mul_le_mul_of_nonneg_left hx hp.le]
  have p := Real.mul_abs_le_abs_sin h
  rw [abs_mul,abs_of_pos hp,show 2/Real.pi*(Real.pi*|x|) = 2*|x| by field_simp] at p
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith only [p]

theorem circleJump_bounds (x : ℝ) : ‖circleJump x‖ ≤ 2 ∧ ‖circleJump x‖ ≤ (2*Real.pi)*|x| := by
  have sn : ‖turn (↑x)‖ = 1 := Circle.norm_coe _
  constructor
  · simpa only [circleJump,sn,norm_one,one_add_one_eq_two] using norm_sub_le (turn (↑x)) 1
  · rw [circleJump,turn_exp]
    apply (Real.norm_exp_I_mul_ofReal_sub_one_le (x:=2*Real.pi*x)).trans_eq
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]

/-- The factor Iπ is the positive-frequency derivative of cos(2πt).
The phase absorbs physical motion, the first transverse translate, and the
original prescribed phases. -/
def derivativeCoeff (q ρ s : ℝ) (u e : ℤ → ℝ) (θ : PhaseTorus) (j : ℤ) : ℂ :=
  I * (↑(Real.pi*q^j*u j):ℂ) * coord θ j * circleJump (ρ^j*e j*s)

theorem norm_derivativeCoeff {q : ℝ} (hq : 0 < q) (ρ s : ℝ) (u e : ℤ → ℝ)
    (θ : PhaseTorus) (j : ℤ) :
    ‖derivativeCoeff q ρ s u e θ j‖ =
      Real.pi*q^j*|u j| *‖circleJump (ρ^j*e j*s)‖ := by
  simp only [derivativeCoeff,norm_mul,Complex.norm_I,one_mul,norm_coord,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,abs_of_pos (zpow_pos hq j)]

def physicalEnvelope (q ρ s : ℝ) (j : ℤ) : ℝ :=
  if 0 ≤ j then (2*Real.pi^2*|s|)*(q*ρ)^j else (2*Real.pi)*q^j

theorem summable_physicalEnvelope {q ρ : ℝ} (hq : 1 < q) (hρ : 0 < ρ) (hQ : q*ρ < 1) (s : ℝ) :
    Summable (physicalEnvelope q ρ s) := by
  apply Summable.of_nat_of_neg_add_one
  · simpa [physicalEnvelope] using (summable_geometric_of_lt_one (mul_pos (zero_lt_one.trans hq) hρ).le hQ).mul_left (2*Real.pi^2*|s|)
  · have small := summable_geometric_of_lt_one (inv_pos.mpr (zero_lt_one.trans hq)).le
        (inv_lt_one_of_one_lt₀ hq)
    apply (small.mul_left (2*Real.pi*q⁻¹)).congr
    intro n
    rw [physicalEnvelope,if_neg (by omega),show -(↑n+1:ℤ) = -((n+1:ℕ):ℤ) by omega,
      zpow_neg,zpow_natCast,←inv_pow,pow_succ]; ring

theorem physical_bounds {q ρ : ℝ} (hq : 0 < q) (hρ : 0 < ρ)
    (s : ℝ) {u e : ℤ → ℝ} (hu : ∀ j, |u j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (θ : PhaseTorus) (j : ℤ) :
    ‖derivativeCoeff q ρ s u e θ j‖ ≤ (2*Real.pi^2*|s|)*(q*ρ)^j ∧
      ‖derivativeCoeff q ρ s u e θ j‖ ≤ 2*Real.pi*q^j := by
  rw [norm_derivativeCoeff hq]
  have A : Real.pi*q^j*|u j| ≤ Real.pi*q^j := mul_le_of_le_one_right (by positivity) (hu j)
  have ebd : ρ^j*|e j| ≤ ρ^j := mul_le_of_le_one_right (by positivity) (he j)
  have J := circleJump_bounds (ρ^j*e j*s)
  have J' := J.2
  rw [abs_mul,abs_mul,abs_of_pos (zpow_pos hρ j)] at J'
  constructor
  · apply (mul_le_mul A (J'.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right ebd (abs_nonneg _)) (by positivity))) (norm_nonneg _) (by positivity)).trans_eq
    rw [mul_zpow]; ring
  · exact (mul_le_mul A J.1 (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem derivative_frequent {q ρ s δ : ℝ} (hq : 0 < q) (hρ : 0 < ρ) (hρ' : ρ < 1)
    {u e : ℤ → ℝ} (he : ∀ j, |e j| ≤ 1) (θ : PhaseTorus)
    (good : ∃ᶠ n : ℕ in atTop, δ ≤ |u n*e n|) :
    ∃ᶠ n : ℕ in atTop, (4*Real.pi*|s| *δ)*(q*ρ)^n ≤ ‖derivativeCoeff q ρ s u e θ n‖ := by
  have sm := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ').mul_const |s|
  rw [zero_mul] at sm
  apply (good.and_eventually (sm.eventually_lt_const (show (0:ℝ)<1/2 by norm_num))).mono
  rintro n ⟨g,small⟩
  rw [norm_derivativeCoeff hq,zpow_natCast,zpow_natCast]
  have ebd := mul_le_of_le_one_right (pow_nonneg hρ.le n) (he n)
  have a : |ρ^n*e n*s| ≤ 1/2 := by
    rw [abs_mul,abs_mul,abs_of_pos (pow_pos hρ n)]
    exact (mul_le_mul_of_nonneg_right ebd (abs_nonneg _)).trans small.le
  have J := circleJump_large _ a
  rw [abs_mul,abs_mul,abs_of_pos (pow_pos hρ n)] at J
  apply le_trans _ (mul_le_mul_of_nonneg_left J (by positivity : 0 ≤ Real.pi*q^n*|u n|))
  rw [mul_pow]
  rw [abs_mul] at g
  calc
    _ ≤ (4*Real.pi*|s| *(|u n| *|e n|))*(q^n*ρ^n) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left g (by positivity)) (by positivity)
    _ = _ := by ring

end Weierstrass.RaySeed
