module

public import Weierstrass.RaySeed
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Uniform harmonic bounds after a single physical half-turn, at every scale.
The first difference makes the rescaled negative tail absolutely summable. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology ENNReal ComplexConjugate
namespace Weierstrass.RaySeed

def coord (z : PhaseTorus) (j : ℤ) := turn (z j)

theorem norm_coord (z : PhaseTorus) (j : ℤ) : ‖coord z j‖ = 1 := Circle.norm_coe _

theorem turn_add (x y : UnitAddCircle) : turn (x+y) = turn x*turn y := by
  simp [turn,AddCircle.toCircle_add]

theorem turn_neg (x : UnitAddCircle) : turn (-x) = conj (turn x) := by
  unfold turn
  rw [AddCircle.toCircle_neg,Circle.coe_inv_eq_conj]

theorem relative_positive {B : ℂ} (n : ℕ) (j : ℤ) (z : complexPhaseGroup B) :
    turn (relativeAngle 1 j n z) = coord z.val ((n:ℤ)+j)*conj (coord z.val n) := by
  simp [relativeAngle,sub_eq_add_neg,turn_add,turn_neg,coord]

theorem relative_negative {B : ℂ} (n : ℕ) (j : ℤ) (z : complexPhaseGroup B) :
    turn (relativeAngle (-1) j n z) = conj (coord z.val ((n:ℤ)+j))*conj (coord z.val n) := by
  simp [relativeAngle,sub_eq_add_neg,turn_add,turn_neg,coord]

def jump (B : ℂ) (j : ℤ) := turn (↑((B^j/2).re) : UnitAddCircle)-1

def coefficient (B : ℂ) (Q : ℝ) (a : ℤ → ℂ) (n : ℕ) (j : ℤ) :=
  (a ((n:ℤ)+j)/(Q:ℂ)^n)*jump B j

def envelope (b Q M : ℝ) (j : ℤ) :=
  if 0 ≤ j then (2*M)*Q^j else (Real.pi*M)*(Q*b)^j

theorem envelope_summable {b Q : ℝ} (hQ : 0 < Q) (hQ' : Q < 1) (hQb : 1 < Q*b) (M : ℝ) :
    Summable (envelope b Q M) := by
  apply Summable.of_nat_of_neg_add_one
  · simpa [envelope] using (summable_geometric_of_lt_one hQ.le hQ').mul_left (2*M)
  · have h := summable_geometric_of_lt_one (inv_pos.mpr (zero_lt_one.trans hQb)).le
        (inv_lt_one_of_one_lt₀ hQb)
    apply (h.mul_left ((Real.pi*M)*(Q*b)⁻¹)).congr
    intro n
    rw [envelope,if_neg (by omega),show -(↑n+1:ℤ) = -((n+1:ℕ):ℤ) by omega,
      zpow_neg,zpow_natCast,←inv_pow,pow_succ]
    ring

theorem turn_exp (x : ℝ) :
    turn (↑x) = Complex.exp (I*(↑(2*Real.pi*x):ℂ)) := by
  have e := fourier_coe_apply (T:=(1:ℝ)) (n:=1) (x:=x)
  simp only [fourier_apply,one_zsmul] at e
  change (AddCircle.toCircle (↑x : UnitAddCircle) : ℂ) = _
  rw [e]
  congr 1
  push_cast
  ring

theorem jump_bounds (B : ℂ) (j : ℤ) :
    ‖jump B j‖ ≤ 2 ∧ ‖jump B j‖ ≤ Real.pi*‖B‖^j := by
  have sn : ‖turn (↑((B^j/2).re) : UnitAddCircle)‖ = 1 := Circle.norm_coe _
  constructor
  · have b := norm_sub_le (turn (↑((B^j/2).re))) 1
    simpa only [jump,sn,norm_one,one_add_one_eq_two] using b
  · rw [jump,turn_exp]
    refine (Real.norm_exp_I_mul_ofReal_sub_one_le (x:=2*Real.pi*(B^j/2).re)).trans ?_
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi)]
    have le := Complex.abs_re_le_norm (B^j/2)
    rw [norm_div,Complex.norm_ofNat,norm_zpow] at le
    nlinarith only [mul_le_mul_of_nonneg_left le Real.pi_pos.le]

theorem jump_zero (B : ℂ) : jump B 0 = -2 := by
  rw [jump,zpow_zero,show ((1:ℂ)/2).re = 1/2 by norm_num,turn_half]
  norm_num

theorem shifted_coord {B : ℂ} (hb : B ≠ 0) (n : ℕ) (j : ℤ) :
    coord (halfOrbit B 1 n).val ((n:ℤ)+j)-1 = jump B j := by
  change turn (↑((B^((n:ℤ)+j)*((B⁻¹)^n*((1/2)/1))).re)) - 1 = _
  have e : B^((n:ℤ)+j)*((B⁻¹)^n*((1/2)/1)) = B^j/2 := by
    rw [zpow_add₀ hb,zpow_natCast,inv_pow]
    field_simp
  rw [e]; rfl

theorem coefficient_bound {B : ℂ} {Q M : ℝ} (hQ : 0 < Q)
    (a : ℤ → ℂ) (bound : ∀ j : ℤ, ‖a j‖ ≤ M*Q^j) (n : ℕ) (j : ℤ) :
    ‖coefficient B Q a n j‖ ≤ envelope ‖B‖ Q M j := by
  have scale : ‖a ((n:ℤ)+j)/(Q:ℂ)^n‖ ≤ M*Q^j := by
    rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ]
    apply (div_le_iff₀ (pow_pos hQ n)).mpr
    apply (bound _).trans_eq
    rw [zpow_add₀ hQ.ne',zpow_natCast]; ring
  rw [coefficient,norm_mul]
  by_cases hj : 0 ≤ j
  · rw [envelope,if_pos hj]
    exact (mul_le_mul scale (jump_bounds B j).1 (norm_nonneg _) (norm_nonneg _ |>.trans scale)).trans_eq (by ring)
  · rw [envelope,if_neg hj,mul_zpow]
    exact (mul_le_mul scale (jump_bounds B j).2 (norm_nonneg _) (norm_nonneg _ |>.trans scale)).trans_eq (by ring)

def symmetricSeries (a : ℤ → ℂ) (z : PhaseTorus) : ℂ :=
  ∑' j : ℤ, (a j*coord z j+conj (a j*coord z j))

private theorem symmetric_summable {a : ℤ → ℂ} (ha : Summable (fun j ↦ ‖a j‖)) (z : PhaseTorus) :
    Summable (fun j ↦ a j*coord z j+conj (a j*coord z j)) := by
  apply (ha.mul_left 2).of_norm_bounded
  intro j
  exact (norm_add_le _ _).trans (by simp [norm_coord,two_mul])

/-- Exact modulation of the increment. Both Fourier signs are retained. -/
theorem modulated_increment {B : ℂ} {Q : ℝ} (hB : B ≠ 0) (_hQ : 0 < Q)
    {a : ℤ → ℂ} (ha : Summable (fun j ↦ ‖a j‖)) (n : ℕ) (z : complexPhaseGroup B) :
    ((symmetricSeries a ((halfOrbit B 1 n+z).val)-symmetricSeries a z.val)/(Q:ℂ)^n) *
      conj (coord z.val n) =
    ∑' j : ℤ, (coefficient B Q a n j*turn (relativeAngle 1 j n z)+
      conj (coefficient B Q a n j)*turn (relativeAngle (-1) j n z)) := by
  let v := halfOrbit B 1 n
  let f (j : ℤ) := a j*coord (v+z).val j+conj (a j*coord (v+z).val j)
  let g (j : ℤ) := a j*coord z.val j+conj (a j*coord z.val j)
  change (((∑' j, f j)-(∑' j,g j))/(Q:ℂ)^n)*conj (coord z.val n) = _
  rw [←Summable.tsum_sub (symmetric_summable ha (v+z).val) (symmetric_summable ha z.val),
    div_eq_mul_inv,←tsum_mul_right,←tsum_mul_right]
  rw [← (Equiv.addLeft (n:ℤ)).tsum_eq]
  apply tsum_congr
  intro j
  change ((f ((n:ℤ)+j)-g ((n:ℤ)+j))*((Q:ℂ)^n)⁻¹)*_ = _
  have coordAdd (i : ℤ) : coord (v+z).val i = coord v.val i*coord z.val i := turn_add _ _
  rw [relative_positive,relative_negative,coefficient,←shifted_coord hB n j]
  dsimp only [f,g]
  simp only [coordAdd,map_sub,map_mul,div_eq_mul_inv,map_inv₀,map_pow,Complex.conj_ofReal,map_one,v]
  ring

end Weierstrass.RaySeed
