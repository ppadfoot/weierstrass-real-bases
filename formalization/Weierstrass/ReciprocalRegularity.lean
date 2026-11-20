module

public import Weierstrass.StripDual

/-! Hölder control of the physical Taylor remainder in Proposition 2. -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Weierstrass.Reciprocal
open CriticalRay StripProof

private theorem τpos : 0 < τ := by dsimp [τ]; positivity

theorem mixed_product (z x y : ℝ) : |cosineMixed z x y| ≤ τ^2*|x| *|y| := by
  let f (s : ℝ) := Real.cos (τ*(z+y*s+x)) - Real.cos (τ*(z+y*s))
  let f' (s : ℝ) := (-Real.sin (τ*(z+y*s+x)) + Real.sin (τ*(z+y*s)))*(τ*y)
  have hf (s : ℝ) : HasDerivAt f (f' s) s := by
    have h := (((hasDerivAt_id s).const_mul y).const_add z)
    apply HasDerivAt.congr_deriv ((((h.add_const x).const_mul τ).cos).sub ((h.const_mul τ).cos))
    dsimp [f']; ring
  obtain ⟨s,_,eq⟩ := exists_hasDerivAt_eq_slope f f' zero_lt_one
    (fun a _ ↦ (hf a).continuousAt.continuousWithinAt) (fun s _ ↦ hf s)
  have val : cosineMixed z x y = f' s := by simpa [cosineMixed,f] using eq.symm
  have sl := Real.abs_sin_sub_sin_le (τ*(z+y*s)) (τ*(z+y*s+x))
  rw [show τ*(z+y*s)-τ*(z+y*s+x) = -(τ*x) by ring,abs_neg,abs_mul,abs_of_pos τpos] at sl
  rw [val]; dsimp only [f']; rw [abs_mul,abs_mul,abs_of_pos τpos,neg_add_eq_sub]
  calc _ ≤ (τ*|x|)*(τ*|y|) := mul_le_mul_of_nonneg_right sl (mul_nonneg τpos.le (abs_nonneg _))
       _ = _ := by ring

private theorem mixed_coe (z x y : ℝ) : cosineMixed z x y =
    (angleCos ((↑z:UnitAddCircle)+↑y+↑x) - angleCos ((↑z:UnitAddCircle)+↑y)) -
      (angleCos ((↑z:UnitAddCircle)+↑x) - angleCos (↑z)) := by
  simp only [← AddCircle.coe_add, angleCos_coe, cosineMixed, τ]

theorem min_one_le_rpow {α u : ℝ} (hα : 0 < α) (ha : α ≤ 1) (hu : 0 ≤ u) :
    min 1 u ≤ u^α := by
  rcases hu.eq_or_lt with h|h
  · simp [← h, Real.zero_rpow hα.ne']
  by_cases h1 : u ≤ 1
  · rw [min_eq_right h1, ← Real.rpow_one u]
    nth_rw 2 [Real.rpow_one]
    exact Real.rpow_le_rpow_of_exponent_ge h h1 ha
  · exact (min_le_left _ _).trans (Real.one_le_rpow (le_of_not_ge h1) hα.le)

theorem remainder_mode {α : ℝ} (hα : 0 < α) (ha : α ≤ 1) (z x y : ℝ) :
    |cosineMixed z x y - x*(forcingDerivative (↑(z+y))-forcingDerivative (↑z))| ≤
      3*τ^3*|x|^2*|y|^α := by
  let u := if |y| ≤ 1 then y else Int.fract y
  have angle : (↑u:UnitAddCircle) = ↑y := by dsimp [u]; split_ifs <;> simp
  have small : |u| ≤ min 1 |y| := by
    dsimp [u]
    split_ifs with h
    · simp [h]
    · rw [min_eq_left (le_of_not_ge h), abs_of_nonneg (Int.fract_nonneg _)]
      exact (Int.fract_lt_one _).le
  have eqm : cosineMixed z x u = cosineMixed z x y := by rw [mixed_coe z x u,mixed_coe z x y,angle]
  have eqa : (↑(z+u):UnitAddCircle) = ↑(z+y) := by simp only [AddCircle.coe_add,angle]
  have eq := mixed_slope_remainder z x u
  rw [eqm,eqa] at eq
  exact eq.trans (mul_le_mul_of_nonneg_left (small.trans (min_one_le_rpow hα ha (abs_nonneg _))) (by have := τpos; positivity))

private theorem small_to_rpow {α u : ℝ} (hα : 0 < α) (ha : α ≤ 1) (hu : 0 ≤ u) (hu2 : u ≤ 2) :
    u ≤ 2*u^α := by
  by_cases h : u ≤ 1
  · have H := min_one_le_rpow hα ha hu; rw [min_eq_right h] at H
    linarith [Real.rpow_nonneg hu α]
  · linarith [Real.one_le_rpow (le_of_not_ge h) hα.le]

/-- The modulus constant is independent of all angular factors and all forcing phases. -/
def regularityConstant (b g ρ α A : ℝ) :=
  (2*τ^2+3*τ^3*|A|)*∑' j : ℤ, tails (b*g*ρ) (b^2*g*ρ^α) j

/-- For the strict reciprocal case, the normalized physical increment differs from
its past slope by a uniformly Hölder function of the transverse displacement. -/
theorem regularity {b g ρ α A : ℝ} (hb : 1 < b) (hg : 0 < g) (hg1 : g < 1) (hbg : 1 < b*g)
    (hρ : 0 < ρ) (hfast : b*g*ρ < 1) (hα : 0 < α) (ha : α ≤ 1) (hslow : 1 < b^2*g*ρ^α)
    {c d e : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (z : PhaseTorus) (t h : ℝ) (ht : |t| ≤ A) (hh : |h| ≤ 2) :
    |circleRay b g c d (z+transverseOrbit ρ e h) t - circleRay b g c d z t -
      t*(pastSlope b g c d (z+transverseOrbit ρ e h)-pastSlope b g c d z)| ≤
        regularityConstant b g ρ α A * |t| * |h|^α := by
  have bp := zero_lt_one.trans hb
  let z' := z+transverseOrbit ρ e h
  let C := 2*τ^2+3*τ^3*|A|
  have tp := τpos
  have htA : 0 ≤ A := (abs_nonneg t).trans ht
  have hp := Real.rpow_pos_of_pos hρ α
  have sum := summable_tails (show 0 ≤ b*g*ρ by positivity) hfast hslow
  have P := ((summable_past hbg hc hd z').hasSum.sub (summable_past hbg hc hd z).hasSum).mul_left t
  have F := (mixedMode_sum bp hg hg1 hbg ρ hc hd e z t h).sub P
  apply F.norm_le_of_bounded (((sum.hasSum.mul_left C).mul_right |t|).mul_right (|h|^α))
  intro j
  let X := b^j*d j*t
  let Y := ρ^j*e j*h
  have hx : |X| ≤ b^j*|t| := scaled_abs bp (hd j) t j
  have hy : |Y| ≤ ρ^j*|h| := scaled_abs hρ (he j) h j
  have hw : |g^j*c j| ≤ g^j := by rw [abs_mul,abs_of_pos (zpow_pos hg _)]; exact mul_le_of_le_one_right (zpow_pos hg _).le (hc _)
  have ph : (↑(phaseLift z j + Y) : UnitAddCircle) = z' j := by simp [z',Y,transverseOrbit,lift_eq]
  change |mixedMode b g ρ c d e z t h j - t*(pastTerm b g c d z' j - pastTerm b g c d z j)| ≤
    C*tails (b*g*ρ) (b^2*g*ρ^α) j * |t| * |h|^α
  by_cases hj : j < 0
  · rw [pastTerm,pastTerm,if_pos hj,if_pos hj,tails,if_neg (show ¬0 ≤ j by omega),← ph, ← lift_eq z j]
    change |g^j*c j*cosineMixed (phaseLift _ j) X Y - _| ≤ _
    have eq : g^j*c j*cosineMixed (phaseLift z j) X Y - t*((b*g)^j*c j*d j*forcingDerivative (↑(phaseLift z j+Y)) -
        (b*g)^j*c j*d j*forcingDerivative (↑(phaseLift z j))) =
        (g^j*c j)*(cosineMixed (phaseLift z j) X Y -
          X*(forcingDerivative (↑(phaseLift z j+Y))-forcingDerivative (↑(phaseLift z j)))) := by
      dsimp [X]; rw [mul_zpow]; ring
    rw [eq,abs_mul]
    have hpow : (b^j)^2 = (b^2)^j := by rw [← zpow_natCast (b^j) 2,← zpow_mul,mul_comm j,
      zpow_mul,zpow_natCast]
    have hyα : |Y|^α ≤ (ρ^α)^j*|h|^α := by
      rw [Real.rpow_zpow_comm hρ.le, ← Real.mul_rpow (zpow_pos hρ j).le (abs_nonneg _)]
      exact Real.rpow_le_rpow (abs_nonneg Y) hy hα.le
    calc
      _ ≤ g^j*(3*τ^3*(b^j*|t|)^2*((ρ^α)^j*|h|^α)) := by
        apply mul_le_mul hw ((remainder_mode hα ha _ X Y).trans ?_) (abs_nonneg _) (zpow_pos hg j).le
        gcongr
      _ = (3*τ^3*|t|)*(b^2*g*ρ^α)^j*|t| *|h|^α := by rw [mul_pow (b^j) |t|,hpow,mul_zpow,mul_zpow]; ring
      _ ≤ _ := by
        gcongr
        dsimp [C]; rw [abs_of_nonneg htA]
        linarith [mul_le_mul_of_nonneg_left ht (show 0 ≤ 3*τ^3 by positivity),sq_nonneg τ]
  · rw [pastTerm,pastTerm,if_neg hj,if_neg hj,sub_self,mul_zero,sub_zero,tails,if_pos (by omega)]
    change |(g^j*c j)*cosineMixed (phaseLift z j) X Y| ≤ _
    rw [abs_mul]
    calc
      _ ≤ g^j*(τ^2*(b^j*|t|)*(ρ^j*|h|)) := by
        apply mul_le_mul hw ((mixed_product _ X Y).trans ?_) (abs_nonneg _) (zpow_pos hg _).le
        gcongr
      _ ≤ g^j*(τ^2*(b^j*|t|)*(ρ^j*(2*|h|^α))) := by gcongr; exact small_to_rpow hα ha (abs_nonneg h) hh
      _ = (2*τ^2)*(b*g*ρ)^j*|t| *|h|^α := by rw [mul_zpow,mul_zpow]; ring
      _ ≤ _ := by gcongr; dsimp [C]; exact le_add_of_nonneg_right (by positivity)

end Weierstrass.Reciprocal
