module

public import Weierstrass.RayInformation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Physical equal-rate strip linearization and the past slope -/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Weierstrass.StripProof
open CriticalRay

private theorem τpos : 0 < τ := by dsimp [τ]; positivity

/-- The oriented physical derivative of the forcing on the phase circle. -/
def forcingDerivative (z : UnitAddCircle) : ℝ := τ * angleCos (z+↑(1/4:ℝ))

theorem forcingDerivative_coe (z : ℝ) : forcingDerivative (↑z) = -τ*Real.sin (τ*z) := by
  rw [forcingDerivative,← AddCircle.coe_add,angleCos_coe,
    show 2*Real.pi*(z+1/4)=τ*z+Real.pi/2 by dsimp [τ]; ring,Real.cos_add_pi_div_two]; ring

/-- The quadratic physical Taylor remainder is Lipschitz in the transverse phase;
the constant is independent of the transverse displacement. -/
theorem mixed_slope_remainder (z x y : ℝ) :
    |cosineMixed z x y - x*(forcingDerivative (↑(z+y))-forcingDerivative (↑z))| ≤
      3*τ^3*|x|^2*|y| := by
  let X := τ*x
  let Y := τ*y
  let Z := τ*z
  have hc : |Real.cos X-1| ≤ X^2/2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one _))]
    linarith [Real.one_sub_sq_div_two_le_cos (x := X)]
  have hsin : |X-Real.sin X| ≤ 2*X^2 := by
    by_cases h : |X| ≤ 1
    · apply (Real.abs_sub_sin_le X).trans
      nlinarith [mul_le_mul_of_nonneg_right h (sq_nonneg |X|),sq_abs X]
    · have hh := (abs_sub X (Real.sin X)).trans (add_le_add (le_refl _) (Real.abs_sin_le_abs (x := X)))
      nlinarith [mul_nonneg (show 0 ≤ |X|-1 by linarith) (abs_nonneg X),sq_abs X]
  have hcz : |Real.cos (Z+Y) - Real.cos Z| ≤ |Y| := by simpa using Real.abs_cos_sub_cos_le (Z+Y) Z
  have hsz : |Real.sin (Z+Y) - Real.sin Z| ≤ |Y| := by simpa using Real.abs_sin_sub_sin_le (Z+Y) Z
  have eq : cosineMixed z x y - x*(forcingDerivative (↑(z+y))-forcingDerivative (↑z)) =
      (Real.cos (Z+Y)-Real.cos Z)*(Real.cos X-1) +
        (Real.sin (Z+Y)-Real.sin Z)*(X-Real.sin X) := by
    rw [forcingDerivative_coe,forcingDerivative_coe]
    unfold cosineMixed
    rw [show τ*(z+y+x)=(Z+Y)+X by dsimp [Z,Y,X]; ring,
      show τ*(z+y)=Z+Y by dsimp [Z,Y]; ring,show τ*(z+x)=Z+X by dsimp [Z,X]; ring,
      Real.cos_add (Z+Y) X,Real.cos_add Z X]
    dsimp [X,Z,Y]; ring
  rw [eq]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul]
  calc
    _ ≤ |Y| *(X^2/2)+|Y| *(2*X^2) := add_le_add
      (mul_le_mul hcz hc (abs_nonneg _) (abs_nonneg _)) (mul_le_mul hsz hsin (abs_nonneg _) (abs_nonneg _))
    _ ≤ _ := by
      dsimp only [X,Y]; rw [abs_mul,abs_of_pos τpos,sq_abs]
      nlinarith [mul_nonneg (show 0 ≤ τ^3*x^2 by positivity) (abs_nonneg y)]

def tails (p q : ℝ) (j : ℤ) : ℝ := if 0 ≤ j then p^j else q^j

theorem summable_tails {p q : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) (hq : 1 < q) :
    Summable (tails p q) := by
  apply Summable.of_nat_of_neg_add_one
  · simpa [tails] using summable_geometric_of_lt_one hp hp1
  · have G := (summable_geometric_of_lt_one (inv_nonneg.mpr (by linarith : 0 ≤ q))
      (inv_lt_one_of_one_lt₀ hq)).mul_right q⁻¹
    apply G.congr; intro n
    rw [tails,if_neg (by omega),show -(↑n+1:ℤ) = -((n+1:ℕ):ℤ) by omega,
      zpow_neg,zpow_natCast,← inv_pow,pow_succ]

def pastTerm (b g : ℝ) (c d : ℤ → ℝ) (z : PhaseTorus) (j : ℤ) : ℝ :=
  if j < 0 then (b*g)^j*c j*d j*forcingDerivative (z j) else 0

def pastSlope (b g : ℝ) (c d : ℤ → ℝ) (z : PhaseTorus) : ℝ :=
  ∑' j, pastTerm b g c d z j

theorem abs_deriv (z : UnitAddCircle) : |forcingDerivative z| ≤ τ := by
  rw [forcingDerivative,abs_mul,abs_of_pos τpos]
  apply mul_le_of_le_one_right τpos.le
  exact (Complex.abs_re_le_norm _).trans_eq (Circle.norm_coe _)

theorem summable_past {b g : ℝ} (hbg : 1 < b*g) {c d : ℤ → ℝ}
    (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (z : PhaseTorus) :
    Summable (pastTerm b g c d z) := by
  apply ((summable_tails (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (0:ℝ) < 1) hbg).mul_left τ).of_norm_bounded
  intro j
  by_cases hj : j < 0
  · rw [pastTerm,if_pos hj,tails,if_neg (by omega),Real.norm_eq_abs]
    simp only [abs_mul,abs_of_pos (zpow_pos (zero_lt_one.trans hbg) j)]
    calc
      _ ≤ (b*g)^j * 1 * 1 * τ := by gcongr; exacts [hc j,hd j,abs_deriv _]
      _ = _ := by ring
  · rw [pastTerm,if_neg hj,norm_zero,tails,if_pos (by omega)]
    positivity

/-- Choose the actual lifted phases when invoking real trigonometric estimates. -/
def phaseLift (z : PhaseTorus) (j : ℤ) : ℝ := AddCircle.equivIco 1 0 (z j)

theorem lift_eq (z : PhaseTorus) (j : ℤ) : (↑(phaseLift z j) : UnitAddCircle) = z j :=
  AddCircle.coe_equivIco

def mixedMode (b g ρ : ℝ) (c d e : ℤ → ℝ) (z : PhaseTorus) (x h : ℝ) (j : ℤ) : ℝ :=
  g^j*c j*cosineMixed (phaseLift z j) (b^j*d j*x) (ρ^j*e j*h)

theorem mixedMode_sum {b g : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1)
    (hbg : 1 < b*g) (ρ : ℝ) {c d : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1)
    (e : ℤ → ℝ) (z : PhaseTorus) (x h : ℝ) :
    HasSum (mixedMode b g ρ c d e z x h)
      (circleRay b g c d (z+transverseOrbit ρ e h) x - circleRay b g c d z x) := by
  let z' := transversePhase ρ e (phaseLift z) h
  have orig : (fun j => (↑(phaseLift z j) : UnitAddCircle)) = z := funext (lift_eq z)
  have tran : (fun j => (↑(z' j) : UnitAddCircle)) = z+transverseOrbit ρ e h := by
    funext j; simp [z',transversePhase,transverseOrbit,lift_eq]
  have e1 : circleRay b g c d (z+transverseOrbit ρ e h) x = rayIncrement b g c d z' x :=
    tran ▸ circleRay_real b g c d z' x
  have e2 : circleRay b g c d z x = rayIncrement b g c d (phaseLift z) x := by
    exact (congrArg (fun a => circleRay b g c d a x) orig).symm.trans (circleRay_real _ _ _ _ _ _)
  rw [e1,e2]
  have H := (summable_rayTerm hb hg hg1 hbg hc hd z' x).hasSum.sub
    (summable_rayTerm hb hg hg1 hbg hc hd (phaseLift z) x).hasSum
  apply H.congr_fun
  intro j
  dsimp [mixedMode,rayTerm,z',transversePhase,cosineMixed,τ]
  ring

theorem scaled_abs {b : ℝ} (hb : 0 < b) {u : ℝ} (hu : |u| ≤ 1) (x : ℝ) (j : ℤ) :
    |b^j*u*x| ≤ b^j*|x| := by
  rw [abs_mul,abs_mul,abs_of_pos (zpow_pos hb _)]
  gcongr; exact mul_le_of_le_one_right (zpow_pos hb _).le hu

/-- The constant in B2 is independent of phases, weights, directions and strip scale. -/
def linearizationConstant (b g : ℝ) := (2*τ+27*τ^3) * ∑' j : ℤ, tails (g*b⁻¹) (b*g) j

/-- **B2** on the actual equal-rate weighted circle model. The estimate is global in the
stable displacement h and applies at an arbitrary starting phase. -/
theorem equal_rate_linearization_on {b g : ℝ} (hb : 1 < b) (hg : 0 < g) (hg1 : g < 1) (hbg : 1 < b*g)
    {c d e : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (z : PhaseTorus) {x X₀ : ℝ} (hx : |x| ≤ X₀) (h : ℝ) :
    |circleRay b g c d (z+transverseOrbit b⁻¹ e h) x - circleRay b g c d z x -
      x*(pastSlope b g c d (z+transverseOrbit b⁻¹ e h)-pastSlope b g c d z)| ≤
        ((2*τ+3*τ^3*X₀^2) * ∑' j : ℤ, tails (g*b⁻¹) (b*g) j) * |h| := by
  have bp : 0 < b := zero_lt_one.trans hb
  have rp := inv_pos.mpr bp
  have ri := inv_lt_one_of_one_lt₀ hb
  let z' := z+transverseOrbit b⁻¹ e h
  let C := 2*τ+3*τ^3*X₀^2
  have tp := τpos
  have ht := summable_tails (mul_pos hg rp).le ((mul_lt_of_lt_one_right hg ri).trans hg1) hbg
  have P := ((summable_past hbg hc hd z').hasSum.sub (summable_past hbg hc hd z).hasSum).mul_left x
  have F := (mixedMode_sum bp hg hg1 hbg b⁻¹ hc hd e z x h).sub P
  apply F.norm_le_of_bounded ((ht.hasSum.mul_left C).mul_right |h|)
  intro j
  let X := b^j*d j*x
  let Y := b⁻¹^j*e j*h
  have hx' : |X| ≤ b^j*X₀ := (scaled_abs bp (hd _) _ _).trans (by gcongr)
  have hy : |Y| ≤ b⁻¹^j*|h| := scaled_abs rp (he _) _ _
  have hw : |g^j*c j| ≤ g^j := by rw [abs_mul,abs_of_pos (zpow_pos hg _)]; exact mul_le_of_le_one_right (zpow_pos hg _).le (hc _)
  have ph : ((↑(phaseLift z j + Y) : UnitAddCircle)) = z' j := by simp [z',Y,transverseOrbit,lift_eq]
  change |mixedMode b g b⁻¹ c d e z x h j - x*(pastTerm b g c d z' j - pastTerm b g c d z j)| ≤
    C*tails (g*b⁻¹) (b*g) j * |h|
  by_cases hj : j < 0
  · rw [pastTerm,pastTerm,if_pos hj,if_pos hj,tails,if_neg (show ¬0 ≤ j by omega),← ph,
      ← lift_eq z j]
    change |g^j*c j*cosineMixed (phaseLift _ j) X Y - _| ≤ _
    have hE : g^j*c j*cosineMixed (phaseLift z j) X Y - x*((b*g)^j*c j*d j*forcingDerivative (↑(phaseLift z j+Y)) -
        (b*g)^j*c j*d j*forcingDerivative (↑(phaseLift z j))) =
        (g^j*c j)*(cosineMixed (phaseLift z j) X Y -
          X*(forcingDerivative (↑(phaseLift z j+Y))-forcingDerivative (↑(phaseLift z j)))) := by
      dsimp [X]; rw [mul_zpow]; ring
    rw [hE,abs_mul]
    have eqpow : g^j*(b^j)^2*(b⁻¹)^j = (b*g)^j := by
      rw [inv_zpow,mul_zpow]; field_simp
    calc
      _ ≤ g^j * (3*τ^3*(b^j*X₀)^2*(b⁻¹^j*|h|)) :=
        mul_le_mul hw ((mixed_slope_remainder _ X Y).trans (by gcongr)) (abs_nonneg _) (zpow_pos hg _).le
      _ = (3*τ^3*X₀^2) * (b*g)^j * |h| := by rw [← eqpow]; ring
      _ ≤ _ := by dsimp only [C]; gcongr; linarith
  · rw [pastTerm,pastTerm,if_neg hj,if_neg hj,sub_self,mul_zero,sub_zero,tails,if_pos (by omega)]
    change |(g^j*c j)*cosineMixed (phaseLift z j) X Y| ≤ _
    rw [abs_mul,cosineMixed_symm]
    calc
      _ ≤ g^j * (2*τ*(b⁻¹^j*|h|)) :=
        mul_le_mul hw ((cosineMixed_bound _ Y X).trans (by gcongr)) (abs_nonneg _) (zpow_pos hg _).le
      _ = 2*τ*(g*b⁻¹)^j*|h| := by rw [mul_zpow]; ring
      _ ≤ _ := by dsimp only [C]; gcongr; exact le_add_of_nonneg_right (by positivity)


/-- The normalization on the physical window of radius three used in Section 5. -/
theorem equal_rate_linearization {b g : ℝ} (hb : 1 < b) (hg : 0 < g) (hg1 : g < 1) (hbg : 1 < b*g)
    {c d e : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (z : PhaseTorus) {x : ℝ} (hx : |x| ≤ 3) (h : ℝ) :
    |circleRay b g c d (z+transverseOrbit b⁻¹ e h) x - circleRay b g c d z x -
      x*(pastSlope b g c d (z+transverseOrbit b⁻¹ e h)-pastSlope b g c d z)| ≤
        linearizationConstant b g * |h| := by
  convert! equal_rate_linearization_on hb hg hg1 hbg hc hd he z hx h using 1
  unfold linearizationConstant
  ring

end Weierstrass.StripProof

