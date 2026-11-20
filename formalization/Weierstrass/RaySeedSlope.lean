module

public import Weierstrass.RaySeedDerivative
public import Weierstrass.RayInformation

/-! Uniformity for the derivative of the actual circle-valued environments.
The compact parameter controls the modulus along every physical line. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology ENNReal ComplexConjugate
namespace Weierstrass.RaySeed

local instance (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

def slope (b g ρ : ℝ) (c d e : ℤ → ℝ) (ω z : PhaseTorus) (h₁ h₀ t : ℝ) :=
  ∑' j, slopeTerm b g ρ c d e ω z h₁ h₀ t j

theorem ofReal_slope (b g ρ : ℝ) (c d e : ℤ → ℝ) (ω z : PhaseTorus) (h₁ h₀ t : ℝ) :
    (slope b g ρ c d e ω z h₁ h₀ t : ℂ) = symmetricSeries
      (derivativeCoeff (b*g) ρ (h₁-h₀) (fun j ↦ c j*d j) e (phaseAt b ρ h₀ d e ω t)) z := by
  rw [slope,Complex.ofReal_tsum,symmetricSeries]
  apply tsum_congr
  intro j
  rw [Complex.add_conj];rfl

theorem slope_rephase (b g ρ : ℝ) (c d e : ℤ → ℝ) (ω z : PhaseTorus) (h₁ h₀ t : ℝ) :
    slope b g ρ c d e ω z h₁ h₀ t = slope b g ρ c d e 0 (ω+z) h₁ h₀ t := by
  unfold slope
  apply tsum_congr
  intro j
  unfold slopeTerm derivativeCoeff
  have eq : coord (phaseAt b ρ h₀ d e ω t) j * coord z j =
      coord (phaseAt b ρ h₀ d e 0 t) j * coord (ω+z) j := by
    simp only [coord,phaseAt,Pi.add_apply,Pi.zero_apply,zero_add,turn_add]
    ring
  rw [show ∀ A C v w : ℂ, (A*v*C)*w = A*(v*w)*C by intros;ring,eq]
  ring

/-- The harmonic estimate applies to the derivative of the actual difference
of two weighted increments on the phase torus. -/
theorem circle_derivative {b g ρ : ℝ} (hb : 0 < b) (hg : 0 < g) (hg' : g < 1)
    (hq : 1 < b*g) (hρ : 0 < ρ) (hQ : (b*g)*ρ < 1)
    {c d e : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (ω z : PhaseTorus) (h₁ h₀ t : ℝ) :
    HasDerivAt (fun x ↦ CriticalRay.circleRay b g c d ((ω+z)+CriticalRay.transverseOrbit ρ e h₁) x -
      CriticalRay.circleRay b g c d ((ω+z)+CriticalRay.transverseOrbit ρ e h₀) x)
      (slope b g ρ c d e ω z h₁ h₀ t) t := by
  let w (j : ℤ) : ℝ := AddCircle.equivIco (1:ℝ) 0 ((ω+z) j)
  have rep : (fun j ↦ (↑(w j):UnitAddCircle)) = ω+z := funext fun _ ↦ AddCircle.coe_equivIco
  have translate (h : ℝ) : (fun j ↦ (↑(transversePhase ρ e w h j):UnitAddCircle)) =
      (ω+z)+CriticalRay.transverseOrbit ρ e h := by
    funext j
    change (↑(w j+ρ^j*e j*h):UnitAddCircle) = (ω+z) j+↑(ρ^j*e j*h)
    rw [AddCircle.coe_add,congrFun rep j]
  rw [slope_rephase,←rep]
  have h := derivative_of_transverse_difference hb hg hg' hq hρ hQ hc hd he w h₁ h₀ t
  simpa only [rep,←translate,CriticalRay.circleRay_real,slope] using h

theorem uniform_circle_small_derivative {B : ℂ} (hb : 1 < ‖B‖) {g ρ δ : ℝ}
    (hq : 1 < ‖B‖*g) (hρ : 0 < ρ) (hρ' : ρ < 1) (hQ : (‖B‖*g)*ρ < 1)
    (hbQ : 1 < ((‖B‖*g)*ρ)*‖B‖) (hδ : 0 < δ) (D : ℕ)
    (μ : Measure (complexPhaseGroup B)) [IsProbabilityMeasure μ] [Measure.IsAddLeftInvariant μ]
    [μ.InnerRegularCompactLTTop] (h₁ h₀ : ℝ) (hne : h₁ ≠ h₀)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (c d e : ℤ → ℝ), (∀ j, |c j| ≤ 1) → (∀ j, |d j| ≤ 1) →
      (∀ j, |e j| ≤ 1) → (∀ m : ℕ, ∃ k : Fin D,
        δ ≤ |(c (m+k.val:ℕ)*d (m+k.val:ℕ))*e (m+k.val:ℕ)|) →
      ∀ (ω : PhaseTorus) (t : ℝ), μ.real {z : complexPhaseGroup B |
        |slope ‖B‖ g ρ c d e ω z.val h₁ h₀ t| ≤ r n} < ε := by
  have lim := uniform_transverse_derivative hb hq hρ hρ' hQ hbQ (sub_ne_zero.mpr hne) hδ D μ hr hε
  filter_upwards [lim] with n h
  intro c d e hc hd he gd ω t
  let u j : Icc (-1:ℝ) 1 := ⟨c j*d j,abs_le.mp <| by rw [abs_mul]
                                                     exact (mul_le_of_le_one_right (abs_nonneg _) (hd j)).trans (hc j)⟩
  let ev j : Icc (-1:ℝ) 1 := ⟨e j,abs_le.mp (he j)⟩
  let X : Profile := (u,ev,phaseAt ‖B‖ ρ h₀ d e ω t)
  have ok : X ∈ admissible D δ := gd
  have est := h X ok
  change μ.real _ < ε at est
  convert est using 1
  congr 1
  ext z
  change |slope ‖B‖ g ρ c d e ω z.val h₁ h₀ t| ≤ r n ↔
    ‖symmetricSeries (derivativeCoeff _ _ _ _ _ _) z.val‖ ≤ r n
  rw [← ofReal_slope,Complex.norm_real,Real.norm_eq_abs]

end Weierstrass.RaySeed
