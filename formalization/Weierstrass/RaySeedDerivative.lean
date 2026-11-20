module

public import Weierstrass.RaySeedEstimate
public import Weierstrass.CriticalOccupation

/-! Identification of the isolated harmonics with the ordinary physical
derivative of the difference of two actual transverse translates. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology ENNReal ComplexConjugate
namespace Weierstrass.RaySeed

private theorem turn_im (x : ℝ) : (turn (↑x)).im = Real.sin (2*Real.pi*x) := by
  rw [turn_exp,mul_comm I,Complex.exp_ofReal_mul_I_im]

private theorem derivative_harmonic (A x y : ℝ) :
    2*(I*(A:ℂ)*turn (↑x)*circleJump y).re =
      2*A*(Real.sin (2*Real.pi*x)-Real.sin (2*Real.pi*(x+y))) := by
  have id : turn (↑x)*circleJump y = turn (↑(x+y))-turn (↑x) := by
    rw [circleJump,mul_sub,mul_one,AddCircle.coe_add,turn_add]
  rw [mul_assoc (I*(A:ℂ)),id,←turn_im,←turn_im]
  simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,one_mul,sub_zero,Complex.sub_im]
  ring

def phaseAt (b ρ h : ℝ) (d e : ℤ → ℝ) (ω : PhaseTorus) (t : ℝ) (j : ℤ) : UnitAddCircle :=
  ω j+↑(ρ^j*e j*h+b^j*d j*t)

def variationTerm (b g ρ : ℝ) (c d e z : ℤ → ℝ) (h₁ h₀ t : ℝ) (j : ℤ) :=
  rayTerm b g c d (transversePhase ρ e z h₁) t j -
  rayTerm b g c d (transversePhase ρ e z h₀) t j

def slopeTerm (b g ρ : ℝ) (c d e : ℤ → ℝ) (ω z : PhaseTorus) (h₁ h₀ t : ℝ) (j : ℤ) :=
  2*(derivativeCoeff (b*g) ρ (h₁-h₀) (fun i ↦ c i*d i) e
    (phaseAt b ρ h₀ d e ω t) j*coord z j).re

private theorem slope_identity (b g ρ : ℝ) (c d e w : ℤ → ℝ) (h₁ h₀ t : ℝ) (j : ℤ) :
    slopeTerm b g ρ c d e 0 (fun i ↦ ↑(w i)) h₁ h₀ t j =
      (2*Real.pi*(b*g)^j*(c j*d j)) *
       (Real.sin (2*Real.pi*(w j + ρ^j*e j*h₀ + b^j*d j*t)) -
        Real.sin (2*Real.pi*(w j + ρ^j*e j*h₁ + b^j*d j*t))) := by
  let X := w j+ρ^j*e j*h₀+b^j*d j*t
  let Y := ρ^j*e j*(h₁-h₀)
  let A := Real.pi*(b*g)^j*(c j*d j)
  have k : coord (phaseAt b ρ h₀ d e 0 t) j * coord (fun i ↦ ↑(w i)) j = turn (↑X) := by
    dsimp only [phaseAt,coord,Pi.zero_apply,zero_add]
    rw [←turn_add,zero_add,←AddCircle.coe_add]
    congr 2
    dsimp [X];ring
  have v : X+Y=w j+ρ^j*e j*h₁+b^j*d j*t := by dsimp [X,Y];ring
  unfold slopeTerm derivativeCoeff
  rw [show I*(↑(Real.pi*(b*g)^j*(c j*d j)):ℂ)*coord (phaseAt b ρ h₀ d e 0 t) j *
       circleJump Y * coord (fun i ↦ ↑(w i)) j =
      I*(A:ℂ)*(coord (phaseAt b ρ h₀ d e 0 t) j * coord (fun i ↦ ↑(w i)) j)*circleJump Y by
        dsimp only [A];ring,k,derivative_harmonic,v]
  dsimp only [A,X];ring

theorem variationTerm_deriv (b g ρ : ℝ) (c d e z : ℤ → ℝ) (h₁ h₀ t : ℝ) (j : ℤ) :
    HasDerivAt (fun x ↦ variationTerm b g ρ c d e z h₁ h₀ x j)
      (slopeTerm b g ρ c d e 0 (fun i ↦ ↑(z i)) h₁ h₀ t j) t := by
  have hf (h : ℝ) : HasDerivAt (fun x ↦ rayTerm b g c d (transversePhase ρ e z h) x j)
      ((g^j*c j)*(-Real.sin (2*Real.pi*(z j+ρ^j*e j*h+b^j*d j*t))*(2*Real.pi*(b^j*d j)))) t := by
    have lin := (((hasDerivAt_id t).const_mul (b^j*d j)).const_add (z j+ρ^j*e j*h)).const_mul (2*Real.pi)
    simpa! only [rayTerm,transversePhase,mul_one,id_eq] using ((lin.cos.sub_const _).const_mul (g^j*c j))
  apply ((hf h₁).sub (hf h₀)).congr_deriv
  rw [slope_identity,mul_zpow];ring

theorem bound_slopeTerm {b g ρ : ℝ} (hb : 0 < b) (hg : 0 < g) (hρ : 0 < ρ)
    {c d e : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (ω z : PhaseTorus) (h₁ h₀ t : ℝ) (j : ℤ) :
    ‖slopeTerm b g ρ c d e ω z h₁ h₀ t j‖ ≤ 2*physicalEnvelope (b*g) ρ (h₁-h₀) j := by
  have hu j : |c j*d j| ≤ 1 := by
    rw [abs_mul];exact (mul_le_of_le_one_right (abs_nonneg _) (hd j)).trans (hc j)
  have h := physical_bounds (mul_pos hb hg) hρ (h₁-h₀) hu he (phaseAt b ρ h₀ d e ω t) j
  rw [slopeTerm,norm_mul,Real.norm_of_nonneg (by norm_num : 0 ≤ (2:ℝ))]
  apply mul_le_mul_of_nonneg_left _ zero_le_two
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_mul,norm_coord,mul_one]
  unfold physicalEnvelope
  split <;> first | exact h.1 | exact h.2

theorem derivative_of_transverse_difference {b g ρ : ℝ} (hb : 0 < b) (hg : 0 < g) (hg' : g < 1)
    (hq : 1 < b*g) (hρ : 0 < ρ) (hQ : (b*g)*ρ < 1)
    {c d e : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (z : ℤ → ℝ) (h₁ h₀ t : ℝ) :
    HasDerivAt (fun x ↦ rayIncrement b g c d (transversePhase ρ e z h₁) x -
      rayIncrement b g c d (transversePhase ρ e z h₀) x)
      (∑' j, slopeTerm b g ρ c d e 0 (fun i ↦ ↑(z i)) h₁ h₀ t j) t := by
  let S h x := summable_rayTerm hb hg hg' hq hc hd (transversePhase ρ e z h) x
  have eq (x : ℝ) : rayIncrement b g c d (transversePhase ρ e z h₁) x -
      rayIncrement b g c d (transversePhase ρ e z h₀) x =
      ∑' j, variationTerm b g ρ c d e z h₁ h₀ x j := ((S h₁ x).tsum_sub (S h₀ x)).symm
  simp_rw [eq]
  exact hasDerivAt_tsum ((summable_physicalEnvelope hq hρ hQ (h₁-h₀)).mul_left 2)
    (fun j x ↦ variationTerm_deriv _ _ _ _ _ _ _ _ _ _ _)
    (fun j x ↦ bound_slopeTerm hb hg hρ hc hd he _ _ _ _ x j) ((S h₁ 0).sub (S h₀ 0)) t

end Weierstrass.RaySeed
