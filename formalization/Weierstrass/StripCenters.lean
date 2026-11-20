module

public import Weierstrass.StripDual
public import Weierstrass.StripFamily

/-! # Centered input tests for B3 and B4 in the weighted phase model -/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace Weierstrass.StripProof
open CriticalRay

private theorem τpos : 0 < τ := by dsimp [τ]; positivity

/-- The full stable input law in a single cell after dilation to [0,1]. -/
def stableLaw : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure stableLaw where
  measure_univ := by simp [stableLaw,Real.volume_Icc]

set_option maxHeartbeats 850000 in
/-- The stable test centered at a sampled input is bounded by an actual dual anchored
occupation in its shifted and reversed environment. -/
theorem centered_direction_mass {b g ρ : ℝ} (hbg : 1 < b*g) (hr : 0 < ρ)
    (hdual : 1 < ρ⁻¹*(b*g)⁻¹) {c d e : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1)
    (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1) (z : PhaseTorus) (m : ℕ) {u l : ℝ}
    (hu : u ∈ Icc 0 1) (hl : (ρ/(b*g)⁻¹)^m ≤ l) :
    stableLaw {v | |direction b g ρ c d e z m v-direction b g ρ c d e z m u| ≤ 2*l} ≤
      rayOccupation ρ⁻¹ (b*g)⁻¹ (reversedParameters c d e m)
        (reversedEnvironment (z+transverseOrbit ρ e (ρ^m*u)) m) 1 ((2+dualError b g ρ)/τ) l := by
  let p := reversedParameters c d e m
  let w := reversedEnvironment (z+transverseOrbit ρ e (ρ^m*u)) m
  let A := (2+dualError b g ρ)/τ
  let Z : Set ℝ := {y | y ∈ Icc (-1) 1 ∧ |circleRay ρ⁻¹ (b*g)⁻¹ p.1 p.2 w y| ≤ A*l}
  let H := direction b g ρ c d e z m
  have Epos : 0 ≤ dualError b g ρ := by
    unfold dualError; exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (sub_nonneg.mpr (inv_lt_one_of_one_lt₀ hdual).le))
  change stableLaw {v | |H v-H u| ≤ 2*l} ≤ volume Z
  rw [stableLaw,Measure.restrict_apply' measurableSet_Icc]
  calc
    _ ≤ volume ((fun v : ℝ => v+(-u)) ⁻¹' Z) := by
      apply measure_mono
      rintro v ⟨hv,hv'⟩
      have ht : |v-u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1,hv'.1,hu.2,hv'.2],by linarith [hu.1,hv'.1,hu.2,hv'.2]⟩
      have eq := direction_recenter hbg hr hdual hc hd he z m u v
      change |H v - H u - τ*circleRay ρ⁻¹ (b*g)⁻¹ p.1 p.2 w (v-u)| ≤ _ at eq
      have err : dualError b g ρ*(ρ/(b*g)⁻¹)^m*|v-u| ≤ dualError b g ρ*l := by
        apply (mul_le_of_le_one_right (mul_nonneg Epos (pow_nonneg (div_nonneg hr.le
          (inv_nonneg.mpr (zero_lt_one.trans hbg).le)) m)) ht).trans
        exact mul_le_mul_of_nonneg_left hl Epos
      have lower := abs_le.mp (eq.trans err)
      change |H v-H u| ≤ 2*l at hv
      have vv := abs_le.mp hv
      change v + -u ∈ Icc (-1) 1 ∧ |circleRay ρ⁻¹ (b*g)⁻¹ p.1 p.2 w (v + -u)| ≤ A*l
      rw [← sub_eq_add_neg]
      refine ⟨abs_le.mp ht,?_⟩
      dsimp [A]; rw [div_mul_eq_mul_div,le_div_iff₀ τpos,← abs_of_pos τpos,← abs_mul]
      rw [abs_le]; constructor <;> nlinarith only [lower.1,lower.2,vv.1,vv.2]
    _ = _ := by
      exact measure_preimage_add_right _ _ _

def shiftedParameters (p : RayParameters) (n : ℤ) : RayParameters :=
  (fun j => p.1 (j+n), fun j => p.2 (j+n))

def physicalEnvironment (b : ℝ) (d : ℤ → ℝ) (z : PhaseTorus) (n : ℤ) (x : ℝ) : PhaseTorus :=
  fun j => z (j+n)+↑(b^(j+n)*d (j+n)*x)

/-- A centered normalized strip box for the frozen height has measure at most one
horizontal Jacobian times an actual anchored occupation of the shifted original model. -/
theorem centered_physical_mass {b g : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1)
    (hbg : 1 < b*g) {p : RayParameters} (hc : ∀ j, |p.1 j| ≤ 1) (hd : ∀ j, |p.2 j| ≤ 1)
    (z : PhaseTorus) (x : ℝ) (n : ℕ) {l Δ : ℝ} (hl : l ≤ (b^n)⁻¹) :
    volume {y | |y-x| ≤ 2*l ∧ |circleRay b g p.1 p.2 z y - circleRay b g p.1 p.2 z x| ≤ 2*Δ*l} ≤
      ENNReal.ofReal ((b^n)⁻¹) * rayOccupation b g (shiftedParameters p n)
        (physicalEnvironment b p.2 z n x) 2 2 (Δ*l/(g^n)) := by
  let Z : Set ℝ := {v | v ∈ Icc (-2) 2 ∧ |circleRay b g (shiftedParameters p n).1
    (shiftedParameters p n).2 (physicalEnvironment b p.2 z n x) v| ≤ 2*(Δ*l/(g^n))}
  have bp : 0 < b^n := pow_pos hb _
  have gp : 0 < g^n := pow_pos hg _
  calc
    _ ≤ volume ((fun y : ℝ => y+(-x)) ⁻¹' ((fun u : ℝ => b^n*u) ⁻¹' Z)) := by
      apply measure_mono
      rintro y ⟨h1,h2⟩
      let v := b^n*(y-x)
      have vmag : |v| ≤ 2 := by
        dsimp [v]; rw [abs_mul,abs_of_pos bp]
        calc
          _ ≤ b^n*(2*(b^n)⁻¹) := mul_le_mul_of_nonneg_left (by linarith) bp.le
          _ = _ := by field_simp
      have H := circleRay_recenter_scale hb hg hg1 hbg hc hd z (n:ℤ) x v
      rw [zpow_neg,zpow_natCast,zpow_natCast,show x+(b^n)⁻¹*v=y by dsimp [v]; field_simp; ring] at H
      change b^n*(y + -x) ∈ Z
      rw [← sub_eq_add_neg]; refine ⟨abs_le.mp vmag,?_⟩
      rw [H,abs_mul,abs_of_pos gp] at h2
      change |circleRay b g (shiftedParameters p n).1 (shiftedParameters p n).2 (physicalEnvironment b p.2 z n x) v| ≤ 2*(Δ*l/g^n)
      rw [show 2*(Δ*l/g^n) = 2*Δ*l/g^n by ring,le_div_iff₀ gp,mul_comm]
      exact h2
    _ = _ := by rw [measure_preimage_add_right,Real.volume_preimage_mul_left bp.ne',
      abs_of_pos (inv_pos.mpr bp)]; rfl

end Weierstrass.StripProof
