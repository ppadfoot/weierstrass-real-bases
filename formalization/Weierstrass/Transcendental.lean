module

public import Weierstrass.Anchored
public import Mathlib.RingTheory.Algebraic.Defs

/-! Finite integer characters of the bilateral phase orbit at a transcendental base. -/

@[expose] public noncomputable section
open Set Polynomial
open scoped BigOperators
namespace Weierstrass

/-- A finite Laurent character has nonzero frequency at a transcendental base.
Translate all exponents by the smallest index in the window and evaluate the resulting polynomial. -/
theorem transcendental_frequency_ne_zero {b : ℝ} (hb : b ≠ 0) (ht : Transcendental ℤ b)
    (S : Finset ℤ) (c : ℤ → ℤ) (hc : ∃ j ∈ S, c j ≠ 0) :
    (∑ j ∈ S, (c j : ℝ) * b ^ j) ≠ 0 := by
  classical
  obtain ⟨j₀, hj₀, hc₀⟩ := hc
  let m := S.min' ⟨j₀, hj₀⟩
  let e (j : ℤ) := (j - m).toNat
  have he (j : ℤ) (hj : j ∈ S) : (e j : ℤ) = j - m :=
    Int.toNat_of_nonneg (sub_nonneg.mpr (S.min'_le j hj))
  let p : ℤ[X] := ∑ j ∈ S, monomial (e j) (c j)
  have hcoeff : p.coeff (e j₀) = c j₀ := by
    simp only [p, finsetSum_coeff, coeff_monomial]
    rw [Finset.sum_eq_single j₀]
    · simp
    · intro j hj hneq
      have hj' : e j ≠ e j₀ := by
        intro heq
        apply hneq
        have h := congrArg ((↑) : ℕ → ℤ) heq
        rw [he j hj, he j₀ hj₀] at h
        omega
      simp [hj']
    · simp [hj₀]
  intro hzero
  have hp : aeval b p = 0 := by
    simp only [p, map_sum, aeval_monomial, eq_intCast]
    calc
      _ = ∑ j ∈ S, ((c j : ℝ) * b ^ j) / b ^ m := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← zpow_natCast b (e j), he j hj, zpow_sub₀ hb]
        ring
      _ = 0 := by rw [← Finset.sum_div, hzero, zero_div]
  have hpzero := transcendental_iff.mp ht p hp
  rw [hpzero] at hcoeff
  exact hc₀ (by simpa using hcoeff.symm)

/-- A finitely supported integer character in additive-circle coordinates. -/
def torusCharacter (S : Finset ℤ) (c : ℤ → ℤ) (z : PhaseTorus) : AddCircle (1 : ℝ) :=
  ∑ j ∈ S, c j • z j

theorem character_phaseOrbit (b : ℝ) (S : Finset ℤ) (c : ℤ → ℤ) (x : ℝ) :
    torusCharacter S c (phaseOrbit b x) = ↑((∑ j ∈ S, (c j : ℝ) * b ^ j) * x) := by
  let q := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
  change (∑ j ∈ S, c j • q (b ^ j * x)) = q ((∑ j ∈ S, (c j : ℝ) * b ^ j) * x)
  rw [Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← map_zsmul, zsmul_eq_mul, mul_assoc]

/-- Every nontrivial finite integer character maps the physical orbit onto the circle. -/
theorem character_phaseOrbit_surjective {b : ℝ} (hb : b ≠ 0) (ht : Transcendental ℤ b)
    (S : Finset ℤ) (c : ℤ → ℤ) (hc : ∃ j ∈ S, c j ≠ 0) :
    Function.Surjective (fun x : ℝ ↦ torusCharacter S c (phaseOrbit b x)) := by
  intro z
  let y : ℝ := AddCircle.equivIco 1 0 z
  let a : ℝ := ∑ j ∈ S, (c j : ℝ) * b ^ j
  have ha : a ≠ 0 := transcendental_frequency_ne_zero hb ht S c hc
  refine ⟨y / a, ?_⟩
  change torusCharacter S c (phaseOrbit b (y / a)) = z
  rw [character_phaseOrbit]
  change (↑(a * (y / a)) : AddCircle (1 : ℝ)) = z
  rw [mul_div_cancel₀ y ha]
  exact AddCircle.coe_equivIco

end Weierstrass
