module

public import Weierstrass.Grid
public import Weierstrass.Partition
public import Mathlib.MeasureTheory.Measure.Real

/-! Section 5, Lemma 5.2. All masses in the statement are ordinary real numbers.
A fixed measurable union of whole cells covers the heavy centers. This also avoids
any need to assume measurability of the heavy-center set in the argument. -/

public noncomputable section
open Set MeasureTheory Function
open scoped BigOperators

namespace Weierstrass

open Partition

set_option maxHeartbeats 1600000 in
/-- Full ball mass from retained collisions, for every probability measure on the real line. -/
theorem fullBallFromRetainedCollisions
    (ν η : Measure ℝ) [IsProbabilityMeasure ν] (hην : η ≤ ν)
    {R τ M : ℝ} (hR : 0 < R) (hτ : 0 < τ) (hM : 1 < M) :
    ν.real {x : ℝ | τ < ν.real (Icc (x - R) (x + R))} ≤
      1 - η.real univ + 3 / M +
        (M / τ) * (η.prod η).real {p : ℝ × ℝ | |p.1 - p.2| ≤ R} := by
  classical
  let : IsFiniteMeasure η := isFiniteMeasure_of_le ν hην
  let f (i : ℤ) := ν.real (cell R i)
  let q (i : ℤ) := η.real (cell R i) * η.real (cell R i)
  let tri (i : ℤ) := f (i - 1) + f i + f (i + 1)
  let A (i : ℤ) := if τ < tri i then cell R i else ∅
  let U := ⋃ i : ℤ, A i
  have hAsub (i : ℤ) : A i ⊆ cell R i := by
    dsimp [A]; split <;> simp
  have hAm (i : ℤ) : MeasurableSet (A i) := by
    dsimp [A]; split
    · exact cell_measurable _ _
    · exact MeasurableSet.empty
  have hAd : Pairwise (Disjoint on A) := fun i j hij =>
    (cell_disjoint hR hij).mono (hAsub i) (hAsub j)
  have hUm : MeasurableSet U := MeasurableSet.iUnion hAm
  have hcover : {x : ℝ | τ < ν.real (Icc (x - R) (x + R))} ⊆ U := by
    intro x hx
    let i : ℤ := ⌊x/R⌋
    have hxi : x ∈ cell R i := (mem_cell_iff hR).mpr rfl
    have h3 := measureReal_mono (μ := ν) (ball_subset_triple hxi)
    have hsum := measureReal_union_le (μ := ν) (cell R (i-1) ∪ cell R i) (cell R (i+1))
    have hsum' := measureReal_union_le (μ := ν) (cell R (i-1)) (cell R i)
    have htri : τ < tri i := by
      change τ < ν.real _ at hx
      dsimp [tri,f]
      linarith
    exact mem_iUnion.mpr ⟨i, by simpa [A, htri] using hxi⟩
  have hcharge (i : ℤ) : η.real (A i) ≤ M⁻¹ * tri i + (M / τ) * q i := by
    apply Grid.cell_charge (lt_trans zero_lt_one hM) hτ
    · dsimp [tri,f]; positivity
    · exact measureReal_nonneg
    · exact measureReal_mono (hAsub i)
    · by_cases h : τ < tri i
      · exact Or.inr h
      · exact Or.inl (by simp [A,h])
  have hf : HasSum f (1 : ℝ) := by simpa [f] using hasSum_cell ν hR
  have shift (k : ℤ) : HasSum (fun i : ℤ => f (i+k)) 1 :=
    ((Equiv.addRight k).hasSum_iff).mpr hf
  have ht : HasSum tri 3 := by
    simpa [tri, sub_eq_add_neg, show (1:ℝ)+1+1=3 by norm_num] using ((shift (-1)).add hf).add (shift 1)
  have hq : Summable q := summable_squares η hR
  have hη := hasSum_disjoint η A hAm hAd
  have hcost := (ht.mul_left M⁻¹).add (hq.hasSum.mul_left (M/τ))
  have htotal := hasSum_le hcharge hη hcost
  have hcol := mul_le_mul_of_nonneg_left (square_tsum_le η hR) (div_nonneg (le_trans zero_le_one hM.le) hτ.le)
  have hcomp : η.real Uᶜ ≤ ν.real Uᶜ := ENNReal.toReal_mono (measure_ne_top _ _) (hην _)
  have h1 := measureReal_add_measureReal_compl (μ := ν) hUm
  have h2 := measureReal_add_measureReal_compl (μ := η) hUm
  have hν : ν.real univ = 1 := by simp
  have he := measureReal_mono (μ := ν) hcover
  change η.real U ≤ M⁻¹ * 3 + (M / τ) * ∑' i, q i at htotal
  change (M / τ) * (∑' i, q i) ≤ _ at hcol
  rw [div_eq_mul_inv 3 M]
  linarith

end Weierstrass
