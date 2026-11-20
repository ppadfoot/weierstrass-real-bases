module

public import Weierstrass.Graph
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! The unweighted physical increment in §2 and the comparison used in Appendix A. -/

@[expose] public noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace Weierstrass

/-- Bilateral summand at real lifts of the circle coordinates, measured in turns. -/
def incrementTerm (b lam : ℝ) (z : ℤ → ℝ) (u : ℝ) (i : ℤ) : ℝ :=
  lam ^ i * (Real.cos (2 * Real.pi * (z i + b ^ i * u)) - Real.cos (2 * Real.pi * z i))

def bilateralIncrement (b lam : ℝ) (z : ℤ → ℝ) (u : ℝ) : ℝ :=
  ∑' i : ℤ, incrementTerm b lam z u i

/-- Environment at scale n, using any two-sided extension of the prescribed phases. -/
def environment (b : ℝ) (phase : ℤ → ℝ) (n : ℕ) (x : ℝ) (i : ℤ) : ℝ :=
  b ^ ((n : ℤ) + i) * x + phase ((n : ℤ) + i)

theorem incrementTerm_bound (b lam : ℝ) (hl : 0 < lam) (z : ℤ → ℝ) (u : ℝ) (i : ℤ) :
    ‖incrementTerm b lam z u i‖ ≤ 2 * lam ^ i := by
  unfold incrementTerm
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (zpow_pos hl _), mul_comm 2 (lam ^ i)]
  apply mul_le_mul_of_nonneg_left _ (zpow_pos hl _).le
  apply (abs_sub _ _).trans
  linarith [Real.abs_cos_le_one (2 * Real.pi * (z i + b ^ i * u)), Real.abs_cos_le_one (2 * Real.pi * z i)]

theorem incrementTerm_lipschitz (b lam : ℝ) (hb : 0 < b) (hl : 0 < lam)
    (z : ℤ → ℝ) (u : ℝ) (i : ℤ) :
    ‖incrementTerm b lam z u i‖ ≤ (2 * Real.pi * |u|) * (b * lam) ^ i := by
  unfold incrementTerm
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (zpow_pos hl _)]
  calc
    _ ≤ lam ^ i * |2 * Real.pi * (z i + b ^ i * u) - 2 * Real.pi * z i| :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le _ _) (zpow_pos hl _).le
    _ = _ := by
      rw [show 2 * Real.pi * (z i + b ^ i * u) - 2 * Real.pi * z i =
          (2 * Real.pi * b ^ i) * u by ring, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * b ^ i), mul_zpow]
      ring

private theorem negative_tail_majorant {b lam : ℝ} (hb : 0 < b) (hl : 0 < lam)
    (z : ℤ → ℝ) (u : ℝ) (n j : ℕ) :
    ‖incrementTerm b lam z u (-(j + 1 : ℤ) - n)‖ ≤
      ((2 * Real.pi * |u|) * ((b * lam)⁻¹ ^ (n + 1))) * ((b * lam)⁻¹ ^ j) := by
  refine (incrementTerm_lipschitz b lam hb hl z u _).trans_eq ?_
  rw [show -(j + 1 : ℤ) - n = -((↑(n + 1 + j) : ℤ)) by omega, zpow_neg, zpow_natCast,
    ← inv_pow, pow_add]
  ring

theorem summable_incrementTerm {b lam : ℝ} (hb : 1 < b) (hl : b⁻¹ < lam) (h1 : lam < 1)
    (z : ℤ → ℝ) (u : ℝ) : Summable (incrementTerm b lam z u) := by
  have hb0 := zero_lt_one.trans hb
  have hl0 := (inv_pos.mpr hb0).trans hl
  have hq := (inv_lt_iff_one_lt_mul₀' hb0).mp hl
  apply Summable.of_nat_of_neg_add_one
  · apply ((summable_geometric_of_lt_one hl0.le h1).mul_left 2).of_norm_bounded
    intro j
    simpa using incrementTerm_bound b lam hl0 z u (j : ℤ)
  · apply ((summable_geometric_of_lt_one (inv_pos.mpr (mul_pos hb0 hl0)).le
        (inv_lt_one_of_one_lt₀ hq)).mul_left ((2 * Real.pi * |u|) * (b * lam)⁻¹ ^ (0 + 1 : ℕ))).of_norm_bounded
    intro j
    simpa using negative_tail_majorant hb0 hl0 z u 0 j

private theorem physical_term {b lam : ℝ} (hb : 0 < b) (hl : 0 < lam)
    (phase : ℤ → ℝ) (n k : ℕ) (x u : ℝ) :
    incrementTerm b lam (environment b phase n x) u ((k : ℤ) - n) =
      (lam ^ n)⁻¹ * (term b lam (fun j : ℕ ↦ phase j) k (x + (b ^ n)⁻¹ * u) -
        term b lam (fun j : ℕ ↦ phase j) k x) := by
  simp only [incrementTerm, environment, term, show (n : ℤ) + ((k : ℤ) - n) = k by omega, zpow_sub₀ hl.ne',
    zpow_sub₀ hb.ne', zpow_natCast]
  rw [show b ^ k * x + phase k + b ^ k / b ^ n * u =
       b ^ k * (x + (b ^ n)⁻¹ * u) + phase k by ring]
  ring

/-- For every phase extension, all base points and all real displacements, the error is bounded
by an explicit geometric factor times |u|. On |u| ≤ 1 the bound is uniform in displacement. -/
theorem physical_increment_comparison {b lam : ℝ} (hb : 1 < b) (hl : b⁻¹ < lam) (h1 : lam < 1)
    (phase : ℤ → ℝ) (n : ℕ) (x u : ℝ) :
    |bilateralIncrement b lam (environment b phase n x) u -
      (lam ^ n)⁻¹ * (series b lam (fun j : ℕ ↦ phase j) (x + (b ^ n)⁻¹ * u) -
        series b lam (fun j : ℕ ↦ phase j) x)| ≤
      (2 * Real.pi * |u|) * (b * lam)⁻¹ ^ (n + 1) * (1 - (b * lam)⁻¹)⁻¹ := by
  have hb0 := zero_lt_one.trans hb
  have hl0 := (inv_pos.mpr hb0).trans hl
  have hq := (inv_lt_iff_one_lt_mul₀' hb0).mp hl
  let f := incrementTerm b lam (environment b phase n x) u
  let g (j : ℤ) := f (j - n)
  have sx := summable_term hl0.le h1 b (fun j : ℕ ↦ phase j) (x + (b ^ n)⁻¹ * u)
  have sy := summable_term hl0.le h1 b (fun j : ℕ ↦ phase j) x
  have hpos : HasSum (fun j : ℕ ↦ g j) ((lam ^ n)⁻¹ *
      (series b lam (fun j : ℕ ↦ phase j) (x + (b ^ n)⁻¹ * u) -
       series b lam (fun j : ℕ ↦ phase j) x)) := by
    simpa only [g, f, series, physical_term hb0 hl0] using
      (sx.hasSum.sub sy.hasSum).mul_left (lam ^ n)⁻¹
  have hmajor := (hasSum_geometric_of_lt_one (inv_pos.mpr (mul_pos hb0 hl0)).le
    (inv_lt_one_of_one_lt₀ hq)).mul_left ((2 * Real.pi * |u|) * (b * lam)⁻¹ ^ (n + 1))
  have hbnd (j : ℕ) := negative_tail_majorant hb0 hl0 (environment b phase n x) u n j
  have hneg : Summable (fun j : ℕ ↦ g (-(j + 1 : ℤ))) := hmajor.summable.of_norm_bounded hbnd
  have hsplit := (hpos.of_nat_of_neg_add_one hneg.hasSum).tsum_eq
  have hreindex : bilateralIncrement b lam (environment b phase n x) u = ∑' j : ℤ, g j :=
    ((Equiv.addRight (-(n : ℤ))).tsum_eq (f := f)).symm
  rw [hreindex, hsplit, add_sub_cancel_left, ← Real.norm_eq_abs]
  exact tsum_of_norm_bounded hmajor hbnd

theorem bilateralIncrement_add_int_phase (b lam : ℝ) (z : ℤ → ℝ) (k : ℤ → ℤ) (u : ℝ) :
    bilateralIncrement b lam (fun i ↦ z i + k i) u = bilateralIncrement b lam z u := by
  apply tsum_congr
  intro i
  simp only [incrementTerm]
  rw [show 2 * Real.pi * (z i + k i + b ^ i * u) =
      2 * Real.pi * (z i + b ^ i * u) + k i * (2 * Real.pi) by ring,
    show 2 * Real.pi * (z i + k i) = 2 * Real.pi * z i + k i * (2 * Real.pi) by ring,
    Real.cos_add_int_mul_two_pi, Real.cos_add_int_mul_two_pi]

abbrev PhaseTorus := ℤ → AddCircle (1 : ℝ)

/-- The real orbit in the product torus. -/
def phaseOrbit (b : ℝ) : ℝ →+ PhaseTorus where
  toFun x i := ↑(b ^ i * x)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp [mul_add]

def phaseGroup (b : ℝ) : AddSubgroup PhaseTorus := (phaseOrbit b).range.topologicalClosure

instance phaseGroupCompact (b : ℝ) : CompactSpace (phaseGroup b) :=
  isCompact_iff_compactSpace.mp (phaseOrbit b).range.isClosed_topologicalClosure.isCompact

/-- Haar measure on the orbit closure, normalized on the entire compact group. -/
def phaseHaar (b : ℝ) : @Measure (phaseGroup b) (borel _) := by
  letI : MeasurableSpace (phaseGroup b) := borel _
  letI : BorelSpace (phaseGroup b) := ⟨rfl⟩
  exact Measure.addHaarMeasure (⊤ : TopologicalSpace.PositiveCompacts (phaseGroup b))

theorem phaseHaar_univ (b : ℝ) : phaseHaar b univ = 1 := by
  let _ : MeasurableSpace (phaseGroup b) := borel _
  let _ : BorelSpace (phaseGroup b) := ⟨rfl⟩
  simpa [phaseHaar] using
    Measure.addHaarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (phaseGroup b)))

def circleIncrement (b lam : ℝ) (z : PhaseTorus) (u : ℝ) : ℝ :=
  bilateralIncrement b lam (fun i ↦ (AddCircle.equivIco 1 0 (z i) : ℝ)) u

theorem circleIncrement_of_real (b lam : ℝ) (z : ℤ → ℝ) (u : ℝ) :
    circleIncrement b lam (fun i ↦ ↑(z i)) u = bilateralIncrement b lam z u := by
  unfold circleIncrement
  have hrep (i : ℤ) : (AddCircle.equivIco (1 : ℝ) 0 (↑(z i)) : ℝ) = z i + ((-⌊z i⌋ : ℤ) : ℝ) := by
    simp [AddCircle.coe_equivIco_mk_apply, Int.fract, sub_eq_add_neg]
  simp_rw [hrep]
  exact bilateralIncrement_add_int_phase b lam z (fun i ↦ -⌊z i⌋) u

theorem circle_increment_comparison {b lam : ℝ} (hb : 1 < b) (hl : b⁻¹ < lam) (h1 : lam < 1)
    (phase : ℤ → ℝ) (n : ℕ) (x u : ℝ) (hu : |u| ≤ 1) :
    |circleIncrement b lam (fun i ↦ ↑(environment b phase n x i)) u -
      (lam ^ n)⁻¹ * (series b lam (fun j : ℕ ↦ phase j) (x + (b ^ n)⁻¹ * u) -
        series b lam (fun j : ℕ ↦ phase j) x)| ≤
      (2 * Real.pi * (b * lam)⁻¹ ^ (n + 1)) * (1 - (b * lam)⁻¹)⁻¹ := by
  rw [circleIncrement_of_real]
  refine (physical_increment_comparison hb hl h1 phase n x u).trans ?_
  have hb0 := zero_lt_one.trans hb
  have hl0 := (inv_pos.mpr hb0).trans hl
  have hγ := inv_lt_one_of_one_lt₀ ((inv_lt_iff_one_lt_mul₀' hb0).mp hl)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (by positivity) hu) (by positivity)) (inv_nonneg.mpr (sub_nonneg.mpr hγ.le))

/-- Unweighted physical form of assertion (2.2). The supremum is over translates
of the compact phase group. Occupation time is Lebesgue measure on the time axis. -/
def AnchoredEstimate (b lam s : ℝ) : Prop :=
  ∀ h : ℝ, 0 < h → h < s → ∀ T A : ℝ, 0 < T → 0 < A →
    Tendsto (fun r : ℝ ↦ ⨆ ω : PhaseTorus,
      phaseHaar b {z : phaseGroup b | ENNReal.ofReal (r ^ h) <
        volume {u : ℝ | u ∈ Icc (-T) T ∧ |circleIncrement b lam (ω + z.val) u| ≤ A * r}})
      (𝓝[>] 0) (𝓝 0)

end Weierstrass
