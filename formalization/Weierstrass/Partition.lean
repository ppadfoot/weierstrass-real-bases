module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! # The real-line partition used in Section 5

The cells are Borel, tile the entire line, and pairs of points from a single cell
contribute to the retained product-measure collision at the original radius.
-/
public noncomputable section
open Set MeasureTheory Function
open scoped ENNReal

namespace Weierstrass.Partition

/-- Half-open cells of width R. -/
def cell (R : ℝ) (i : ℤ) : Set ℝ := Ico ((i : ℝ)*R) (((i : ℝ)+1)*R)

theorem cell_measurable (R : ℝ) (i : ℤ) : MeasurableSet (cell R i) :=
  measurableSet_Ico

theorem mem_cell_iff {R x : ℝ} (hR : 0 < R) {i : ℤ} :
    x ∈ cell R i ↔ ⌊x/R⌋ = i := by
  rw [Int.floor_eq_iff]
  exact and_congr (le_div_iff₀ hR).symm (div_lt_iff₀ hR).symm

theorem cell_disjoint {R : ℝ} (hR : 0 < R) : Pairwise (Disjoint on cell R) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hij (((mem_cell_iff hR).mp hx).symm.trans ((mem_cell_iff hR).mp hy))

theorem iUnion_cell {R : ℝ} (hR : 0 < R) : (⋃ i : ℤ, cell R i) = univ :=
  iUnion_eq_univ_iff.mpr fun x => ⟨⌊x/R⌋, (mem_cell_iff hR).mpr rfl⟩

theorem ball_subset_triple {R x : ℝ} {i : ℤ} (hx : x ∈ cell R i) :
    Icc (x-R) (x+R) ⊆ (cell R (i-1) ∪ cell R i) ∪ cell R (i+1) := by
  intro y hy
  obtain ⟨hxl, hxr⟩ := hx
  obtain ⟨hyl, hyr⟩ := hy
  by_cases hl : y < (i : ℝ)*R
  · left; left
    simp only [cell, mem_Ico, Int.cast_sub, Int.cast_one]
    constructor <;> grind
  · by_cases hu : y < ((i : ℝ)+1)*R
    · left; right
      exact ⟨le_of_not_gt hl, hu⟩
    · right
      simp only [cell, mem_Ico, Int.cast_add, Int.cast_one]
      constructor <;> grind

theorem rectangle_subset_collision {R : ℝ} (i : ℤ) :
    (cell R i ×ˢ cell R i) ⊆ {p : ℝ × ℝ | |p.1-p.2| ≤ R} := by
  intro p hp
  obtain ⟨⟨hl, hr⟩, ⟨hl', hr'⟩⟩ := hp
  change |p.1-p.2| ≤ R
  rw [abs_le]
  constructor <;> grind

theorem tsum_cell (μ : Measure ℝ) {R : ℝ} (hR : 0 < R) :
    (∑' i, μ (cell R i)) = μ univ := by
  rw [← measure_iUnion (cell_disjoint hR) (cell_measurable R), iUnion_cell hR]

private theorem rectangle_disjoint {R : ℝ} (hR : 0 < R) :
    Pairwise (Disjoint on fun i => cell R i ×ˢ cell R i) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro p hp hq
  exact Set.disjoint_left.mp (cell_disjoint hR hij) hp.1 hq.1

theorem square_tsum_le_ennreal (η : Measure ℝ) [SFinite η] {R : ℝ} (hR : 0 < R) :
    (∑' i, η (cell R i) * η (cell R i)) ≤
      (η.prod η) {p : ℝ × ℝ | |p.1-p.2| ≤ R} := by
  let A (i : ℤ) := cell R i ×ˢ cell R i
  have hm (i) : MeasurableSet (A i) := (cell_measurable R i).prod (cell_measurable R i)
  calc
    _ = ∑' i, (η.prod η) (A i) := by simp only [A, Measure.prod_prod]
    _ = (η.prod η) (⋃ i, A i) := (measure_iUnion (rectangle_disjoint hR) hm).symm
    _ ≤ _ := measure_mono (iUnion_subset rectangle_subset_collision)

/-- Countable additivity on disjoint measurable sets, in real-valued mass. -/
theorem hasSum_disjoint {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) [IsFiniteMeasure μ] (A : ι → Set α)
    (hm : ∀ i, MeasurableSet (A i)) (hd : Pairwise (Disjoint on A)) :
    HasSum (fun i => μ.real (A i)) (μ.real (⋃ i, A i)) := by
  have he := measure_iUnion (μ := μ) hd hm
  have hs : Summable (fun i => (μ (A i)).toReal) :=
    ENNReal.summable_toReal (by rw [← he]; exact measure_ne_top _ _)
  have h := congrArg ENNReal.toReal he
  rw [ENNReal.tsum_toReal_eq (fun i => measure_ne_top μ (A i))] at h
  change HasSum (fun i => (μ (A i)).toReal) (μ (⋃ i, A i)).toReal
  rw [h]
  exact hs.hasSum

theorem hasSum_cell (μ : Measure ℝ) [IsFiniteMeasure μ] {R : ℝ} (hR : 0 < R) :
    HasSum (fun i => μ.real (cell R i)) (μ.real univ) := by
  have h := hasSum_disjoint μ (cell R) (cell_measurable R) (cell_disjoint hR)
  rwa [iUnion_cell hR] at h

private theorem hasSum_squares (η : Measure ℝ) [IsFiniteMeasure η] {R : ℝ} (hR : 0 < R) :
    HasSum (fun i => η.real (cell R i) * η.real (cell R i))
      ((η.prod η).real (⋃ i, cell R i ×ˢ cell R i)) := by
  let A (i : ℤ) := cell R i ×ˢ cell R i
  have hm (i) : MeasurableSet (A i) := (cell_measurable R i).prod (cell_measurable R i)
  have hh := hasSum_disjoint (η.prod η) A hm (rectangle_disjoint hR)
  simpa only [A, measureReal_prod_prod] using hh

theorem summable_squares (η : Measure ℝ) [IsFiniteMeasure η] {R : ℝ} (hR : 0 < R) :
    Summable (fun i => η.real (cell R i) * η.real (cell R i)) :=
  (hasSum_squares η hR).summable

theorem square_tsum_le (η : Measure ℝ) [IsFiniteMeasure η] {R : ℝ} (hR : 0 < R) :
    (∑' i, η.real (cell R i) * η.real (cell R i)) ≤
      (η.prod η).real {p : ℝ × ℝ | |p.1-p.2| ≤ R} := by
  rw [(hasSum_squares η hR).tsum_eq]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (iUnion_subset rectangle_subset_collision))

end Weierstrass.Partition
