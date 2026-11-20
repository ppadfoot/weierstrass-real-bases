module

public import Weierstrass.DescentDifferentiation

/-! Actual physical cylinders at arbitrary real bases in §6. The end of the
parent interval and the exact, generally nonintegral expansion are retained. -/
@[expose] public noncomputable section
open Set MeasureTheory Weierstrass.CriticalRay Weierstrass.StripProof
open scoped ENNReal BigOperators
namespace Weierstrass.Descent

def childLength (b T : ℝ) (n N : ℕ) := T*b^n/N

def cell (N : ℕ) (i : Fin N) : Set ℝ := Ico ((i:ℝ)/N) (((i:ℝ)+1)/N)

def anchor (T : ℝ) {N : ℕ} (i : Fin N) := T*((i:ℝ)/N)

theorem mesh_length {b T : ℝ} {n : ℕ} (h : 2 ≤ T*b^n) :
    0 < ⌊T*b^n⌋₊ ∧ 1 ≤ childLength b T n ⌊T*b^n⌋₊ ∧ childLength b T n ⌊T*b^n⌋₊ ≤ 2 := by
  let N := ⌊T*b^n⌋₊
  have hN : 0 < N := Nat.floor_pos.mpr (by linarith)
  have pos : 0 < (N:ℝ) := by exact_mod_cast hN
  have one : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  refine ⟨hN,(one_le_div pos).mpr (Nat.floor_le (by linarith)),(div_le_iff₀ pos).mpr ?_⟩
  have lt : T*b^n < (N:ℝ)+1 := Nat.lt_floor_add_one _
  linarith

theorem cell_disjoint {N : ℕ} (hn : 0 < N) {i j : Fin N} (h : i ≠ j) : Disjoint (cell N i) (cell N j) := by
  have hp : 0 < (N:ℝ) := by exact_mod_cast hn
  rcases lt_or_gt_of_ne h with l|l
  · have h' : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast l
    exact Set.disjoint_left.mpr (fun _ hx hy ↦ lt_irrefl _ (hx.2.trans_le ((div_le_div_of_nonneg_right h' hp.le).trans hy.1)))
  · have h' : (j:ℝ)+1 ≤ (i:ℝ) := by exact_mod_cast l
    exact Set.disjoint_left.mpr (fun _ hx hy ↦ lt_irrefl _ (hy.2.trans_le ((div_le_div_of_nonneg_right h' hp.le).trans hx.1)))

theorem cell_subset {N : ℕ} (hn : 0 < N) (i : Fin N) : cell N i ⊆ Ico 0 1 := by
  have hp : 0 < (N:ℝ) := by exact_mod_cast hn
  have endpt : (i:ℝ)+1 ≤ N := by exact_mod_cast i.isLt
  exact fun _ hx ↦ ⟨(div_nonneg (Nat.cast_nonneg _) hp.le).trans hx.1,
    hx.2.trans_le ((div_le_one hp).mpr endpt)⟩

theorem cell_mass {N : ℕ} (hn : 0 < N) (i : Fin N) :
    (volume.restrict (Ico (0:ℝ) 1)) (cell N i) = ENNReal.ofReal (N:ℝ)⁻¹ := by
  rw [Measure.restrict_apply (show MeasurableSet (cell N i) from measurableSet_Ico),
    inter_eq_self_of_subset_left (cell_subset hn i),cell,Real.volume_Ico]
  congr 1;ring

theorem cell_covers {N : ℕ} (hn : 0 < N) {x : ℝ} (hx : x ∈ Ico 0 1) : ∃ i : Fin N, x ∈ cell N i := by
  have hp : 0 < (N:ℝ) := by exact_mod_cast hn
  have p : 0 ≤ x*N := mul_nonneg hx.1 hp.le
  have l : ⌊x*N⌋₊ < N := (Nat.floor_lt p).mpr (by simpa using mul_lt_mul_of_pos_right hx.2 hp)
  exact ⟨⟨_,l⟩,(div_le_iff₀ hp).mpr (Nat.floor_le p),(lt_div_iff₀ hp).mpr (Nat.lt_floor_add_one _)⟩

/-- Exact derivative scaling on each cell. At the next marking step one can
choose the original transverse direction again. No integer-base assumption. -/
theorem derivative_cell_oscillation {b g ρ T : ℝ} {n N : ℕ} (hb : 0 < b) (hg : 0 < g)
    (hg1 : g < 1) (hr : 0 < ρ) (hr1 : ρ < 1) (hh : 1 < b*(g*ρ)) (hT : 0 ≤ T)
    (hN : 0 < N) (hlen : childLength b T n N ≤ 2) {c d e : ℤ → ℝ} (hc : ∀ j, |c j| ≤ 1)
    (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1) (z : PhaseTorus) (i : Fin N) {x : ℝ}
    (hx : x ∈ cell N i) :
    |derivRay b g ρ c d e z (T*x)-derivRay b g ρ c d e z (anchor T i)| ≤
      (τ*rayBound b (g*ρ) 2)*(g*ρ)^n := by
  let y := b^n*(T*x-anchor T i)
  have _Npos : 0 < (N:ℝ) := by exact_mod_cast hN
  have hlow : 0 ≤ T*x-anchor T i := sub_nonneg.mpr (mul_le_mul_of_nonneg_left hx.1 hT)
  have hup : T*x-anchor T i ≤ T/N := by
    have u := mul_le_mul_of_nonneg_left hx.2.le hT
    dsimp only [anchor]; calc
      _ ≤ T*(((i:ℝ)+1)/N) - T*((i:ℝ)/N) := sub_le_sub_right u _
      _ = _ := by ring
  have hy : |y| ≤ 2 := by
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg hb.le _) hlow)]
    exact (mul_le_mul_of_nonneg_left hup (pow_nonneg hb.le _)).trans (by simpa only [childLength,mul_div_assoc,mul_comm T] using hlen)
  have h1 := mul_pos hg hr
  have h2 : g*ρ < 1 := (mul_lt_of_lt_one_right hg hr1).trans hg1
  have hce j : |c j*e j| ≤ 1 := by
    rw [abs_mul];exact (mul_le_of_le_one_right (abs_nonneg _) (he _)).trans (hc _)
  have H := circleRay_recenter_scale hb h1 h2 hh hce hd (quarter z) (n:ℤ) (anchor T i) y
  have eq : anchor T i+b^(-(n:ℤ))*y = T*x := by
    rw [zpow_neg,zpow_natCast];dsimp [y];field_simp;ring
  rw [eq,zpow_natCast] at H
  unfold derivRay;rw [←mul_sub,H,abs_mul,abs_of_pos (show 0 < τ by dsimp [τ]; positivity),abs_mul,abs_of_pos (pow_pos h1 _)]
  calc
    _ ≤ τ*((g*ρ)^n*rayBound b (g*ρ) 2) := by
      gcongr
      exact circleRay_uniform_bound hb h1 h2 hh (fun j ↦ hce (j+n)) (fun j ↦ hd (j+n)) _ hy
    _ = _ := by ring

/-- Neighbors are determined by the values at the actual left endpoints. -/
def neighbors {N : ℕ} (T : ℝ) (G : ℝ → ℝ) (R : ℝ) (i : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun j ↦ |G (anchor T i)-G (anchor T j)| ≤ R)

theorem neighbor_mass {T D r : ℝ} {N : ℕ} (hN : 0 < N) {G : ℝ → ℝ}
    (osc : ∀ i : Fin N, ∀ y ∈ cell N i, |G (T*y)-G (anchor T i)| ≤ D)
    {i : Fin N} {x : ℝ} (hx : x ∈ cell N i) :
    ((neighbors T G (2*D+r) i).card : ℝ≥0∞)*ENNReal.ofReal (N:ℝ)⁻¹ ≤
    (volume.restrict (Ico (0:ℝ) 1)) {y | |G (T*y)-G (T*x)| ≤ 4*D+r} := by
  classical
  let J := neighbors T G (2*D+r) i
  have disj : (J : Set (Fin N)).PairwiseDisjoint (cell N) := fun _ _ _ _ h ↦ cell_disjoint hN h
  have sum : (volume.restrict (Ico (0:ℝ) 1)) (⋃ j ∈ J, cell N j) = (J.card:ℝ≥0∞)*ENNReal.ofReal (N:ℝ)⁻¹ := by
    rw [measure_biUnion_finset disj (fun _ _ ↦ measurableSet_Ico)]
    simp only [cell_mass hN,Finset.sum_const,nsmul_eq_mul]
  rw [←sum];apply measure_mono
  intro y hy;obtain ⟨j,hj,cy⟩ := mem_iUnion₂.mp hy
  have near := (Finset.mem_filter.mp hj).2
  have a := abs_le.mp (osc j y cy)
  have b := abs_le.mp (osc i x hx)
  have d := abs_le.mp near
  change |G (T*y)-G (T*x)| ≤ 4*D+r
  exact abs_le.mpr ⟨by linarith only [a.1,b.2,d.2],by linarith only [a.2,b.1,d.1]⟩

end Weierstrass.Descent
