module

public import Weierstrass.Graph

/-! # Sharp upper bound for the Hausdorff dimension of a Hölder graph -/

public noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace Weierstrass

private def square (u v r : ℝ) : Set ℂ :=
  {z | z.re ∈ Icc u (u+r) ∧ z.im ∈ Icc v (v+r)}

private theorem square_ediam (u v r : ℝ) : ediam (square u v r) ≤ ENNReal.ofReal (2*r) := by
  apply Metric.ediam_le
  intro x hx y hy
  rcases hx with ⟨⟨h₁,h₂⟩, ⟨h₃,h₄⟩⟩
  rcases hy with ⟨⟨h₅,h₆⟩, ⟨h₇,h₈⟩⟩
  rw [edist_dist, dist_eq_norm]
  apply ENNReal.ofReal_le_ofReal
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  simp only [Complex.sub_re, Complex.sub_im]
  have H : |x.re-y.re| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
  have V : |x.im-y.im| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

private theorem gridCell {x a w r : ℝ} (hr : 0 < r) (hx : x ∈ Icc a (a+w)) :
    ∃ i : Fin (⌊w/r⌋₊ + 1), x ∈ Icc (a + (i:ℕ)*r) (a + (i:ℕ)*r + r) := by
  have hdiff : 0 ≤ (x-a)/r := div_nonneg (sub_nonneg.mpr hx.1) hr.le
  have hle : (x-a)/r ≤ w/r := by gcongr; linarith [hx.2]
  let i : Fin (⌊w/r⌋₊ + 1) := ⟨⌊(x-a)/r⌋₊, Nat.lt_succ_of_le (Nat.floor_mono hle)⟩
  have hbot := (le_div_iff₀ hr).mp (Nat.floor_le hdiff)
  have htop := (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one ((x-a)/r))
  refine ⟨i, ?_, ?_⟩ <;> dsimp [i] <;> linarith

/-- At mesh `r≤1`, explicit columns and rows give a square cover of one unit of graph.
Its cardinality is at most `(4*C+2) * r^(a-2)`. -/
theorem holder_unit_square_cover (f : ℝ → ℝ) {C a r : ℝ} (hC : 0 ≤ C)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) (u : ℝ)
    (holder : ∀ x y, |x-y| ≤ 1 → |f x-f y| ≤ C * |x-y| ^ a) :
    ∃ P Q : ℕ, ∃ cover : Fin P × Fin Q → Set ℂ,
      (∀ i, ediam (cover i) ≤ ENNReal.ofReal (2*r)) ∧
      ((fun x : ℝ => (⟨x,f x⟩ : ℂ)) '' Icc u (u+1) ⊆ ⋃ i, cover i) ∧
      (P:ℝ)*Q ≤ (4*C+2) * r ^ (a-2) := by
  let H := C*r^a
  have hH : 0 ≤ H := mul_nonneg hC (Real.rpow_nonneg hr.le _)
  let P := ⌊1/r⌋₊+1
  let Q := ⌊(2*H)/r⌋₊+1
  let left (i : Fin P) : ℝ := u + (i:ℕ)*r
  let bottom (i : Fin P) (j : Fin Q) : ℝ := f (left i) - H + (j:ℕ)*r
  let cover (ij : Fin P × Fin Q) := square (left ij.1) (bottom ij.1 ij.2) r
  refine ⟨P, Q, cover, fun ij => square_ediam _ _ _, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hix⟩ := gridCell hr hx
    change x ∈ Icc (left i) (left i+r) at hix
    have habs : |x-left i| ≤ r := abs_le.mpr ⟨by linarith [hix.1], by linarith [hix.2]⟩
    have height : |f x-f (left i)| ≤ H := (holder _ _ (habs.trans hr1)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) habs ha) hC)
    obtain ⟨hlo,hhi⟩ := abs_le.mp height
    have hy : f x ∈ Icc (f (left i)-H) ((f (left i)-H)+2*H) := ⟨by linarith, by linarith⟩
    obtain ⟨j, hj⟩ := gridCell hr hy
    exact mem_iUnion.mpr ⟨(i,j), hix, hj⟩
  · have horizontal : (P:ℝ) ≤ 2/r := by
      dsimp [P]; push_cast
      have floorle := Nat.floor_le (by positivity : 0 ≤ 1/r)
      have h : 1 ≤ 1/r := (le_div_iff₀ hr).mpr (by linarith)
      calc
        _ ≤ 1/r + 1/r := add_le_add floorle h
        _ = 2/r := by ring
    have vertical : (Q:ℝ) ≤ (2*C+1)*(r^a/r) := by
      dsimp [Q]; push_cast
      have floorle := Nat.floor_le (by positivity : 0 ≤ 2*H/r)
      have h : 1 ≤ r^a/r := (le_div_iff₀ hr).mpr (by simpa using Real.self_le_rpow_of_le_one hr.le hr1 ha1)
      calc
        _ ≤ 2*H/r + 1 := by linarith
        _ ≤ 2*H/r + (r^a/r) := by linarith
        _ = _ := by dsimp [H]; ring
    calc
      _ ≤ (2/r)*((2*C+1)*(r^a/r)) := mul_le_mul horizontal vertical (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [Real.rpow_sub hr, Real.rpow_two]; ring

/-- The critical Hausdorff measure is finite on each unit of the graph. -/
private theorem holder_unit_measure (f : ℝ → ℝ) {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (ha1 : a ≤ 1) (u : ℝ) (holder : ∀ x y, |x-y| ≤ 1 → |f x-f y| ≤ C * |x-y| ^ a) :
    μH[2-a] ((fun x : ℝ => (⟨x,f x⟩ : ℂ)) '' Icc u (u+1)) < ∞ := by
  let r (n : ℕ) : ℝ := 1/(n+1:ℝ)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hr1 (n : ℕ) : r n ≤ 1 := by dsimp [r]; rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
  choose P Q cover hd hcov hcard using fun n =>
    holder_unit_square_cover f hC ha ha1 (hr n) (hr1 n) u holder
  have zero : Tendsto (fun n => ENNReal.ofReal (2*r n)) atTop (𝓝 0) := by
    have H : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (H.const_mul 2)
  apply lt_of_le_of_lt (Measure.hausdorffMeasure_le_liminf_sum _ _ _ zero cover
    (.of_forall hd) (.of_forall hcov))
  apply lt_of_le_of_lt (b := ENNReal.ofReal ((4*C+2)*2^(2-a))) _ ENNReal.ofReal_lt_top
  apply liminf_le_of_frequently_le' (Frequently.of_forall ?_)
  intro n
  have hd0 : 0 ≤ 2-a := by linarith
  calc
    _ ≤ (Fintype.card (Fin (P n) × Fin (Q n))) • (ENNReal.ofReal (2*r n))^(2-a) := by
      apply (Finset.sum_le_card_nsmul _ _ _ fun i _ => ENNReal.rpow_le_rpow (hd n i) hd0).trans_eq
      rw [Finset.card_univ]
    _ = ENNReal.ofReal (((P n:ℝ)*Q n) * ((2*r n)^(2-a))) := by
      simp only [nsmul_eq_mul, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
        ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ 2*r n) hd0,
        ENNReal.ofReal_mul (by positivity : 0 ≤ (P n:ℝ)*Q n),
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ ((4*C+2)*(r n)^(a-2)) * (2*r n)^(2-a) :=
          mul_le_mul_of_nonneg_right (hcard n) (Real.rpow_nonneg (by positivity) _)
        _ = _ := by
          rw [Real.mul_rpow (by norm_num) (hr n).le]
          have cancel : (r n)^(a-2) * (r n)^(2-a) = 1 := by
            rw [← Real.rpow_add (hr n), show a-2+(2-a)=0 by ring, Real.rpow_zero]
          linear_combination (4*C+2)*2^(2-a)*cancel

/-- Sharp general upper dimension estimate for a graph with a local Hölder bound. -/
theorem dimH_holder_graph_le (f : ℝ → ℝ) {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (ha1 : a ≤ 1) (holder : ∀ x y, |x-y| ≤ 1 → |f x-f y| ≤ C * |x-y| ^ a) (I : Set ℝ) :
    dimH ((fun x : ℝ => (⟨x,f x⟩ : ℂ)) '' I) ≤ ENNReal.ofReal (2-a) := by
  let portion (k : ℤ) := (fun x : ℝ => (⟨x,f x⟩ : ℂ)) '' Icc (k:ℝ) (k+1)
  have cover : (fun x : ℝ => (⟨x,f x⟩ : ℂ)) '' I ⊆ ⋃ k, portion k := by
    rintro _ ⟨x, _, rfl⟩
    exact mem_iUnion.mpr ⟨⌊x⌋, x, ⟨Int.floor_le x, (Int.lt_floor_add_one x).le⟩, rfl⟩
  apply (dimH_mono cover).trans
  rw [dimH_iUnion]
  apply iSup_le
  intro k
  have hpos : 0 ≤ 2-a := by linarith
  rw [ENNReal.ofReal_eq_coe_nnreal hpos]
  exact dimH_le_of_hausdorffMeasure_ne_top (holder_unit_measure f hC ha ha1 k holder).ne

/-- The upper half of the graph dimension formula, for every permitted pair,
every prescribed phase sequence and every set of physical inputs. -/
theorem graph_dim_le_formula {b lam : ℝ} (hb : 1 < b) (hl : b⁻¹ < lam) (h1 : lam < 1)
    (phase : ℕ → ℝ) (I : Set ℝ) : dimH (graph b lam phase I) ≤ ENNReal.ofReal (2-alpha b lam) := by
  obtain ⟨C, hC, increment⟩ := holder_estimate hb hl h1
  obtain ⟨hpos,hlt⟩ := alpha_mem_Ioo hb hl h1
  rw [graph_eq_image]
  exact dimH_holder_graph_le _ hC.le hpos.le hlt.le (increment phase) I

end Weierstrass
