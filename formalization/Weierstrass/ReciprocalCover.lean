module

public import Weierstrass.RayInformationTransport

/-! Two-scale covering by averaging over centers in Proposition 2. -/
@[expose] public noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal Topology
namespace Weierstrass.Reciprocal

/-- The open neighborhood of all retained transverse points. -/
def neighborhood (E : Set ℝ) (u : ℝ) : Set ℝ := ⋃ x ∈ E, ball x u

theorem neighborhood_mem {E : Set ℝ} {u y : ℝ} :
    y ∈ neighborhood E u ↔ ∃ x ∈ E, |y-x| < u := by
  simp [neighborhood, Real.dist_eq]

theorem open_neighborhood (E : Set ℝ) (u : ℝ) : IsOpen (neighborhood E u) :=
  isOpen_iUnion (fun _ ↦ isOpen_iUnion (fun _ ↦ isOpen_ball))

theorem neighborhood_contains (E : Set ℝ) {u : ℝ} (hu : 0 < u) : E ⊆ neighborhood E u :=
  fun x hx ↦ neighborhood_mem.mpr ⟨x,hx,by simpa using hu⟩

/-- Controlling the length of an occupied fine neighborhood inside every
coarse test interval contracts its entire length by the same factor. -/
theorem neighborhood_step (E : Set ℝ) {u v : ℝ} (hu : 0 < u) (hvu : v ≤ u/2) (q : ℝ≥0∞)
    (localBound : ∀ y ∈ neighborhood E u, volume (ball y (u/2) ∩ neighborhood E v) ≤ ENNReal.ofReal u * q) :
    volume (neighborhood E v) ≤ q*volume (neighborhood E u) := by
  let V := neighborhood E v
  let U := neighborhood E u
  let μ := volume.restrict V
  let ν := volume.restrict U
  let X := {p : ℝ × ℝ | dist p.1 p.2 < u/2}
  have mX : MeasurableSet X := measurableSet_lt (continuous_fst.dist continuous_snd).measurable measurable_const
  have cover {x : ℝ} (hx : x ∈ V) : ball x (u/2) ⊆ U := by
    obtain ⟨r,hr,close⟩ := neighborhood_mem.mp hx
    intro y hy
    refine neighborhood_mem.mpr ⟨r,hr,(abs_sub_le y x r).trans_lt ?_⟩
    rw [mem_ball, Real.dist_eq] at hy
    linarith
  have time (x : ℝ) (hx : x ∈ V) : ν (Prod.mk x ⁻¹' X) = ENNReal.ofReal u := by
    have eq : Prod.mk x ⁻¹' X = ball x (u/2) := by ext y; change dist x y < u/2 ↔ dist y x < u/2; rw [dist_comm x y]
    rw [eq, show ν = volume.restrict U from rfl, Measure.restrict_apply isOpen_ball.measurableSet,
      inter_eq_self_of_subset_left (cover hx), Real.volume_ball]
    congr 1; ring
  have centers (y : ℝ) (hy : y ∈ U) : μ ((fun x ↦ (x,y)) ⁻¹' X) ≤ ENNReal.ofReal u*q := by
    change volume.restrict V (ball y (u/2)) ≤ _
    rw [Measure.restrict_apply isOpen_ball.measurableSet]
    exact localBound y hy
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_ne_zero_iff.mpr hu) ENNReal.ofReal_ne_top).mp
  calc
    ENNReal.ofReal u * volume V = ∫⁻ x, ν (Prod.mk x ⁻¹' X) ∂μ := by
      calc
        _ = ∫⁻ _ : ℝ in V, ENNReal.ofReal u := by simp
        _ = _ := setLIntegral_congr_fun (open_neighborhood _ _).measurableSet (fun x hx ↦ (time x hx).symm)
    _ = (μ.prod ν) X := (Measure.prod_apply mX).symm
    _ = ∫⁻ y, μ ((fun x ↦ (x,y)) ⁻¹' X) ∂ν := Measure.prod_apply_symm mX
    _ ≤ ∫⁻ _ : ℝ in U, ENNReal.ofReal u*q := setLIntegral_mono measurable_const centers
    _ = ENNReal.ofReal u * (q*volume U) := by simp [mul_assoc]

/-- A unit segment has bounded neighborhood throughout all scales up to one. -/
theorem initial_neighborhood {E : Set ℝ} (hE : E ⊆ Icc 0 1) {u : ℝ} (hu : u ≤ 1) :
    volume (neighborhood E u) ≤ 3 := by
  have sub : neighborhood E u ⊆ Icc (-1) 2 := by
    intro y hy
    obtain ⟨x,hx,hxy⟩ := neighborhood_mem.mp hy
    have xx := hE hx
    rw [abs_lt] at hxy
    exact ⟨by linarith [xx.1,hxy.1],by linarith [xx.2,hxy.2]⟩
  exact (measure_mono sub).trans_eq (by rw [Real.volume_Icc]; norm_num)


/-- Iteration of a finite sequence of retained-neighborhood estimates.
Consecutive amplitude factors telescope exactly, independently of stage count. -/
theorem neighborhood_chain {γ ρ σ : ℝ} (gp : 0 < γ) (rp : 0 < ρ) (r1 : ρ ≤ 1)
    (E : Set ℝ) (hE : E ⊆ Icc 0 1) (m : ℕ → ℕ) (D : ℕ)
    (order : ∀ i < D, m i ≤ m (i+1))
    (step : ∀ i < D, volume (neighborhood E (ρ^(m (i+1)))) ≤
      ENNReal.ofReal ((γ^(m (i+1)-m i))^σ)*volume (neighborhood E (ρ^(m i)))) :
    volume E ≤ 3*ENNReal.ofReal ((γ^(m D-m 0))^σ) := by
  have run : ∀ j ≤ D, m 0 ≤ m j ∧ volume (neighborhood E (ρ^(m j))) ≤
      3*ENNReal.ofReal ((γ^(m j-m 0))^σ) := by
    intro j hj
    induction j with
    | zero =>
      refine ⟨le_rfl,?_⟩
      simpa using initial_neighborhood hE (pow_le_one₀ rp.le r1 : ρ^(m 0) ≤ 1)
    | succ j ih =>
      obtain ⟨h₀,bound⟩ := ih (by omega)
      have mono := order j (by omega)
      refine ⟨h₀.trans mono,(step j (by omega)).trans ((mul_le_mul_right bound _).trans_eq ?_)⟩
      rw [← mul_left_comm, ← mul_assoc]
      rw [show (3:ℝ≥0∞)*ENNReal.ofReal ((γ^(m (j+1)-m j))^σ)*ENNReal.ofReal ((γ^(m j-m 0))^σ) =
        3*(ENNReal.ofReal ((γ^(m (j+1)-m j))^σ)*ENNReal.ofReal ((γ^(m j-m 0))^σ)) by ring]
      rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos (pow_pos gp _) _).le,
        ← Real.mul_rpow (pow_pos gp _).le (pow_pos gp _).le,← pow_add,show m (j+1)-m j+(m j-m 0)=m (j+1)-m 0 by omega]
  exact (measure_mono (neighborhood_contains E (pow_pos rp _))).trans (run D le_rfl).2

end Weierstrass.Reciprocal
