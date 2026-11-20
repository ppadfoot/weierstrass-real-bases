module

public import Weierstrass.HalfFamily

/-! Transverse derivative and one-dimensional sublevel estimates for the
actual maps in §6. Uniform time continuity follows from a summable two-tail
bound and compactness of the coefficient, phase and input parameters. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Complex Weierstrass.CriticalRay Weierstrass.StripProof
open scoped BigOperators Topology ENNReal
namespace Weierstrass.Descent

def quarter (z : PhaseTorus) (j : ℤ) : UnitAddCircle := z j+↑(1/4:ℝ)

def derivRay (b g ρ : ℝ) (c d e : ℤ → ℝ) (z : PhaseTorus) (x : ℝ) : ℝ :=
  τ * circleRay b (g*ρ) (fun j ↦ c j*e j) d (quarter z) x

theorem deriv_circleRay {b g ρ : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hbgρ : 1 < b*(g*ρ)) {c d e : ℤ → ℝ}
    (hc : ∀ j, |c j| ≤ 1) (hd : ∀ j, |d j| ≤ 1) (he : ∀ j, |e j| ≤ 1)
    (z : PhaseTorus) (x t : ℝ) :
    HasDerivAt (fun u ↦ circleRay b g c d (z+transverseOrbit ρ e u) x)
      (derivRay b g ρ c d e (z+transverseOrbit ρ e t) x) t := by
  let w (j : ℤ) : ℝ := AddCircle.equivIco 1 0 (z j)
  have rep (j : ℤ) : (↑(w j):UnitAddCircle) = z j := AddCircle.coe_equivIco
  have env (v : ℝ) : (fun j ↦ (↑(transversePhase ρ e w v j):UnitAddCircle)) = z+transverseOrbit ρ e v := by
    funext j
    change (↑(w j+ρ^j*e j*v):UnitAddCircle) = z j+↑(ρ^j*e j*v)
    rw [AddCircle.coe_add,rep]
  have envq : (fun j ↦ (↑(transversePhase ρ e w t j+1/4):UnitAddCircle)) = quarter (z+transverseOrbit ρ e t) := by
    funext j
    rw [AddCircle.coe_add,congrFun (env t) j];rfl
  have H := hasDerivAt_transverse_rayIncrement hb hg hg1 hρ hρ1 hbgρ hc hd he w x t
  unfold derivRay
  simp_rw [←envq,←env,circleRay_real]
  exact H

abbrev SeqBound := ℤ → Icc (-1:ℝ) 1
private theorem bound (w : SeqBound) (j : ℤ) : |(w j:ℝ)| ≤ 1 := abs_le.mpr (w j).2
abbrev Family (T : ℝ) := SeqBound × SeqBound × SeqBound × PhaseTorus × Icc (-T) T

private def varied (b g ρ T : ℝ) (a : Family T) (u : ℝ) :=
  derivRay b g ρ (fun j ↦ (a.1 j:ℝ)) (fun j ↦ (a.2.1 j:ℝ)) (fun j ↦ (a.2.2.1 j:ℝ))
    (a.2.2.2.1+transverseOrbit ρ (fun j ↦ (a.2.2.1 j:ℝ)) u) a.2.2.2.2

private theorem continuous_varied {b g ρ T : ℝ} (hb : 0 < b) (hg : 0 < g)
    (hg1 : g < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hbgρ : 1 < b*(g*ρ)) (hT : 0 ≤ T) :
    Continuous (fun a : Family T × ℝ ↦ varied b g ρ T a.1 a.2) := by
  let H := g*ρ
  have hp : 0 < H := mul_pos hg hρ
  have hp1 : H < 1 := (mul_lt_of_lt_one_right hg hρ1).trans hg1
  have tp : 0 < τ := by dsimp [τ];positivity
  apply continuous_const.mul
  change Continuous (fun a : Family T × ℝ ↦ ∑' j, angleTerm b H
    (fun i ↦ (a.1.1 i:ℝ)*(a.1.2.2.1 i:ℝ)) (fun i ↦ (a.1.2.1 i:ℝ))
    (quarter (a.1.2.2.2.1+transverseOrbit ρ (fun i ↦ (a.1.2.2.1 i:ℝ)) a.2)) a.1.2.2.2.2 j)
  apply continuous_tsum (u:=fun j ↦ (2+τ*T)*tails H (b*H) j)
  · intro j
    unfold angleTerm angleCos quarter transverseOrbit
    fun_prop
  · exact (summable_tails hp.le hp1 hbgρ).mul_left _
  · intro j a
    have hu i : |(a.1.1 i:ℝ)*(a.1.2.2.1 i:ℝ)| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (bound _ _)).trans (bound _ _)
    have hx : |((a.1.2.2.2.2:ℝ))| ≤ T := abs_le.mpr a.1.2.2.2.2.property
    rw [Real.norm_eq_abs,tails]
    split
    · apply (angleTerm_bounded hp b hu _ _ _ _).trans
      gcongr
      linarith only [mul_nonneg tp.le hT]
    · apply (angleTerm_lipschitz hb hp hu (bound _) _ _ _).trans
      gcongr
      linarith only [mul_le_mul_of_nonneg_left hx tp.le]

private theorem uniform_slice {X : Type*} [TopologicalSpace X] [SeqCompactSpace X]
    (F : X → ℝ → ℝ) (cf : Continuous (Function.uncurry F)) {ε : ℝ} (he : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x u, |u| ≤ δ → |F x u-F x 0| ≤ ε := by
  by_contra! bad
  let r (n:ℕ) : ℝ := 1/((n:ℝ)+1)
  choose x u small big using fun n : ℕ ↦ bad (r n) (by dsimp [r];positivity)
  obtain ⟨a,k,hk,cv⟩ := SeqCompactSpace.tendsto_subseq x
  have lim : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ut : Tendsto u atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun _ ↦ abs_nonneg _) small lim)
  have c1 := cf.continuousAt.tendsto.comp (cv.prodMk_nhds (ut.comp hk.tendsto_atTop))
  have c2 := cf.continuousAt.tendsto.comp (cv.prodMk_nhds (tendsto_const_nhds (x:=(0:ℝ))))
  have zero := (c1.sub c2).abs
  rw [sub_self,abs_zero] at zero
  obtain ⟨n,h⟩ := (zero.eventually_lt_const he).exists
  exact (not_lt_of_ge (big (k n)).le) h

/-- All two-sided derivatives of the translated physical model have a common
continuity modulus on every bounded physical interval, uniformly in the
transverse base point and the full deterministic phase. -/
theorem derivative_uniform_modulus {b g ρ T : ℝ} (hb : 0 < b) (hg : 0 < g)
    (hg1 : g < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hbgρ : 1 < b*(g*ρ)) (hT : 0 ≤ T)
    {ε : ℝ} (he : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (c d e : ℤ → ℝ), (∀ j, |c j| ≤ 1) → (∀ j, |d j| ≤ 1) →
      (∀ j, |e j| ≤ 1) → ∀ (z : PhaseTorus) (x s t : ℝ), |x| ≤ T → |s-t| ≤ δ →
      |derivRay b g ρ c d e (z+transverseOrbit ρ e s) x -
       derivRay b g ρ c d e (z+transverseOrbit ρ e t) x| ≤ ε := by
  obtain ⟨δ,hδ,v⟩ := uniform_slice (varied b g ρ T) (continuous_varied hb hg hg1 hρ hρ1 hbgρ hT) he
  refine ⟨δ,hδ,?_⟩
  intro c d e hc hd he z x s t hx hst
  let w (f : ℤ → ℝ) (hf : ∀ i, |f i| ≤ 1) : SeqBound := fun i ↦ ⟨f i,abs_le.mp (hf i)⟩
  let a : Family T := (w c hc,w d hd,w e he,z+transverseOrbit ρ e t,⟨x,abs_le.mp hx⟩)
  have H := v a (s-t) hst
  have A : z+transverseOrbit ρ e t+transverseOrbit ρ e (s-t)= z+transverseOrbit ρ e s := by
    rw [add_assoc,←transverseOrbit_add];congr 2;ring
  have Z : transverseOrbit ρ e 0 = 0 := by ext j;simp [transverseOrbit]
  change |derivRay b g ρ c d e (z+transverseOrbit ρ e t+transverseOrbit ρ e (s-t)) x -
      derivRay b g ρ c d e (z+transverseOrbit ρ e t+transverseOrbit ρ e 0) x| ≤ ε at H
  rwa [A,Z,add_zero] at H

end Weierstrass.Descent
