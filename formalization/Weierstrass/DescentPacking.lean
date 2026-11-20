module

public import Weierstrass.DescentIteration

/-! Collision at depth k for actual physical label words. All deterministic
states and all Haar translates are included in the induction. -/
@[expose] public noncomputable section
open Set MeasureTheory Filter Weierstrass.CriticalRay Weierstrass.StripProof
open scoped BigOperators ENNReal
namespace Weierstrass.Descent
local instance packGroupMeasure (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance packGroupBorel (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

open Predecessor (collision collision_integrable wordCoefficient_sparse averaged_retained_collision)

theorem retained_collision_cost {B : ℂ} (hb : 0 < ‖B‖) {g ρ : ℝ} (hg : 0 < g) (hg1 : g < 1)
    (hr : 0 < ρ) (hr1 : ρ < 1) (hh : 1 < ‖B‖*(g*ρ)) (n : ℕ) (hn : 2 ≤ ‖B‖^n)
    {e : ℤ → ℝ} (he : ∀ j, |e j| ≤ 1) (hm : ∀ x, transverseOrbit ρ e x ∈ complexPhaseGroup B)
    {P : Set RayParameters} (weights : ∀ p ∈ P, (∀ j, |p.1 j| ≤ 1) ∧ (∀ j, |p.2 j| ≤ 1) ∧ shiftedParameters p n ∈ P)
    {A t δ : ℝ} (hA : 0 < A) (ht : 0 ≤ t) (ht' : t ≤ 1) (hδ : 0 ≤ δ) :
    ∃ C : ℝ, 0<C ∧ ∀ k : ℕ, ∀ {T : ℝ}, 1 ≤ T → T ≤ 3 → ∀ {p : RayParameters}, p ∈ P → ∀ ω : PhaseTorus,
      (∫⁻ w : complexPhaseGroup B, let μ := retainedLaw ‖B‖ g ρ ((g^n:ℝ)^t) n e k ⌊δ*k⌋₊ T p (ω+w.val)
        ENNReal.ofReal (Predecessor.collision μ μ (A*(g^n)^k)) ∂complexPhaseHaar B) ≤
      ENNReal.ofReal (C*(k+1:ℝ)*(12*(g^n:ℝ)^(t*(1-δ)))^k) := by
  let q := g^n
  have pq := pow_pos hg n
  have sq : q≤1 := pow_le_one₀ hg.le hg1.le
  have hbg : 1 < ‖B‖*g := hh.trans (mul_lt_mul_of_pos_left (mul_lt_of_lt_one_right hg hr1) hb)
  obtain ⟨K,hK,iter⟩ := energy_iteration hb hg hg1 hr hr1 hh n hn he hm weights hA ht'
  refine ⟨3*K,by positivity,?_⟩
  intro k T T1 T3 p hp ω
  let μ (w : complexPhaseGroup B) := retainedLaw ‖B‖ g ρ (q^t) n e k ⌊δ*k⌋₊ T p (ω+w.val)
  let I := Predecessor.sparseStatusWords k ⌊δ*k⌋₊
  let V (w : complexPhaseGroup B) (v : I) := wordLaw ‖B‖ g ρ (q^t) n e (List.ofFn v.val) T p (ω+w.val)
  let R := A*q^k
  let U := K*(k+1:ℝ)*(3*q^(t*(1-δ)))^k
  have bp : 0 ≤ U := by dsimp only [U];positivity
  obtain ⟨hc,hd,_⟩ := weights p hp
  have mω : Measurable (fun w : complexPhaseGroup B ↦ ω+w.val) := measurable_const.add continuous_subtype_val.measurable
  have bound (v : I) (w : complexPhaseGroup B) : V w v univ ≤ 1 :=
    (wordLaw_le hb hg hg1 hbg ρ (q^t) n e _ T hc hd _ univ).trans_eq measure_univ
  have mb (w : complexPhaseGroup B) : μ w univ ≤ 1 := (retained_le hb hg hg1 hbg ρ (q^t) n e k _ T hc hd _ univ).trans_eq measure_univ
  have mf (w : complexPhaseGroup B) : IsFiniteMeasure (μ w) := ⟨(mb w).trans_lt ENNReal.one_lt_top⟩
  have vf (w : complexPhaseGroup B) (v : I) : IsFiniteMeasure (V w v) := ⟨(bound v w).trans_lt ENNReal.one_lt_top⟩
  have Vint (v : I) : Integrable (fun w ↦ Predecessor.collision (V w v) (V w v) R) (complexPhaseHaar B) :=
    collision_integrable _ _ ((measurable_wordLaw hb hg hg1 hbg ρ (q^t) n e _ T hc hd).comp mω) (bound v) R
  have mm : Measurable μ := (retained_measurable hb hg hg1 hbg ρ (q^t) n e k _ T hc hd).comp mω
  have mi := collision_integrable (complexPhaseHaar B) μ mm mb R
  have Vintegral (v : I) : (∫ w, Predecessor.collision (V w v) (V w v) R ∂complexPhaseHaar B) ≤ U := by
    have bd := iter (List.ofFn v.val) T1 T3 hp ω
    simp only [List.length_ofFn] at bd
    unfold wordEnergy at bd
    rw [←ofReal_integral_eq_lintegral_ofReal (Vint v) (Eventually.of_forall (fun _ ↦ measureReal_nonneg))] at bd
    apply (ENNReal.ofReal_le_ofReal_iff bp).mp
    apply bd.trans (ENNReal.ofReal_le_ofReal _)
    rw [mul_assoc (K*(k+1:ℝ))]
    exact mul_le_mul_of_nonneg_left (wordCoefficient_sparse pq sq ht hδ v.property) (by positivity)
  have cmp (w : complexPhaseGroup B) : μ w ≤ ∑ v : I, V w v := by
    exact (Finset.sum_coe_sort I (fun v ↦ wordLaw ‖B‖ g ρ (q^t) n e (List.ofFn v) T p (ω+w.val))).symm.le
  have est := averaged_retained_collision (complexPhaseHaar B) μ V (mul_pos hA (pow_pos pq k)) cmp Vint Vintegral
  rw [←ofReal_integral_eq_lintegral_ofReal mi (.of_forall fun _ ↦ measureReal_nonneg)]
  apply ENNReal.ofReal_le_ofReal (est.trans _)
  have card : (Fintype.card I:ℝ) ≤ (2:ℝ)^k := by
    exact_mod_cast (show Fintype.card I ≤ 2^k from by simpa using Fintype.card_le_of_injective (fun v : I => v.val) Subtype.val_injective)
  calc
    _ ≤ 3*((2:ℝ)^k)^2*U := by gcongr
    _ = _ := by
      dsimp only [q,U];rw [show (12:ℝ)=2*2*3 by norm_num,mul_pow,mul_pow,mul_pow,mul_pow];ring

end Weierstrass.Descent
