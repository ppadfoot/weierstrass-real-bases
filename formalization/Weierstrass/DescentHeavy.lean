module

public import Weierstrass.DescentPacking

/-! Collision at depth k for actual physical label words. All deterministic
states and all Haar translates are included in the induction. -/
@[expose] public noncomputable section
open Set MeasureTheory Filter Weierstrass.CriticalRay Weierstrass.StripProof
open scoped BigOperators ENNReal
namespace Weierstrass.Descent
local instance heavyGroupMeasure (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance heavyGroupBorel (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

open Predecessor (unitLaw)

def heavy (B : ℂ) (g T : ℝ) (p : RayParameters) (ω : PhaseTorus) (R τ : ℝ) : ℝ≥0∞ :=
  ((complexPhaseHaar B).prod Predecessor.unitLaw) {z : complexPhaseGroup B × ℝ |
    let y := ordinate ‖B‖ g T p (ω+z.1.val) z.2
    ENNReal.ofReal τ < fullLaw ‖B‖ g T p (ω+z.1.val) (Icc (y-R) (y+R))}

theorem heavy_mono (B : ℂ) (g T : ℝ) (p : RayParameters) (ω : PhaseTorus) {R S θ τ : ℝ}
    (rs : R ≤ S) (tt : θ ≤ τ) : heavy B g T p ω R τ ≤ heavy B g T p ω S θ := by
  apply measure_mono;intro z hz
  exact ((ENNReal.ofReal_le_ofReal tt).trans_lt hz).trans_le (measure_mono (Icc_subset_Icc
    (sub_le_sub_left rs _) (add_le_add_right rs _)))

set_option maxHeartbeats 2300000 in
theorem physical_heavy_mesh {B : ℂ} (hb : 0 < ‖B‖) {g ρ : ℝ} (hg : 0 < g) (hg1 : g < 1)
    (hr : 0 < ρ) (hr1 : ρ < 1) (hh : 1 < ‖B‖*(g*ρ)) (n : ℕ) (hn : 2 ≤ ‖B‖^n)
    {e : ℤ → ℝ} (he : ∀ j, |e j| ≤ 1) (hm : ∀ x, transverseOrbit ρ e x ∈ complexPhaseGroup B)
    {P : Set RayParameters} (weights : ∀ p ∈ P, (∀ j, |p.1 j| ≤ 1) ∧ (∀ j, |p.2 j| ≤ 1) ∧ shiftedParameters p n ∈ P)
    {A t δ M ε : ℝ} (hA : 0 < A) (ht : 0 ≤ t) (ht' : t ≤ 1) (hδ : 0 < δ) (hM : 1 < M) (heps : 0 ≤ ε)
    (bad : ∀ p ∈ P, ∀ {T : ℝ}, 1 ≤ T → T ≤ 3 → ∀ ω : PhaseTorus,
      (∫⁻ z : complexPhaseGroup B, badShare ‖B‖ g ρ T ((g^n:ℝ)^t) n (arity ‖B‖ T n) p e (ω+z.val) ∂complexPhaseHaar B) ≤ ENNReal.ofReal ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (k : ℕ) (u : ℝ), ∀ {T : ℝ}, 1 ≤ T → T ≤ 3 → ∀ {p : RayParameters}, p ∈ P → ∀ ω : PhaseTorus,
      let q := g^n
      heavy B g T p ω (A*q^k) ((q^k:ℝ)^u) ≤ ENNReal.ofReal
        (ε/δ + 3/M + M*C*(k+1:ℝ)*(12*q^(t*(1-δ)-u))^k) := by
  obtain ⟨C,hC,packing⟩ := retained_collision_cost hb hg hg1 hr hr1 hh n hn he hm weights hA ht ht' hδ.le
  refine ⟨C,hC,?_⟩
  intro k u T T1 T3 p hp ω
  let q := g^n
  let m := ⌊δ*k⌋₊
  let μ (w : complexPhaseGroup B) := retainedLaw ‖B‖ g ρ (q^t) n e k m T p (ω+w.val)
  let f (w : complexPhaseGroup B) := ordinate ‖B‖ g T p (ω+w.val)
  have hbg : 1 < ‖B‖*g := hh.trans (mul_lt_mul_of_pos_left (mul_lt_of_lt_one_right hg hr1) hb)
  obtain ⟨hc,hd,_⟩ := weights p hp
  have mω : Measurable (fun w : complexPhaseGroup B ↦ ω+w.val) := measurable_const.add continuous_subtype_val.measurable
  have mz : Measurable (fun v : complexPhaseGroup B × ℝ ↦ ω+v.1.val) := mω.comp measurable_fst
  have mv : Measurable (fun v : complexPhaseGroup B × ℝ ↦ (ω+v.1.val,v.2)) := mz.prodMk measurable_snd
  have mf : Measurable (Function.uncurry f) := by
    change Measurable ((fun v : PhaseTorus × ℝ ↦ ordinate ‖B‖ g T p v.1 v.2) ∘ (fun v : complexPhaseGroup B × ℝ ↦ (ω+v.1.val,v.2)))
    exact (ordinate_joint ‖B‖ g T p).comp mv
  have mm : Measurable μ := (retained_measurable hb hg hg1 hbg ρ (q^t) n e k m T hc hd).comp mω
  have qp := pow_pos hg n
  have rp := pow_pos qp k
  have τp := Real.rpow_pos_of_pos rp u
  have H := Predecessor.sampled_full_ball (complexPhaseHaar B) f mf μ mm (fun w ↦ retained_le hb hg hg1 hbg ρ (q^t) n e k m T hc hd (ω+w.val)) (mul_pos hA rp) τp hM
  apply H.trans
  let F (w : complexPhaseGroup B) := countMass ‖B‖ g ρ (q^t) n e k T p (ω+w.val)
  have mF : Measurable F := (countMass_measurable hb hg hg1 hbg ρ (q^t) n e k T hc hd).comp mω
  have disc : (∫⁻ w, 1-μ w univ ∂complexPhaseHaar B) ≤ ENNReal.ofReal ε/ENNReal.ofReal δ := by
    apply (lintegral_mono (g:=fun w ↦ F w/((m+1:ℕ):ℝ≥0∞)) (fun w ↦ discarded_le_count hb hg hg1 hbg ρ (q^t) n e k m T hc hd (ω+w.val))).trans
    simp only [div_eq_mul_inv,lintegral_mul_const _ mF]
    have count := countMass_haar_bound hb hg hg1 hbg ρ (q^t) n hn e weights bad k hp T1 T3 ω
    exact (mul_le_mul_left count _).trans (Predecessor.discard_floor_bound k hδ _)
  have col := packing k T1 T3 hp ω
  apply (add_le_add (add_le_add_left disc _) (mul_le_mul_right col _)).trans_eq
  have cst : 0 ≤ C*(k+1:ℝ)*(12*q^(t*(1-δ)))^k := by positivity
  rw [←ENNReal.ofReal_div_of_pos hδ,←ENNReal.ofReal_add (div_nonneg heps hδ.le) (div_nonneg (by norm_num) (zero_lt_one.trans hM).le),
    ←ENNReal.ofReal_mul (div_nonneg (zero_lt_one.trans hM).le τp.le),←ENNReal.ofReal_add (by positivity) (mul_nonneg (div_nonneg (zero_lt_one.trans hM).le τp.le) cst)]
  congr 1
  have eq : (q^k:ℝ)^u=(q^u)^k := by rw [←Real.rpow_natCast_mul qp.le,←Real.rpow_mul_natCast qp.le,mul_comm]
  rw [eq,Real.rpow_sub qp,mul_pow,mul_pow,div_pow];ring

end Weierstrass.Descent
