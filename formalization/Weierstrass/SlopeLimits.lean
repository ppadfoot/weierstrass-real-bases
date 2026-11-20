module

public import Weierstrass.SlopePacking

/-! Complete finite-depth estimates for the induction at every real amplitude. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Weierstrass.Predecessor

theorem badSlope_eventually {p d : ℕ} (hp : 0<p) (a : ℕ → ℤ) {c g s t v : ℝ}
    (hg : 0<g) (hc : 0<c) (h1 : g*c<1) (v0 : 0<v) (vs : v<s) (test : (g*c)^v ≤ g^t)
    (info : SlopeInformation hp d a (g*c) s) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ η, statusMass hp d a n g c ((p:ℝ)^n*(g^n:ℝ)^t) [true] η ≤ ENNReal.ofReal ε := by
  let h := g*c
  have ph := mul_pos hg hc
  have Apos : 0<4*(1-h)⁻¹+1 := by have := inv_pos.mpr (sub_pos.mpr h1);dsimp only [h];linarith
  have lim : Tendsto (fun n : ℕ ↦ h^n) atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_pow_atTop_nhds_zero_of_lt_one ph.le h1,Eventually.of_forall (fun n ↦ pow_pos ph n)⟩
  filter_upwards [lim.eventually (info v v0 vs _ Apos _ hε)] with n valid
  intro η
  have pp : 0<(p:ℝ) := by exact_mod_cast hp
  have pp' := pow_pos pp n
  have eq (x : ℝ) (px : 0<x) (v : ℝ) : (x^n:ℝ)^v = (x^v)^n := by
    rw [← Real.rpow_natCast_mul px.le,← Real.rpow_mul_natCast px.le,mul_comm]
  have th : (h^n:ℝ)^v ≤ ((p:ℝ)^n*(g^n:ℝ)^t)*(p:ℝ)⁻¹^n := by
    rw [eq h ph,eq g hg,inv_pow,show (p:ℝ)^n*(g^t)^n*((p:ℝ)^n)⁻¹ = (g^t)^n by field_simp]
    exact pow_le_pow_left₀ (Real.rpow_nonneg ph.le _) test _
  apply (statusMass_bad_le_derivative hp d a n g c _ ph.le h1 (by positivity) η).trans
  exact (slopeHeavy_mono hp d a h _ le_rfl th).trans (valid (fun k => η k+Real.pi/2))

set_option maxHeartbeats 1000000 in
/-- Explicit finite mesh probability bound, uniform over the phase strings. -/
theorem slopeHeavy_mesh_rate {p d : ℕ} (hp : 0<p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c g : ℝ} (hg : 0<g) (hg' : g<1) (hc : 0<c) (hc' : c<1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) (n : ℕ)
    {t δ : ℝ} (ht : 0≤t) (ht' : t≤1) (hδ : 0<δ) {A M : ℝ} (hA : 0<A) (hM : 1<M)
    {e : ℝ} (he : 0≤e) (bad : ∀ η, statusMass hp (d+1) a n g c ((p:ℝ)^n*(g^n:ℝ)^t) [true] η ≤ ENNReal.ofReal e) :
    ∃ C : ℝ, 0<C ∧ C = 3*max 1 (slopeSliceBound g c n*A) ∧ ∀ (k : ℕ) (u : ℝ) (η : ℕ → ℝ), let q := g^n
      slopeHeavy hp (d+1) a g η (A*q^k) ((q^k:ℝ)^u) ≤ ENNReal.ofReal
        (e/δ + 3/M + M*C*(k+1:ℝ)*(12*q^(t*(1-δ)-u))^k) := by
  obtain ⟨C,hC,hEq,packing⟩ := retained_collision_cost_rate hp a ha hg hg' hc hc' hbc hpoly n ht ht' hδ.le hA
  refine ⟨C,hC,hEq,?_⟩
  intro k u η
  let q := g^n
  let T := (p:ℝ)^n*q^t
  let Ω := Fin (d+1) → UnitAddCircle
  let μ := retainedStatusLaw hp (d+1) a n k ⌊δ*k⌋₊ g c T η
  let f (w : Ω) (x : ℝ) := codedSlope (d+1) (fun i ↦ (a i:ℝ)) p g (centralLift w) η (uniformCode p hp x)
  have mf : Measurable (Function.uncurry f) := measurable_coded_sample hp (d+1) a
    (fun z : Ω × ℝ => centralLift z.1) (fun i ↦ (measurable_centralLift _ i).comp measurable_fst) Prod.snd measurable_snd η g
  have mm : Measurable μ := Finset.measurable_fun_sum _ (fun v _ ↦ measurable_statusSlopeLaw hp (d+1) a n hg.le hg' c T _ η)
  have qp := pow_pos hg n
  have rp := pow_pos qp k
  have τp := Real.rpow_pos_of_pos rp u
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  have hb := sampled_full_ball (volume : Measure Ω) f mf μ mm (fun w ↦ retainedStatusLaw_domination hp (d+1) a n k _ hg.le hg' c T η w)
    (mul_pos hA rp) τp hM
  apply hb.trans
  have disc := (retainedStatusLaw_discard hp a ha n hg.le hg' c T bad k ⌊δ*k⌋₊ η).trans (discard_floor_bound _ hδ _)
  have col := packing k η
  apply (add_le_add (add_le_add_left disc _) (mul_le_mul_right col _)).trans_eq
  have cst : 0 ≤ C*(k+1:ℝ)*(12*q^(t*(1-δ)))^k := by positivity
  rw [←ENNReal.ofReal_div_of_pos hδ,←ENNReal.ofReal_add (div_nonneg he hδ.le) (div_nonneg (by norm_num) (zero_lt_one.trans hM).le),
    ←ENNReal.ofReal_mul (div_nonneg (zero_lt_one.trans hM).le τp.le),←ENNReal.ofReal_add (by positivity) (mul_nonneg (div_nonneg (zero_lt_one.trans hM).le τp.le) cst)]
  congr 1
  have eq : (q^k:ℝ)^u=(q^u)^k := by rw [←Real.rpow_natCast_mul qp.le,←Real.rpow_mul_natCast qp.le,mul_comm]
  rw [eq,Real.rpow_sub qp,mul_pow,mul_pow,div_pow];ring

theorem slopeHeavy_mesh {p d : ℕ} (hp : 0<p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {b c g : ℝ} (hg : 0<g) (hg' : g<1) (hc : 0<c) (hc' : c<1) (hbc : b*c=1)
    (hpoly : (p:ℝ)+b*∑ k ∈ Finset.range (d+1), (a k:ℝ)*b^k = 0) (n : ℕ)
    {t δ : ℝ} (ht : 0≤t) (ht' : t≤1) (hδ : 0<δ) {A M : ℝ} (hA : 0<A) (hM : 1<M)
    {e : ℝ} (he : 0≤e) (bad : ∀ η, statusMass hp (d+1) a n g c ((p:ℝ)^n*(g^n:ℝ)^t) [true] η ≤ ENNReal.ofReal e) :
    ∃ C : ℝ, 0<C ∧ ∀ (k : ℕ) (u : ℝ) (η : ℕ → ℝ), let q := g^n
      slopeHeavy hp (d+1) a g η (A*q^k) ((q^k:ℝ)^u) ≤ ENNReal.ofReal
        (e/δ + 3/M + M*C*(k+1:ℝ)*(12*q^(t*(1-δ)-u))^k) := by
  obtain ⟨C,hC,_,H⟩ := slopeHeavy_mesh_rate hp a ha hg hg' hc hc' hbc hpoly n ht ht' hδ hA hM he bad
  exact ⟨C,hC,H⟩

end Weierstrass.Predecessor
