module

public import Weierstrass.BranchMarks
public import Weierstrass.BranchRandomization

/-! Simultaneous retention on a finite array of varying window lengths,
and transfer of the randomized estimate to the physical Haar cosets. -/
@[expose] public noncomputable section
open Set MeasureTheory Filter Weierstrass.Predecessor
open scoped ENNReal Topology BigOperators
namespace Weierstrass.Branch

def gridGood {p K L : ℕ} (hp : 0<p) (d : ℕ) (a : ℕ → ℤ) (g c D σ : ℝ) (η : ℕ → ℝ)
    (depth step : Fin K → Fin L → ℕ → ℕ) (m : ℕ) : Set ((Fin d → UnitAddCircle) × ℝ) :=
  {z | ∀ i j, goodStep hp d a g c D (centralLift z.1) η (uniformCode p hp z.2)
      (depth i j m) (step i j m) (ENNReal.ofReal ((g^(step i j m):ℝ)^σ))}

theorem measurableSet_gridGood {p K L : ℕ} (hp : 0<p) (d : ℕ) (a : ℕ → ℤ) (g c D σ : ℝ) (η : ℕ → ℝ)
    (depth step : Fin K → Fin L → ℕ → ℕ) (m : ℕ) : MeasurableSet (gridGood hp d a g c D σ η depth step m) := by
  simp only [gridGood,Set.ofPred_forall]
  apply MeasurableSet.iInter;intro i;apply MeasurableSet.iInter;intro j
  exact measurable_goodStep hp d a g c D _ (fun _ ↦ η) _ (fun k ↦ (measurable_centralLift _ k).comp measurable_fst)
    (fun _ ↦ measurable_const) (fun k ↦ (measurable_uniformCode p hp k).comp measurable_snd) _ _ _

theorem gridGood_loss {p d K L : ℕ} (hp : 0<p) (a : ℕ → ℤ) (ha : a d ≠ 0)
    {g s σ : ℝ} (hg : 0<g) (h1 : g<1) (info : SlopeInformation hp (d+1) a g s)
    (hσ : 0<σ) (hs : σ<s) (c D : ℝ) {δ : ℝ} (hδ : 0<δ) (depth step : Fin K → Fin L → ℕ → ℕ)
    (long : ∀ i j, Tendsto (step i j) atTop atTop) :
    ∀ᶠ m : ℕ in atTop, ∀ η, centerAndSeed (d+1) (gridGood hp (d+1) a g c D σ η depth step m)ᶜ ≤ ENNReal.ofReal δ := by
  let e := δ/((K:ℝ)*L+1)
  have hden : 0<(K:ℝ)*L+1 := by positivity
  have e0 : 0<e := div_pos hδ hden
  let S (η : ℕ → ℝ) (m : ℕ) (i : Fin K) (j : Fin L) :=
    {z : (Fin (d+1) → UnitAddCircle) × ℝ | ¬goodStep hp (d+1) a g c D (centralLift z.1) η (uniformCode p hp z.2)
      (depth i j m) (step i j m) (ENNReal.ofReal ((g^(step i j m):ℝ)^σ))}
  have each (i : Fin K) (j : Fin L) : ∀ᶠ m : ℕ in atTop, ∀ η, centerAndSeed (d+1) (S η m i j) ≤ ENNReal.ofReal e := by
    filter_upwards [(long i j).eventually (goodPrefix_loss hp a ha hg h1 info hσ hs c D e0)] with m h
    exact fun η ↦ h (depth i j m) η
  filter_upwards [eventually_all.mpr fun i ↦ eventually_all.mpr (each i)] with m hm
  intro η
  have cov : (gridGood hp (d+1) a g c D σ η depth step m)ᶜ ⊆ ⋃ i, ⋃ j, S η m i j := by
    intro z hz
    simp only [gridGood,Set.mem_compl_iff,Set.mem_ofPred_eq,not_forall] at hz
    obtain ⟨i,j,h⟩ := hz
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,h⟩⟩
  apply (measure_mono cov).trans ((measure_iUnion_fintype_le _ _).trans _)
  apply (Finset.sum_le_sum fun i _ ↦ (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun j _ ↦ hm i j η)).trans
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [show (K:ℝ≥0∞) = ENNReal.ofReal (K:ℝ) by simp,show (L:ℝ≥0∞) = ENNReal.ofReal (L:ℝ) by simp,
    ←ENNReal.ofReal_mul (Nat.cast_nonneg L),←ENNReal.ofReal_mul (Nat.cast_nonneg K)]
  apply ENNReal.ofReal_le_ofReal
  have eq := div_mul_cancel₀ δ hden.ne'
  change e*((K:ℝ)*L+1)=δ at eq
  nlinarith only [eq,e0]

local instance (b : ℝ) : MeasurableSpace (phaseGroup b) := borel _
local instance (b : ℝ) : BorelSpace (phaseGroup b) := ⟨rfl⟩

theorem bounded_haar_shift {b : ℝ} (hb : b ≠ 0) (E : PrimitiveEquation b) {U : Set PhaseTorus} (mU : MeasurableSet U)
    {δ : ℝ≥0∞} (small : ∀ z : PhaseTorus, centerAndSeed (E.d+1)
        {v | z+(auxiliary hb E v.1 v.2).val ∈ U} ≤ δ) (ω : PhaseTorus) :
    phaseHaar b {z : phaseGroup b | ω+z.val ∈ U} ≤ δ := by
  let S := {z : phaseGroup b | ω+z.val ∈ U}
  have mS : MeasurableSet S := ((continuous_const.add continuous_subtype_val).measurable) mU
  have h := auxiliary_haar hb E
  change phaseHaar b S ≤ δ
  rw [← h.map_eq,Measure.map_apply h.measurable mS,Measure.prod_apply (h.measurable mS)]
  apply le_trans _ (show (∫⁻ _ : phaseGroup b, δ ∂phaseHaar b) = δ by rw [lintegral_const,phaseHaar_univ,mul_one]).le
  apply lintegral_mono;intro z
  change centerAndSeed _ {v | ω+(z.val+(auxiliary hb E v.1 v.2).val) ∈ U} ≤ δ
  simpa only [add_assoc] using small (ω+z.val)

end Weierstrass.Branch
