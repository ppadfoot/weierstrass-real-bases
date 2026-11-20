module

public import Weierstrass.BranchRandomization
public import Weierstrass.BranchChain
public import Weierstrass.FirstMoment

/-! Radius-band estimates for true bilateral increments restricted to a good path. -/
@[expose] public noncomputable section
open Set MeasureTheory Weierstrass.Predecessor
open scoped ENNReal BigOperators Topology
namespace Weierstrass.Branch

/-- Fubini, with a separate conditional probability on every displacement band. -/
theorem integral_bands {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {K : ℕ} (S : Set (X × ℝ)) (mS : MeasurableSet S) (C : Set ℝ)
    (B : Fin K → Set ℝ) (mB : ∀ i, MeasurableSet (B i)) (q : Fin K → ℝ≥0∞)
    (cover : ∀ x ∈ S, x.2 ∈ C ∨ ∃ i, x.2 ∈ B i)
    (bound : ∀ i, ∀ u ∈ B i, μ ((fun x ↦ (x,u)) ⁻¹' S) ≤ q i) :
    (μ.prod volume) S ≤ volume C + ∑ i, volume (B i)*q i := by
  let R (i : Fin K) := S ∩ Prod.snd ⁻¹' B i
  let P : Set (X × ℝ) := Prod.snd ⁻¹' C
  have cp : S ⊆ P ∪ ⋃ i, R i := by
    intro x hx
    rcases cover x hx with h|⟨i,hi⟩
    · exact Or.inl h
    · exact Or.inr (mem_iUnion.mpr ⟨i,hx,hi⟩)
  have center : (μ.prod volume) P=volume C := by
    change (μ.prod volume) (Prod.snd ⁻¹' C)=_
    rw [show (Prod.snd ⁻¹' C : Set (X × ℝ))=univ ×ˢ C by ext;simp,Measure.prod_prod,measure_univ,one_mul]
  have each (i : Fin K) : (μ.prod volume) (R i) ≤ volume (B i)*q i := by
    rw [Measure.prod_apply_symm (mS.inter (measurable_snd (mB i)))]
    have side (u : ℝ) : μ ((fun x ↦ (x,u)) ⁻¹' R i) ≤ (B i).indicator (fun _ ↦ q i) u := by
      by_cases mem : u∈B i
      · rw [indicator_of_mem mem];exact (measure_mono (Set.preimage_mono Set.inter_subset_left)).trans (bound i u mem)
      · rw [indicator_of_notMem mem,show (fun x : X ↦ (x,u)) ⁻¹' R i = ∅ from Set.eq_empty_iff_forall_notMem.mpr (fun _ hx ↦ mem hx.2),measure_empty]
    exact (lintegral_mono side).trans_eq (by rw [lintegral_indicator (mB i),lintegral_const,Measure.restrict_apply_univ,mul_comm])
  calc
    (μ.prod volume) S ≤ _ := measure_mono cp
    _ ≤ _ := measure_union_le P (⋃ i, R i)
    _ ≤ volume C + ∑ i, volume (B i)*q i := by
      rw [center];gcongr
      exact (measure_iUnion_le _).trans (by rw [tsum_fintype];exact Finset.sum_le_sum (fun i _ ↦ each i))

theorem retained_window_cap {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) {g c : ℝ} (hg : 0 < g) (hg1 : g < 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (w η : ℕ → ℝ) (u U y : ℝ) {B : ℝ} (bpos : 0 ≤ B) (n k : ℕ → ℕ) (q : ℕ → ℝ≥0∞) (L F : ℕ)
    (order : ∀ i j, i<j → j<L → n i+k i ≤ n j) (final : ∀ i<L,n i+k i ≤ F)
    (small : ∀ i<L, |c^(n i)*u| ≤ U*g^(k i)) {D : ℝ} (hD : 2*(slopeError g*U+((1-g)⁻¹+B))+(1-g)⁻¹ ≤ D) :
    unitLaw {x | let I := uniformCode p hp x
      (∀ i<L,goodStep hp d a g c D w η I (n i) (k i) (q i)) ∧
        |fullSecant d (fun j ↦ (a j:ℝ)) p g c w η I u-y| ≤ B*g^F} ≤ ∏ i ∈ Finset.range L,q i := by
  apply le_trans _ (chain_cap hp d a hg hg1 hc hc1 w η u U ((1-g)⁻¹+B) y n k q L order small hD)
  apply measure_mono;intro x h
  apply mem_prefixWindows.mpr;intro i hi
  refine ⟨h.1 i hi,?_⟩
  let I := uniformCode p hp x
  let P := partialSecant d (fun j ↦ (a j:ℝ)) p g c w η I u (n i+k i)
  let V := fullSecant d (fun j ↦ (a j:ℝ)) p g c w η I u
  have rem : |V-P| ≤ (1-g)⁻¹*g^(n i+k i) := secant_remainder _ _ _ _ hg.le hg1 _ _ _ _ _
  have err : |V-y| ≤ B*g^F := h.2
  have ord : g^F ≤ g^(n i+k i) := pow_le_pow_of_le_one hg.le hg1.le (final i hi)
  change |P-y| ≤ ((1-g)⁻¹+B)*g^(n i+k i)
  rw [abs_sub_comm] at rem
  linarith only [abs_sub_le P V y,rem,err,mul_le_mul_of_nonneg_left ord bpos]

end Weierstrass.Branch
