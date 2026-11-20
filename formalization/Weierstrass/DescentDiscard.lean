module

public import Weierstrass.DescentCounts
public import Weierstrass.SlopeWordRates

/-! Discarding paths with too many bad physical labels costs at most the
single-block error divided by the allowed fraction. -/
@[expose] public noncomputable section
open Set MeasureTheory Weierstrass.CriticalRay Weierstrass.StripProof
open scoped BigOperators ENNReal
namespace Weierstrass.Descent
local instance discardGroupMeasure (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance discardGroupBorel (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

theorem mesh_inherits {b T : ℝ} {n : ℕ} (hn : 2 ≤ b^n) (hT : 1 ≤ T) :
    1 ≤ childLength b T n (arity b T n) ∧ childLength b T n (arity b T n) ≤ 2 := by
  have h : 2 ≤ T*b^n := hn.trans (le_mul_of_one_le_left (by linarith : 0 ≤ b^n) hT)
  rw [arity_floor h];exact (mesh_length h).2

theorem weight_sum {N : ℕ} (hn : 0 < N) (K : ℝ≥0∞) :
    (∑ _ : Fin N, ENNReal.ofReal (N:ℝ)⁻¹*K)=K := by
  have hp : 0 < (N:ℝ) := by exact_mod_cast hn
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←mul_assoc,
    ←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul hp.le,mul_inv_cancel₀ hp.ne',ENNReal.ofReal_one,one_mul]

/-- Finite-horizon expectation; the type of the physical states changes its
arity at every node and each child's Haar law has its own deterministic coset. -/
theorem countMass_haar_bound {B : ℂ} (hb : 0 < ‖B‖) {g : ℝ} (hg : 0 < g) (hg1 : g < 1) (hbg : 1 < ‖B‖*g)
    (ρ θ : ℝ) (n : ℕ) (hn : 2 ≤ ‖B‖^n) (e : ℤ → ℝ) {P : Set RayParameters}
    (weights : ∀ p ∈ P, (∀ j, |p.1 j| ≤ 1) ∧ (∀ j, |p.2 j| ≤ 1) ∧ shiftedParameters p n ∈ P)
    {ε : ℝ≥0∞} (bad : ∀ p ∈ P, ∀ {T : ℝ}, 1 ≤ T → T ≤ 3 → ∀ ω : PhaseTorus,
      (∫⁻ z : complexPhaseGroup B, badShare ‖B‖ g ρ T θ n (arity ‖B‖ T n) p e (ω+z.val) ∂complexPhaseHaar B) ≤ ε)
    (k : ℕ) {p : RayParameters} (hp : p ∈ P) {T : ℝ} (T1 : 1 ≤ T) (T3 : T ≤ 3) (ω : PhaseTorus) :
    (∫⁻ z : complexPhaseGroup B, countMass ‖B‖ g ρ θ n e k T p (ω+z.val) ∂complexPhaseHaar B) ≤ k*ε := by
  induction k generalizing p T ω with
  | zero => simp [countMass,badCount]
  | succ k ih =>
    obtain ⟨hc,hd,mem⟩ := weights p hp
    let N := arity ‖B‖ T n
    let s := ENNReal.ofReal (N:ℝ)⁻¹
    let T' := childLength ‖B‖ T n N
    let F := countMass ‖B‖ g ρ θ n e k T' (shiftedParameters p n)
    let off (i : Fin N) (z : complexPhaseGroup B) := physicalEnvironment ‖B‖ p.2 (ω+z.val) n (anchor T i)
    have mF : Measurable F := countMass_measurable hb hg hg1 hbg ρ θ n e k T' (weights _ mem).1 (weights _ mem).2.1
    have mo (i : Fin N) : Measurable (off i) := (Measurable.of_uncurry_right (f:=fun z x ↦ physicalEnvironment ‖B‖ p.2 z n x)
      (measurable_physicalEnvironment _ _ _) (y:=anchor T i)).comp (measurable_const.add continuous_subtype_val.measurable)
    have mZ (i : Fin N) : Measurable (fun z ↦ s*F (off i z)) := measurable_const.mul (mF.comp (mo i))
    have update (z : complexPhaseGroup B) : countMass ‖B‖ g ρ θ n e (k+1) T p (ω+z.val) =
        badShare ‖B‖ g ρ T θ n N p e (ω+z.val)+∑ i : Fin N, s*F (off i z) := count_step hb hg hg1 hbg ρ θ n e k T hc hd _
    simp_rw [update];rw [lintegral_add_right _ (show Measurable (fun z ↦ ∑ i : Fin N, s*F (off i z)) from
      Finset.measurable_fun_sum _ (fun i _ ↦ mZ i)),lintegral_finsetSum _ (fun i _ ↦ mZ i)]
    have tx := mesh_inherits hn T1
    have le (i : Fin N) : (∫⁻ z : complexPhaseGroup B, s*F (off i z) ∂complexPhaseHaar B) ≤ s*(k*ε) := by
      rw [lintegral_const_mul s (show Measurable (fun z ↦ F (off i z)) from mF.comp (mo i)),show (∫⁻ z : complexPhaseGroup B, F (off i z) ∂complexPhaseHaar B)=_ from
        child_haar_mean (norm_pos_iff.mp hb) p.2 ω n (anchor T i) F mF]
      exact mul_le_mul_right (ih mem tx.1 (tx.2.trans (by norm_num)) _) _
    exact (add_le_add (bad p hp T1 T3 ω) ((Finset.sum_le_sum (fun i _ ↦ le i)).trans_eq (weight_sum (arity_pos ..) _))).trans_eq
      (by rw [Nat.cast_succ,add_mul,one_mul,add_comm])

def retainedLaw (b g ρ θ : ℝ) (n : ℕ) (e : ℤ → ℝ) (k m : ℕ) (T : ℝ) (p : RayParameters) (z : PhaseTorus) : Measure ℝ :=
  ∑ v ∈ Predecessor.sparseStatusWords k m, wordLaw b g ρ θ n e (List.ofFn v) T p z

theorem retained_le {b g : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1) (hbg : 1 < b*g)
    (ρ θ : ℝ) (n : ℕ) (e : ℤ → ℝ) (k m : ℕ) (T : ℝ) {p : RayParameters}
    (hc : ∀ j, |p.1 j| ≤ 1) (hd : ∀ j, |p.2 j| ≤ 1) (z : PhaseTorus) :
    retainedLaw b g ρ θ n e k m T p z ≤ fullLaw b g T p z := by
  rw [←sum_wordLaw hb hg hg1 hbg ρ θ n e k T hc hd z];unfold retainedLaw
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ bot_le)

theorem retained_measurable {b g : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1) (hbg : 1 < b*g)
    (ρ θ : ℝ) (n : ℕ) (e : ℤ → ℝ) (k m : ℕ) (T : ℝ) {p : RayParameters}
    (hc : ∀ j, |p.1 j| ≤ 1) (hd : ∀ j, |p.2 j| ≤ 1) : Measurable (retainedLaw b g ρ θ n e k m T p) :=
  Finset.measurable_fun_sum _ (fun _ _ ↦ measurable_wordLaw hb hg hg1 hbg ρ θ n e _ T hc hd)

theorem discarded_le_count {b g : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1) (hbg : 1 < b*g)
    (ρ θ : ℝ) (n : ℕ) (e : ℤ → ℝ) (k m : ℕ) (T : ℝ) {p : RayParameters}
    (hc : ∀ j, |p.1 j| ≤ 1) (hd : ∀ j, |p.2 j| ≤ 1) (z : PhaseTorus) :
    1-retainedLaw b g ρ θ n e k m T p z univ ≤ countMass b g ρ θ n e k T p z/(m+1:ℕ) := by
  let A := Predecessor.sparseStatusWords k m
  let μ (v : Fin k → Bool) := wordLaw b g ρ θ n e (List.ofFn v) T p z univ
  have total : ∑ v, μ v=1 := by
    have H := congrArg (fun m : Measure ℝ ↦ m univ) (sum_wordLaw hb hg hg1 hbg ρ θ n e k T hc hd z)
    simpa only [Measure.finsetSum_apply,measure_univ] using H
  have rem : 1 - retainedLaw b g ρ θ n e k m T p z univ ≤ ∑ v ∈ Aᶜ, μ v := by
    apply tsub_le_iff_right.mpr;rw [retainedLaw,Measure.finsetSum_apply,←total]
    exact le_of_eq ((Finset.sum_add_sum_compl A μ).symm.trans (add_comm _ _))
  apply rem.trans;apply (ENNReal.le_div_iff_mul_le (.inl (by positivity)) (.inl (by finiteness))).mpr
  rw [Finset.sum_mul];unfold countMass
  refine le_trans (Finset.sum_le_sum fun v hv ↦ ?_) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ bot_le))
  rw [badCount_fin,mul_comm]
  have mlt : m < (Finset.univ.filter (fun i ↦ v i=true)).card := by simpa [A,Predecessor.sparseStatusWords] using hv
  exact mul_le_mul_left (by exact_mod_cast mlt : ((m+1:ℕ):ℝ≥0∞) ≤ (Finset.univ.filter (fun i ↦ v i=true)).card) _

end Weierstrass.Descent
