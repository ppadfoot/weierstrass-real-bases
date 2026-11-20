module

public import Weierstrass.BranchSecants

/-! Conditional bounds for nested prefix windows in Appendix B. Both
quantities used to mark a child are determined at that child's depth. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory Weierstrass.Predecessor
open scoped ENNReal BigOperators
namespace Weierstrass.Branch

def ballMass (ν : Measure ℝ) (y r : ℝ) := ν (Icc (y-r) (y+r))

def goodPrefix {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (g c D : ℝ) (w η : ℕ → ℝ) (I : ℕ → Fin p) (k : ℕ) (q : ℝ≥0∞) :=
  ballMass (baseSlopeLaw hp d a w η g) (partialSecant d (fun j ↦ (a j:ℝ)) p g c w η I 0 k) (D*g^k) ≤ q

theorem partialSecant_prefix {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ g c : ℝ) (w η : ℕ → ℝ) (u : ℝ) (k : ℕ)
    {I J : ℕ → Fin p} (h : ∀ j<k, I j=J j) : partialSecant d a a₀ g c w η I u k=partialSecant d a a₀ g c w η J u k := by
  apply Finset.sum_congr rfl;intro j hj;unfold secantTerm
  rw [pathState_prefix d a a₀ w (I:=I) (J:=J) (j+1) (fun i hi ↦ h i (by have t := Finset.mem_range.mp hj;omega))]

theorem measurable_partialSecant {X : Type*} [MeasurableSpace X] {p : ℕ} (d : ℕ) (a : ℕ → ℝ) (a₀ g c : ℝ)
    (W η : X → ℕ → ℝ) (I : X → ℕ → Fin p) (u : X → ℝ) (k : ℕ) (mW : ∀ j, Measurable fun x ↦ W x j)
    (mη : ∀ j, Measurable fun x ↦ η x j) (mI : ∀ j, Measurable fun x ↦ I x j) (mu : Measurable u) :
    Measurable (fun x ↦ partialSecant d a a₀ g c (W x) (η x) (I x) (u x) k) := by
  unfold partialSecant
  apply Finset.measurable_fun_sum;intro j _
  unfold secantTerm
  apply Measurable.const_mul
  change Measurable ((Function.uncurry sineMean) ∘ (fun x : X ↦ (2*Real.pi*pathState d a a₀ (W x) (I x) (j+1) 0+η x j,2*Real.pi*c^(j+1)*u x)))
  apply measurable_sineMean.comp
  exact ((measurable_const.mul (measurable_pathState d a a₀ W I mW mI (j+1) 0)).add (mη j)).prodMk (measurable_const.mul mu)

def slopeError (g : ℝ) := (1-g)⁻¹*(2*Real.pi)

theorem slopeError_nonneg {g : ℝ} (h : g < 1) : 0 ≤ slopeError g := by unfold slopeError;positivity

/-- At a restarted state, all admissible digit prefixes satisfying the
secant window, collectively, have conditional mass at most q. The center
is chosen from the same good children, so q is paid only once per stage. -/
theorem conditional_window {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) {g c v : ℝ}
    (hg : 0 ≤ g) (hg1 : g < 1) (hc : 0 ≤ c) (hc1 : c ≤ 1) (w η : ℕ → ℝ) (k : ℕ)
    (U : ℝ) (small : |v| ≤ U*g^k) (A y : ℝ) (q : ℝ≥0∞) {D : ℝ} (hD : 2*(slopeError g*U+A)+(1-g)⁻¹ ≤ D) :
    unitLaw {x | let I := uniformCode p hp x
      goodPrefix hp d a g c D w η I k q ∧ |partialSecant d (fun i ↦ (a i:ℝ)) p g c w η I v k-y| ≤ A*g^k} ≤ q := by
  let P (x : ℝ) := partialSecant d (fun j ↦ (a j:ℝ)) p g c w η (uniformCode p hp x) 0 k
  let F (x : ℝ) := codedSlope d (fun j ↦ (a j:ℝ)) p g w η (uniformCode p hp x)
  let S (x : ℝ) := partialSecant d (fun j ↦ (a j:ℝ)) p g c w η (uniformCode p hp x) v k
  let selected := {x : ℝ | goodPrefix hp d a g c D w η (uniformCode p hp x) k q ∧ |S x-y| ≤ A*g^k}
  change unitLaw selected ≤ q
  rcases selected.eq_empty_or_nonempty with empty|⟨x₀,xgood⟩
  · simp [empty]
  have pp := pow_nonneg hg k
  have offset (x : ℝ) : |S x-P x| ≤ (slopeError g*U)*g^k := by
    have h := secant_offset d (fun i ↦ (a i:ℝ)) (p:ℝ) hg hg1 hc hc1 w η (uniformCode p hp x) v k
    change |S x-P x| ≤ _ at h
    rw [←mul_assoc] at h
    rw [mul_assoc];exact h.trans (mul_le_mul_of_nonneg_left small (slopeError_nonneg hg1))
  have cap (x : ℝ) (h : x ∈ selected) : |P x-y| ≤ (slopeError g*U+A)*g^k := by
    have o := offset x
    rw [abs_sub_comm] at o
    have t := abs_sub_le (P x) (S x) y
    linarith only [t,h.2,o]
  have tail (x : ℝ) : |F x-P x| ≤ (1-g)⁻¹*g^k := by
    simpa only [F,P,partialSecant_zero] using truncatedSlope_tail d (fun i ↦ (a i:ℝ)) p w η (uniformCode p hp x) hg hg1 k
  have bound (x : ℝ) (h : x ∈ selected) : |F x-P x₀| ≤ D*g^k := by
    have c1 := cap x h
    have c2 := cap x₀ xgood
    rw [abs_sub_comm] at c2
    have t1 := abs_sub_le (P x) y (P x₀)
    have t2 := abs_sub_le (F x) (P x) (P x₀)
    have DH := mul_le_mul_of_nonneg_right hD pp
    linarith only [tail x,t1,t2,c1,c2,DH]
  have mF : Measurable F := measurable_coded_sample hp d a (fun _ : ℝ ↦ w) (fun _ ↦ measurable_const) id measurable_id η g
  have hsub : selected ⊆ F ⁻¹' Icc (P x₀-D*g^k) (P x₀+D*g^k) := by
    intro x hx;have z := abs_le.mp (bound x hx);exact ⟨by linarith [z.1],by linarith [z.2]⟩
  have G := xgood.1
  change (unitLaw.map F) (Icc (P x₀-D*g^k) (P x₀+D*g^k)) ≤ q at G
  rw [Measure.map_apply mF measurableSet_Icc] at G
  exact (measure_mono hsub).trans G

end Weierstrass.Branch
