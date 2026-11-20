module

public import Weierstrass.BranchMarks

/-! Product contraction across genuine nested secant windows sharing a single uniform digit path. -/
@[expose] public noncomputable section
open Set MeasureTheory Weierstrass.Predecessor
open scoped ENNReal BigOperators
namespace Weierstrass.Branch

def window {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (g c D : ℝ) (w η : ℕ → ℝ) (u A y : ℝ) (n k : ℕ) (q : ℝ≥0∞) :=
  {x : ℝ | let I := uniformCode p hp x
    goodStep hp d a g c D w η I n k q ∧ |partialSecant d (fun j ↦ (a j:ℝ)) p g c w η I u (n+k)-y| ≤ A*g^(n+k)}

theorem measurable_window {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (g c D : ℝ) (w η : ℕ → ℝ)
    (u A y : ℝ) (n k : ℕ) (q : ℝ≥0∞) : MeasurableSet (window hp d a g c D w η u A y n k q) := by
  let I := uniformCode p hp
  let W (_ : ℝ) := w
  let H (_ : ℝ) := η
  let V (_ : ℝ) := u
  have hm := measurable_goodStep hp d a g c D W H I (fun _ ↦ measurable_const)
    (fun _ ↦ measurable_const) (measurable_uniformCode p hp) n k q
  have mt := measurable_partialSecant d (fun j ↦ (a j:ℝ)) (p:ℝ) g c W H I V (n+k) (fun _ ↦ measurable_const)
    (fun _ ↦ measurable_const) (measurable_uniformCode p hp) measurable_const
  exact hm.inter (measurableSet_le (continuous_abs.measurable.comp (mt.sub_const y)) measurable_const)

theorem window_congr {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) (g c D : ℝ) (w η : ℕ → ℝ)
    (u A y : ℝ) (n k : ℕ) (q : ℝ≥0∞) {x x' : ℝ} (e : ∀ j<n+k, uniformCode p hp x j=uniformCode p hp x' j) :
    x ∈ window hp d a g c D w η u A y n k q ↔ x' ∈ window hp d a g c D w η u A y n k q := by
  change _ ∧ _ ↔ _ ∧ _
  exact and_congr (goodStep_congr hp d a g c D w η n k q e) (by rw [partialSecant_prefix d (fun j ↦ (a j:ℝ)) p g c w η u (n+k) e])

theorem window_cap {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) {g c : ℝ} (hg : 0 < g) (hg1 : g < 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (w η : ℕ → ℝ) (u U A y : ℝ) (n k : ℕ) (small : |c^n*u| ≤ U*g^k)
    (q : ℝ≥0∞) {D : ℝ} (hD : 2*(slopeError g*U+A)+(1-g)⁻¹ ≤ D) (I : ℕ → Fin p) :
    unitLaw (prefixSeed I n ⁻¹' window hp d a g c D w η u A y n k q) ≤ q := by
  let w' := pathState d (fun j ↦ (a j:ℝ)) p w I n
  let η' := fun j ↦ η (n+j)
  let P := partialSecant d (fun j ↦ (a j:ℝ)) p g c w η I u n
  let y' := (y-P)/g^n
  apply le_trans _ (conditional_window hp d a hg.le hg1 hc hc1 w' η' k U small A y' q hD)
  apply measure_mono_ae
  have hx : ∀ᵐ x ∂unitLaw, x ∈ Ico (0:ℝ) 1 := ae_restrict_mem measurableSet_Ico
  filter_upwards [hx] with x hx
  intro h
  let J := uniformCode p hp (prefixSeed I n x)
  obtain ⟨e₁,e₂⟩ := prefixSeed_codes hp I n hx
  have ew : pathState d (fun j ↦ (a j:ℝ)) p w J n=w' := pathState_prefix _ _ _ w n e₁
  have et : (fun j ↦ J (n+j))=uniformCode p hp x := funext e₂
  have eP : partialSecant d (fun j ↦ (a j:ℝ)) p g c w η J u n=P := partialSecant_prefix _ _ _ g c w η u n e₁
  change goodStep hp d a g c D w η J n k q ∧ |partialSecant d (fun j ↦ (a j:ℝ)) p g c w η J u (n+k)-y| ≤ A*g^(n+k) at h
  obtain ⟨mark,hit⟩ := h
  unfold goodStep at mark
  rw [ew,et] at mark
  refine ⟨mark,?_⟩
  rw [secant_prefix_append,eP,ew,et,pow_add] at hit
  have gp := pow_pos hg n
  let S := partialSecant d (fun j ↦ (a j:ℝ)) p g c w' η' (uniformCode p hp x) (c^n*u) k
  have ident : g^n*(S-y')=P+g^n*S-y := by dsimp [y'];field_simp;ring
  change |S-y'| ≤ A*g^k
  apply (le_of_mul_le_mul_left (a:=g^n) _ gp)
  rw [←abs_of_pos gp,←abs_mul,ident,abs_of_pos gp]
  nlinarith only [hit]

def prefixWindows (W : ℕ → Set ℝ) : ℕ → Set ℝ
  | 0 => univ
  | j+1 => prefixWindows W j ∩ W j

theorem mem_prefixWindows {W : ℕ → Set ℝ} {k : ℕ} {x : ℝ} : x∈prefixWindows W k ↔ ∀ i<k, x∈W i := by
  induction k with
  | zero => simp [prefixWindows]
  | succ k ih =>
    simp only [prefixWindows,Set.mem_inter_iff,ih]
    exact ⟨fun ⟨h,t⟩ i hi ↦ (lt_or_eq_of_le (Nat.le_of_lt_succ hi)).elim (h i) (fun e ↦ e.symm ▸ t),
      fun h ↦ ⟨fun i hi ↦ h i (Nat.lt_succ_of_lt hi),h k (Nat.lt_succ_self k)⟩⟩

theorem chain_cap {p : ℕ} (hp : 0 < p) (d : ℕ) (a : ℕ → ℤ) {g c : ℝ} (hg : 0 < g) (hg1 : g < 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (w η : ℕ → ℝ) (u U A y : ℝ) (n k : ℕ → ℕ) (q : ℕ → ℝ≥0∞) (L : ℕ)
    (order : ∀ i j, i<j → j<L → n i+k i ≤ n j) (small : ∀ i<L, |c^(n i)*u| ≤ U*g^(k i))
    {D : ℝ} (hD : 2*(slopeError g*U+A)+(1-g)⁻¹ ≤ D) :
    unitLaw (prefixWindows (fun i ↦ window hp d a g c D w η u A y (n i) (k i) (q i)) L) ≤ ∏ i ∈ Finset.range L, q i := by
  let W := fun i ↦ window hp d a g c D w η u A y (n i) (k i) (q i)
  have mW (i) : MeasurableSet (W i) := measurable_window .. 
  have mP (i) : MeasurableSet (prefixWindows W i) := by induction i with | zero => exact MeasurableSet.univ | succ i ih => exact ih.inter (mW i)
  have induct (j) (hj : j ≤ L) : unitLaw (prefixWindows W j) ≤ ∏ i ∈ Finset.range j, q i := by
    induction j with
    | zero => simp [prefixWindows]
    | succ j ih =>
      have jj : j<L := by omega
      rw [Finset.prod_range_succ]
      apply (prefix_contraction hp (n j) (prefixWindows W j) (W j) (mP j) (mW j) ?_ (window_cap hp d a hg hg1 hc hc1 w η u U A y (n j) (k j) (small j jj) (q j) hD)).trans
      · gcongr;exact ih (by omega)
      · intro x x' e
        rw [mem_prefixWindows,mem_prefixWindows]
        exact forall₂_congr (fun i hi ↦ window_congr hp d a g c D w η u A y (n i) (k i) (q i)
          (fun t ht ↦ e t (lt_of_lt_of_le ht (order i j hi jj))))
  exact induct L le_rfl

end Weierstrass.Branch
