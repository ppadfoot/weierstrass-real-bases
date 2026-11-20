module

public import Weierstrass.DescentWords

/-! The physical good/bad decomposition preserves all mass at every finite
depth, with inherited phase and variable arity. -/
@[expose] public noncomputable section
open Set MeasureTheory Weierstrass.CriticalRay Weierstrass.StripProof
open scoped ENNReal BigOperators
namespace Weierstrass.Descent

theorem measurable_wordLaw {b g : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1) (hbg : 1 < b*g)
    (ρ θ : ℝ) (n : ℕ) (e : ℤ → ℝ) (w : List Bool) (T : ℝ) {p : RayParameters}
    (hc : ∀ j, |p.1 j| ≤ 1) (hd : ∀ j, |p.2 j| ≤ 1) : Measurable (wordLaw b g ρ θ n e w T p) := by
  induction w generalizing T p with
  | nil => exact fullLaw_measurable _ _ _ _
  | cons a as ih =>
    let N := arity b T n
    let T' := childLength b T n N
    let P := shiftedParameters p n
    have hc' (j : ℤ) : |P.1 j| ≤ 1 := hc (j+n)
    have hd' (j : ℤ) : |P.2 j| ≤ 1 := hd (j+n)
    have mchild (i : Fin N) : Measurable (fun z : PhaseTorus ↦ physicalEnvironment b p.2 z n (anchor T i)) :=
      Measurable.of_uncurry_right (f:=fun z x ↦ physicalEnvironment b p.2 z n x) (measurable_physicalEnvironment _ _ _)
    have mo (i : Fin N) : Measurable (fun z : PhaseTorus ↦ circleRay b g p.1 p.2 z (anchor T i)) :=
      Measurable.of_uncurry_right (f:=circleRay b g p.1 p.2) (measurable_circleRay ..)
    apply Finset.measurable_fun_sum
    intro i _
    let ν (z : PhaseTorus) := if badCell b g ρ T θ p e z n i = a then
      wordLaw b g ρ θ n e as T' P (physicalEnvironment b p.2 z n (anchor T i)) else 0
    have mν : Measurable ν := ((ih T' hc' hd').comp (mchild i)).ite (badCell_measurable ..) measurable_const
    have one (z : PhaseTorus) : ν z univ ≤ 1 := by
      unfold ν;split
      · exact (wordLaw_le hb hg hg1 hbg ρ θ n e as T' hc' hd' _ univ).trans_eq (measure_univ)
      · simp
    have M := Predecessor.measurable_map_affine ν mν one (mo i) (g^n)
    apply Measure.measurable_of_measurable_coe
    intro S mS
    simp only [Measure.smul_apply,smul_eq_mul]
    exact measurable_const.mul ((Measure.measurable_coe mS).comp M)

/-- Moving the sum over possible first statuses past a test gives the
unmarked normalized child mixture, for any fixed suffix laws. -/
theorem split_first {N : ℕ} (s : ℝ≥0∞) (a : Fin N → Bool) (μ : Fin N → Measure ℝ)
    (F : Fin N → ℝ → ℝ) :
    (∑ c : Bool, ∑ i : Fin N, s • ((if a i = c then μ i else 0) : Measure ℝ).map (F i)) =
      ∑ i, s • (μ i).map (F i) := by
  rw [Finset.sum_comm];apply Finset.sum_congr rfl
  intro i _;cases a i <;> simp

theorem split_suffix {N : ℕ} {ι : Type*} [Fintype ι] (s : ℝ≥0∞) (a : Fin N → Bool) (c : Bool)
    (μ : ι → Fin N → Measure ℝ) (F : Fin N → ℝ → ℝ) (mF : ∀ i, Measurable (F i)) :
    (∑ v : ι, ∑ i : Fin N, s • ((if a i=c then μ v i else 0):Measure ℝ).map (F i)) =
      ∑ i, s • ((if a i=c then ∑ v, μ v i else 0):Measure ℝ).map (F i) := by
  rw [Finset.sum_comm];apply Finset.sum_congr rfl; intro i _
  by_cases h : a i = c
  · simp only [h,if_true,←Finset.smul_sum]; congr 1
    rw [←Measure.sum_fintype,←Measure.sum_fintype,Measure.map_sum (mF i).aemeasurable]
  · simp [h]

theorem word_sum_succ {α : Type*} [AddCommMonoid α] (k : ℕ) (F : List Bool → α) :
    (∑ v : Fin (k+1) → Bool, F (List.ofFn v)) = ∑ c, ∑ w : Fin k → Bool, F (c::List.ofFn w) := by
  let E := Fin.consEquiv (fun _ : Fin (k+1) ↦ Bool)
  rw [← E.sum_comp (fun v ↦ F (List.ofFn v)),Fintype.sum_prod_type]
  change (∑ c, ∑ w : Fin k → Bool, F (List.ofFn (Fin.cons c w))) = _
  simp only [List.ofFn_cons]

/-- The sum of all actual status laws is the full probability measure.
The identity is pointwise in the entire phase, before averaging it. -/
theorem sum_wordLaw {b g : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1) (hbg : 1 < b*g)
    (ρ θ : ℝ) (n : ℕ) (e : ℤ → ℝ) (k : ℕ) (T : ℝ) {p : RayParameters} (hc : ∀ j, |p.1 j| ≤ 1)
    (hd : ∀ j, |p.2 j| ≤ 1) (z : PhaseTorus) :
    (∑ v : Fin k → Bool, wordLaw b g ρ θ n e (List.ofFn v) T p z) = fullLaw b g T p z := by
  induction k generalizing T p z with
  | zero => simp [wordLaw]
  | succ k ih =>
    let N := arity b T n
    let off (i : Fin N) := physicalEnvironment b p.2 z n (anchor T i)
    let P := shiftedParameters p n
    have hp' (j : ℤ) : |P.1 j| ≤ 1 := hc (j+n)
    have hd' (j : ℤ) : |P.2 j| ≤ 1 := hd (j+n)
    rw [word_sum_succ k (fun w ↦ wordLaw b g ρ θ n e w T p z)]
    simp only [wordLaw]
    have mf (i : Fin N) : Measurable (pushChild b g T p z i n) := measurable_const.add (measurable_const.mul measurable_id)
    have one (c : Bool) := split_suffix (ENNReal.ofReal (N:ℝ)⁻¹) (badCell b g ρ T θ p e z n) c
      (fun (v : Fin k → Bool) (i : Fin N) ↦ wordLaw b g ρ θ n e (List.ofFn v) (childLength b T n N) P (off i)) _ mf
    let s₀ := ENNReal.ofReal (N:ℝ)⁻¹
    let a := badCell b g ρ T θ p e z n (N:=N)
    let f (i : Fin N) := pushChild b g T p z i n
    let ν (v : Fin k → Bool) (i : Fin N) := wordLaw b g ρ θ n e (List.ofFn v) (childLength b T n N) P (off i)
    change (∑ c : Bool, ∑ v : Fin k → Bool, ∑ i, s₀ • ((if a i=c then ν v i else 0) : Measure ℝ).map (f i)) = _
    calc
      _ = ∑ c : Bool, ∑ i, s₀ • ((if a i=c then ∑ v, ν v i else 0):Measure ℝ).map (f i) :=
        Finset.sum_congr rfl (fun c _ ↦ one c)
      _ = ∑ i, s₀ • (∑ v, ν v i).map (f i) := split_first _ _ _ _
      _ = fullLaw b g T p z := ?_
    have hsum (i : Fin N) : (∑ v, ν v i) = fullLaw b g (childLength b T n N) P (off i) := ih _ hp' hd' _
    simp_rw [hsum]
    rw [←sum_cellLaw (N:=N) (arity_pos b T n) b g T p z]
    apply Finset.sum_congr rfl; intro i _;exact (fullLaw_child hb hg hg1 hbg hc hd z (arity_pos b T n) i n).symm

end Weierstrass.Descent
