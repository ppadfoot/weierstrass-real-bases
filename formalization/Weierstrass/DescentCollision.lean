module

public import Weierstrass.DescentBranchCost
public import Weierstrass.DescentInheritance

/-! The actual one-step collision recursion (D) for an arbitrary prescribed
status word of physical interval children, uniformly in phase cosets. -/
@[expose] public noncomputable section
open Set MeasureTheory Weierstrass.CriticalRay Weierstrass.StripProof
open scoped ENNReal BigOperators
namespace Weierstrass.Descent
local instance stepGroupMeasure (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance stepGroupBorel (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

def wordEnergy (B : ℂ) (g ρ θ : ℝ) (n : ℕ) (e : ℤ → ℝ) (w : List Bool) (T : ℝ) (p : RayParameters)
    (ω : PhaseTorus) (r : ℝ) := ∫⁻ z : complexPhaseGroup B, ENNReal.ofReal (Predecessor.collision
      (wordLaw ‖B‖ g ρ θ n e w T p (ω+z.val)) (wordLaw ‖B‖ g ρ θ n e w T p (ω+z.val)) r) ∂complexPhaseHaar B

theorem physical_word_step {B : ℂ} (hb : 0 < ‖B‖) {g ρ : ℝ} (hg : 0 < g) (hg1 : g < 1)
    (hr : 0 < ρ) (hr1 : ρ < 1) (hh : 1 < ‖B‖*(g*ρ)) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T θ : ℝ}, 1 ≤ T → T ≤ 3 → 0 ≤ θ → childLength ‖B‖ T n (arity ‖B‖ T n) ≤ 2 →
      ∀ {p : RayParameters} {e : ℤ → ℝ}, (∀ j, |p.1 j| ≤ 1) → (∀ j, |p.2 j| ≤ 1) →
      (∀ j, |e j| ≤ 1) → (∀ x, transverseOrbit ρ e x ∈ complexPhaseGroup B) →
      ∀ (ω : PhaseTorus) (a : Bool) (w : List Bool) {r : ℝ}, 0 < r → ∀ {E : ℝ≥0∞},
      (∀ ξ : PhaseTorus, wordEnergy B g ρ θ n e w (childLength ‖B‖ T n (arity ‖B‖ T n))
        (shiftedParameters p n) ξ (r/g^n) ≤ E) →
      wordEnergy B g ρ θ n e (a::w) T p ω r ≤ ENNReal.ofReal (C*r)+ENNReal.ofReal (3*(if a then 1 else θ))*E := by
  obtain ⟨C,hC,farCost⟩ := haar_off_cost hb hg hg1 hr hr1 hh n
  refine ⟨C,hC,?_⟩;intro T θ T1 T3 hθ len p e hc hd he hm ω a w r rpos E bound
  let b := ‖B‖
  let N := arity b T n
  have npos := arity_pos b T n
  have np : 0 < (N:ℝ) := by exact_mod_cast npos
  let s := (N:ℝ)⁻¹
  have sp : 0 ≤ s := (inv_pos.mpr np).le
  let U : ℝ := if a then 1 else θ
  have u0 : 0 ≤ U := by cases a <;> simp [U,hθ]
  have hbg : 1 < b*g := hh.trans (by rw [←mul_assoc];exact mul_lt_of_lt_one_right (mul_pos hb hg) hr1)
  let P := shiftedParameters p n
  have hc' (j : ℤ) : |P.1 j| ≤ 1 := hc (j+n)
  have hd' (j : ℤ) : |P.2 j| ≤ 1 := hd (j+n)
  let T' := childLength b T n N
  let ξ := wordLaw b g ρ θ n e w T' P
  have hdom (z : PhaseTorus) := wordLaw_le hb hg hg1 hbg ρ θ n e w T' hc' hd' z
  have mξ : Measurable ξ := measurable_wordLaw hb hg hg1 hbg ρ θ n e w T' hc' hd'
  have one z : ξ z univ ≤ 1 := (hdom z univ).trans_eq measure_univ
  let Q (z : PhaseTorus) := ENNReal.ofReal (Predecessor.collision (ξ z) (ξ z) (r/g^n))
  have mq : Measurable Q := Predecessor.measurable_diagonal_collision ξ mξ one _
  let env (z : PhaseTorus) (i : Fin N) := physicalEnvironment b p.2 z n (anchor T i)
  let G (z : PhaseTorus) := derivRay b g ρ p.1 p.2 e z
  let W := widthMark b g ρ n
  let closeCost (z : complexPhaseGroup B) := ∑ i : Fin N, Q (env (ω+z.val) i)
  let off (z : complexPhaseGroup B) := ∑ i : Fin N, ∑ j : Fin N,
    if W < |G (ω+z.val) (anchor T i)-G (ω+z.val) (anchor T j)| then
      ENNReal.ofReal (Predecessor.collision (cellLaw b g T p (ω+z.val) i) (cellLaw b g T p (ω+z.val) j) r) else 0
  let gain := ENNReal.ofReal (3*((N:ℝ)*U)*s^2)
  have mqenv (i : Fin N) : Measurable (fun z : complexPhaseGroup B ↦ Q (env (ω+z.val) i)) :=
    mq.comp ((Measurable.of_uncurry_right (f:=fun z x ↦ physicalEnvironment b p.2 z n x)
      (measurable_physicalEnvironment _ _ _) (y:=anchor T i)).comp (measurable_const.add continuous_subtype_val.measurable))
  have mclose : Measurable closeCost := Finset.measurable_fun_sum _ (fun i _ ↦ mqenv i)
  have integralClose : ∫⁻ z : complexPhaseGroup B, closeCost z ∂complexPhaseHaar B ≤ (N:ℝ≥0∞)*E := by
    change (∫⁻ z, ∑ i : Fin N, Q (env (ω+z.val) i) ∂complexPhaseHaar B) ≤ _
    rw [lintegral_finsetSum _ (fun i _ ↦ mqenv i)]
    apply (Finset.sum_le_sum (g:=fun _ ↦ E) _).trans_eq (by simp)
    intro i _
    rw [show (∫⁻ z : complexPhaseGroup B, Q (env (ω+z.val) i) ∂complexPhaseHaar B) = _ from
      child_haar_mean (norm_pos_iff.mp hb) p.2 ω n (anchor T i) Q mq]
    exact bound _
  have coeff : 0 ≤ 3*((N:ℝ)*U)*s^2 := by positivity
  have point (zz : complexPhaseGroup B) : let μ := wordLaw b g ρ θ n e (a::w) T p (ω+zz.val)
      ENNReal.ofReal (Predecessor.collision μ μ r) ≤ off zz+gain*closeCost zz := by
    let z := ω+zz.val
    let μ (i : Fin N) := ξ (env z i)
    let (i : Fin N) : IsFiniteMeasure (μ i) := ⟨(one (env z i)).trans_lt ENNReal.one_lt_top⟩
    let f (i : Fin N) := cellLaw b g T p z i
    let forb (i j : Fin N) := W < |G z (anchor T i)-G z (anchor T j)|
    let accept (i : Fin N) := decide (badCell b g ρ T θ p e z n i = a)
    have full (i : Fin N) : ENNReal.ofReal s • (μ i).map (pushChild b g T p z i n) ≤ f i := by
      rw [show f i = _ from fullLaw_child hb hg hg1 hbg hc hd z npos i n]
      apply _root_.smul_le_smul_left
      exact Measure.map_mono (hdom _) (measurable_const.add (measurable_const.mul measurable_id))
    have rows (i : Fin N) : (∑ j, if accept i = true ∧ accept j=true ∧ ¬forb i j then (1:ℝ) else 0) ≤ N*U := by
      simpa only [accept,decide_eq_true_eq] using status_degree npos b g ρ T θ hθ p e z n a i
    have H := Predecessor.marked_block_collision μ f (fun i ↦ circleRay b g p.1 p.2 z (anchor T i)) rpos (pow_pos hg n) sp accept forb
      (fun i j ↦ by change W < |_ - _| ↔ W < |_ - _|;rw [abs_sub_comm]) (mul_nonneg np.le u0) rows full
    simp only [accept,decide_eq_true_eq] at H
    apply (ENNReal.ofReal_le_ofReal H).trans_eq
    let Cij (i j : Fin N) := if forb i j then Predecessor.collision (f i) (f j) r else 0
    have nn (i j : Fin N) : 0 ≤ Cij i j := by dsimp [Cij];split <;> first | exact measureReal_nonneg | rfl
    let D (i : Fin N) := Predecessor.collision (μ i) (μ i) (r/g^n)
    have dnn i : 0 ≤ D i := measureReal_nonneg
    change ENNReal.ofReal ((∑ i, ∑ j, Cij i j)+(3*((N:ℝ)*U)*s^2)*(∑ i, D i)) = _
    rw [ENNReal.ofReal_add (Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ nn i j)))
      (mul_nonneg coeff (Finset.sum_nonneg (fun i _ ↦ dnn i))),ENNReal.ofReal_mul coeff,
      ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ nn i j)),ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ dnn i)]
    congr 1
    apply Finset.sum_congr rfl; intro i _;rw [ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ nn i j)]
    apply Finset.sum_congr rfl;intro j _
    change ENNReal.ofReal (if forb i j then _ else 0) = (if forb i j then _ else 0)
    by_cases h : forb i j <;> simp only [h,if_true,if_false,ENNReal.ofReal_zero]
    rfl
  apply (lintegral_mono point).trans
  have mc : Measurable (fun z ↦ gain*closeCost z) := measurable_const.mul mclose
  rw [lintegral_add_right off mc,lintegral_const_mul gain mclose]
  apply add_le_add (farCost T T1 T3 N npos len p e hc hd he hm ω r rpos.le)
  apply (mul_le_mul_right integralClose gain).trans_eq
  rw [←mul_assoc];congr 1
  change ENNReal.ofReal (3*((N:ℝ)*U)*s^2)*N = ENNReal.ofReal (3*U)
  rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul coeff];congr 1;dsimp [s];field_simp

end Weierstrass.Descent
