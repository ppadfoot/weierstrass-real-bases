module

public import Weierstrass.DescentDiscard
public import Weierstrass.DescentCollision
public import Weierstrass.SlopePacking

/-! Collision at depth k for actual physical label words. All deterministic
states and all Haar translates are included in the induction. -/
@[expose] public noncomputable section
open Set MeasureTheory Filter Weierstrass.CriticalRay Weierstrass.StripProof
open scoped BigOperators ENNReal
namespace Weierstrass.Descent
local instance iterGroupMeasure (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance iterGroupBorel (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

theorem energy_iteration {B : ℂ} (hb : 0 < ‖B‖) {g ρ : ℝ} (hg : 0 < g) (hg1 : g < 1)
    (hr : 0 < ρ) (hr1 : ρ < 1) (hh : 1 < ‖B‖*(g*ρ)) (n : ℕ) (hn : 2 ≤ ‖B‖^n)
    {e : ℤ → ℝ} (he : ∀ j, |e j| ≤ 1) (hm : ∀ x, transverseOrbit ρ e x ∈ complexPhaseGroup B)
    {P : Set RayParameters} (weights : ∀ p ∈ P, (∀ j, |p.1 j| ≤ 1) ∧ (∀ j, |p.2 j| ≤ 1) ∧ shiftedParameters p n ∈ P)
    {A t : ℝ} (hA : 0 < A) (ht : t ≤ 1) : ∃ K : ℝ, 0 < K ∧ ∀ w : List Bool, ∀ {T : ℝ},
    1 ≤ T → T ≤ 3 → ∀ {p : RayParameters}, p ∈ P → ∀ ω : PhaseTorus,
      wordEnergy B g ρ ((g^n:ℝ)^t) n e w T p ω (A*(g^n)^w.length) ≤
        ENNReal.ofReal (K*(w.length+1:ℝ)*(w.map (Predecessor.wordCoefficient (g^n) t)).prod*(g^n)^w.length) := by
  obtain ⟨C,hC,step⟩ := physical_word_step hb hg hg1 hr hr1 hh n
  let K := 1+C*A
  have kp : 0 < K := lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (mul_nonneg hC hA.le))
  let q := g^n
  let coef := Predecessor.wordCoefficient q t
  have qp : 0 < q := pow_pos hg n
  have hcoef (a : Bool) : 1 ≤ coef a := Predecessor.wordCoefficient_ge qp (pow_le_one₀ hg.le hg1.le) ht a
  have prod1 (w : List Bool) : 1 ≤ (w.map coef).prod := by
    induction w with
    | nil => simp
    | cons a w ih => exact one_le_mul_of_one_le_of_one_le (hcoef a) ih
  refine ⟨K,kp,?_⟩;intro w
  induction w with
  | nil =>
    intro T _ _ p _ ω
    simp only [List.length_nil,Nat.cast_zero,zero_add,List.map_nil,List.prod_nil,pow_zero,mul_one]
    apply le_trans (b:=(1:ℝ≥0∞))
    · change (∫⁻ z : complexPhaseGroup B, ENNReal.ofReal (Predecessor.collision (fullLaw ‖B‖ g T p (ω+z.val))
        (fullLaw ‖B‖ g T p (ω+z.val)) A) ∂complexPhaseHaar B) ≤ _
      refine (lintegral_mono (g:=fun _ ↦ 1) (fun z ↦ ?_)).trans_eq (by simp)
      rw [←ENNReal.ofReal_one]; apply ENNReal.ofReal_le_ofReal
      exact measureReal_le_one
    · rw [←ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (mul_nonneg hC hA.le) : 1 ≤ K)
  | cons a w ih =>
    intro T T1 T3 p hp ω
    obtain ⟨hc,hd,mem⟩ := weights p hp
    let V := K*(w.length+1:ℝ)*(w.map coef).prod*q^w.length
    have pV : 0 ≤ V := by dsimp only [V];have := zero_le_one.trans (prod1 w);positivity
    have mesh := mesh_inherits hn T1
    have R : 0 < A*q^(w.length+1) := mul_pos hA (pow_pos qp _)
    have next (ξ : PhaseTorus) : wordEnergy B g ρ (q^t) n e w (childLength ‖B‖ T n (arity ‖B‖ T n)) (shiftedParameters p n) ξ ((A*q^(w.length+1))/g^n) ≤ ENNReal.ofReal V := by
      rw [pow_succ,←mul_assoc,mul_div_cancel_right₀ _ qp.ne'];exact ih mesh.1 (mesh.2.trans (by norm_num)) mem ξ
    have h := step T1 T3 (Real.rpow_pos_of_pos qp t).le mesh.2 hc hd he hm ω a w R next
    apply h.trans
    have coeff0 : 0 ≤ 3*(if a then 1 else q^t) := by cases a <;> simp only [Bool.false_eq_true,if_false,if_true] <;> positivity
    rw [←ENNReal.ofReal_mul coeff0,←ENNReal.ofReal_add (mul_nonneg hC R.le) (mul_nonneg coeff0 pV)]
    apply ENNReal.ofReal_le_ofReal
    have mult : 3*(if a then 1 else q^t) = q*coef a := by dsimp only [coef,Predecessor.wordCoefficient];field_simp
    have big : C*A ≤ K*(coef a*(w.map coef).prod) :=
      (show C*A ≤ K by dsimp only [K];linarith).trans (le_mul_of_one_le_right kp.le (prod1 (a::w)))
    have bd := mul_le_mul_of_nonneg_right big (pow_nonneg qp.le (w.length+1))
    rw [mult];dsimp only [V];simp only [List.length_cons,List.map_cons,List.prod_cons,Nat.cast_succ]
    change C*(A*q^(w.length+1)) + q*coef a*(K*(w.length+1:ℝ)*(w.map coef).prod*q^w.length) ≤
       K*((w.length:ℝ)+1+1)*(coef a*(w.map coef).prod)*q^(w.length+1)
    rw [pow_succ] at bd ⊢;linarith only [bd]

end Weierstrass.Descent
