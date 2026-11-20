module

public import Weierstrass.StripRates

/-! ε-allocation between information tests, discarded centers and retained collisions. -/
@[expose] public noncomputable section
namespace Weierstrass.StripProof

theorem strip_probability_budget (J : ℕ) {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) :
    ∃ M η δ : ℝ, 1 < M ∧ 0 < η ∧ 0 < δ ∧ ∀ {x : ℝ}, x ≤ δ →
      J*η+(1+2*T)*((J+1)*η+3/M+M*(1+2*T)*x) ≤ ε := by
  let S := 1+2*T
  let M := 1+12*S/ε
  let η := ε/(4*(((J:ℝ)+1))*(1+S))
  let δ := ε/(4*M*S^2)
  have sp : 0 < S := by dsimp [S]; linarith
  have mone : 1 < M := by dsimp [M]; linarith [div_pos (mul_pos (by norm_num : (0:ℝ)<12) sp) hε]
  have mp := zero_lt_one.trans mone
  have ep : 0 < η := by dsimp [η]; positivity
  have dp : 0 < δ := by dsimp [δ]; positivity
  refine ⟨M,η,δ,mone,ep,dp,?_⟩
  intro x hx
  have a : (J:ℝ)*η+S*((J:ℝ)+1)*η ≤ ε/4 := by
    calc
      _ ≤ ((J:ℝ)+1)*η+S*((J:ℝ)+1)*η := by nlinarith
      _ = _ := by dsimp [η]; field_simp
  have b : S*(3/M) ≤ ε/4 := by
    rw [← mul_div_assoc,div_le_iff₀ mp]
    dsimp [M]; rw [mul_add,mul_one]; field_simp; nlinarith
  have c : M*S^2*x ≤ ε/4 := (mul_le_mul_of_nonneg_left hx (mul_nonneg mp.le (sq_nonneg S))).trans_eq (by
    dsimp [δ]; field_simp)
  change ↑J*η+S*((↑J+1)*η+3/M+M*S*x) ≤ ε
  nlinarith only [a,b,c,hε]

end Weierstrass.StripProof
