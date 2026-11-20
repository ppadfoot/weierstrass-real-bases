module

public import Weierstrass.PredecessorProof

/-! Growth of the actual good/bad energy coefficients. The crude bound
2^k on the number of words suffices since n is subsequently arbitrarily large. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Weierstrass.Predecessor

def wordCoefficient (q t : ℝ) (a : Bool) := (3/q)*(if a = true then 1 else q^t)

theorem wordCoefficient_ge {q t : ℝ} (hq : 0 < q) (hq' : q ≤ 1) (ht : t ≤ 1) (a : Bool) :
    1 ≤ wordCoefficient q t a := by
  have hpow : q ≤ q^t := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hq hq' ht
  cases a <;> simp only [wordCoefficient,Bool.false_eq_true,if_false,if_true,mul_one]
  · have c := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 3/q)
    rw [div_mul_cancel₀ _ hq.ne'] at c;linarith
  · exact (one_le_div hq).mpr (by linarith)

theorem wordCoefficient_rows {p n : ℕ} (hp : 0<p) {q : ℝ} (hq : 0<q) (t : ℝ) (a : Bool) :
    3*(if a = true then (p:ℝ)^n else (p:ℝ)^n*q^t)*(p:ℝ)⁻¹^n ≤ q * wordCoefficient q t a := by
  have pp : 0 < (p:ℝ) := by exact_mod_cast hp
  cases a <;> simp only [wordCoefficient,Bool.false_eq_true,if_false,if_true,mul_one,inv_pow] <;>
    field_simp <;> ring_nf <;> exact le_rfl

theorem wordCoefficient_sparse {q t δ : ℝ} (hq : 0<q) (hq' : q≤1) (ht : 0≤t) (hδ : 0≤δ)
    {k : ℕ} {v : Fin k → Bool} (hv : v ∈ sparseStatusWords k ⌊δ*k⌋₊) :
    ((List.ofFn v).map (wordCoefficient q t)).prod*q^k ≤ (3*q^(t*(1-δ)))^k := by
  let bad := Finset.univ.filter fun i => v i = true
  let good := Finset.univ.filter fun i => ¬ v i = true
  have hc : good.card+bad.card = k := by simpa only [good,bad,Finset.card_univ,Fintype.card_fin,add_comm] using Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun i => v i = true)
  have hb : bad.card ≤ ⌊δ*k⌋₊ := (Finset.mem_filter.mp hv).2
  have hb' : (bad.card:ℝ) ≤ δ*k := (by exact_mod_cast hb : (bad.card:ℝ) ≤ (⌊δ*k⌋₊:ℝ)).trans (Nat.floor_le (by positivity))
  have hc' : (good.card:ℝ)+(bad.card:ℝ)=k := by exact_mod_cast hc
  have exp : t*(1-δ)*k ≤ t*good.card := by
    have w : (1-δ)*k ≤ good.card := by linarith
    rw [mul_assoc];exact mul_le_mul_of_nonneg_left w ht
  have pw := Real.rpow_le_rpow_of_exponent_ge hq hq' exp
  have prod : (∏ i, if v i = true then (1:ℝ) else q^t) = (q^t)^good.card := by
    rw [Finset.prod_ite];simp [good]
  rw [List.map_ofFn,List.prod_ofFn]
  simp only [Function.comp_apply,wordCoefficient,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,prod,mul_pow,div_pow]
  rw [show (3:ℝ)^k/q^k*(q^t)^good.card*q^k = 3^k*(q^t)^good.card by field_simp]
  rw [←Real.rpow_mul_natCast hq.le,←Real.rpow_mul_natCast hq.le]
  exact mul_le_mul_of_nonneg_left pw (by positivity)

theorem discard_floor_bound (k : ℕ) {δ : ℝ} (hδ : 0<δ) (e : ℝ≥0∞) :
    k*e/((⌊δ*k⌋₊+1:ℕ):ℝ≥0∞) ≤ e/ENNReal.ofReal δ := by
  have P : 0 < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
  have Q : 0 < ((⌊δ*k⌋₊+1:ℕ):ℝ≥0∞) := by positivity
  apply (ENNReal.le_div_iff_mul_le (.inl P.ne') (.inl ENNReal.ofReal_ne_top)).mpr
  rw [div_eq_mul_inv,mul_right_comm,←div_eq_mul_inv]
  apply (ENNReal.div_le_iff Q.ne' (by finiteness)).mpr
  rw [mul_right_comm,mul_comm e]
  apply mul_le_mul_left
  have hh := (Nat.lt_floor_add_one (δ*k)).le
  have H := ENNReal.ofReal_le_ofReal hh
  simpa only [ENNReal.ofReal_mul hδ.le,ENNReal.ofReal_natCast,Nat.cast_succ,ENNReal.ofReal_add (Nat.cast_nonneg _)
    zero_le_one,ENNReal.ofReal_one,mul_comm] using H

/-- The order of limits used by both the physical and polynomial predecessor
recursions. First choose the discarded fraction and full-ball parameter,
then the block length, and finally the number of blocks. -/
theorem finite_mesh_information_budget {g t σ ε : ℝ} (hg : 0<g) (hg' : g<1) (hσ : 0<σ)
    (hgap : σ<t) (hε : 0<ε) :
    ∃ δ K e : ℝ, 0<δ ∧ δ<1 ∧ 1<K ∧ 0<e ∧ ∀ᶠ n : ℕ in atTop, ∀ C : ℝ, 0<C →
      ∀ᶠ k : ℕ in atTop, e/δ + 3/K + K*C*(k+1:ℝ)*(12*(g^n:ℝ)^(t*(1-δ)-σ))^k ≤ ε := by
  have hT := hσ.trans hgap
  let δ := (t-σ)/(2*t)
  let K := 2+12/ε
  let e := ε*δ/4
  have dp : 0<δ := div_pos (sub_pos.mpr hgap) (by positivity)
  have dl : δ<1 := (div_lt_one (by positivity : 0<2*t)).mpr (by linarith)
  have Kp : 1<K := by dsimp [K];linarith [div_pos (by norm_num : (0:ℝ)<12) hε]
  have ep : 0<e := by dsimp only [e];positivity
  have eq : e/δ=ε/4 := by dsimp [e];field_simp
  have Kb : 3/K<ε/4 := by
    apply (div_lt_iff₀ (zero_lt_one.trans Kp)).mpr
    dsimp only [K];rw [mul_add];field_simp;linarith
  have exp : 0<t*(1-δ)-σ := by dsimp only [δ];field_simp;linarith
  have gn : Tendsto (fun n : ℕ => g^n) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one hg.le hg'
  have lim := ((Real.continuousAt_rpow_const 0 _ (.inr exp.le)).tendsto.comp gn).const_mul (12:ℝ)
  rw [Real.zero_rpow exp.ne',mul_zero] at lim
  refine ⟨δ,K,e,dp,dl,Kp,ep,?_⟩
  filter_upwards [lim.eventually_lt_const zero_lt_one] with n small
  let v := 12*(g^n:ℝ)^(t*(1-δ)-σ)
  have vp : 0≤v := mul_nonneg (by norm_num) (Real.rpow_nonneg (pow_nonneg hg.le _) _)
  have v1 : v<1 := small
  intro C _hC
  have decay := ((tendsto_self_mul_const_pow_of_lt_one vp v1).add (tendsto_pow_atTop_nhds_zero_of_lt_one vp v1)).const_mul (K*C)
  rw [add_zero,mul_zero] at decay
  filter_upwards [decay.eventually_lt_const (show 0<ε/2 by positivity)] with k van
  change K*C*((k:ℝ)*v^k + v^k) < ε/2 at van
  change e/δ+3/K+K*C*(k+1:ℝ)*v^k ≤ ε
  rw [eq];linarith only [van,Kb]

end Weierstrass.Predecessor
