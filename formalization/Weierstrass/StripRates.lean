module

public import Weierstrass.RayInformation
public import Weierstrass.HarmonicScale

/-! Scale conversion and interpolation for the equal-rate strip argument. -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Weierstrass.StripProof

theorem amplitude_as_width {b g : ℝ} (hb : 1 < b) (hg : 0 < g) (n : ℕ) :
    ((b^n)⁻¹:ℝ)^alpha b g = g^n := by
  have bn := pow_pos (zero_lt_one.trans hb) n
  rw [Real.rpow_def_of_pos (inv_pos.mpr bn),Real.log_inv,Real.log_pow,alpha,
    show -(n*Real.log b)*(-Real.log g/Real.log b) = n*Real.log g by field_simp [(Real.log_pos hb).ne'],
    ←Real.log_pow,Real.exp_log (pow_pos hg n)]

theorem dual_as_width {b g : ℝ} (hb : 1 < b) (hg : 0 < g) (m : ℕ) :
    ((b*g)⁻¹)^m = ((b^m)⁻¹:ℝ)^(1-alpha b g) := by
  rw [Real.rpow_sub (inv_pos.mpr (pow_pos (zero_lt_one.trans hb) m)),Real.rpow_one,
    amplitude_as_width hb hg,inv_pow,mul_pow];ring

/-- A physical box of relative width l fits at one integer scale, and the
same choice gives the exact B4 power l^(1+βs) including its Jacobian. -/
theorem strip_physical_scale {b g : ℝ} (hb : 1 < b) (hg : b⁻¹ < g) (hg1 : g < 1)
    {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    ∃ n : ℕ, l ≤ (b^n)⁻¹ ∧ (b^n)⁻¹ ≤ b*l ∧ ∀ {Δ s : ℝ}, 0 < Δ → 0 ≤ s →
      Δ*l/g^n ≤ Δ*l^(1-alpha b g) ∧
      (b^n)⁻¹*(Δ*l/g^n)^s ≤ b*Δ^s*l^(1+(1-alpha b g)*s) := by
  have bpos := zero_lt_one.trans hb
  have gpos := (inv_pos.mpr bpos).trans hg
  obtain ⟨n,low,up⟩ := exists_nat_pow_near_of_lt_one hl hl1 (inv_pos.mpr bpos) (inv_lt_one_of_one_lt₀ hb)
  rw [inv_pow] at up
  rw [pow_succ,inv_pow,←div_eq_mul_inv] at low
  have scale := (div_lt_iff₀ bpos).mp low
  have hi : (b^n)⁻¹ ≤ b*l := by simpa only [mul_comm] using scale.le
  refine ⟨n,up,hi,?_⟩
  intro Δ s hΔ hs
  have lp := Real.rpow_pos_of_pos hl (alpha b g)
  have gp := pow_pos gpos n
  have a := (Real.rpow_le_rpow hl.le up (alpha_mem_Ioo hb hg hg1).1.le).trans_eq (amplitude_as_width hb gpos n)
  have nd : Δ*l/g^n ≤ Δ*l^(1-alpha b g) := by
    rw [Real.rpow_sub hl,Real.rpow_one,←mul_div_assoc]
    exact div_le_div_of_nonneg_left (by positivity) lp a
  refine ⟨nd,?_⟩
  apply (mul_le_mul hi (Real.rpow_le_rpow (by positivity) nd hs) (by positivity) (by positivity)).trans_eq
  rw [Real.mul_rpow hΔ.le (Real.rpow_nonneg hl.le _),←Real.rpow_mul hl.le,Real.rpow_add hl,Real.rpow_one]
  ring

/-- Exact final exponent when d is multiplied by a fixed positive constant. -/
theorem strip_final_power {r K : ℝ} (hr : 0 < r) (hK : 0 < K) (β s p : ℝ) :
    (r^β)^s*(K*r/r^β)^p = K^p*r^(β*s+(1-β)*p) := by
  have eq : K*r/r^β = K*r^(1-β) := by rw [Real.rpow_sub hr,Real.rpow_one];ring
  rw [eq,Real.mul_rpow hK.le (Real.rpow_nonneg hr.le _),←Real.rpow_mul hr.le,←Real.rpow_mul hr.le,Real.rpow_add hr]
  ring

def stripGain (β s t : ℝ) := β*s+(1-β)*min 1 (β*s+t)

/-- Strict exponents and a finite mesh suffice to beat any target below B1. -/
theorem strip_gain_slack {β s t u : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hu : u < stripGain β s t) :
    ∃ s' t' : ℝ, 0 < s' ∧ s' < s ∧ 0 < t' ∧ t' < t ∧ ∃ J : ℕ, 2 ≤ J ∧
      u < β*s'+(1-β)*(min 1 (β*s'+t')-1/(J:ℝ)) := by
  let d (n : ℕ) : ℝ := 1/(n+1:ℕ)
  have lim : Tendsto d atTop (𝓝 0) := by
    simpa only [d,Nat.cast_add,Nat.cast_one] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  let F (x : ℝ) := β*(s-x)+(1-β)*(min 1 (β*(s-x)+(t-x))-x)
  have cf : Continuous F := by dsimp [F];fun_prop
  have gain : u < F 0 := by simpa [F,stripGain] using hu
  obtain ⟨n,hn,small,g⟩ := ((eventually_ge_atTop 1).and
    ((lim.eventually_lt_const (lt_min hs ht)).and ((cf.continuousAt.tendsto.comp lim).eventually (eventually_gt_nhds gain)))).exists
  have dn : 0 < d n := by dsimp [d];positivity
  exact ⟨s-d n,t-d n,sub_pos.mpr (small.trans_le (min_le_left _ _)),sub_lt_self _ dn,
    sub_pos.mpr (small.trans_le (min_le_right _ _)),sub_lt_self _ dn,n+1,by omega,g⟩

/-- Transfer anchored tests from geometric radii to arbitrary positive radii.
The radius coefficient may depend on the fixed mesh ratio. -/
theorem rayInformation_of_geometric {B : ℂ} {g s q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    {P : Set RayParameters}
    (grid : ∀ h : ℝ, 0 < h → h < s → ∀ T A : ℝ, 0 < T → 0 < A →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∀ ω : PhaseTorus, ∀ p ∈ P,
        (complexPhaseHaar B).real {z : complexPhaseGroup B | ENNReal.ofReal ((q^k:ℝ)^h) <
          rayOccupation ‖B‖ g p (ω+z.val) T A (q^k)} ≤ ε) : RayInformation B g s P := by
  intro h hh hhs T A hT hA ε hε
  obtain ⟨N,good⟩ := eventually_atTop.mp (grid h hh hhs T (A/q) hT (div_pos hA hq) ε hε)
  filter_upwards [self_mem_nhdsWithin,((eventually_lt_nhds (pow_pos hq N)).filter_mono nhdsWithin_le_nhds),
    ((eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds)] with r (pr : 0 < r) small r1
  obtain ⟨k,lo,up⟩ := exists_nat_pow_near_of_lt_one pr r1.le hq hq1
  have kn : N ≤ k+1 := by
    by_contra! wrong
    have v := pow_le_pow_of_le_one hq.le hq1.le wrong.le
    exact (small.trans_le v).asymm lo
  intro ω p hp
  apply le_trans (measureReal_mono (μ:=complexPhaseHaar B) _ (measure_ne_top _ _)) (good _ kn ω p hp)
  intro z hz
  have threshold := ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (pow_pos hq _).le lo.le hh.le)
  have target : A*r ≤ A/q * q^(k+1) := by
    rw [pow_succ,show A/q*(q^k*q)=A*q^k by field_simp]
    exact mul_le_mul_of_nonneg_left up hA.le
  exact (threshold.trans_lt hz).trans_le (measure_mono (fun u hu ↦ ⟨hu.1,hu.2.trans target⟩))

end Weierstrass.StripProof
