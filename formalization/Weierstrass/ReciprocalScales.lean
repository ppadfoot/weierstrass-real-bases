module

public import Weierstrass.ReciprocalRegularity

/-! Exact integer choices for the sequence of reciprocal scales. -/
@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace Weierstrass.Reciprocal

/-- Choose the Hölder exponent and an integer step ratio slightly bigger
than one. Both hold simultaneously throughout the reciprocal iteration. -/
theorem exponent_and_step {b g ρ : ℝ} (hb : 1 < b) (hbg : 1 < b*g) (hρ : 0 < ρ)
    (hrγ : ρ < (b*g)⁻¹) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ 1 < b^2*g*ρ^α ∧ ∃ a : ℕ, 0 < a ∧ (ρ^α)^a ≤ ((b*g)⁻¹)^(a+1) := by
  let γ := (b*g)⁻¹
  have bp := zero_lt_one.trans hb
  have gp : 0 < γ := inv_pos.mpr (zero_lt_one.trans hbg)
  have gl : γ < 1 := inv_lt_one_of_one_lt₀ hbg
  have mlt : max ρ (γ/b) < γ := max_lt hrγ ((div_lt_self gp hb))
  obtain ⟨u,ml,ul⟩ := exists_between mlt
  have ρu := (le_max_left _ _).trans_lt ml
  have up := hρ.trans ρu
  have u1 := ul.trans gl
  have lρ := Real.log_neg hρ (ρu.trans u1)
  let α := Real.log u/Real.log ρ
  have αp : 0 < α := div_pos_of_neg_of_neg (Real.log_neg up u1) lρ
  have αl : α < 1 := by
    rw [show α=Real.log u/Real.log ρ from rfl,div_lt_one_of_neg lρ]
    exact Real.log_lt_log hρ ρu
  have eq : ρ^α = u := (Real.mul_log_eq_log_iff hρ up).mp (div_mul_cancel₀ _ lρ.ne)
  have fast : 1 < b^2*g*ρ^α := by
    have val := (div_lt_iff₀ bp).mp ((le_max_right _ _).trans_lt ml)
    change (b*g)⁻¹ < u*b at val
    rw [inv_lt_iff_one_lt_mul₀ (zero_lt_one.trans hbg)] at val
    rw [eq]; nlinarith only [val]
  have ug : u/γ < 1 := (div_lt_one gp).mpr ul
  obtain ⟨a,aa⟩ := exists_pow_lt_of_lt_one gp ug
  have ap : 0 < a := by
    by_contra! h
    have az : a=0 := by omega
    rw [az,pow_zero] at aa
    linarith
  refine ⟨α,αp,αl,fast,a,ap,?_⟩
  rw [eq]; change u^a ≤ γ^(a+1)
  rw [div_pow,div_lt_iff₀ (pow_pos gp _)] at aa
  simpa only [pow_succ, mul_comm γ] using aa.le

/-- Scale i of an integer construction with base multiplicity n and terminal depth D. -/
def stage (a D n i : ℕ) : ℕ := (a+1)^i * a^(D-i) * n

theorem stage_zero (a D n : ℕ) : stage a D n 0 = a^D*n := by simp [stage]
theorem stage_terminal (a D n : ℕ) : stage a D n D = (a+1)^D*n := by simp [stage]

theorem stage_pair {a D i : ℕ} (ap : 0 < a) (hi : i < D) (n : ℕ) :
    ∃ k ≥ n, stage a D n i = a*k ∧ stage a D n (i+1) = (a+1)*k := by
  let k := (a+1)^i * a^(D-(i+1)) * n
  refine ⟨k,Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos ap)),?_,?_⟩
  · dsimp [stage,k]
    rw [show D-i=(D-(i+1))+1 by omega, pow_succ]
    ring
  · dsimp [stage,k]
    rw [pow_succ]
    ring

/-- Successive scales have the required two power separations once the base
multiplicity exceeds the fixed cutoff. -/
theorem stage_separation {γ ρ α : ℝ} (rp : 0 < ρ) (r1 : ρ < 1)
    {a D i n N : ℕ} (ap : 0 < a) (hi : i < D) (hn : N ≤ n)
    (hN : ρ^N ≤ 1/2) (rate : (ρ^α)^a ≤ γ^(a+1)) :
    let m := stage a D n i
    let M := stage a D n (i+1)
    m ≤ M ∧ n ≤ M-m ∧ ρ^M ≤ ρ^m/2 ∧ (ρ^m)^α ≤ γ^M := by
  obtain ⟨k,kn,e₁,e₂⟩ := stage_pair ap hi n
  dsimp only
  rw [e₁,e₂]
  have val : (a+1)*k=a*k+k := Nat.add_one_mul a k
  have pk : ρ^k ≤ 1/2 := (pow_le_pow_of_le_one rp.le r1.le (hn.trans kn)).trans hN
  refine ⟨by omega,by omega,?_,?_⟩
  · rw [val, pow_add, div_eq_mul_inv]; gcongr
    simpa using pk
  · rw [← Real.rpow_pow_comm rp.le,pow_mul,pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg (Real.rpow_pos_of_pos rp _).le _) rate _

/-- Reserve a strict exponent gain after the initial and final unused scales. -/
theorem choose_depths {σ h : ℝ} (hp : 0 < h) (hσ : h < σ) {a : ℕ} (ap : 0 < a) :
    ∃ D P : ℕ, 0 < D ∧ 1 < P ∧
      (P:ℝ)*((a+1)^D:ℕ)*h < (P-1:ℕ)*(((a+1)^D:ℕ)-(a^D:ℝ))*σ := by
  obtain ⟨s,hs,hsσ⟩ := exists_between hσ
  have s0 := hp.trans hs
  have σp := s0.trans hsσ
  let r : ℝ := (a:ℝ)/(a+1)
  have rp : 0 < r := by dsimp [r]; positivity
  have r1 : r < 1 := by dsimp [r]; apply (div_lt_one (by positivity)).mpr; linarith
  obtain ⟨D,hd⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr ((div_lt_one σp).mpr hsσ)) r1
  have dp : 0 < D := by
    by_contra! bad
    have dz : D=0 := by omega
    rw [dz,pow_zero] at hd
    linarith [div_pos s0 σp]
  have sep : ((a+1)^D:ℕ)*s < (((a+1)^D:ℕ)-(a^D:ℝ))*σ := by
    dsimp [r] at hd
    rw [div_pow,div_lt_iff₀ (by positivity),sub_mul,one_mul,div_mul_eq_mul_div] at hd
    have hmul := (lt_sub_iff_add_lt').mp hd
    rw [← lt_sub_iff_add_lt,div_lt_iff₀ σp] at hmul
    push_cast
    nlinarith only [hmul]
  obtain ⟨P,pbound⟩ := exists_nat_gt (s/(s-h)+1)
  have Ppos : 1 < P := by exact_mod_cast (show (1:ℝ) < P by linarith [div_pos s0 (sub_pos.mpr hs)])
  have ps : (P:ℝ)*h < (P-1:ℕ)*s := by
    rw [Nat.cast_sub (by omega : 1 ≤ P),Nat.cast_one]
    have := (div_lt_iff₀ (sub_pos.mpr hs)).mp (show s/(s-h) < P by linarith)
    nlinarith
  refine ⟨D,P,dp,Ppos,?_⟩
  have Bpos : 0 < (((a+1)^D:ℕ):ℝ) := by positivity
  have Apos : 0 < ((P-1:ℕ):ℝ) := by exact_mod_cast (show 0<P-1 by omega)
  nlinarith only [mul_lt_mul_of_pos_right ps Bpos,mul_lt_mul_of_pos_left sep Apos]

end Weierstrass.Reciprocal
