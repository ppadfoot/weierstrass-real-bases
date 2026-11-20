module

public import Weierstrass.RealBootstrap
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Ring

/-! The explicit uniform count of parameter steps in the unequal-rate
recursion of §6. Normalize the amplitude and increment by the larger log
rate. A non-wrapping step gains at least a factor of 1+ρ. -/
@[expose] public noncomputable section
open Finset Real
open scoped BigOperators
namespace Weierstrass.Bootstrap

def amplitudePhase (x ρ : ℝ) (i : ℕ) := Int.fract (x+i*ρ)

def gainSteps (x ρ : ℝ) (n : ℕ) :=
  ∑ i ∈ Finset.range n, if amplitudePhase x ρ i+ρ<1 then (1:ℕ) else 0

theorem gainSteps_floor {x ρ : ℝ} (x0 : 0≤x) (x1 : x<1) (r0 : 0≤ρ) (r1 : ρ≤1) (n : ℕ) :
    (gainSteps x ρ n : ℤ)+⌊x+(n:ℝ)*ρ⌋ = n := by
  induction n with
  | zero =>
    simp [gainSteps,Int.floor_eq_zero_iff.mpr ⟨x0,x1⟩]
  | succ n ih =>
    let y := x+(n:ℝ)*ρ
    have ys : x+(n+1:ℕ)*ρ=y+ρ := by dsimp [y];push_cast;ring
    have plus : ⌊y+ρ⌋=⌊Int.fract y+ρ⌋+⌊y⌋ := by
      rw [←Int.floor_add_intCast];congr 1;linarith only [Int.fract_add_floor y]
    have lt := Int.fract_lt_one y
    have nn := Int.fract_nonneg y
    have eq : gainSteps x ρ (n+1)=gainSteps x ρ n+(if Int.fract y+ρ<1 then 1 else 0) := Finset.sum_range_succ .. 
    rw [eq,ys,plus]
    change (gainSteps x ρ n:ℤ)+⌊y⌋=n at ih
    by_cases h : Int.fract y+ρ<1
    · rw [if_pos h,Int.floor_eq_zero_iff.mpr ⟨add_nonneg nn r0,h⟩];omega
    · have one : ⌊Int.fract y+ρ⌋=1 := Int.floor_eq_iff.mpr ⟨by simpa using le_of_not_gt h,by push_cast;linarith⟩
      rw [if_neg h,one];omega

theorem gainSteps_mono (x ρ : ℝ) : Monotone (gainSteps x ρ) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [gainSteps,Finset.sum_range_succ];omega

private theorem later_wrap {x ρ : ℝ} (r0 : 0<ρ) (N : ℕ) :
    ∃ i < ⌈1/ρ⌉₊, 1≤amplitudePhase x ρ (N+i)+ρ := by
  let m := ⌈1/ρ⌉₊
  by_contra! fails
  have iterate (k : ℕ) (hk : k≤m) : amplitudePhase x ρ (N+k) = amplitudePhase x ρ N + (k:ℝ)*ρ := by
    induction k with
    | zero => simp
    | succ k ih =>
      have h : amplitudePhase x ρ (N+k)+ρ<1 := fails k (by omega)
      have hy : Int.fract (x+(N+k:ℕ)*ρ)+ρ<1 := h
      let y := x+(N+k:ℕ)*ρ
      have nz : 0≤Int.fract y+ρ := add_nonneg (Int.fract_nonneg _) r0.le
      have ystep : amplitudePhase x ρ (N+(k+1))=amplitudePhase x ρ (N+k)+ρ := by
        change Int.fract (x+(N+(k+1):ℕ)*ρ)=Int.fract y+ρ
        rw [show x+(N+(k+1):ℕ)*ρ=Int.fract y+ρ+⌊y⌋ by
          have yy := Int.fract_add_floor y;dsimp only [y] at yy ⊢;push_cast at yy ⊢;linarith only [yy],
          Int.fract_add_intCast,Int.fract_eq_self.mpr ⟨nz,hy⟩]
      rw [ystep,ih (by omega)];push_cast;ring
  have big := (div_le_iff₀ r0).mp (Nat.le_ceil (1/ρ))
  have lt := Int.fract_lt_one (x+(N+m:ℕ)*ρ)
  change amplitudePhase x ρ (N+m)<1 at lt
  have nn := Int.fract_nonneg (x+(N:ℝ)*ρ)
  change 0≤amplitudePhase x ρ N at nn
  rw [iterate m le_rfl] at lt
  linarith only [lt,nn,big]

/-- By the stated deadline there is either a critical visit or a seed
visit preceded by enough increasing steps to amplify 1/2 to one. -/
theorem explicit_amplitude_budget {x ρ : ℝ} (x0 : 0<x) (x1 : x<1) (r0 : 0<ρ) (r1 : ρ<1) :
    let k := ⌈Real.log 2/Real.log (1+ρ)⌉₊
    let N := ⌈((k:ℝ)+1)/(1-ρ)⌉₊
    ∃ j < N+⌈1/ρ⌉₊, (amplitudePhase x ρ j+ρ=1) ∨
      (1<amplitudePhase x ρ j+ρ ∧ k≤gainSteps x ρ j ∧ 2≤(1+ρ)^(gainSteps x ρ j)) := by
  intro k N
  obtain ⟨i,im,ir⟩ := later_wrap (x:=x) r0 N
  refine ⟨N+i,by omega,?_⟩
  rcases eq_or_lt_of_le ir with critical | seed
  · exact Or.inl critical.symm
  have before : k≤gainSteps x ρ N := by
    have time := (div_le_iff₀ (sub_pos.mpr r1)).mp (Nat.le_ceil (((k:ℝ)+1)/(1-ρ)))
    change (k:ℝ)+1≤N*(1-ρ) at time
    have count := gainSteps_floor x0.le x1 r0.le r1.le N
    have countR : (gainSteps x ρ N:ℝ)+(⌊x+(N:ℝ)*ρ⌋:ℤ)=N := by exact_mod_cast count
    have fl := Int.floor_le (x+(N:ℝ)*ρ)
    exact_mod_cast (show (k:ℝ)≤gainSteps x ρ N by linarith)
  have all := before.trans (gainSteps_mono x ρ (show N≤N+i by omega))
  refine Or.inr ⟨seed,all,?_⟩
  have gt : 1<1+ρ := by linarith
  have lpos := Real.log_pos gt
  have lk := (div_le_iff₀ lpos).mp (Nat.le_ceil (Real.log 2/Real.log (1+ρ)))
  apply (Real.log_le_log_iff (by norm_num : (0:ℝ)<2) (pow_pos (zero_lt_one.trans gt) _)).mp
  rw [Real.log_pow]
  exact lk.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast all) lpos.le)

end Weierstrass.Bootstrap
