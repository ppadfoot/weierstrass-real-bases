module

public import Weierstrass.ReciprocalLocal
public import Weierstrass.ReciprocalScales
public import Weierstrass.ReciprocalPhases

/-! The physical occupation estimate after finitely many reciprocal stages. -/
@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Weierstrass.Reciprocal
open CriticalRay Angular StripProof

local instance (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

private theorem target_pos {b g ρ α A Q : ℝ} (hQ : 0 < Q) : 0 < targetConstant b g ρ α A Q := by
  have : 0 < τ := by dsimp [τ]; positivity
  unfold targetConstant slopeConstant
  positivity

/-- Physical radii and the exponential bound on retained mean occupation at
integer scale n. Here L is the number of separately tested physical annuli. -/
def physicalRate (γ : ℝ) (a D L : ℕ) := γ^((a+1)^D*(L+1))
def retainedRate (γ σ : ℝ) (a D L : ℕ) := (γ^(((a+1)^D-a^D)*L))^σ

set_option maxHeartbeats 1300000 in
theorem retained_mean {B B' : ℂ} (hb : 1 < ‖B‖) (hB' : B' ≠ 0) {g ρ α s σ A K δ : ℝ}
    (hg : 0 < g) (hg1 : g < 1) (hbg : 1 < ‖B‖*g) (hρ : 0 < ρ) (hrγ : ρ < (‖B‖*g)⁻¹)
    (hα : 0 < α) (haα : α ≤ 1) (hslow : 1 < ‖B‖^2*g*ρ^α)
    (normD : ‖B'‖=ρ⁻¹) (rev : (complexPhaseGroup B).map reversePhase=complexPhaseGroup B')
    (hσ : 0 < σ) (hσs : σ < s) (hσ1 : σ ≤ 1) (hA : 0 < A) (hK : 0 < K) (hδ : 0 < δ)
    {ζ v₀ : Circle} {e : ℤ → ℝ} (he : Weight ζ v₀ 1 e)
    (orbit : ∀ x, transverseOrbit ρ e x ∈ complexPhaseGroup B)
    (k : ℕ) (dual : RayInformation B' (‖B‖*g)⁻¹ s (physicalFamily B' ζ v₀ (k+1)))
    (a D L : ℕ) (ap : 0 < a) (rate : (ρ^α)^a ≤ ((‖B‖*g)⁻¹)^(a+1)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ ω : PhaseTorus, ∀ p ∈ physicalFamily B ζ v₀ k,
      ∃ G : Set (complexPhaseGroup B), MeasurableSet G ∧ complexPhaseHaar B Gᶜ ≤ ENNReal.ofReal δ ∧
        ∫⁻ t in Icc (-A) A, complexPhaseHaar B {z | z ∈ G ∧ |circleRay ‖B‖ g p.1 p.2 (ω+z.val) t| ≤
            K*(physicalRate (‖B‖*g)⁻¹ a D L)^n} ≤
          ENNReal.ofReal (((L:ℝ)+1)*3*(2*A)*(retainedRate (‖B‖*g)⁻¹ σ a D L)^n) := by
  let γ := (‖B‖*g)⁻¹
  have gp : 0 < γ := inv_pos.mpr (zero_lt_one.trans hbg)
  have gl : γ < 1 := inv_lt_one_of_one_lt₀ hbg
  have ρl : ρ < 1 := hrγ.trans gl
  let b₀ := (a+1)^D
  let a₀ := a^D
  let w := b₀-a₀
  have leAB : a₀ ≤ b₀ := Nat.pow_le_pow_left (by omega) _
  let Q := K/A
  have qp : 0 < Q := div_pos hK hA
  let C := targetConstant ‖B‖ g ρ α A Q
  obtain ⟨N₀,hN⟩ := retained_dual_tests hB' rev gp gl hσ hσs (target_pos qp) hδ dual (Fin L × Fin D)
    (K := C)
  obtain ⟨N₁,small⟩ := exists_pow_lt_of_lt_one (by norm_num : (0:ℝ)<1/2) ρl
  refine ⟨max N₀ N₁,?_⟩
  intro n hn ω p hp
  let muls (j : ℕ) := (L-j)*n
  let m (i : Fin L × Fin D) := stage a D (muls i.1) i.2
  let M (i : Fin L × Fin D) := stage a D (muls i.1) (i.2+1)
  have hn₁ : N₁ ≤ n := (Nat.le_max_right _ _).trans hn
  have hn₀ : N₀ ≤ n := (Nat.le_max_left _ _).trans hn
  have props (i : Fin L × Fin D) : m i ≤ M i ∧ n ≤ M i-m i ∧ ρ^(M i) ≤ ρ^(m i)/2 ∧
       (ρ^(m i))^α ≤ γ^(M i) := by
    have qn : n ≤ muls i.1 := Nat.le_mul_of_pos_left _ (Nat.sub_pos_of_lt i.1.isLt)
    have H := stage_separation hρ ρl ap i.2.isLt (hn₁.trans qn) small.le rate
    exact ⟨H.1,qn.trans H.2.1,H.2.2⟩
  obtain ⟨G,hG,mG,good⟩ := hN ω (fun i ↦ reversedParameters p.1 p.2 e (m i)) m
    (fun i ↦ M i-m i) (fun i ↦ reversedParameters_mem hB' hρ normD rev hp he orbit (m i))
    (fun i ↦ hn₀.trans (props i).2.1)
  refine ⟨G,hG,mG,?_⟩
  let ψ := (γ^(w*n))^σ
  have ψp : 0 < ψ := Real.rpow_pos_of_pos (pow_pos gp _) _
  have ψ₁ : ψ ≤ 1 := Real.rpow_le_one (pow_pos gp _).le (pow_le_one₀ gp.le gl.le) hσ.le
  have ψge : γ^(b₀*n) ≤ ψ := by
    have H := min_one_le_rpow hσ hσ1 (pow_pos gp (w*n)).le
    rw [min_eq_right (pow_le_one₀ gp.le gl.le)] at H
    exact (pow_le_pow_of_le_one gp.le gl.le (Nat.mul_le_mul_right n (Nat.sub_le b₀ a₀))).trans H
  let R := (physicalRate γ a D L)^n
  let event (t : ℝ) := {z : complexPhaseGroup B | z ∈ G ∧ |circleRay ‖B‖ g p.1 p.2 (ω+z.val) t| ≤ K*R}
  have shell (j : ℕ) (jl : j ≤ L) (t : ℝ) (low : A*ψ^(j+1) ≤ |t|) (high : |t| ≤ A) :
      complexPhaseHaar B (event t) ≤ 3*ENNReal.ofReal (ψ^(L-j)) := by
    by_cases last : j=L
    · subst j; simpa using (prob_le_one (μ := complexPhaseHaar B) (s := event t)).trans (by norm_num : (1:ℝ≥0∞)≤3)
    let idx : Fin L := ⟨j,by omega⟩
    have tpos := (mul_pos hA (pow_pos ψp (j+1))).trans_le low
    have expo : b₀*(L+1)*n=b₀*muls j+(b₀*n)*(j+1) := by
      have := Nat.sub_add_cancel jl
      dsimp [muls]
      nlinarith only [congrArg (fun z : ℕ ↦ b₀*z*n) this]
    have rho : R = γ^(b₀*muls j)*(γ^(b₀*n))^(j+1) := by
      change (γ^(b₀*(L+1)))^n = _
      rw [← pow_mul,expo,pow_add,pow_mul γ (b₀*n) (j+1)]
    have cap : K*R ≤ Q*γ^(b₀*muls j)*|t| := by
      rw [rho]
      calc
        _ ≤ K*(γ^(b₀*muls j)*ψ^(j+1)) := by gcongr
        _ = Q*γ^(b₀*muls j)*(A*ψ^(j+1)) := by dsimp [Q]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left low (mul_pos qp (pow_pos gp _)).le
    have hevent : MeasurableSet (event t) := by
      have env : Continuous (fun z : complexPhaseGroup B ↦ ω+z.val) := continuous_const.add continuous_subtype_val
      have f := (measurable_circleRay ‖B‖ g p.1 p.2).comp (env.measurable.prodMk (measurable_const (a := t)))
      exact hG.inter (measurableSet_le f.abs measurable_const)
    apply haar_le_of_transverse_slices (complexPhaseHaar B) orbit (event t) hevent
    intro z
    let z₀ := ω+z.val
    let zz (x : ℝ) : complexPhaseGroup B := z+⟨transverseOrbit ρ e x,orbit x⟩
    let E := {x : ℝ | x ∈ Icc 0 1 ∧ zz x ∈ event t}
    have zr (x : ℝ) : ω+(zz x).val=z₀+transverseOrbit ρ e x := (add_assoc _ _ _).symm
    let st := stage a D (muls j)
    have mono (i : ℕ) (hi : i < D) : st i ≤ st (i+1) := (props (idx,⟨i,hi⟩)).1
    have step (i : ℕ) (hi : i < D) : volume (neighborhood E (ρ^(st (i+1)))) ≤
        ENNReal.ofReal ((γ^(st (i+1)-st i))^σ)*volume (neighborhood E (ρ^(st i))) := by
      let i' : Fin L × Fin D := (idx,⟨i,hi⟩)
      have data := props i'
      refine retained_neighborhood_step (Q := Q) hb hg hg1 hbg hρ hrγ hα haα hslow hp.1.1.bounded hp.1.2.bounded he.bounded
        (st i) (st (i+1)) data.1 data.2.2.1 data.2.2.2 z₀ t high tpos E ?_ ?_
      · intro x hx
        have f : |circleRay ‖B‖ g p.1 p.2 (ω+(zz x).val) t| ≤ K*R := hx.2.2
        rw [zr] at f
        have order : st (i+1) ≤ st D := by
          have aux : MonotoneOn st (Iic D) := monotoneOn_of_le_succ Set.ordConnected_Iic (fun a _ _ h ↦ mono a (show a+1 ≤ D from h))
          exact aux (show i+1 ∈ Iic D from hi) (Set.mem_Iic.mpr le_rfl) hi
        have cap' : γ^(b₀*muls j) ≤ γ^(st (i+1)) := by
          change γ^((a+1)^D*muls j) ≤ _
          rw [← stage_terminal a D]
          exact pow_le_pow_of_le_one gp.le gl.le order
        exact (f.trans cap).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left cap' qp.le) (abs_nonneg _))
      · intro x hx
        have ok := good (zz x) hx.2.1 i'
        rw [normD,zr] at ok
        exact ok
    have hh := neighborhood_chain gp hρ ρl.le E (fun _ hx ↦ hx.1) st D mono step
    refine hh.trans_eq ?_
    congr 2
    change (γ^(stage a D (muls j) D - stage a D (muls j) 0))^σ = ψ^(L-j)
    rw [stage_terminal,stage_zero,← Nat.sub_mul]
    dsimp only [ψ,w,muls,b₀,a₀]
    rw [Real.rpow_pow_comm (pow_pos gp _).le,← pow_mul]
    congr 2; ring
  have bound := geometric_shell_integral hA ψp ψ₁ L 3 (by norm_num) (fun t ↦ complexPhaseHaar B (event t))
    (fun _ ↦ prob_le_one) shell
  refine bound.trans_eq ?_
  have eq : ψ^L = (retainedRate γ σ a D L)^n := by
    dsimp [ψ,retainedRate,w,b₀,a₀]; rw [Real.rpow_pow_comm,Real.rpow_pow_comm,← pow_mul,← pow_mul] <;> try positivity
    congr 2; ring
  rw [eq, ENNReal.ofReal_mul (p := ((L:ℝ)+1)*3*(2*A)) (by positivity),
    ENNReal.ofReal_mul (p := ((L:ℝ)+1)*3) (by positivity),ENNReal.ofReal_mul (p := (L:ℝ)+1) (by positivity),
    ENNReal.ofReal_mul (p := 2*A) (by positivity)]
  simp [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one,mul_assoc,γ]

end Weierstrass.Reciprocal
