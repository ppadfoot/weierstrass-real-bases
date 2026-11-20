module

public import Weierstrass.Graph

/-! Integer scales for the finite magnification windows of Appendix B. -/
@[expose] public noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace Weierstrass.Branch

/-- Outer annuli, their inner cutoff, and the nested windows used in each
annulus. `edge i m` is the outer endpoint of annulus i at radius `q^m`. -/
structure WindowGrid (g c h s : ℝ) where
  K : ℕ
  L : ℕ
  q : ℝ
  e : ℝ
  σ : ℝ
  q_pos : 0 < q
  q_lt_one : q < 1
  h_lt : h < e
  e_lt : e < σ
  σ_lt : σ < s
  K_pos : 0 < K
  L_pos : 0 < L
  edge : ℕ → ℕ → ℝ
  depth : ℕ → ℕ → ℕ → ℕ
  step : ℕ → ℕ → ℕ → ℕ
  edge_zero : ∀ m, edge 0 m = 1
  edge_pos : ∀ i m, 0 < edge i m
  edge_anti : ∀ i m, edge (i+1) m ≤ edge i m
  center : ∀ m, edge K m ≤ (q^m)^e
  terminal : ∀ i < K, ∀ m, q^m / edge (i+1) m ≤ g^(depth i L m)
  advance : ∀ i < K, ∀ j < L, ∀ m, depth i j m + step i j m = depth i (j+1) m
  physical : ∀ i < K, ∀ j < L, ∀ m, c^(depth i j m) ≤ g^(step i j m)
  linear_growth : ∀ i < K, ∀ j < L, ∀ m, m ≤ step i j m
  growth : ∀ i < K, ∀ j < L, Tendsto (step i j) atTop atTop
  cost : ∀ i < K, ∀ m, edge i m * ∏ j ∈ Finset.range L, (g^(step i j m))^σ ≤ (q^m)^e

/-- Every normalized displacement of size at most one belongs to the center or
to one of the finitely many annuli. Endpoints are assigned exactly once. -/
theorem WindowGrid.locate {g c h s : ℝ} (G : WindowGrid g c h s) (m : ℕ) {z : ℝ} (hz : z ≤ 1) :
    z ≤ G.edge G.K m ∨ ∃ i < G.K, G.edge (i+1) m < z ∧ z ≤ G.edge i m := by
  have go (k : ℕ) : z ≤ G.edge k m ∨ ∃ i < k, G.edge (i+1) m < z ∧ z ≤ G.edge i m := by
    induction k with
    | zero => exact .inl ((G.edge_zero m).symm ▸ hz)
    | succ k ih =>
      rcases le_or_gt z (G.edge (k+1) m) with yes|no
      · exact .inl yes
      · right
        obtain old|⟨i,hi,hz'⟩ := ih
        · exact ⟨k,Nat.lt_succ_self k,no,old⟩
        · exact ⟨i,hi.trans (Nat.lt_succ_self k),hz'⟩
  exact go G.K

private def old (J L j M : ℕ) := (J+1)^j*J^(L-j)*M
private def jump (J L j M : ℕ) := (J+1)^j*J^(L-(j+1))*M

private theorem old_step {J L j M : ℕ} (hj : j<L) :
    old J L j M = J*jump J L j M ∧ old J L (j+1) M = (J+1)*jump J L j M := by
  have sub : L-j = L-(j+1)+1 := by omega
  constructor
  · unfold old jump;rw [sub,pow_succ];ring
  · unfold old jump;rw [pow_succ];ring

private theorem jump_sum (J L M : ℕ) :
    J^L*M+∑ j ∈ Finset.range L,jump J L j M = (J+1)^L*M := by
  have part (u : ℕ) (hu : u ≤ L) :
      old J L 0 M + ∑ j ∈ Finset.range u, jump J L j M = old J L u M := by
    induction u with
    | zero => simp
    | succ u ih =>
      rw [Finset.sum_range_succ,←Nat.add_assoc,ih (by omega)]
      obtain ⟨a,b⟩ := old_step (J:=J) (M:=M) (show u<L by omega)
      rw [a,b];ring
  simpa [old] using part L le_rfl

private theorem real_pow_product {g : ℝ} (hg : 0 < g) (d : ℕ → ℕ) (σ : ℝ) (L : ℕ) :
    (∏ j ∈ Finset.range L,(g^(d j))^σ) = g^(((∑ j ∈ Finset.range L,d j : ℕ):ℝ)*σ) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.prod_range_succ,Finset.sum_range_succ,ih,Nat.cast_add,add_mul,Real.rpow_add hg,
      Real.rpow_natCast_mul hg.le (d L)]

/-- Construct the finite grid at every positive information exponent with
strict room at both ends. All dimensions use the same integer mesh. -/
theorem grid_exists {g c h s : ℝ} (hg : 0 < g) (hg1 : g<1) (hc : 0<c) (hc1 : c<1)
    (hh : 0<h) (hs : h<s) (s1 : s≤1) : Nonempty (WindowGrid g c h s) := by
  obtain ⟨e,he,hes⟩ := exists_between hs
  obtain ⟨σ,hes',hσ⟩ := exists_between hes
  have σp := hh.trans (he.trans hes')
  have σ1 := hσ.le.trans s1
  have lim : Tendsto (fun k : ℕ => (1-(k:ℝ)⁻¹)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub tendsto_inv_atTop_nhds_zero_nat
  have lim2 : Tendsto (fun k : ℕ => σ*(1-(k:ℝ)⁻¹)^2) atTop (𝓝 σ) := by
    simpa using (lim.pow 2).const_mul σ
  obtain ⟨K,fit,rK⟩ := ((lim2.eventually_const_lt hes').and (eventually_ge_atTop 3)).exists
  have Kpos : 0 < K := by omega
  have kr : 0 < (K:ℝ) := by exact_mod_cast Kpos
  let a := 1-(K:ℝ)⁻¹
  have ap : 0 ≤ a := sub_nonneg.mpr ((inv_le_one₀ kr).mpr (by exact_mod_cast (show 1≤K by omega)))
  have a1 : a ≤ 1 := by dsimp [a];linarith [inv_nonneg.mpr kr.le]
  have ak : a*(K:ℝ)=(K:ℝ)-1 := by dsimp [a];field_simp
  have ef : e ≤ σ*a*a := by simpa only [pow_two,←mul_assoc] using fit.le
  obtain ⟨J,hJ⟩ := exists_pow_lt_of_lt_one hg hc1
  have Jpos : 0<J := by
    by_contra! z
    have eq : J=0 := by omega
    rw [eq,pow_zero] at hJ
    exact (not_lt_of_ge hg1.le) hJ
  have jp : 0 < (J:ℝ)+1 := by positivity
  have jr : (J:ℝ)/((J:ℝ)+1) < 1 := (div_lt_one jp).mpr (by linarith)
  obtain ⟨L,hL⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr kr) jr
  have Lpos : 0<L := by
    by_contra! z;have eq : L=0 := by omega
    rw [eq,pow_zero] at hL;linarith only [hL,ap,show a=1-(K:ℝ)⁻¹ from rfl]
  let N := (J+1)^L
  let U := J^L
  let D := K*N
  let M := fun i m : ℕ => (K-1-i)*m
  let edge := fun i m : ℕ => g^(i*N*m)
  have np : 0<N := pow_pos (by omega) L
  have dp : 0<D := Nat.mul_pos Kpos np
  have Np : 0 < (N:ℝ) := by exact_mod_cast np
  have Lratio : (U:ℝ) ≤ (K:ℝ)⁻¹*N := by
    rw [div_pow] at hL
    apply le_of_lt
    convert (div_lt_iff₀ (pow_pos jp L)).mp hL using 1 <;> simp [U,N]
  have fraction : a*N ≤ (N:ℝ)-U := by
    dsimp [a];linarith only [Lratio]
  have psmall : σ*a ≤ 1 := (mul_le_mul_of_nonneg_left a1 σp.le).trans (by simpa using σ1)
  have qpow (m : ℕ) : (g^D)^m = g^(D*m) := (pow_mul _ _ _).symm
  have stepBound (i : ℕ) (hi : i<K-1) (j m : ℕ) : m ≤ jump J L j (M i m) := by
    have uP : 1 ≤ (J+1)^j*J^(L-(j+1))*(K-1-i) := Nat.mul_pos
      (Nat.mul_pos (pow_pos (by omega : 0<J+1) j) (pow_pos Jpos (L-(j+1)))) (by omega)
    dsimp [jump,M];rw [←Nat.mul_assoc]
    exact Nat.le_mul_of_pos_left m uP
  refine ⟨⟨K-1,L,g^D,e,σ,pow_pos hg _,pow_lt_one₀ hg.le hg1 (by omega),he,hes',hσ,
    by omega,Lpos,edge,(fun i j m => old J L j (M i m)),(fun i j m => jump J L j (M i m)),
    ?_,?_,?_,?_,?_,?_,?_,(fun i hi j _ => stepBound i hi j),?_,?_⟩⟩
  · intro m;simp [edge]
  · intro i m;exact pow_pos hg _
  · intro i m;apply pow_le_pow_of_le_one hg.le hg1.le;gcongr;omega
  · intro m
    change g^((K-1)*N*m) ≤ ((g^D)^m)^e
    rw [qpow,← Real.rpow_natCast_mul hg.le,←Real.rpow_natCast g ((K-1)*N*m)]
    apply Real.rpow_le_rpow_of_exponent_ge hg hg1.le
    push_cast
    rw [Nat.cast_sub (show 1≤K by omega),Nat.cast_one]
    have e1 : e ≤ a := ef.trans ((mul_le_mul_of_nonneg_right psmall ap).trans_eq (one_mul a))
    have t := mul_le_mul_of_nonneg_right e1 kr.le
    rw [ak] at t
    change (↑(K*N):ℝ)*m*e ≤ _
    push_cast; nlinarith only [mul_le_mul_of_nonneg_right t (mul_nonneg Np.le (Nat.cast_nonneg m))]
  · intro i hi m
    rw [div_le_iff₀ (pow_pos hg _),qpow]
    unfold old; simp only [Nat.sub_self,pow_zero,mul_one,←pow_add]
    apply pow_le_pow_of_le_one hg.le hg1.le
    have z : K-1-i+(i+1) = K := by omega
    dsimp [M,D,N]
    nlinarith only [congrArg (fun u : ℕ => u*((J+1)^L*m)) z]
  · intro i _ j hj m
    obtain ⟨a,b⟩ := old_step (J:=J) (M:=M i m) hj
    rw [a,b];ring
  · intro i _ j hj m
    rw [(old_step (J:=J) (M:=M i m) hj).1,pow_mul]
    exact pow_le_pow_left₀ (pow_pos hc _).le hJ.le _
  · intro i hi j _;apply tendsto_atTop.mpr
    intro b;filter_upwards [eventually_ge_atTop b] with m hm
    exact hm.trans (stepBound i hi j m)
  · intro i hi m
    change g^(i*N*m)*(∏ j ∈ Finset.range L,(g^(jump J L j (M i m)))^σ) ≤ ((g^D)^m)^e
    rw [qpow,real_pow_product hg,←Real.rpow_natCast_mul hg.le,←Real.rpow_natCast g (i*N*m),←Real.rpow_add hg]
    apply Real.rpow_le_rpow_of_exponent_ge hg hg1.le
    have eq := jump_sum J L (M i m)
    have asReal := congrArg (fun y : ℕ => (y:ℝ)) eq
    simp only [Nat.cast_add,Nat.cast_mul] at asReal
    have Mrep : (M i m:ℝ) = ((K:ℝ)-1-i)*m := by
      dsimp [M];rw [Nat.cast_mul,Nat.cast_sub (by omega),Nat.cast_sub (by omega),Nat.cast_one]
    change (U:ℝ)*(M i m:ℝ)+_=(N:ℝ)*(M i m:ℝ) at asReal
    have econ := mul_le_mul_of_nonneg_right ef (mul_nonneg kr.le (mul_nonneg Np.le (Nat.cast_nonneg m)))
    have fr := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right fraction (Nat.cast_nonneg (M i m))) σp.le
    have iw := mul_le_mul_of_nonneg_right psmall (mul_nonneg (Nat.cast_nonneg i) (mul_nonneg Np.le (Nat.cast_nonneg m)))
    have ident := congrArg (fun y : ℝ => σ*a*y*N*m) ak
    rw [Mrep] at fr asReal
    change (↑(K*N*m):ℝ)*e ≤ ↑(i*N*m)+_
    simp only [Nat.cast_sum] at asReal
    push_cast
    nlinarith only [econ,fr,iw,ident,asReal,congrArg (fun y : ℝ => y*σ) asReal]

end Weierstrass.Branch
