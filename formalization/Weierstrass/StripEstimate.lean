module

public import Weierstrass.StripCollision

/-! # The finite-mesh strip projection estimate B5 -/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace Weierstrass.StripProof

def mesh (G : ℝ) (j : ℕ) : ℝ := (G^j)⁻¹

/-- Geometric bands cover every nonzero integer radial frequency up to the last mesh. -/
private theorem geometric_cover {G y : ℝ} (_hG : 1 ≤ G) (hy : 1 ≤ y) {J : ℕ}
    (hJ : 0 < J) (h : y ≤ G^J) : ∃ j < J, G^j ≤ y ∧ y ≤ G^(j+1) := by
  induction J with
  | zero => omega
  | succ J ih =>
    by_cases hj : J = 0
    · subst J; exact ⟨0,by omega,by simpa using hy,h⟩
    by_cases hh : y ≤ G^J
    · obtain ⟨j,hj',hs⟩ := ih (by omega) hh
      exact ⟨j,by omega,hs⟩
    · exact ⟨J,by omega,(le_of_not_ge hh),h⟩

private theorem sum_bands {N J : ℕ} {G : ℝ} (hG : 1 ≤ G) (hN : (N:ℝ) ≤ G^J) (hJ : 0 < J)
    (F : ℤ → ℝ) (hF : ∀ k, 0 ≤ F k) :
    ∑ k ∈ integers N, F k ≤ F 0 + ∑ j ∈ Finset.range J, ∑ k ∈ (integers N).filter
      (fun k : ℤ => G^j ≤ |(k:ℝ)| ∧ |(k:ℝ)| ≤ G^(j+1)), F k := by
  classical
  let P := fun (j : ℕ) (k : ℤ) => G^j ≤ |(k:ℝ)| ∧ |(k:ℝ)| ≤ G^(j+1)
  have point (k : ℤ) (hk : k ∈ integers N) : F k ≤ (if k=0 then F 0 else 0) +
      ∑ j ∈ Finset.range J, (if P j k then F k else 0) := by
    by_cases h : k=0
    · subst k; simp only [if_true,le_add_iff_nonneg_right]
      exact Finset.sum_nonneg fun j _ => by split_ifs <;> first | apply hF | exact le_rfl
    · have k1 : (1:ℝ) ≤ |(k:ℝ)| := by exact_mod_cast (show (1:ℤ) ≤ |k| from abs_pos.mpr h)
      have k2 : |(k:ℝ)| ≤ G^J := by
        apply le_trans _ hN
        have i := Finset.mem_Icc.mp hk
        exact_mod_cast abs_le.mpr i
      obtain ⟨j,hj,hp⟩ := geometric_cover hG k1 hJ k2
      rw [if_neg h,zero_add]
      have eq : (if P j k then F k else 0) = F k := if_pos hp
      apply eq.ge.trans (Finset.single_le_sum (s := Finset.range J) (f := fun i => if P i k then F k else 0)
        (by intro i _; split_ifs <;> first | apply hF | exact le_rfl) (Finset.mem_range.mpr hj))
  calc
    _ ≤ ∑ k ∈ integers N, ((if k=0 then F 0 else 0) + ∑ j ∈ Finset.range J, if P j k then F k else 0) :=
      Finset.sum_le_sum point
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_comm (s := integers N) (t := Finset.range J)]
      simp only [Finset.sum_ite_eq',integers,Finset.mem_Icc,neg_nonpos,Nat.cast_nonneg,
        and_self,if_true]
      congr 1; apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_filter]

def growth (G : ℝ) (J : ℕ) (D t : ℝ) : ℝ := max 1 ((mesh G J)^(D+t-2))

/-- Total radial-frequency energy of one strip. The right side retains both the
individual strip mass and the common physical density coefficient B. -/
theorem radial_mesh_energy (μ : Measure Plane) (σ : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure σ] {G S T A B D t : ℝ} {J N : ℕ} (hG : 1 ≤ G) (hJ : 0 < J)
    (hN : (N:ℝ) ≤ G^J) (hT : 1 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hσmass : σ.real univ ≤ 1) (hμmass : μ.real univ ≤ B)
    (hp : ∀ᵐ p ∂μ, p ∈ box 0 S) (hθ : ∀ᵐ θ ∂σ, |θ| ≤ T)
    (hσ : ∀ j < J, ∀ x, σ.real (Icc x (x+mesh G (j+1))) ≤ A*(mesh G (j+1))^t)
    (hμ : ∀ j < J, ∀ z, μ.real (box z (mesh G (j+1))) ≤ B*(mesh G (j+1))^D) :
    ∑ k ∈ integers N, radialEnergy μ σ k ≤
      (1 + J * (96*Real.exp (2+2*S^2)*Real.pi^2*T^2*A) * G * growth G J D t) * B * μ.real univ := by
  classical
  have h0 : 0 < G := by linarith
  let K := 96*Real.exp (2+2*S^2)*Real.pi^2*T^2*A
  let bands := fun j => (integers N).filter (fun k : ℤ => G^j ≤ |(k:ℝ)| ∧ |(k:ℝ)| ≤ G^(j+1))
  have mid (j : ℕ) (hj : j < J) : ∑ k ∈ bands j, radialEnergy μ σ k ≤
      K*G*growth G J D t*B*μ.real univ := by
    let l := mesh G (j+1)
    have hl : 0 < l := inv_pos.mpr (pow_pos h0 _)
    have hl1 : l ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hG)
    have dpos : 0 < mesh G J := inv_pos.mpr (pow_pos h0 _)
    have dl : mesh G J ≤ l := inv_anti₀ (pow_pos h0 _) (pow_le_pow_right₀ hG hj)
    have gpos : 0 ≤ growth G J D t := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_left _ _)
    have powBound : l^(D+t-2) ≤ growth G J D t := by
      by_cases he : 0 ≤ D+t-2
      · exact (Real.rpow_le_one hl.le hl1 he).trans (le_max_left _ _)
      · exact (Real.rpow_le_rpow_of_nonpos dpos dl (le_of_not_ge he)).trans (le_max_right _ _)
    have freq (k : ℤ) (hk : k ∈ bands j) : G^j ≤ |(k:ℝ)| ∧ |(k:ℝ)| ≤ l⁻¹ := by
      simpa [l,mesh] using (Finset.mem_filter.mp hk).2
    have H := directional_band_energy μ σ (bands j) hl hl1 (pow_pos h0 j) hT freq hθ (hσ j hj) hp (hμ j hj)
    have ratio : (2/(G^j*l)+2) ≤ 4*G := by
      have prod : G^j*l = G⁻¹ := by dsimp [l,mesh]; rw [pow_succ]; field_simp
      rw [prod,div_inv_eq_mul]; linarith
    have Eq : (T/l)^2 * (l^t * l^D) = T^2 * l^(D+t-2) := by
      rw [Real.rpow_sub hl,Real.rpow_add hl,Real.rpow_two]; ring
    apply H.trans
    calc
      _ = 24*Real.exp (2+2*S^2)*Real.pi^2*A*B*μ.real univ*(2/(G^j*l)+2) *
        ((T/l)^2 * (l^t*l^D)) := by dsimp only [l] at *; ring
      _ ≤ 24*Real.exp (2+2*S^2)*Real.pi^2*A*B*μ.real univ*(4*G)*
        (T^2*growth G J D t) := by rw [Eq]; gcongr
      _ = _ := by dsimp [K]; ring
  have base : radialEnergy μ σ 0 ≤ B*μ.real univ := by
    unfold radialEnergy
    calc
      _ ≤ ∫ _ : ℝ, (μ.real univ)^2 ∂σ := by
        apply integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) (integrable_const _)
        exact ae_of_all _ fun θ => pow_le_pow_left₀ (norm_nonneg _) (fourier_bound _ _) _
      _ = σ.real univ*(μ.real univ)^2 := by rw [integral_const,smul_eq_mul]
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hσmass) (sq_nonneg (μ.real univ)),
        mul_le_mul_of_nonneg_right hμmass (measureReal_nonneg : 0 ≤ μ.real univ)]
  have H := sum_bands hG hN hJ (radialEnergy μ σ) (radialEnergy_nonneg μ σ)
  apply H.trans ((add_le_add base (Finset.sum_le_sum fun j hj => mid j (Finset.mem_range.mp hj))).trans_eq ?_)
  simp [K]; ring

/-- The finite positive meshes in the statement of B3 and B4. -/
def paperMesh (d : ℝ) (J j : ℕ) : ℝ := d^((j:ℝ)/J)

def stripConstant (J : ℕ) (S T A : ℝ) : ℝ :=
  4*(1+J*(96*Real.exp (2+2*S^2)*Real.pi^2*T^2*A))

/-- **Single pair in B5.** All quantities on the left are actual projected collision
masses. The bound is uniform in both strip translations, the scale and the physical
laws. The factor B is the common coefficient Δ^{s'} in B4. -/
theorem pair_strip_estimate (μ ν : Measure Plane) (σ : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure σ]
    {d S T A B D t : ℝ} {J : ℕ} (hd : 0 < d) (hd1 : d ≤ 1) (hJ : 0 < J)
    (hT : 1 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hσmass : σ.real univ ≤ 1) (hμmass : μ.real univ ≤ B) (hνmass : ν.real univ ≤ B)
    (hp : ∀ᵐ p ∂μ, p ∈ box 0 S) (hp' : ∀ᵐ p ∂ν, p ∈ box 0 S)
    (hθ : ∀ᵐ θ ∂σ, |θ| ≤ T)
    (hσ : ∀ j < J, ∀ x, σ.real (Icc x (x+paperMesh d J (j+1))) ≤ A*(paperMesh d J (j+1))^t)
    (hμ : ∀ j < J, ∀ z, μ.real (box z (paperMesh d J (j+1))) ≤ B*(paperMesh d J (j+1))^D)
    (hν : ∀ j < J, ∀ z, ν.real (box z (paperMesh d J (j+1))) ≤ B*(paperMesh d J (j+1))^D)
    (s u : ℝ) :
    ∫ θ, collision μ ν s u θ d ∂σ ≤ stripConstant J S T A *
      d^(min 1 (D+t-1) - 1/J) * B * (μ.real univ + ν.real univ) := by
  let N := ⌊d⁻¹⌋₊
  let G := (d^((J:ℝ)⁻¹))⁻¹
  let K := 96*Real.exp (2+2*S^2)*Real.pi^2*T^2*A
  have Jpos : 0 < (J:ℝ) := by exact_mod_cast hJ
  have hN : 0 < N := Nat.floor_pos.mpr ((one_le_inv₀ hd).mpr hd1)
  have Npos : 0 < (N:ℝ) := by exact_mod_cast hN
  have Nle : (N:ℝ) ≤ d⁻¹ := Nat.floor_le (inv_nonneg.mpr hd.le)
  have hG : 1 ≤ G := (one_le_inv₀ (Real.rpow_pos_of_pos hd _)).mpr
    (Real.rpow_le_one hd.le hd1 (inv_nonneg.mpr Jpos.le))
  have Geq : G^J = d⁻¹ := by dsimp [G]; rw [inv_pow,Real.rpow_inv_natCast_pow hd.le hJ.ne']
  have msh (j : ℕ) : mesh G j = paperMesh d J j := by
    dsimp [G,mesh,paperMesh]; rw [inv_pow,inv_inv,← Real.rpow_natCast,← Real.rpow_mul hd.le]
    congr 1; ring
  have Ncut : (N:ℝ)*d ≤ 1 := by simpa [hd.ne'] using mul_le_mul_of_nonneg_right Nle hd.le
  have ratio : 2/(N:ℝ) ≤ 4*d := by
    apply (div_le_iff₀ Npos).mpr
    have frac : d⁻¹ < (N:ℝ)+1 := Nat.lt_floor_add_one _
    have one : (1:ℝ) ≤ N := by exact_mod_cast hN
    have fx := mul_le_mul_of_nonneg_right (show d⁻¹ ≤ 2*(N:ℝ) by linarith) hd.le
    rw [inv_mul_cancel₀ hd.ne'] at fx; linarith
  have eσ : ∀ j < J, ∀ x, σ.real (Icc x (x+mesh G (j+1))) ≤ A*(mesh G (j+1))^t := by
    simpa only [msh] using hσ
  have upper (m : Measure Plane) [IsFiniteMeasure m] (hmass : m.real univ ≤ B)
      (hs : ∀ᵐ p ∂m, p ∈ box 0 S)
      (hm : ∀ j < J, ∀ z, m.real (box z (paperMesh d J (j+1))) ≤ B*(paperMesh d J (j+1))^D) :
      ∑ k ∈ integers N, radialEnergy m σ k ≤ (1+J*K*G*growth G J D t)*B*m.real univ := by
    apply radial_mesh_energy m σ hG hJ (Geq ▸ Nle) hT hA hB hσmass hmass hs hθ eσ
    simpa only [msh] using hm
  have E := add_le_add (upper μ hμmass hp hμ) (upper ν hνmass hp' hν)
  let V := growth G J D t
  let M := μ.real univ + ν.real univ
  have hi : 1 ≤ V := le_max_left _ _
  have Vpos : 0 ≤ V := zero_le_one.trans hi
  have Mpos : 0 ≤ M := add_nonneg measureReal_nonneg measureReal_nonneg
  have Kpos : 0 ≤ K := by dsimp [K]; positivity
  have cost : d*G*V = d^(min 1 (D+t-1)-1/(J:ℝ)) := by
    have dmesh : mesh G J = d := by rw [msh,paperMesh,div_self Jpos.ne',Real.rpow_one]
    dsimp only [V,growth]; rw [dmesh]
    have rr : G = d^(-(1/(J:ℝ))) := by rw [Real.rpow_neg hd.le,one_div]
    rw [rr]
    by_cases pos : 0 ≤ D+t-2
    · rw [max_eq_left (Real.rpow_le_one hd.le hd1 pos),mul_one,min_eq_left (by linarith),
        Real.rpow_sub hd,Real.rpow_one,Real.rpow_neg hd.le]
      rfl
    · rw [max_eq_right (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (le_of_not_ge pos)),
        min_eq_right (by linarith)]
      calc
        _ = (d^((1:ℝ) + -(1/(J:ℝ)))) * d^(D+t-2) := by rw [Real.rpow_add hd,Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hd]; congr 1; ring
  apply (mean_collision_fourier μ ν σ s u hN Ncut).trans
  calc
    _ ≤ (2/N)*((1+J*K*G*V)*B*M) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [M,V,mul_add] using E
    _ ≤ (4*d)*((1+J*K*G*V)*B*M) := mul_le_mul_of_nonneg_right ratio (by positivity)
    _ ≤ 4*(1+J*K)*(d*G*V)*B*M := by
      have gv := one_le_mul_of_one_le_of_one_le hG hi
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left gv hd.le) hB) Mpos
      nlinarith only [hh]
    _ = _ := by rw [cost]; rfl

end Weierstrass.StripProof
