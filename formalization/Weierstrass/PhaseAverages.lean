module

public import Weierstrass.PhaseDensity
public import Weierstrass.Lacunary
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Physical-scale orbit averages of finite characters and their uniform
closure on the bilateral phase torus. -/

@[expose] public noncomputable section
open Set Filter MeasureTheory TopologicalSpace Polynomial Complex
open scoped BigOperators Topology ComplexConjugate
namespace Weierstrass

def phaseCharacter (h : ℤ →₀ ℤ) : C(PhaseTorus,ℂ) where
  toFun z := (AddCircle.toCircle (Finsupp.linearCombination ℤ z h) : ℂ)
  continuous_toFun := by
    simp only [Finsupp.linearCombination_apply,Finsupp.sum]
    exact continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp
      (continuous_finsetSum _ (fun j _ ↦ (continuous_zsmul (h j)).comp (continuous_apply j))))

private theorem character_add_index (h k : ℤ →₀ ℤ) :
    phaseCharacter (h+k) = phaseCharacter h * phaseCharacter k := by
  ext z
  simp [phaseCharacter,AddCircle.toCircle_add]

private theorem character_neg_index (h : ℤ →₀ ℤ) :
    phaseCharacter (-h) = star (phaseCharacter h) := by
  ext z
  change (↑(AddCircle.toCircle ((Finsupp.linearCombination ℤ z) (-h))) : ℂ) =
    star (↑(AddCircle.toCircle ((Finsupp.linearCombination ℤ z) h)) : ℂ)
  rw [map_neg,AddCircle.toCircle_neg]
  exact Circle.coe_inv_eq_conj _

private theorem character_zero_index :
    phaseCharacter 0 = 1 := by
  ext z
  simp [phaseCharacter]

private def phaseCharacterAlgebra : StarSubalgebra ℂ C(PhaseTorus,ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range phaseCharacter)
  star_mem' := by
    change Algebra.adjoin ℂ (range phaseCharacter) ≤ star (Algebra.adjoin ℂ (range phaseCharacter))
    refine Algebra.adjoin_le ?_
    rintro _ ⟨h,rfl⟩
    exact Algebra.subset_adjoin ⟨-h,character_neg_index h⟩

theorem phaseCharacters_dense :
    (Submodule.span ℂ (range phaseCharacter)).topologicalClosure = ⊤ := by
  have span : phaseCharacterAlgebra.toSubalgebra.toSubmodule = Submodule.span ℂ (range phaseCharacter) := by
    apply Algebra.adjoin_eq_span_of_subset
    refine .trans (fun x ↦ Submonoid.closure_induction (fun _ ↦ id) ⟨0,character_zero_index⟩ ?_) Submodule.subset_span
    rintro _ _ _ _ ⟨m,rfl⟩ ⟨n,rfl⟩
    exact ⟨m+n,character_add_index m n⟩
  have sep : phaseCharacterAlgebra.SeparatesPoints := by
    intro z w h
    obtain ⟨i,hi⟩ : ∃ i, z i ≠ w i := by simpa [funext_iff] using h
    let v := Finsupp.single i (1:ℤ)
    refine ⟨_,⟨phaseCharacter v,Algebra.subset_adjoin ⟨_,rfl⟩,rfl⟩,?_⟩
    simp only [v,phaseCharacter,ContinuousMap.coe_mk,Finsupp.linearCombination_single,one_smul]
    exact fun he ↦ hi (AddCircle.injective_toCircle one_ne_zero (Subtype.ext he))
  rw [←span]
  exact congrArg (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints phaseCharacterAlgebra sep)

private theorem phaseCharacter_add (h : ℤ →₀ ℤ) (z w : PhaseTorus) :
    phaseCharacter h (z+w) = phaseCharacter h z * phaseCharacter h w := by
  simp [phaseCharacter,Finsupp.linearCombination_apply,Finsupp.sum,smul_add,
    Finset.sum_add_distrib,AddCircle.toCircle_add]

def phaseFrequency (b : ℝ) (h : ℤ →₀ ℤ) := ∑ i ∈ h.support, (h i : ℝ)*b^i

theorem phaseCharacter_orbit (b : ℝ) (h : ℤ →₀ ℤ) (x : ℝ) :
    phaseCharacter h (phaseOrbit b x) = Lacunary.wave (2*Real.pi*phaseFrequency b h) x := by
  have he := character_phaseOrbit b h.support h x
  change (AddCircle.toCircle (torusCharacter h.support h (phaseOrbit b x)) : ℂ) = _
  rw [he]
  have hh := fourier_coe_apply (T := (1:ℝ)) (n:=1) (x:=phaseFrequency b h * x)
  simp only [fourier_apply,one_zsmul] at hh
  change (AddCircle.toCircle (↑(phaseFrequency b h*x) : AddCircle (1:ℝ)) : ℂ) = _
  rw [hh,Lacunary.wave]
  congr 1
  push_cast
  ring

local instance averagesPhaseBorel (b : ℝ) : MeasurableSpace (phaseGroup b) := borel _

private theorem phaseCharacter_trivial {b : ℝ} {h : ℤ →₀ ℤ} (hd : phaseFrequency b h = 0)
    (z : phaseGroup b) : phaseCharacter h z.val = 1 := by
  have hclosed : IsClosed {w | phaseCharacter h w = 1} := isClosed_eq (phaseCharacter h).continuous continuous_const
  have hmem : z.val ∈ closure (Set.range (phaseOrbit b)) := z.property
  apply closure_minimal (t := {w | phaseCharacter h w = 1}) _ hclosed hmem
  rintro _ ⟨x,rfl⟩
  simp [phaseCharacter_orbit,hd,Lacunary.wave]

private theorem phaseCharacter_mean_zero {b : ℝ} {h : ℤ →₀ ℤ} (hd : phaseFrequency b h ≠ 0) :
    (∫ z : phaseGroup b, phaseCharacter h z.val ∂phaseHaar b) = 0 := by
  let _ : BorelSpace (phaseGroup b) := ⟨rfl⟩
  let _ : Measure.IsAddLeftInvariant (phaseHaar b) := by unfold phaseHaar; infer_instance
  let x := (2 * phaseFrequency b h)⁻¹
  let v : phaseGroup b := ⟨phaseOrbit b x, (phaseOrbit b).range.le_topologicalClosure ⟨x,rfl⟩⟩
  have nontriv : phaseCharacter h v.val ≠ 1 := by
    rw [show v.val=phaseOrbit b x from rfl,phaseCharacter_orbit,Lacunary.wave]
    have hx : (2*Real.pi*phaseFrequency b h:ℝ)*x = Real.pi := by dsimp [x]; field_simp
    rw [show ((↑(2*Real.pi*phaseFrequency b h):ℂ)*I*↑x) = (↑Real.pi : ℂ)*I by
      rw [mul_right_comm,←Complex.ofReal_mul,hx],Complex.exp_pi_mul_I]
    norm_num
  let J := ∫ z : phaseGroup b, phaseCharacter h z.val ∂phaseHaar b
  have inv : phaseCharacter h v.val * J = J := by
    have hinv := integral_add_left_eq_self (μ:=phaseHaar b)
      (fun z : phaseGroup b ↦ phaseCharacter h z.val) v
    change (∫ z : phaseGroup b, phaseCharacter h (v.val+z.val) ∂phaseHaar b) = J at hinv
    simp only [phaseCharacter_add,integral_const_mul] at hinv
    exact hinv
  by_contra hzero
  exact nontriv (mul_right_cancel₀ hzero (inv.trans (one_mul J).symm))

private def haarEvaluation (b : ℝ) (v : PhaseTorus) : C(PhaseTorus,ℂ) →L[ℂ] ℂ := by
  let _ : IsProbabilityMeasure (phaseHaar b) := ⟨phaseHaar_univ b⟩
  let _ : BorelSpace (phaseGroup b) := ⟨rfl⟩
  let p : C(phaseGroup b,PhaseTorus) := ⟨fun z ↦ v+z.val,continuous_const.add continuous_subtype_val⟩
  exact (L1.integralCLM' ℂ).comp ((ContinuousMap.toLp 1 (phaseHaar b) ℂ).comp (ContinuousMap.compCLM ℂ ℂ p))

private theorem haarEvaluation_apply (b : ℝ) (v : PhaseTorus) (f : C(PhaseTorus,ℂ)) :
    haarEvaluation b v f = ∫ z : phaseGroup b, f (v+z.val) ∂phaseHaar b := by
  let _ : IsProbabilityMeasure (phaseHaar b) := ⟨phaseHaar_univ b⟩
  let _ : BorelSpace (phaseGroup b) := ⟨rfl⟩
  let p : C(phaseGroup b,PhaseTorus) := ⟨fun z ↦ v+z.val,continuous_const.add continuous_subtype_val⟩
  rw [haarEvaluation, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← L1.integral_eq', L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (phaseHaar b) (𝕜:=ℂ) (p:=1) (f.comp p))

/-- Difference of empirical integration and its Haar coset mean at the same indices. -/
private def discrepancy (b : ℝ) (S : Finset ℕ) (θ ψ : ℕ → PhaseTorus) :
    C(PhaseTorus,ℂ) →L[ℂ] ℂ :=
  (S.card : ℂ)⁻¹ • ∑ i ∈ S, (ContinuousMap.evalCLM ℂ (θ i) - haarEvaluation b (ψ i))

private theorem discrepancy_apply (b : ℝ) (S : Finset ℕ) (θ ψ : ℕ → PhaseTorus)
    (f : C(PhaseTorus,ℂ)) :
    discrepancy b S θ ψ f = (S.card:ℂ)⁻¹ * ∑ i ∈ S,
      (f (θ i) - ∫ z : phaseGroup b, f (ψ i+z.val) ∂phaseHaar b) := by
  simp [discrepancy,haarEvaluation_apply,ContinuousMap.evalCLM]

private theorem discrepancy_bound (b : ℝ) (S : Finset ℕ) (θ ψ : ℕ → PhaseTorus)
    (f : C(PhaseTorus,ℂ)) : ‖discrepancy b S θ ψ f‖ ≤ 2*‖f‖ := by
  let _ : IsProbabilityMeasure (phaseHaar b) := ⟨phaseHaar_univ b⟩
  by_cases hS : S.card = 0
  · simp [discrepancy,hS]
  rw [discrepancy_apply,norm_mul,norm_inv,Complex.norm_natCast]
  have hs : 0 < (S.card:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hS
  apply (inv_mul_le_iff₀ hs).mpr
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _i ∈ S, (2*‖f‖) := by
      apply Finset.sum_le_sum
      intro i _
      have hI := norm_integral_le_of_norm_le_const (μ:=phaseHaar b)
        (f:=fun z : phaseGroup b ↦ f (ψ i+z.val)) (.of_forall fun z ↦ f.norm_coe_le_norm _)
      rw [probReal_univ,mul_one] at hI
      exact (norm_sub_le _ _).trans (by linarith [f.norm_coe_le_norm (θ i),hI])
    _ = _ := by simp [nsmul_eq_mul]

/-- Uniform boundedness for finite windows allows a single full-measure set of
inputs to work for every continuous test function. -/
private theorem discrepancy_dense_extension (b : ℝ) (S : ℕ → Finset ℕ) (θ ψ : ℕ → PhaseTorus)
    (onChars : ∀ h : ℤ →₀ ℤ, Tendsto (fun n ↦ discrepancy b (S n) θ ψ (phaseCharacter h))
      atTop (𝓝 0)) (f : C(PhaseTorus,ℂ)) :
    Tendsto (fun n ↦ discrepancy b (S n) θ ψ f) atTop (𝓝 0) := by
  have hon (v : C(PhaseTorus,ℂ)) (hv : v ∈ Submodule.span ℂ (range phaseCharacter)) :
      Tendsto (fun n ↦ discrepancy b (S n) θ ψ v) atTop (𝓝 0) := by
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨k,rfl⟩ := hx; exact onChars k
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add,add_zero] using hx.add hy
    | smul c x _ hx => simpa only [map_smul,smul_zero] using hx.const_smul c
  have hclosure : f ∈ closure ((Submodule.span ℂ (range phaseCharacter) : Submodule ℂ _) : Set _) := by
    change f ∈ (Submodule.span ℂ (range phaseCharacter)).topologicalClosure
    rw [phaseCharacters_dense]; trivial
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨v,hv,hd⟩ := Metric.mem_closure_iff.mp hclosure (ε/4) (by positivity)
  filter_upwards [(Metric.tendsto_nhds.mp (hon v hv)) (ε/2) (by positivity)] with n hn
  rw [dist_zero_right] at hn ⊢
  have split := (discrepancy b (S n) θ ψ).map_sub f v
  have hb := discrepancy_bound b (S n) θ ψ (f-v)
  rw [split] at hb
  rw [dist_eq_norm] at hd
  have tri : ‖discrepancy b (S n) θ ψ f‖ ≤
      ‖discrepancy b (S n) θ ψ f-discrepancy b (S n) θ ψ v‖+‖discrepancy b (S n) θ ψ v‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      (discrepancy b (S n) θ ψ f-discrepancy b (S n) θ ψ v) (discrepancy b (S n) θ ψ v)
  linarith

/-- Along windows whose endpoints have limiting ratios to their length, the
empirical means of every continuous phase observable agree asymptotically
with the corresponding means of the translated Haar integrals. Each prescribed
sequence is fixed before the Lebesgue-null exceptional set is chosen. -/
theorem phase_window_haar_comparison (b g : ℝ) (hg : 1 < g) (ψ : ℕ → PhaseTorus)
    (l r : ℕ → ℕ) (hl : Tendsto l atTop atTop) (hr : Tendsto r atTop atTop)
    (order : ∀ᶠ n in atTop, l n ≤ r n) {a d : ℝ}
    (ha : Tendsto (fun n ↦ (l n:ℝ)/((r n-l n:ℕ):ℝ)) atTop (𝓝 a))
    (hd : Tendsto (fun n ↦ (r n:ℝ)/((r n-l n:ℕ):ℝ)) atTop (𝓝 d)) (v : ℝ) :
    ∀ᵐ x ∂volume.restrict (Ioc v (v+1)), ∀ f : C(PhaseTorus,ℂ),
      Tendsto (fun n ↦ ((r n-l n:ℕ):ℂ)⁻¹ * ∑ j ∈ Finset.Ico (l n) (r n),
        (f (ψ j+phaseOrbit b (g^j*x)) -
          ∫ z : phaseGroup b, f (ψ j+z.val) ∂phaseHaar b)) atTop (𝓝 0) := by
  classical
  let _ : IsProbabilityMeasure (phaseHaar b) := ⟨phaseHaar_univ b⟩
  let θ (x : ℝ) (j : ℕ) := ψ j + phaseOrbit b (g^j*x)
  let S (n : ℕ) := Finset.Ico (l n) (r n)
  have each (h : ℤ →₀ ℤ) : ∀ᵐ x ∂volume.restrict (Ioc v (v+1)),
      Tendsto (fun n ↦ discrepancy b (S n) (θ x) ψ (phaseCharacter h)) atTop (𝓝 0) := by
    by_cases hz : phaseFrequency b h = 0
    · apply Eventually.of_forall
      intro x
      have hsame (i : ℕ) : phaseCharacter h (θ x i) -
          (∫ z : phaseGroup b, phaseCharacter h (ψ i+z.val) ∂phaseHaar b) = 0 := by
        have h₁ (z : phaseGroup b) := phaseCharacter_trivial hz z
        simp [θ,phaseCharacter_add,phaseCharacter_orbit,hz,Lacunary.wave,h₁]
      simpa only [discrepancy_apply,hsame,Finset.sum_const_zero,mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0:ℂ)) atTop (𝓝 0))
    · let D := 2*Real.pi*phaseFrequency b h
      let w (j : ℕ) := phaseCharacter h (ψ j)
      have hD : D ≠ 0 := mul_ne_zero (by positivity) hz
      have hw (j : ℕ) : ‖w j‖ = 1 := Circle.norm_coe _
      filter_upwards [Lacunary.average_tendsto_zero_ae hD hg w hw v] with x hx
      apply (Lacunary.window_of_prefix_limit D g w x hx l r hl hr order ha hd).congr'
      apply Eventually.of_forall
      intro n
      dsimp only
      rw [discrepancy_apply]
      simp only [S,Nat.card_Ico]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simp only [θ,phaseCharacter_add,phaseCharacter_orbit,integral_const_mul,
        phaseCharacter_mean_zero hz,mul_zero,sub_zero,Lacunary.term,Lacunary.wave,w,D]
      congr 2
      push_cast
      ring
  let _ : Countable (ℤ →₀ ℤ) := (Finsupp.graph_injective ℤ ℤ).countable
  filter_upwards [ae_all_iff.mpr each] with x hx
  intro f
  exact (discrepancy_dense_extension b S (θ x) ψ hx f).congr
    (by intro n; simp only [discrepancy_apply,S,θ,Nat.card_Ico])

end Weierstrass
