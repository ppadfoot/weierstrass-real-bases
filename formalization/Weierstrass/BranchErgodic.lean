module

public import Weierstrass.RayInformationTransport
public import Mathlib.Dynamics.Ergodic.Action.OfMinimal

/-! Every nonzero time shift of the physical phase group is ergodic. The dense
physical orbit contracts under the inverse shift, forcing invariance under
all of its translations in measure (Hopf's argument). -/
@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal symmDiff
namespace Weierstrass.Branch
local instance ergGroupMs (b : ℂ) : MeasurableSpace (complexPhaseGroup b) := borel _
local instance ergGroupBorel (b : ℂ) : BorelSpace (complexPhaseGroup b) := ⟨rfl⟩

private def leaf (B x : ℂ) : complexPhaseGroup B :=
  ⟨complexPhaseOrbit B x,(complexPhaseOrbit B).range.le_topologicalClosure ⟨x,rfl⟩⟩

private theorem leaf_cont (B : ℂ) : Continuous (leaf B) := by
  apply Continuous.subtype_mk;apply continuous_pi;intro j
  change Continuous (fun x : ℂ ↦ (↑((B^j*x).re) : UnitAddCircle))
  fun_prop

private theorem leaf_dense (B : ℂ) : DenseRange (leaf B) := by
  intro x
  rw [Topology.IsInducing.closure_eq_preimage_closure_image Topology.IsEmbedding.subtypeVal.isInducing]
  have eq : Subtype.val '' range (leaf B) = range (complexPhaseOrbit B) := by ext v;simp [leaf]
  rw [eq]
  exact x.property

private def time {B : ℂ} (hb : B ≠ 0) (n : ℤ) := inducedPhaseMap B B (shiftPhase n) (shiftPhase_group hb n)

private theorem time_leaf {B : ℂ} (hb : B ≠ 0) (n : ℤ) (x : ℂ) :
    time hb n (leaf B x)=leaf B (B^n*x) := by
  apply Subtype.ext;funext j
  change (↑((B^(j+n)*x).re) : UnitAddCircle)= ↑((B^j*(B^n*x)).re)
  rw [zpow_add₀ hb,mul_assoc]

private theorem time_pos {B : ℂ} (hB : 1< ‖B‖) (n : ℕ) (nn : 0<n) :
    Ergodic (time (norm_pos_iff.mp (zero_lt_one.trans hB)) (n:ℤ)) (complexPhaseHaar B) := by
  let G : Type := complexPhaseGroup B
  let μ := complexPhaseHaar B
  let hb := norm_pos_iff.mp (zero_lt_one.trans hB)
  let F := time hb (n:ℤ)
  have mf : MeasurePreserving F μ μ := shiftPhase_preserving hb n
  have _ : Measure.IsAddHaarMeasure μ := by unfold μ complexPhaseHaar;infer_instance
  let _ : MeasurableAdd₂ (complexPhaseGroup B) := ⟨by
    change @Measurable _ (complexPhaseGroup B) _ (borel _) _
    rw [←(Subtype.borelSpace (fun z : PhaseTorus ↦ z ∈ complexPhaseGroup B)).measurable_eq]
    apply Measurable.subtype_mk
    have mv : Measurable (fun z : complexPhaseGroup B ↦ z.val) := continuous_subtype_val.measurable
    exact (mv.comp measurable_fst).add (mv.comp measurable_snd)⟩
  let _ : MeasurableNeg (complexPhaseGroup B) := ⟨continuous_neg.measurable⟩
  refine ⟨mf,⟨?_⟩⟩
  intro S mS inv
  change F ⁻¹' S = S at inv
  let shift (x : G) := fun y : G ↦ x+y
  let disp (x : G) := μ ((shift x ⁻¹' S) ∆ S)
  have dInv (x : G) : disp (F x)=disp x := by
    have inv' (y : G) : F y∈S ↔ y∈S := Set.ext_iff.mp inv y
    have eq : F ⁻¹' ((shift (F x) ⁻¹' S) ∆ S) = (shift x ⁻¹' S) ∆ S := by
      rw [preimage_symmDiff,inv]
      congr 1;ext y
      change F x+F y∈S ↔ x+y∈S
      rw [←map_add];exact inv' _
    have m : MeasurableSet ((shift (F x) ⁻¹' S) ∆ S) := ((measurable_const.add measurable_id) mS).symmDiff mS
    exact (mf.measure_preimage m.nullMeasurableSet).symm.trans (congrArg μ eq)
  apply aeconst_of_dense_setOfPred_preimage_vadd_ae (M:=G) (μ:=μ) mS.nullMeasurableSet
  apply (leaf_dense B).mono
  rintro _ ⟨x,rfl⟩
  change (shift (leaf B x) ⁻¹' S)=ᵐ[μ] S
  apply measure_symmDiff_eq_zero_iff.mp
  let a := (B^n)⁻¹
  have an : ‖a‖ < 1 := by dsimp [a];rw [norm_inv,norm_pow];exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hB nn.ne')
  let u (k : ℕ) := leaf B (a^k*x)
  have decay : Tendsto u atTop (𝓝 0) := by
    have t := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one an).mul_const x
    convert ((leaf_cont B).tendsto 0).comp (by simpa only [zero_mul] using t) using 1
    · rfl
    · congr 1;apply Subtype.ext;exact (complexPhaseOrbit B).map_zero.symm
  have ref (k : ℕ) : F (u (k+1)) = u k := by
    dsimp [F,u];rw [time_leaf,zpow_natCast,pow_succ];congr 1
    dsimp [a];field_simp
  have const (k : ℕ) : disp (u k)=disp (leaf B x) := by
    induction k with
    | zero => simp [u]
    | succ k ih => rw [←dInv (u (k+1)),ref,ih]
  let A : C(G × G,G) := ⟨fun v ↦ v.1+v.2,continuous_add⟩
  have lim := tendsto_measure_symmDiff_preimage_nhds_zero (A.curry.continuous.continuousAt.tendsto.comp decay)
    (μ:=μ) (ν:=μ) (Eventually.of_forall fun k ↦ measurePreserving_add_left μ (u k))
    (measurePreserving_add_left μ (0:G)) mS.nullMeasurableSet (measure_ne_top _ _)
  have lim' : Tendsto (fun k : ℕ ↦ disp (u k)) atTop (𝓝 0) := by
    change Tendsto (fun k ↦ μ ((shift (u k) ⁻¹' S) ∆ ((fun y : G ↦ 0+y) ⁻¹' S))) atTop (𝓝 0) at lim
    rw [show ((fun y : G ↦ 0+y) ⁻¹' S)=S by ext y;change 0+y∈S ↔ y∈S;rw [zero_add]] at lim
    exact lim
  simp_rw [const] at lim'
  exact tendsto_nhds_unique tendsto_const_nhds lim'

/-- Total ergodicity for each expanding complex base, hence in particular
for the real algebraic bases of Appendix B. -/
theorem phase_shift_ergodic {B : ℂ} (hB : 1< ‖B‖) (n : ℤ) (hn : n ≠ 0) :
    Ergodic (inducedPhaseMap B B (shiftPhase n) (shiftPhase_group (norm_pos_iff.mp (zero_lt_one.trans hB)) n))
      (complexPhaseHaar B) := by
  let hb := norm_pos_iff.mp (zero_lt_one.trans hB)
  cases n with
  | ofNat k => exact time_pos hB k (Nat.pos_of_ne_zero (by intro z;subst k;exact hn rfl))
  | negSucc k =>
    refine ⟨shiftPhase_preserving hb _,⟨?_⟩⟩
    intro S mS inv
    apply (time_pos hB (k+1) (by omega)).aeconst_set mS
    ext z
    have h := Set.ext_iff.mp inv (time hb (↑(k+1):ℤ) z)
    change time hb (Int.negSucc k) (time hb ((k+1:ℕ):ℤ) z)∈S ↔ time hb ((k+1:ℕ):ℤ) z∈S at h
    have eq : time hb (Int.negSucc k) (time hb ((k+1:ℕ):ℤ) z)=z := by
      apply Subtype.ext;funext j
      change z.val ((j+Int.negSucc k)+((k+1:ℕ):ℤ)) = z.val j
      apply congrArg z.val;omega
    rw [eq] at h;exact h.symm

end Weierstrass.Branch
