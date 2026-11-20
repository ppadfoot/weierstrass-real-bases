module

public import Weierstrass.BranchExtension
public import Weierstrass.BranchSecants
public import Weierstrass.PrimitiveEquation

/-! Conditional randomization on the original phase group using a deterministic
right extension and an independent random past. -/
@[expose] public noncomputable section
open Set MeasureTheory Weierstrass.Predecessor
open scoped BigOperators ENNReal
namespace Weierstrass.Branch
local instance branchHaarMeasurable (b : ℝ) : MeasurableSpace (phaseGroup b) := borel _
local instance branchHaarBorel (b : ℝ) : BorelSpace (phaseGroup b) := ⟨rfl⟩

theorem positive_digits {b : ℝ} (E : PrimitiveEquation b) : 0 < E.p := by exact_mod_cast E.constant.symm ▸ E.constant_pos

def auxiliary {b : ℝ} (hb : b ≠ 0) (E : PrimitiveEquation b) (w : Fin (E.d+1) → UnitAddCircle) (x : ℝ) : phaseGroup b :=
  ⟨twoSided (E.d+1) E.a (centralLift w) (uniformCode E.p (positive_digits E) x),
    twoSided_mem hb (positive_digits E) (E.d+1) E.a E.leading
      (fun Q hQ ↦ by rw [characteristic_form,←E.recurrence_polynomial];exact (E.annihilator Q).mp hQ) _ _⟩

theorem measurable_rightLift {X : Type*} [MeasurableSpace X] (d : ℕ) (A : ℕ → ℤ) (w : X → ℕ → ℝ)
    (mw : ∀ i, Measurable (fun x ↦ w x i)) (n : ℕ) : Measurable (fun x ↦ rightLift d A (w x) n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < d
    · simpa only [rightLift_start _ _ _ hn] using mw n
    · simp_rw [rightLift.eq_1 (m:=n),if_neg hn]
      apply Measurable.div_const;apply Measurable.neg;apply Finset.measurable_fun_sum
      intro j _;exact measurable_const.mul (ih (n-d+j) (by omega))

theorem auxiliary_measurable {b : ℝ} (hb : b ≠ 0) (E : PrimitiveEquation b) :
    Measurable (Function.uncurry (auxiliary hb E)) := by
  let V := (Fin (E.d+1) → UnitAddCircle) × ℝ
  let f (v : V) (i : ℕ) := centralLift v.1 i
  have mf (i : ℕ) : Measurable (fun v ↦ f v i) := (measurable_centralLift _ i).comp measurable_fst
  change @Measurable V (phaseGroup b) _ (borel _) _
  rw [←(Subtype.borelSpace (fun z : PhaseTorus ↦ z ∈ phaseGroup b)).measurable_eq]
  apply Measurable.subtype_mk;apply measurable_pi_lambda;intro i;apply AddCircle.measurable_mk'.comp
  cases i with
  | ofNat k => exact measurable_rightLift _ _ f mf k
  | negSucc k => exact measurable_pathState (E.d+1) (fun j ↦ (E.a j:ℝ)) E.p f (fun v : V ↦ uniformCode E.p (positive_digits E) v.2) mf (fun j ↦ (measurable_uniformCode E.p (positive_digits E) j).comp measurable_snd) (k+1) 0

def centerAndSeed (d : ℕ) := (volume : Measure (Fin d → UnitAddCircle)).prod unitLaw

instance (d : ℕ) : IsProbabilityMeasure (centerAndSeed d) := by
  let _ : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  unfold centerAndSeed;infer_instance

/-- The resampled environment has exactly the original Haar law. Given the
old environment and central block, the entire new future is fixed, while
the new past is computed with independent uniformly distributed digits. -/
theorem auxiliary_haar {b : ℝ} (hb : b ≠ 0) (E : PrimitiveEquation b) :
    MeasurePreserving (fun v : phaseGroup b × ((Fin (E.d+1) → UnitAddCircle) × ℝ) ↦ v.1+auxiliary hb E v.2.1 v.2.2)
      ((phaseHaar b).prod (centerAndSeed (E.d+1))) (phaseHaar b) := by
  let _ : IsProbabilityMeasure (phaseHaar b) := ⟨phaseHaar_univ b⟩
  let _ : Measure.IsAddLeftInvariant (phaseHaar b) := by unfold phaseHaar;infer_instance
  let Y := Function.uncurry (auxiliary hb E)
  have mY : Measurable Y := auxiliary_measurable hb E
  let F (v : phaseGroup b × ((Fin (E.d+1) → UnitAddCircle) × ℝ)) := v.1+Y v.2
  have mz : Measurable (fun z : phaseGroup b ↦ z.val) := continuous_subtype_val.measurable
  have ma : Measurable (fun x : phaseGroup b × phaseGroup b ↦ x.1+x.2) := by
    change @Measurable _ (phaseGroup b) _ (borel _) _
    rw [←(Subtype.borelSpace (fun z : PhaseTorus ↦ z ∈ phaseGroup b)).measurable_eq]
    apply Measurable.subtype_mk
    exact (mz.comp measurable_fst).add (mz.comp measurable_snd)
  have mF : Measurable F := ma.comp (measurable_fst.prodMk (mY.comp measurable_snd))
  refine ⟨mF,?_⟩
  ext S mS
  change (((phaseHaar b).prod (centerAndSeed (E.d+1))).map F) S = _
  rw [Measure.map_apply mF mS,Measure.prod_apply_symm (mF mS)]
  have eq (x : (Fin (E.d+1) → UnitAddCircle) × ℝ) : phaseHaar b ((fun z ↦ (z,x)) ⁻¹' (F ⁻¹' S)) = phaseHaar b S := by
    change phaseHaar b ((·+Y x) ⁻¹' S)=phaseHaar b S
    exact measure_preimage_add_right (phaseHaar b) _ _
  simp_rw [eq];simp

def phaseLift (z : PhaseTorus) (j : ℤ) : ℝ := AddCircle.equivIco 1 0 (z j)

/-- The nonnegative part of the true bilateral increment is determined by
only the prescribed phase, the central block, and u. -/
def future (b l u : ℝ) (d p : ℕ) (a : ℕ → ℤ) (w : ℕ → ℝ) (z : PhaseTorus) :=
  ∑' k : ℕ, incrementTerm b l (fun j ↦ phaseLift z j+rightLift d (coefficient p a) w j.toNat) u k

def angularTail (z : PhaseTorus) (k : ℕ) := 2*Real.pi*phaseLift z (Int.negSucc k)

theorem increment_split {b l : ℝ} (hb : 1 < b) (hl : b⁻¹ < l) (hl1 : l < 1)
    (E : PrimitiveEquation b) (z : PhaseTorus) (w : Fin (E.d+1) → UnitAddCircle) (x u : ℝ) :
    circleIncrement b l (z+(auxiliary (zero_lt_one.trans hb).ne' E w x).val) u =
      future b l u (E.d+1) E.p E.a (centralLift w) z - u*(2*Real.pi*(b*l)⁻¹)*
        fullSecant (E.d+1) (fun k ↦ (E.a k:ℝ)) E.p (b*l)⁻¹ b⁻¹ (centralLift w) (angularTail z)
          (uniformCode E.p (positive_digits E) x) u := by
  let I := uniformCode E.p (positive_digits E) x
  let w' := centralLift w
  let z' (j : ℤ) := phaseLift z j+twoSidedLift (E.d+1) E.a w' I j
  let f := incrementTerm b l z' u
  have bz := zero_lt_one.trans hb
  have lz := (inv_pos.mpr bz).trans hl
  have ha : (fun j ↦ (↑(z' j):UnitAddCircle)) = z+(auxiliary bz.ne' E w x).val := by
    funext j;unfold z';rw [AddCircle.coe_add,show ((phaseLift z j:ℝ):UnitAddCircle)=z j from AddCircle.coe_equivIco];rfl
  have hs := summable_incrementTerm hb hl hl1 z' u
  rw [←ha,circleIncrement_of_real]
  change (∑' i : ℤ, f i)= _
  rw [tsum_of_nat_of_neg_add_one (hs.comp_injective Int.ofNat_injective) (hs.comp_injective (show Function.Injective (fun k : ℕ ↦ -((k:ℤ)+1)) by intro i j h;change -(↑i+1:ℤ) = -(↑j+1:ℤ) at h;omega))]
  rw [sub_eq_add_neg];congr 1
  unfold fullSecant
  rw [←neg_mul,←tsum_mul_left]
  apply tsum_congr;intro k
  let n := k+1
  let s := 2*Real.pi*pathState (E.d+1) (fun j ↦ (E.a j:ℝ)) E.p w' I (k+1) 0+angularTail z k
  let t := 2*Real.pi*(b⁻¹)^(k+1)*u
  have arg : 2*Real.pi*z' (-(↑k+1))=s := by
    change 2*Real.pi*(phaseLift z (Int.negSucc k)+pathState (E.d+1) (fun j ↦ (E.a j:ℝ)) E.p w' I (k+1) 0)=s
    unfold s angularTail;ring
  have inc : b^(-((k:ℤ)+1))=(b⁻¹)^(k+1) := by rw [←Nat.cast_add_one,zpow_neg,zpow_natCast,inv_pow]
  have powl : l^(-((k:ℤ)+1))=(l⁻¹)^(k+1) := by rw [←Nat.cast_add_one,zpow_neg,zpow_natCast,inv_pow]
  change l^(-((k:ℤ)+1))*(Real.cos (2*Real.pi*(z' (-(↑k+1))+_*u))-Real.cos _)=_
  rw [mul_add,arg,inc,show 2*Real.pi*((b⁻¹)^(k+1)*u)=t by dsimp [t];ring,←sineMean_mul,powl]
  change _ = _*((b*l)⁻¹^k*sineMean s t)
  dsimp only [t];rw [mul_inv_rev,mul_pow,pow_succ,pow_succ];ring

end Weierstrass.Branch
