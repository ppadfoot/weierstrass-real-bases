module

public import Weierstrass.DescentMass
public import Weierstrass.DescentInheritance
public import Weierstrass.StripAngular

/-! The actual expected number of bad physical blocks, for each finite depth. -/
@[expose] public noncomputable section
open Set MeasureTheory Filter Weierstrass.CriticalRay Weierstrass.StripProof
open scoped BigOperators ENNReal Topology
namespace Weierstrass.Descent
local instance countsGroupMeasure (B : ℂ) : MeasurableSpace (complexPhaseGroup B) := borel _
local instance countsGroupBorel (B : ℂ) : BorelSpace (complexPhaseGroup B) := ⟨rfl⟩

def badCount (v : List Bool) : ℝ≥0∞ := (v.map (fun a ↦ if a then (1:ℝ≥0∞) else 0)).sum

theorem badCount_fin {k : ℕ} (v : Fin k → Bool) : badCount (List.ofFn v) =
    (Finset.univ.filter (fun i ↦ v i=true)).card := by
  unfold badCount;rw [List.map_ofFn,List.sum_ofFn];exact Finset.sum_boole _ _

def countMass (b g ρ θ : ℝ) (n : ℕ) (e : ℤ → ℝ) (k : ℕ) (T : ℝ) (p : RayParameters) (z : PhaseTorus) : ℝ≥0∞ :=
  ∑ v : Fin k → Bool, badCount (List.ofFn v)*wordLaw b g ρ θ n e (List.ofFn v) T p z univ

theorem countMass_measurable {b g : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1) (hbg : 1 < b*g)
    (ρ θ : ℝ) (n : ℕ) (e : ℤ → ℝ) (k : ℕ) (T : ℝ) {p : RayParameters}
    (hc : ∀ j, |p.1 j| ≤ 1) (hd : ∀ j, |p.2 j| ≤ 1) : Measurable (countMass b g ρ θ n e k T p) :=
  Finset.measurable_fun_sum _ (fun i _ ↦ measurable_const.mul ((Measure.measurable_coe MeasurableSet.univ).comp
    (measurable_wordLaw hb hg hg1 hbg ρ θ n e (List.ofFn i) T hc hd)))

theorem mass_cons (b g ρ θ : ℝ) (n : ℕ) (e : ℤ → ℝ) (v : List Bool) (a : Bool) (T : ℝ) (p : RayParameters) (z : PhaseTorus) :
    let N := arity b T n
    wordLaw b g ρ θ n e (a::v) T p z univ = ∑ i : Fin N,
      ENNReal.ofReal (N:ℝ)⁻¹*(if badCell b g ρ T θ p e z n i = a then
        wordLaw b g ρ θ n e v (childLength b T n N) (shiftedParameters p n) (physicalEnvironment b p.2 z n (anchor T i)) univ else 0) := by
  intro N;rw [wordLaw,Measure.finsetSum_apply];apply Finset.sum_congr rfl;intro i _
  rw [Measure.smul_apply,smul_eq_mul,Measure.map_apply (show Measurable (pushChild b g T p z i n) from
      measurable_const.add (measurable_const.mul measurable_id)) MeasurableSet.univ,preimage_univ]
  split <;> rfl

private theorem collapse_count {ι : Type*} [Fintype ι] (bad : ι → Bool) (s : ℝ≥0∞) (k : ℕ)
    (q : ι → (Fin k → Bool) → ℝ≥0∞) (hq : ∀ i, ∑ v, q i v=1) :
    (∑ a : Bool, ∑ v : Fin k → Bool, badCount (a::List.ofFn v)*
      (∑ i : ι, s*(if bad i = a then q i v else 0))) =
    (∑ i : ι, if bad i = true then s else 0) + ∑ i : ι, s*(∑ v : Fin k → Bool, badCount (List.ofFn v)*q i v) := by
  calc
    _ = ∑ i : ι, ∑ a : Bool, ∑ v : Fin k → Bool, badCount (a::List.ofFn v)*(s*(if bad i=a then q i v else 0)) := by
      simp only [Finset.mul_sum]
      trans ∑ a : Bool, ∑ i : ι, ∑ v : Fin k → Bool, badCount (a::List.ofFn v)*(s*(if bad i=a then q i v else 0))
      · exact Finset.sum_congr rfl (fun _ _ ↦ Finset.sum_comm)
      · exact Finset.sum_comm
    _ = ∑ i : ι, ((if bad i=true then s else 0)+s*(∑ v : Fin k → Bool, badCount (List.ofFn v)*q i v)) := by
      apply Finset.sum_congr rfl;intro i _
      have val (v : Fin k → Bool) : badCount (true::List.ofFn v) = 1+badCount (List.ofFn v) := by simp [badCount]
      have val0 (v : Fin k → Bool) : badCount (false::List.ofFn v) = badCount (List.ofFn v) := by simp [badCount]
      cases bad i
      · simp only [Fintype.sum_bool,val0,Bool.false_eq_true,if_false,if_true,mul_zero,Finset.sum_const_zero,zero_add]
        rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro v _;ring
      · simp only [Fintype.sum_bool,val,Bool.true_eq_false,if_false,if_true,mul_zero,Finset.sum_const_zero,add_zero,
          add_mul,one_mul,Finset.sum_add_distrib,←Finset.mul_sum,hq,mul_one]
        congr 1;rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro v _;ring
    _ = _ := Finset.sum_add_distrib

theorem count_step {b g : ℝ} (hb : 0 < b) (hg : 0 < g) (hg1 : g < 1) (hbg : 1 < b*g)
    (ρ θ : ℝ) (n : ℕ) (e : ℤ → ℝ) (k : ℕ) (T : ℝ) {p : RayParameters}
    (hc : ∀ j, |p.1 j| ≤ 1) (hd : ∀ j, |p.2 j| ≤ 1) (z : PhaseTorus) :
    let N := arity b T n
    countMass b g ρ θ n e (k+1) T p z = badShare b g ρ T θ n N p e z + ∑ i : Fin N, ENNReal.ofReal (N:ℝ)⁻¹ *
      countMass b g ρ θ n e k (childLength b T n N) (shiftedParameters p n) (physicalEnvironment b p.2 z n (anchor T i)) := by
  intro N
  let T' := childLength b T n N
  let P := shiftedParameters p n
  let env (i : Fin N) := physicalEnvironment b p.2 z n (anchor T i)
  let q (i : Fin N) (v : Fin k → Bool) := wordLaw b g ρ θ n e (List.ofFn v) T' P (env i) univ
  have hq (i : Fin N) : ∑ v,q i v=1 := by
    have tr := congrArg (fun μ : Measure ℝ ↦ μ univ) (sum_wordLaw hb hg hg1 hbg ρ θ n e k T' (p:=P)
      (fun j ↦ hc (j+n)) (fun j ↦ hd (j+n)) (env i))
    simpa only [q,Measure.finsetSum_apply,measure_univ] using tr
  unfold countMass;rw [word_sum_succ k (fun v ↦ badCount v*wordLaw b g ρ θ n e v T p z univ)]
  simp_rw [mass_cons];exact collapse_count _ _ _ q hq

end Weierstrass.Descent
