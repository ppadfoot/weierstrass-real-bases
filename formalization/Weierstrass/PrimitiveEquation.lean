module

public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.AdjoinRoot

/-! The primitive polynomial relation of an algebraic real base, normalized
to have positive constant coefficient. All integer recurrence relations vanishing
at the base are multiples of this polynomial by Gauss's lemma. -/
@[expose] public noncomputable section
open Polynomial
namespace Weierstrass

structure PrimitiveEquation (b : ℝ) where
  P : ℤ[X]
  primitive : P.IsPrimitive
  irreducible : Irreducible (P.map (algebraMap ℤ ℚ))
  root : aeval b P = 0
  constant_pos : 0 < P.coeff 0
  degree_pos : 0 < P.natDegree

private theorem irreducible_integer_root {b : ℝ} (hb : IsAlgebraic ℤ b) :
    ∃ P : ℤ[X], Irreducible P ∧ aeval b P = 0 := by
  obtain ⟨Q,Q0,root⟩ := hb
  let A (p : ℤ[X]) := p ≠ 0 → aeval b p=0 → ∃ P : ℤ[X], Irreducible P ∧ aeval b P=0
  have aux : A Q := by
    apply WfDvdMonoid.induction_on_irreducible (motive:=A)
    · intro h;exact (h rfl).elim
    · intro p hu _ h;exact ((hu.map (aeval b)).ne_zero h).elim
    · intro p i hp hi ih _ h
      rw [map_mul,mul_eq_zero] at h
      exact h.elim (fun h ↦ ⟨i,hi,h⟩) (ih hp)
  exact aux Q0 root

private theorem constant_nonzero_of_root {b : ℝ} (hb : b ≠ 0) {P : ℤ[X]} (hi : Irreducible P)
    (root : aeval b P = 0) : P.coeff 0 ≠ 0 := by
  intro h
  obtain ⟨Q,eq⟩ := X_dvd_iff.mpr h
  have unit : IsUnit Q := (hi.2 eq).resolve_left irreducible_X.not_isUnit
  rw [eq,map_mul,aeval_X] at root
  exact (mul_ne_zero hb (unit.map (aeval b)).ne_zero) root

/-- Every algebraic nonzero real base admits this normalized recurrence,
including bases that are not algebraic integers. -/
theorem primitiveEquation_nonempty {b : ℝ} (hb : b ≠ 0) (alg : IsAlgebraic ℤ b) : Nonempty (PrimitiveEquation b) := by
  obtain ⟨Q,ir,root⟩ := irreducible_integer_root alg
  have c := constant_nonzero_of_root hb ir root
  have data : ∃ P : ℤ[X], Irreducible P ∧ aeval b P=0 ∧ 0 < P.coeff 0 := by
    rcases lt_or_gt_of_ne c with h|h
    · have irr : Irreducible ((-1:ℤ[X])*Q) := irreducible_mul_iff.mpr (Or.inr ⟨ir,isUnit_neg_one⟩)
      exact ⟨-Q,by simpa only [neg_one_mul] using irr,by simp [root],by rw [coeff_neg];omega⟩
    · exact ⟨Q,ir,root,h⟩
  obtain ⟨P,irr,eq,pos⟩ := data
  have deg : P.natDegree ≠ 0 := by
    intro h
    have f := congrArg (aeval b) (eq_C_of_natDegree_eq_zero h)
    rw [eq,aeval_C] at f
    exact (ne_of_gt (show 0 < algebraMap ℤ ℝ (P.coeff 0) by change 0 < (P.coeff 0:ℝ);exact_mod_cast pos)) f.symm
  have prim := irr.isPrimitive deg
  exact ⟨⟨P,prim,(Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast prim).mp irr,eq,pos,Nat.pos_of_ne_zero deg⟩⟩

namespace PrimitiveEquation

def p {b : ℝ} (E : PrimitiveEquation b) := (E.P.coeff 0).toNat

def d {b : ℝ} (E : PrimitiveEquation b) := E.P.natDegree-1

def a {b : ℝ} (E : PrimitiveEquation b) (k : ℕ) := E.P.coeff (k+1)

theorem constant {b : ℝ} (E : PrimitiveEquation b) : (E.p:ℤ)=E.P.coeff 0 := Int.toNat_of_nonneg E.constant_pos.le

theorem degree {b : ℝ} (E : PrimitiveEquation b) : E.d+1=E.P.natDegree := Nat.sub_add_cancel E.degree_pos

theorem leading {b : ℝ} (E : PrimitiveEquation b) : E.a E.d ≠ 0 := by
  rw [a,E.degree,coeff_natDegree];exact leadingCoeff_ne_zero.mpr E.primitive.ne_zero

theorem recurrence_polynomial {b : ℝ} (E : PrimitiveEquation b) : E.P = C (E.p:ℤ)+
    ∑ k ∈ Finset.range (E.d+1), monomial (k+1) (E.a k) := by
  rw [E.constant,E.degree]
  calc
    E.P = ∑ k ∈ Finset.range (E.P.natDegree+1), monomial k (E.P.coeff k) := E.P.as_sum_range
    _ = _ := by rw [Finset.sum_range_succ'];simp only [monomial_zero_left,a,add_comm]

theorem polynomial_relation {b : ℝ} (E : PrimitiveEquation b) :
    (E.p:ℝ)+b*∑ k ∈ Finset.range (E.d+1), (E.a k:ℝ)*b^k = 0 := by
  have eq := E.root
  conv at eq => lhs;arg 2;rw [E.recurrence_polynomial]
  simp only [map_add,map_sum,aeval_C,aeval_monomial,pow_succ] at eq
  change (E.p:ℝ)+∑ k ∈ Finset.range (E.d+1), (E.a k:ℝ)*(b^k*b) = 0 at eq
  rw [Finset.mul_sum];convert eq using 1
  congr 1;apply Finset.sum_congr rfl;intro i _;ring

/-- The annihilator consists exactly of the integral multiples of the
primitive polynomial, including at a nonmonic algebraic base. -/
theorem annihilator {b : ℝ} (E : PrimitiveEquation b) (Q : ℤ[X]) : aeval b Q=0 ↔ E.P ∣ Q := by
  constructor
  · intro h
    let f := E.P.map (algebraMap ℤ ℚ)
    have rm : aeval b f = 0 := (aeval_map_algebraMap ℚ b E.P).trans E.root
    have hmin := minpoly.eq_of_irreducible E.irreducible rm
    have dv : f ∣ minpoly ℚ b := ⟨_,hmin.symm⟩
    apply E.primitive.dvd_of_fraction_map_dvd_fraction_map (K:=ℚ)
    exact dv.trans (minpoly.dvd ℚ b ((aeval_map_algebraMap ℚ b Q).trans h))
  · rintro ⟨q,rfl⟩;simp [E.root]

end PrimitiveEquation
end Weierstrass
