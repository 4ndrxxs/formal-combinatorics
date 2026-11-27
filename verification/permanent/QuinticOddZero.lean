import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic

/-! A polynomial with a simple zero at zero cannot become the square of a
rational function. The lowest degrees give a parity contradiction. -/

namespace QuinticPencil
open Polynomial
variable {K : Type*} [Field K]

theorem rational_nonsquare_of_simple_zero (p : K[X]) (atZero : p.coeff 0 = 0)
    (slope : p.coeff 1 ≠ 0) : ¬ IsSquare (algebraMap K[X] (RatFunc K) p) := by
  intro sq
  obtain ⟨w,hw⟩ := sq
  obtain ⟨a,b,hb,rep⟩ := IsFractionRing.div_surjective K[X] w
  let f := algebraMap K[X] (RatFunc K)
  have inj := RatFunc.algebraMap_injective K
  have bp : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have bf : f b ≠ 0 := fun eq ↦ bp (inj (eq.trans f.map_zero.symm))
  have pp : p ≠ 0 := fun eq ↦ slope (by simp [eq])
  have raw : f p * (f b * f b) = f a * f a := by
    change f a / f b = w at rep
    change f p = w * w at hw
    rw [hw,← rep]
    field_simp
  have cert : p*(b*b) = a*a := inj (by simpa only [map_mul] using raw)
  have ap : a ≠ 0 := by
    intro eq
    rw [eq,zero_mul] at cert
    exact (mul_ne_zero pp (mul_ne_zero bp bp)) cert
  have ord : p.natTrailingDegree = 1 := by
    apply le_antisymm (natTrailingDegree_le_of_ne_zero slope)
    apply le_natTrailingDegree pp
    intro n hn
    have e : n = 0 := by omega
    simpa [e] using atZero
  have mult := congrArg Polynomial.natTrailingDegree cert
  rw [natTrailingDegree_mul pp (mul_ne_zero bp bp),natTrailingDegree_mul bp bp,
    natTrailingDegree_mul ap ap,ord] at mult
  omega

#print axioms rational_nonsquare_of_simple_zero
end QuinticPencil
