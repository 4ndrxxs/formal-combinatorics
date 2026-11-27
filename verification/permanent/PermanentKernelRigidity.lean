import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A linear space of five-by-five matrices with vanishing three-by-three
permanents is supported in two rows if it has a member whose entries in
both rows are all one. The proof uses the cubic on the pencil through this
member and a second, arbitrary member of the space. -/

namespace PermanentKernelRigidity
abbrev Idx := Fin 5
abbrev Cell := Idx × Idx
variable {K : Type*} [Field K] [CharZero K]

/-- Expansion of the three-by-three permanent in its third row. -/
def three (A : Cell → K) (r s t i j k : Idx) : K :=
  (A (r,i) * A (s,j) + A (r,j) * A (s,i)) * A (t,k) +
  (A (r,i) * A (s,k) + A (r,k) * A (s,i)) * A (t,j) +
  (A (r,j) * A (s,k) + A (r,k) * A (s,j)) * A (t,i)

private theorem of_triple_sums (a : Idx → K)
    (h : ∀ i j k : Idx, i ≠ j → i ≠ k → j ≠ k → a i + a j + a k = 0) :
    ∀ i, a i = 0 := by
  have h012 := h 0 1 2 (by decide) (by decide) (by decide)
  have h013 := h 0 1 3 (by decide) (by decide) (by decide)
  have h014 := h 0 1 4 (by decide) (by decide) (by decide)
  have h023 := h 0 2 3 (by decide) (by decide) (by decide)
  have h123 := h 1 2 3 (by decide) (by decide) (by decide)
  have e23 : a 2 = a 3 := by linear_combination h012 - h013
  have e24 : a 2 = a 4 := by linear_combination h012 - h014
  have e01 : a 0 = a 1 := by linear_combination h023 - h123
  have z : 3 * a 2 = 0 := by linear_combination 2 * h023 - h012 - e01 + 2 * e23
  have z2 : a 2 = 0 := (mul_eq_zero.mp z).resolve_left (by norm_num)
  have z0 : a 0 = 0 := by linear_combination h023 + e23 - 2 * z2
  intro i
  fin_cases i
  · exact z0
  · exact e01.symm.trans z0
  · exact z2
  · exact e23.symm.trans z2
  · exact e24.symm.trans z2

/-- The tangent equations force every further row to vanish identically. -/
theorem two_rows_rigid (L : Submodule K (Cell → K)) (r s : Idx)
    (van : ∀ A ∈ L, ∀ t : Idx, t ≠ r → t ≠ s → ∀ i j k : Idx,
      i ≠ j → i ≠ k → j ≠ k → three A r s t i j k = 0)
    {X : Cell → K} (hX : X ∈ L) (hr : ∀ j, X (r,j) = 1) (hs : ∀ j, X (s,j) = 1)
    {Y : Cell → K} (hY : Y ∈ L) (t : Idx) (tr : t ≠ r) (ts : t ≠ s) :
    ∀ i, Y (t,i) = 0 := by
  have xt : ∀ i, X (t,i) = 0 := by
    apply of_triple_sums (fun i ↦ X (t,i))
    intro i j k ij ik jk
    have h := van X hX t tr ts i j k ij ik jk
    simp only [three,hr,hs,one_mul] at h
    have he : 2 * (X (t,i) + X (t,j) + X (t,k)) = 0 := by linear_combination h
    exact (mul_eq_zero.mp he).resolve_left (by norm_num)
  apply of_triple_sums (fun i ↦ Y (t,i))
  intro i j k ij ik jk
  have plus := van (X+Y) (L.add_mem hX hY) t tr ts i j k ij ik jk
  have minus := van (X-Y) (L.sub_mem hX hY) t tr ts i j k ij ik jk
  have pure := van Y hY t tr ts i j k ij ik jk
  simp only [three, Pi.add_apply, Pi.sub_apply, hr, hs, xt, zero_add, zero_sub] at plus minus pure
  have he : 4 * (Y (t,i) + Y (t,j) + Y (t,k)) = 0 := by
    linear_combination plus - minus - 2 * pure
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

#print axioms two_rows_rigid
end PermanentKernelRigidity
