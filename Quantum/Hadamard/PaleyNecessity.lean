import Quantum.Hadamard.ArithmeticNecessity

/-! Integral signed Gram divisibility and the standard determinant obstruction. -/
noncomputable section
namespace HadamardMod

theorem atOrder_of_integral {p n : ℕ} (h : IntegralSolution p n) : AtOrder p n := by
  obtain ⟨A,sign,gram⟩ := h
  let M : RowMatrix p (Fin n) := fun i j => (A i j : ZMod p)
  refine ⟨M,⟨?_,?_⟩⟩
  · intro i j
    rcases sign i j with h|h <;> simp [M,h,Sign]
  · intro i j ne
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (gram i j)
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,ite_eq_right ne,sub_zero,
      Int.cast_sum,Int.cast_mul,M] using h

theorem admissible_iff_even_or_square {p n : ℕ} :
    KuperbergAdmissible p n ↔ Even n ∨ IsSquare (n:ZMod p) := by
  unfold KuperbergAdmissible
  rw [Nat.even_iff]
  exact or_congr_right ⟨fun ⟨a,h⟩ => ⟨a, by simpa [pow_two] using h.symm⟩,
    fun ⟨a,h⟩ => ⟨a, by simpa [pow_two] using h.symm⟩⟩

theorem prime_integral_necessary {p n : ℕ} [Fact p.Prime] (h : IntegralSolution p n) :
    Even n ∨ IsSquare (n:ZMod p) :=
  admissible_iff_even_or_square.mp (necessary_admissible Fact.out (atOrder_of_integral h))

#print axioms prime_integral_necessary
end HadamardMod

