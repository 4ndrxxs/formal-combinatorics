import Quantum.Hadamard.ArithmeticDense
import Quantum.Hadamard.PaleyNecessity

namespace HadamardMod

/-- Every dot product of two sign words in even length is even. At an odd
modulus this supplies an additional factor two in the Gram divisibility. -/
theorem at_double_of_even {b n : ℕ} (odd : (2:ℕ).Coprime b) (hn : Even n)
    (H : AtOrder b n) : AtOrder (2*b) n := by
  classical
  obtain ⟨A,sign,gram⟩ := integer_gram H
  apply atOrder_of_integral
  refine ⟨A,sign,?_⟩
  intro i k
  have all (i j) : ((A i j:ℤ):ZMod 2)=1 := by
    rcases sign i j with h|h <;> rw [h] <;> decide
  have zero : (n:ZMod 2)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr (even_iff_two_dvd.mp hn)
  have even : (2:ℤ) ∣ (A*A.transpose) i k-(if i=k then (n:ℤ) else 0) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    rw [Matrix.mul_apply]
    push_cast
    by_cases h : i=k <;> simp [Matrix.transpose_apply,all,h,zero]
  exact_mod_cast odd.isCoprime.mul_dvd even (gram i k)

theorem at_doubled_order_four_modulus {b n : ℕ} (odd : (2:ℕ).Coprime b)
    (hn : Even n) (H : AtOrder b n) : AtOrder (4*b) (2*n) := by
  have U := at_mul_raise (t := 2) (m := 2*b) (order_two (2*(2*b)))
    (at_double_of_even odd hn H) (dvd_refl 2)
  simpa [show 2*(2*b)=4*b by ring] using U

#print axioms at_doubled_order_four_modulus
end HadamardMod
