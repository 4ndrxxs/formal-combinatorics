import Quantum.Hadamard.ConferenceBitTrace
import Quantum.Hadamard.ConferenceCubicMatrix

/-! An integer trace certificate from row words implies the real determinant
bound for any symmetric conference matrix with the specified principal block. -/
open Matrix

namespace Hadamard.BitTrace

open Hadamard.DeterminantRatio

/-- An explicit integral principal block can be used directly to certify a
balanced real completion whenever its cubic trace meets the integer test. -/
theorem four_fifths_of_word_block (k : ℕ) (words : Fin (k+1) → ℕ)
    {C : Matrix (Fin (k+1) ⊕ Fin (k+1)) (Fin (k+1) ⊕ Fin (k+1)) ℝ}
    (size : 29≤2*(k:ℝ)+1) (hc : C.IsHermitian)
    (square : C*C=(2*(k:ℝ)+1) • (1 : Matrix _ _ ℝ))
    (diag : ∀ i, C i i=0) (off : ∀ i j, i≠j → C i j^2=1)
    (block : C.submatrix Sum.inl Sum.inl = (wordMatrix words-1).map (Int.castRingHom ℝ))
    (margin : let v : ℤ := (k:ℤ)+1
      0 ≤ 87*v^3+375*v*(4*v-3)+1000*((wordMatrix words-1)^3).trace-
        1110*(2*v-1)*(v-1)) :
    (4/5:ℝ)*ewBound k ≤ |(C+diagonal completionSign).det| := by
  apply balanced_four_fifths_cubic k (Fintype.card_fin _) (Fintype.card_fin _) size hc square diag off
  right
  dsimp only
  rw [block, ←Matrix.map_pow, ←AddMonoidHom.map_trace]
  dsimp only at margin
  have lift := Int.cast_nonneg (R := ℝ) margin
  push_cast at lift
  exact lift

#print axioms four_fifths_of_word_block

end Hadamard.BitTrace
