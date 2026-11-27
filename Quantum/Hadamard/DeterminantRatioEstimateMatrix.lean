import Quantum.Hadamard.DeterminantRatioEstimate

/-! Converting the determinant estimate into a statement about real symmetric
matrices with a prescribed diagonal and bounded off-diagonal entries. -/

open scoped BigOperators
open Matrix

namespace Hadamard.DeterminantRatio

variable {I : Type*} [Fintype I] [DecidableEq I] {E : Matrix I I ℝ}

theorem trace_sq_eq_sum_sq_eigenvalues (herm : E.IsHermitian) :
    (E^2).trace = ∑ i, (herm.eigenvalues i)^2 := by
  let u := herm.eigenvectorUnitary
  let D := diagonal herm.eigenvalues
  let α := Unitary.conjStarAlgAut ℝ (Matrix I I ℝ) u
  have hd : E = α D := herm.spectral_theorem
  calc
    (E^2).trace = ((α D)^2).trace := congrArg (fun A : Matrix I I ℝ ↦ (A^2).trace) hd
    _ = (α (D^2)).trace := by rw [map_pow]
    _ = (D^2).trace := trace_units_conj (Unitary.toUnits u) _
    _ = _ := by simp [D, diagonal_pow]

theorem det_shift_eq_prod (herm : E.IsHermitian) (n : ℝ) :
    (n • (1 : Matrix I I ℝ) + E).det = ∏ i, (n + herm.eigenvalues i) := by
  let u := herm.eigenvectorUnitary
  let D := diagonal herm.eigenvalues
  let α := Unitary.conjStarAlgAut ℝ (Matrix I I ℝ) u
  have hd : E = α D := herm.spectral_theorem
  have scalar : α (n • (1 : Matrix I I ℝ)) = n • 1 := by rw [map_smul, map_one]
  calc
    _ = (n • (1 : Matrix I I ℝ) + α D).det := congrArg (fun A : Matrix I I ℝ ↦ (n • 1 + A).det) hd
    _ = (α (n • (1 : Matrix I I ℝ) + D)).det := by rw [map_add, scalar]
    _ = (n • (1 : Matrix I I ℝ) + D).det := det_units_conj (Unitary.toUnits u) _
    _ = _ := by simp [D, smul_one_eq_diagonal, diagonal_add]

/-- A uniform determinant bound for any real symmetric Gram block with common
diagonal `n=2*(k+1)`, off-diagonal entries of absolute value at most two, and
smallest eigenvalue of the deviation matrix at least `-n/13`. -/
theorem four_fifths_of_symmetric_entries (k : ℕ) (hk : 0 < k)
    (card : Fintype.card I = k+1) (herm : E.IsHermitian) (diag : ∀ i, E i i = 0)
    (off : ∀ i j, i ≠ j → E i j ^ 2 ≤ 4)
    (lo : ∀ i, -(2*((k:ℝ)+1))/13 ≤ herm.eigenvalues i) :
    (4/5:ℝ) * (2 * (2*((k:ℝ)+1)) - 2) * (2*((k:ℝ)+1)-2)^k ≤
      ((2*((k:ℝ)+1)) • (1 : Matrix I I ℝ) + E).det := by
  have mean : ∑ i, herm.eigenvalues i = 0 := by
    calc
      _ = E.trace := herm.trace_eq_sum_eigenvalues.symm
      _ = _ := by simp [Matrix.trace, Matrix.diag, diag]
  have row (i : I) : ∑ j, E i j * E j i ≤ 4*(k:ℝ) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), diag i, zero_mul, add_zero]
    calc
      _ ≤ ∑ _j ∈ Finset.univ.erase i, (4:ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        have hs : E j i = E i j := by simpa using herm.apply i j
        rw [hs, ← sq]
        exact off i j hji.symm
      _ = _ := by simp [Finset.card_erase_of_mem, card]; ring
  have moment : ∑ i, (herm.eigenvalues i)^2 ≤ 4*(k:ℝ)*((k:ℝ)+1) := by
    calc
      _ = (E^2).trace := (trace_sq_eq_sum_sq_eigenvalues herm).symm
      _ = ∑ i, ∑ j, E i j * E j i := by simp [Matrix.trace, Matrix.diag, sq, Matrix.mul_apply]
      _ ≤ ∑ _i : I, 4*(k:ℝ) := Finset.sum_le_sum fun i _ ↦ row i
      _ = _ := by simp [card]; ring
  rw [det_shift_eq_prod herm]
  exact four_fifths_gram_block k hk card _ mean moment lo

#print axioms four_fifths_of_symmetric_entries

/-- A positive semidefinite scalar shift is a lower bound on every eigenvalue. -/
theorem eigenvalue_lower_of_shift (herm : E.IsHermitian) {s : ℝ}
    (hp : (s • (1 : Matrix I I ℝ) + E).PosSemidef) (i : I) : -s ≤ herm.eigenvalues i := by
  let u := herm.eigenvectorUnitary
  let α := Unitary.conjStarAlgAut ℝ (Matrix I I ℝ) (star u)
  have pos : (α (s • (1 : Matrix I I ℝ) + E)).PosSemidef :=
    hp.conjTranspose_mul_mul_same (u : Matrix I I ℝ)
  have hd : α E = diagonal herm.eigenvalues := herm.conjStarAlgAut_star_eigenvectorUnitary
  rw [map_add, map_smul, map_one, hd, smul_one_eq_diagonal, diagonal_add] at pos
  have hi := posSemidef_diagonal_iff.mp pos i
  linarith

/-- Recover a determinant bound from the two diagonal blocks of a real Gram
matrix. The block dimensions may differ. -/
theorem abs_det_of_gram_blocks {J : Type*} [Fintype J] [DecidableEq J]
    (M : Matrix (I ⊕ J) (I ⊕ J) ℝ) (P : Matrix I I ℝ) (Q : Matrix J J ℝ)
    (gram : M * M.transpose = fromBlocks P 0 0 Q) {w : ℝ} (hw : 0 ≤ w)
    (hp : w ≤ P.det) (hq : w ≤ Q.det) : w ≤ |M.det| := by
  have h := congrArg Matrix.det gram
  have he : M.det^2 = P.det*Q.det := by simpa [sq, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁] using h
  apply (sq_le_sq₀ hw (abs_nonneg _)).mp
  rw [sq_abs, he, sq]
  exact mul_le_mul hp hq hw (hw.trans hp)

end Hadamard.DeterminantRatio
