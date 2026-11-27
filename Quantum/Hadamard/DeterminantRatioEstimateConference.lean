import Quantum.Hadamard.DeterminantRatioEstimateMatrix

/-! Balanced diagonal completions of a real symmetric conference matrix. -/

open scoped BigOperators
open Matrix

namespace Hadamard.DeterminantRatio

variable {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable [Fintype K] [DecidableEq K]

/-- If a real symmetric matrix squares to `q I`, then `sqrt(q) I + C` is
positive semidefinite. Multiplying it by `2 sqrt(q)` gives its own square. -/
theorem positive_conference_shift {C : Matrix K K ℝ} {q : ℝ} (hq : 0 < q)
    (hc : C.IsHermitian) (square : C*C = q • (1 : Matrix K K ℝ)) :
    (Real.sqrt q • (1 : Matrix K K ℝ) + C).PosSemidef := by
  let s := Real.sqrt q
  let A := s • (1 : Matrix K K ℝ) + C
  have sp : 0 < s := Real.sqrt_pos.mpr hq
  have ss : s*s = q := Real.mul_self_sqrt hq.le
  have herm : A.IsHermitian := (Matrix.isHermitian_one.smul (show IsSelfAdjoint s by rfl)).add hc
  have pos : (A*A).PosSemidef := by simpa only [herm.eq] using posSemidef_conjTranspose_mul_self A
  have eq : A*A = (2*s) • A := by
    change (s • 1 + C)*(s • 1 + C) = (2*s) • (s • 1 + C)
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul,
      mul_one, smul_add, smul_smul, square]
    rw [← ss]
    module
  rw [eq] at pos
  have h := pos.smul (show 0 ≤ (2*s)⁻¹ by positivity)
  rw [smul_smul, inv_mul_cancel₀ (show 2*s ≠ 0 by positivity), one_smul] at h
  exact h

/-- A principal block of a real symmetric conference matrix, scaled by two,
has all eigenvalues at least `-2 sqrt(q)`. -/
theorem conference_principal_lower {C : Matrix K K ℝ} {q : ℝ} (hq : 0 < q)
    (hc : C.IsHermitian) (square : C*C = q • (1 : Matrix K K ℝ))
    (f : I → K) (hf : Function.Injective f) (i : I) :
    -2*Real.sqrt q ≤ ((hc.submatrix f).smul (show IsSelfAdjoint (2:ℝ) by simp)).eigenvalues i := by
  have p := (positive_conference_shift hq hc square).submatrix f
  have eq : (Real.sqrt q • (1 : Matrix K K ℝ) + C).submatrix f f =
      Real.sqrt q • (1 : Matrix I I ℝ) + C.submatrix f f := by
    ext i j
    by_cases ij : i=j
    · subst j; simp [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply]
    · simp [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, ij, hf.ne ij]
  rw [eq] at p
  have p2 := p.smul (show (0:ℝ) ≤ 2 by norm_num)
  rw [smul_add, smul_smul] at p2
  simpa [neg_mul] using eigenvalue_lower_of_shift ((hc.submatrix f).smul (show IsSelfAdjoint (2:ℝ) by simp)) p2 i

/-- Each large half-Gram block meets the four-fifths target for an arbitrary
principal subset containing half the conference indices. -/
theorem four_fifths_conference_principal {C : Matrix K K ℝ} (k : ℕ) (hk : 0 < k)
    (card : Fintype.card I = k+1) (hq : 674 ≤ (2*(k:ℝ)+1)) (hc : C.IsHermitian)
    (square : C*C = (2*(k:ℝ)+1) • (1 : Matrix K K ℝ)) (diag : ∀ i, C i i = 0)
    (off : ∀ i j, i ≠ j → C i j ^ 2 ≤ 1) (f : I → K) (hf : Function.Injective f) :
    (4/5:ℝ) * (2*(2*((k:ℝ)+1))-2) * (2*((k:ℝ)+1)-2)^k ≤
      ((2*((k:ℝ)+1)) • (1 : Matrix I I ℝ) + (2:ℝ) • C.submatrix f f).det := by
  have H := (hc.submatrix f).smul (show IsSelfAdjoint (2:ℝ) by simp)
  apply four_fifths_of_symmetric_entries k hk card H
  · intro i
    simp [Matrix.smul_apply, submatrix_apply, diag]
  · intro i j hij
    have h := off (f i) (f j) (hf.ne hij)
    simp only [Matrix.smul_apply, smul_eq_mul, submatrix_apply]
    nlinarith
  · intro i
    have l := conference_principal_lower (show 0 < 2*(k:ℝ)+1 by positivity) hc square f hf i
    linarith [two_sqrt_le hq]

/-- The diagonal completion assigns opposite signs to the two index sets. -/
def completionSign : I ⊕ J → ℝ := Sum.elim (fun _ ↦ 1) (fun _ ↦ -1)

theorem conference_completion_gram {C : Matrix (I ⊕ J) (I ⊕ J) ℝ} {q : ℝ}
    (hc : C.IsHermitian) (square : C*C = q • (1 : Matrix (I ⊕ J) (I ⊕ J) ℝ)) :
    (C+diagonal completionSign)*(C+diagonal completionSign).transpose =
    fromBlocks ((q+1) • (1 : Matrix I I ℝ) + (2:ℝ) • C.submatrix Sum.inl Sum.inl) 0 0
      ((q+1) • (1 : Matrix J J ℝ) + (2:ℝ) • (-C).submatrix Sum.inr Sum.inr) := by
  have tr : C.transpose = C := by ext i j; simpa using hc.apply i j
  rw [transpose_add, diagonal_transpose, tr]
  rw [add_mul, mul_add, mul_add, square]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.diagonal_apply, Matrix.submatrix_apply, Matrix.one_apply, completionSign,
      Matrix.fromBlocks] <;> split_ifs <;> ring

/-- A balanced diagonal completion of any real symmetric conference matrix of
order `2*(k+1)` attains four fifths of the Ehlich–Wojtas bound for `2*k+1≥674`.
The proof also permits off-diagonal entries of absolute value at most one. -/
theorem balanced_conference_four_fifths {C : Matrix (I ⊕ J) (I ⊕ J) ℝ}
    (k : ℕ) (hk : 0 < k) (ci : Fintype.card I = k+1) (cj : Fintype.card J = k+1)
    (hq : 674 ≤ 2*(k:ℝ)+1) (hc : C.IsHermitian)
    (square : C*C = (2*(k:ℝ)+1) • (1 : Matrix (I ⊕ J) (I ⊕ J) ℝ))
    (diag : ∀ i, C i i = 0) (off : ∀ i j, i≠j → C i j^2 ≤ 1) :
    (4/5:ℝ) * (2*(2*((k:ℝ)+1))-2) * (2*((k:ℝ)+1)-2)^k ≤
      |(C + diagonal completionSign).det| := by
  have NegD (i : I⊕J) : (-C) i i = 0 := by simp [diag]
  have NegO (i j : I⊕J) (h : i≠j) : (-C) i j ^ 2 ≤ 1 := by simpa using off i j h
  have NegS : (-C)*(-C) = (2*(k:ℝ)+1) • (1 : Matrix (I ⊕ J) (I ⊕ J) ℝ) := by simpa using square
  have a := four_fifths_conference_principal k hk ci hq hc square diag off Sum.inl Sum.inl_injective
  have b := four_fifths_conference_principal k hk cj hq hc.neg NegS NegD NegO Sum.inr Sum.inr_injective
  have g := conference_completion_gram hc square
  rw [show 2*(k:ℝ)+1+1=2*((k:ℝ)+1) by ring] at g
  apply abs_det_of_gram_blocks _ _ _ g _ a b
  have kp : 0 ≤ (k:ℝ) := by positivity
  exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (pow_nonneg (by linarith) _)

#print axioms balanced_conference_four_fifths

end Hadamard.DeterminantRatio
