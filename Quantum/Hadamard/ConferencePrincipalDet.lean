import Quantum.Hadamard.ConferenceDiagonalAverage
import Quantum.Hadamard.DeterminantRatioEstimateConference

/-! A single principal submatrix computes a conference completion determinant.
Multiplication by C + I gives a block triangular matrix. -/

open Matrix
open Hadamard.DeterminantRatio (completionSign)

namespace Hadamard.ConferenceAverage

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- A sign completion times the all-positive shift has triangular blocks.
The first block is the principal submatrix on the positive coordinates. -/
theorem completion_triangular (C : Matrix (I ⊕ J) (I ⊕ J) ℝ) (q : ℝ)
    (square : C*C = q • (1 : Matrix (I ⊕ J) (I ⊕ J) ℝ)) :
    (C+1)*(C+diagonal completionSign) =
    fromBlocks ((q+1) • (1 : Matrix I I ℝ) + (2:ℝ) • C.submatrix Sum.inl Sum.inl) 0
      ((2:ℝ) • C.submatrix Sum.inr Sum.inl) ((q-1) • (1 : Matrix J J ℝ)) := by
  rw [add_mul, mul_add, square, one_mul]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_diagonal,
      Matrix.diagonal_apply, Matrix.submatrix_apply, Matrix.one_apply,
      Matrix.fromBlocks, completionSign] <;> (try split_ifs) <;> ring

/-- The absolute determinant at any sign split is a scalar multiple of
the determinant of the positive-coordinate principal Gram block. The
cross-multiplied form also handles an empty positive or negative block. -/
theorem completion_principal_det (C : Matrix (I ⊕ J) (I ⊕ J) ℝ) (v : ℕ) (q : ℝ)
    (card : Fintype.card (I ⊕ J)=2*v) (hq : 1<q) (hc : C.IsHermitian)
    (square : C*C=q • (1 : Matrix (I ⊕ J) (I ⊕ J) ℝ)) (trace : C.trace=0) :
    (q-1)^v * |(C+diagonal completionSign).det| =
      (q-1)^(Fintype.card J) *
        ((q+1) • (1 : Matrix I I ℝ) + (2:ℝ) • C.submatrix Sum.inl Sum.inl).det := by
  have qpos : 0<q := by linarith
  have shifted : (C+1).det=(1-q)^v := by
    simpa using pencil_determinant C v q 1 1 card qpos hc square trace
  let f : I ⊕ J → Bool := Sum.elim (fun _ ↦ true) (fun _ ↦ false)
  have signs : (fun i ↦ (signValue (f i):ℝ)) = completionSign := by
    funext i
    cases i <;> rfl
  have s := absolute_completion C v q card hq hc square trace f
  rw [signs] at s
  have h := congrArg Matrix.det (completion_triangular C q square)
  rw [Matrix.det_mul, shifted, Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul,
    Matrix.det_one, mul_one] at h
  calc
    _ = (1-q)^v*(C+diagonal completionSign).det := by
      rw [s, ←mul_assoc, ←mul_pow]
      congr 2
      ring
    _ = _ := h.trans (mul_comm _ _)

/-- In the balanced case only the principal determinant is needed. -/
theorem balanced_principal_det (C : Matrix (I ⊕ J) (I ⊕ J) ℝ) (v : ℕ) (q : ℝ)
    (ci : Fintype.card I=v) (cj : Fintype.card J=v) (hq : 1<q) (hc : C.IsHermitian)
    (square : C*C=q • (1 : Matrix (I ⊕ J) (I ⊕ J) ℝ)) (trace : C.trace=0) :
    |(C+diagonal completionSign).det| =
      ((q+1) • (1 : Matrix I I ℝ) + (2:ℝ) • C.submatrix Sum.inl Sum.inl).det := by
  have card : Fintype.card (I ⊕ J)=2*v := by rw [Fintype.card_sum, ci, cj]; omega
  have h := completion_principal_det C v q card hq hc square trace
  rw [cj] at h
  exact mul_left_cancel₀ (pow_ne_zero _ (sub_ne_zero.mpr hq.ne')) h

#print axioms balanced_principal_det
#print axioms completion_principal_det

end Hadamard.ConferenceAverage
