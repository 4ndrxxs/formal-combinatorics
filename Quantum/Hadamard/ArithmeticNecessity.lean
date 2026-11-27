import Quantum.Hadamard.Basic

/-! The determinant obstruction for modular Hadamard matrices of odd order. -/

namespace HadamardMod

def KuperbergAdmissible (p n : ℕ) : Prop :=
  n%2 = 0 ∨ ∃ a : ZMod p, a^2 = (n : ZMod p)

theorem necessary_admissible {p n : ℕ} (hp : p.Prime) (h : AtOrder p n) :
    KuperbergAdmissible p n := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases even : n%2 = 0
  · exact Or.inl even
  right
  let a : ZMod p := n
  by_cases zero : a = 0
  · exact ⟨0, by change 0^2 = a; simp [zero]⟩
  obtain ⟨D,hD⟩ := h
  let H : Matrix (Fin n) (Fin n) (ZMod p) := D
  have gram : H*H.transpose = a • (1 : Matrix (Fin n) (Fin n) (ZMod p)) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply]
    by_cases ij : i=j
    · subst j
      simpa [H, a, Matrix.mul_apply, Matrix.transpose_apply] using hD.norm_rows i
    · simpa [H, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_ne ij] using hD.ortho i j ij
  have hdet : H.det^2 = a^n := by
    simpa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, pow_two] using congrArg Matrix.det gram
  obtain ⟨t,ht⟩ : Odd n := Nat.odd_iff.mpr (by omega)
  have power : a^n = a*(a^t)^2 := by
    calc
      a^n = a^(2*t+1) := congrArg (a^·) ht
      _ = a*(a^t)^2 := by rw [pow_succ, Nat.mul_comm 2 t, pow_mul, mul_comm]
  refine ⟨H.det/a^t, ?_⟩
  change (H.det/a^t)^2 = a
  rw [div_pow, div_eq_iff (pow_ne_zero _ (pow_ne_zero _ zero)), hdet, power]

end HadamardMod
