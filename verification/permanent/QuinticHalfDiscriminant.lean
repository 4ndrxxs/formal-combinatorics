import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination

/-! A symmetric form on a twelve-dimensional space containing a totally
isotropic six-plane has square determinant over its field of definition. -/

noncomputable section
open Matrix LinearMap Module
namespace QuinticPencil
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

private abbrev Half := Fin 6
private abbrev Double := Half ⊕ Half
private theorem swap_sign : Equiv.Perm.sign (Equiv.sumComm Half Half) = 1 := by decide +kernel

private theorem block_square (G : Matrix Double Double K) (sym : G.IsSymm)
    (zero : ∀ i j : Half, G (.inl i) (.inl j) = 0) : IsSquare G.det := by
  let B : Matrix Half Half K := G.submatrix Sum.inl Sum.inr
  let C : Matrix Half Half K := G.submatrix Sum.inr Sum.inr
  have flip : G.submatrix _root_.id (Equiv.sumComm Half Half) = Matrix.fromBlocks B 0 C B.transpose := by
    ext i j
    cases i with
    | inl i => cases j with
      | inl j => rfl
      | inr j => exact zero i j
    | inr i => cases j with
      | inl j => rfl
      | inr j => exact (sym.apply (.inr i) (.inl j)).symm
  have eq := congrArg Matrix.det flip
  rw [Matrix.det_permute',swap_sign,Matrix.det_fromBlocks_zero₁₂,Matrix.det_transpose] at eq
  exact ⟨B.det,by simpa using eq⟩

theorem determinant_square_of_six_plane (H : Matrix I I K) (size : Fintype.card I = 12)
    (sym : H.IsSymm) (J : Submodule K (I → K)) (six : 6 ≤ finrank K J)
    (iso : J ≤ H.toBilin'.orthogonal J) : IsSquare H.det := by
  classical
  by_cases zero : H.det = 0
  · rw [zero]
    exact ⟨0,by simp⟩
  let h := H.toBilin'
  have nd : h.Nondegenerate := (Matrix.nondegenerate_iff_det_ne_zero.mpr zero).toBilin'
  have orth := h.finrank_add_finrank_orthogonal' J
  rw [nd.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero,Module.finrank_pi,size] at orth
  have le : finrank K J ≤ finrank K (h.orthogonal J) := Submodule.finrank_mono iso
  have jdim : finrank K J = 6 := by omega
  obtain ⟨P,compl⟩ := J.exists_isCompl
  have pdim := Submodule.finrank_add_eq_of_isCompl compl
  rw [Module.finrank_pi,size,jdim] at pdim
  let jBasis := Module.finBasisOfFinrankEq K J jdim
  let pBasis := Module.finBasisOfFinrankEq K P (show finrank K P = 6 by omega)
  let b := (jBasis.prod pBasis).map (J.prodEquivOfIsCompl P compl)
  let e : Double ≃ I := Fintype.equivOfCardEq (by simp [size])
  let standard := (Pi.basisFun K I).reindex e.symm
  let G := h.toMatrix b
  have left (i : Half) : b (.inl i) ∈ J := by
    simp [b,Module.Basis.prod_apply,Submodule.coe_prodEquivOfIsCompl']
  have gsym : G.IsSymm := by
    ext i j
    simp only [G,h,Matrix.transpose_apply,LinearMap.BilinForm.toMatrix_apply]
    exact (Matrix.isSymm_toBilin'_iff_isSymm.mpr sym).eq (b j) (b i)
  have zz (i j : Half) : G (.inl i) (.inl j) = 0 := by
    rw [show G = h.toMatrix b from rfl,LinearMap.BilinForm.toMatrix_apply]
    exact iso (left j) _ (left i)
  obtain ⟨w,gw⟩ := block_square G gsym zz
  have orig : h.toMatrix standard = H.submatrix e e := by
    ext i j
    simp [h,standard,LinearMap.BilinForm.toMatrix_apply,Pi.basisFun_apply,
      Matrix.toBilin'_single]
  let A := standard.toMatrix b
  have changeBasis : A.transpose * h.toMatrix standard * A = G :=
    LinearMap.BilinForm.toMatrix_mul_basis_toMatrix standard b h
  have unit := congrArg Matrix.det (standard.toMatrix_mul_toMatrix_flip b)
  rw [Matrix.det_mul,Matrix.det_one] at unit
  have nonzero : A.det ≠ 0 := by intro z; change A.det * _ = 1 at unit; simp [z] at unit
  have eq := congrArg Matrix.det changeBasis
  rw [orig,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,Matrix.det_submatrix_equiv_self,gw] at eq
  refine ⟨w/A.det,?_⟩
  field_simp
  linear_combination eq

#print axioms determinant_square_of_six_plane
end QuinticPencil
