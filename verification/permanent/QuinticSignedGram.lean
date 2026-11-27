import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination

/-! The signed determinant of a symmetric form with a half-dimensional
isotropic space is a square, in any even dimension. -/

noncomputable section
open Matrix LinearMap Module
namespace QuinticPencil
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

/-- The sign of interchanging the two halves of an even-dimensional basis. -/
def splitSign (d : ℕ) : ℤ := (Equiv.Perm.sign (Equiv.sumComm (Fin d) (Fin d)) : ℤˣ)

private theorem block_signed_square (d : ℕ) (G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K) (sym : G.IsSymm)
    (zero : ∀ i j : Fin d, G (.inl i) (.inl j) = 0) : IsSquare ((splitSign d : K)*G.det) := by
  let B : Matrix (Fin d) (Fin d) K := G.submatrix Sum.inl Sum.inr
  let C : Matrix (Fin d) (Fin d) K := G.submatrix Sum.inr Sum.inr
  have flip : G.submatrix _root_.id (Equiv.sumComm (Fin d) (Fin d)) = Matrix.fromBlocks B 0 C B.transpose := by
    ext i j
    cases i with
    | inl i => cases j with
      | inl j => rfl
      | inr j => exact zero i j
    | inr i => cases j with
      | inl j => rfl
      | inr j => exact (sym.apply (.inr i) (.inl j)).symm
  have eq := congrArg Matrix.det flip
  rw [Matrix.det_permute',Matrix.det_fromBlocks_zero₁₂,Matrix.det_transpose] at eq
  exact ⟨B.det,eq⟩

theorem determinant_signed_square_of_half (d : ℕ) (H : Matrix I I K) (size : Fintype.card I = 2*d)
    (sym : H.IsSymm) (J : Submodule K (I → K)) (half : d ≤ finrank K J)
    (iso : J ≤ H.toBilin'.orthogonal J) : IsSquare ((splitSign d : K)*H.det) := by
  classical
  by_cases zero : H.det = 0
  · rw [zero]
    exact ⟨0,by simp⟩
  let h := H.toBilin'
  have nd : h.Nondegenerate := (Matrix.nondegenerate_iff_det_ne_zero.mpr zero).toBilin'
  have orth := h.finrank_add_finrank_orthogonal' J
  rw [nd.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero,Module.finrank_pi,size] at orth
  have le : finrank K J ≤ finrank K (h.orthogonal J) := Submodule.finrank_mono iso
  have jdim : finrank K J = d := by omega
  obtain ⟨P,compl⟩ := J.exists_isCompl
  have pdim := Submodule.finrank_add_eq_of_isCompl compl
  rw [Module.finrank_pi,size,jdim] at pdim
  let jBasis := Module.finBasisOfFinrankEq K J jdim
  let pBasis := Module.finBasisOfFinrankEq K P (show finrank K P = d by omega)
  let b := (jBasis.prod pBasis).map (J.prodEquivOfIsCompl P compl)
  let e : (Fin d ⊕ Fin d) ≃ I := Fintype.equivOfCardEq (by simp [size,two_mul])
  let standard := (Pi.basisFun K I).reindex e.symm
  let G := h.toMatrix b
  have left (i : Fin d) : b (.inl i) ∈ J := by
    simp [b,Module.Basis.prod_apply,Submodule.coe_prodEquivOfIsCompl']
  have gsym : G.IsSymm := by
    ext i j
    simp only [G,h,Matrix.transpose_apply,LinearMap.BilinForm.toMatrix_apply]
    exact (Matrix.isSymm_toBilin'_iff_isSymm.mpr sym).eq (b j) (b i)
  have zz (i j : Fin d) : G (.inl i) (.inl j) = 0 := by
    rw [show G = h.toMatrix b from rfl,LinearMap.BilinForm.toMatrix_apply]
    exact iso (left j) _ (left i)
  obtain ⟨w,gw⟩ := block_signed_square d G gsym zz
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
  rw [orig,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,Matrix.det_submatrix_equiv_self] at eq
  refine ⟨w/A.det,?_⟩
  field_simp
  linear_combination (splitSign d : K)*eq + gw

section Frames
variable {K I V : Type*} [Field K] [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem gram_signed_square_from_half (d : ℕ) (H : LinearMap.BilinForm K V) (sym : H.IsSymm)
    (v : I → V) (size : Fintype.card I = 2*d) (J : Submodule K V) (half : d ≤ finrank K J)
    (inside : J ≤ Submodule.span K (Set.range v)) (iso : J ≤ H.orthogonal J) :
    IsSquare ((splitSign d : K) * (Matrix.of (fun i j ↦ H (v i) (v j))).det) := by
  let F := (Pi.basisFun K I).constr K v
  let P := H.comp F F
  let G := Matrix.of (fun i j ↦ H (v i) (v j))
  have eq : P.toMatrix' = G := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix'_apply]
    change H (F (Pi.single i 1)) (F (Pi.single j 1)) = H (v i) (v j)
    have fv (k : I) : F (Pi.single k 1) = v k := by
      simpa only [Pi.basisFun_apply,F] using (Pi.basisFun K I).constr_basis K v k
    rw [fv,fv]
  have onto : J ≤ F.range := inside.trans (Submodule.span_le.mpr (by
    rintro _ ⟨i,rfl⟩
    exact ⟨(Pi.basisFun K I) i,(Pi.basisFun K I).constr_basis K v i⟩))
  have dim := Submodule.finrank_map_le F (J.comap F)
  rw [Submodule.map_comap_eq_self onto] at dim
  have form : G.toBilin' = P := by rw [← eq,Matrix.toBilin'_toMatrix']
  have gsym : G.IsSymm := by
    ext i j
    exact sym.eq (v j) (v i)
  apply determinant_signed_square_of_half d G size gsym (J.comap F) (half.trans dim)
  rw [form]
  exact fun u hu z hz ↦ iso hu (F z) hz

end Frames

#print axioms gram_signed_square_from_half
end QuinticPencil
