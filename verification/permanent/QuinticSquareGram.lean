import QuinticHalfDiscriminant
import Mathlib.LinearAlgebra.Matrix.Rank

/-! If the columns of a twelve-vector frame span a six-dimensional
totally isotropic subspace, the determinant of its Gram matrix is a
square. The frame itself need not be a basis of the ambient space. -/

noncomputable section
open Matrix Module LinearMap
namespace QuinticPencil
variable {K I V : Type*} [Field K] [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem gram_square_from_six (H : LinearMap.BilinForm K V) (sym : H.IsSymm)
    (v : I → V) (size : Fintype.card I = 12) (J : Submodule K V) (six : 6 ≤ finrank K J)
    (inside : J ≤ Submodule.span K (Set.range v)) (iso : J ≤ H.orthogonal J) :
    IsSquare (Matrix.of (fun i j ↦ H (v i) (v j))).det := by
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
  apply determinant_square_of_six_plane G size gsym (J.comap F) (six.trans dim)
  rw [form]
  exact fun u hu z hz ↦ iso hu (F z) hz

#print axioms gram_square_from_six
end QuinticPencil
