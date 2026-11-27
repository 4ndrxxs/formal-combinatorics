import QuinticTorus
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! A Gram matrix cannot have rank greater than its ambient bilinear
form, and a matrix of univariate polynomials cannot gain rank at zero. -/

noncomputable section
open Matrix Module Polynomial
namespace QuinticPencil
variable {K V J : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype J] [DecidableEq J]

theorem gram_rank_le (H : LinearMap.BilinForm K V) (v : J → V) :
    (Matrix.of (fun i j ↦ H (v i) (v j))).rank ≤ finrank K H.range := by
  let F := (Pi.basisFun K J).constr K v
  let T : Dual K V →ₗ[K] (J → K) :=
    { toFun := fun g i ↦ g (v i)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let A := T.comp (LinearMap.comp H F)
  have entries : A.toMatrix' = (Matrix.of (fun i j ↦ H (v i) (v j))).transpose := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    change (H (F (Pi.single j 1))) (v i) = H (v j) (v i)
    have fv : F (Pi.single j 1) = v j := by
      simpa only [Pi.basisFun_apply,F] using (Pi.basisFun K J).constr_basis K v j
    rw [fv]
  rw [← Matrix.rank_transpose (Matrix.of (fun i j ↦ H (v i) (v j))),← entries,
    Matrix.rank,← Matrix.toLin'_apply',Matrix.toLin'_toMatrix']
  change finrank K (T.comp (LinearMap.comp H F)).range ≤ finrank K H.range
  rw [LinearMap.range_comp]
  exact (Submodule.finrank_map_le T (LinearMap.comp H F).range).trans
    (Submodule.finrank_mono (LinearMap.range_comp_le_range F H))

theorem rank_at_zero [Infinite K] (A : Matrix J J K[X]) (r : ℕ)
    (away : ∀ t : K, t ≠ 0 → ((evalRingHom t).mapMatrix A).rank ≤ r) :
    ((evalRingHom 0).mapMatrix A).rank ≤ r := by
  classical
  let H := (evalRingHom 0).mapMatrix A
  by_contra! large
  obtain ⟨V,U,e,_,_,red⟩ := Matrix.exists_rank_normal_form H
  let f : Fin H.rank → J := fun i ↦ e.symm (.inl i)
  let q := ((Polynomial.C.mapMatrix V * A * Polynomial.C.mapMatrix U).submatrix f f).det
  have ev (t : K) : q.eval t = ((V * (evalRingHom t).mapMatrix A * U).submatrix f f).det := by
    dsimp only [q]
    have const (B : Matrix J J K) : (evalRingHom t).mapMatrix (Polynomial.C.mapMatrix B) = B := by
      ext i j; simp
    change (evalRingHom t) _ = _
    rw [RingHom.map_det_submatrix]
    change (((evalRingHom t).mapMatrix (Polynomial.C.mapMatrix V * A *
      Polynomial.C.mapMatrix U)).submatrix f f).det = _
    rw [map_mul,map_mul,const,const]
  have van (t : K) (nz : t ≠ 0) : q.eval t = 0 := by
    rw [ev]
    by_contra nonzero
    have full := Matrix.rank_of_det_ne_zero nonzero
    have lo := Matrix.rank_submatrix_le (V * (evalRingHom t).mapMatrix A * U) f f
    have upper := ((rank_mul_le_left (V * (evalRingHom t).mapMatrix A) U).trans
      (rank_mul_le_right V ((evalRingHom t).mapMatrix A))).trans (away t nz)
    rw [full,Fintype.card_fin] at lo
    exact (not_le_of_gt large) (lo.trans upper)
  have ident : X*q = 0 := Polynomial.funext (fun t ↦ by
    by_cases ht : t = 0 <;> simp [ht,van])
  have zero : q = 0 := (mul_eq_zero.mp ident).resolve_left Polynomial.X_ne_zero
  have one : (V * H * U).submatrix f f = 1 := by
    rw [red]
    ext i j
    simp [f,Matrix.submatrix,Matrix.fromBlocks]
  have eq := ev 0
  change q.eval 0 = ((V * H * U).submatrix f f).det at eq
  simp [zero,one] at eq

#print axioms gram_rank_le
#print axioms rank_at_zero
end QuinticPencil
