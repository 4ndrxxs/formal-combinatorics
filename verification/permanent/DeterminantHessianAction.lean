import PolynomialLinearHessian
import PermanentSmoothSpectrum

/-! Two-sided matrix multiplication induces the usual determinant
symmetry. Its coordinate action transports Hessian ranks and smoothness. -/
noncomputable section
open Matrix Finset Equiv MvPolynomial PermanentFive PermanentBorder QuinticPencil PolynomialLinearChange
namespace DeterminantHessian
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
def board (z : I × I → K) : Matrix I I K := Matrix.of fun i j ↦ z (i,j)
def vec (A : Matrix I I K) (e : I × I) := A e.1 e.2
def detPoly (K I : Type*) [Field K] [Fintype I] [DecidableEq I] : MvPolynomial (I × I) K :=
  (PermanentCuts.generic K I).det
def coordinateMap (V U : Matrix I I K) : Matrix (I × I) (I × I) K :=
  Matrix.of fun e f ↦ V e.1 f.1*U f.2 e.2

omit [DecidableEq I] in
theorem action (V U : Matrix I I K) (z : I × I → K) :
    coordinateMap V U *ᵥ z=vec (V*(board z*U)) := by
  funext ⟨i,j⟩
  simp only [coordinateMap,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,vec,board,
    Matrix.of_apply,Matrix.mul_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

private theorem generic_action (V U : Matrix I I K) :
    (subst (coordinateMap V U)).mapMatrix (PermanentCuts.generic K I)=
      C.mapMatrix V*(PermanentCuts.generic K I*C.mapMatrix U) := by
  apply Matrix.ext
  intro i j
  simp only [RingHom.mapMatrix_apply,Matrix.map_apply,PermanentCuts.generic,Matrix.of_apply,
    subst_X,form,coordinateMap,Fintype.sum_prod_type,Matrix.mul_apply,Finset.mul_sum,map_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem determinant_law (V U : Matrix I I K) :
    subst (coordinateMap V U) (detPoly K I)=C (V.det*U.det)*detPoly K I := by
  rw [detPoly,RingHom.map_det,generic_action,Matrix.det_mul,Matrix.det_mul,←RingHom.map_det,
    ←RingHom.map_det,map_mul]
  ring

theorem determinant_eval (z : I × I → K) : eval z (detPoly K I)=(board z).det := by
  rw [detPoly,RingHom.map_det]
  congr 1
  ext i j
  simp [PermanentCuts.generic,board]

theorem determinant_rank_le (V U : Matrix I I K) (v : IsUnit V) (u : IsUnit U)
    (z : I × I → K) : (hessian (detPoly K I) z).rank≤(hessian (detPoly K I) (vec (V*(board z*U)))).rank := by
  rw [←action]
  exact rank_le_under_symmetry _ _ _ _ (determinant_law V U)
    (mul_ne_zero ((Matrix.isUnit_iff_isUnit_det V).mp v).ne_zero ((Matrix.isUnit_iff_isUnit_det U).mp u).ne_zero)

theorem determinant_rank_eq (V U : Matrix I I K) (v : IsUnit V) (u : IsUnit U)
    (z : I × I → K) : (hessian (detPoly K I) z).rank=(hessian (detPoly K I) (vec (V*(board z*U)))).rank := by
  refine le_antisymm (determinant_rank_le V U v u z) ?_
  obtain ⟨v,rfl⟩ := v
  obtain ⟨u,rfl⟩ := u
  let y := vec ((v : Matrix I I K)*(board z*(u : Matrix I I K)))
  have back : (↑(v⁻¹) : Matrix I I K)*(board y*(↑(u⁻¹) : Matrix I I K))=board z := by
    change _*(((v : Matrix I I K)*(board z*(u : Matrix I I K)))*_)=_
    calc _=((↑(v⁻¹) : Matrix I I K)*(v : Matrix I I K))*board z*((u : Matrix I I K)*(↑(u⁻¹) : Matrix I I K)) := by simp only [Matrix.mul_assoc]
         _=_ := by simp
  have inf := determinant_rank_le (↑(v⁻¹) : Matrix I I K) (↑(u⁻¹) : Matrix I I K)
    v⁻¹.isUnit u⁻¹.isUnit y
  rw [back] at inf
  exact inf

theorem nonzero_grad_transport (V U : Matrix I I K) (v : IsUnit V) (u : IsUnit U)
    (z : I × I → K) (smooth : ∃ e, eval z (pderiv e (detPoly K I))≠0) :
    ∃ e, eval (vec (V*(board z*U))) (pderiv e (detPoly K I))≠0 := by
  obtain ⟨e,h⟩ := smooth
  by_contra! flat
  have chain := grad_chain (coordinateMap V U) (detPoly K I) z e
  rw [determinant_law,action,pderiv_C_mul] at chain
  simp only [map_mul,eval_C,flat,mul_zero,Finset.sum_const_zero] at chain
  exact h ((mul_eq_zero.mp chain).resolve_left (mul_ne_zero
    ((Matrix.isUnit_iff_isUnit_det V).mp v).ne_zero ((Matrix.isUnit_iff_isUnit_det U).mp u).ne_zero))

theorem binary_per_eq_det (binary : (2:K)=0) : per K I=detPoly K I := by
  have t : (2:MvPolynomial (I × I) K)=0 := calc
    _=C (2:K) := (map_natCast (C : K →+* MvPolynomial (I × I) K) 2).symm
    _=0 := by rw [binary,map_zero]
  have neg (x : MvPolynomial (I × I) K) : -x=x := by linear_combination -x*t
  rw [per,Matrix.permanent,detPoly,Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro p _
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h|h <;> simp [h,neg]

#print axioms determinant_rank_eq
#print axioms binary_per_eq_det
end DeterminantHessian
