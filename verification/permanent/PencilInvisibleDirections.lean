import QuinticScalarExtension

/-! Directions invisible in every entry of a normalized pencil give a
zero directional derivative at every input. -/

noncomputable section
open PowerSeries Matrix Module
namespace QuinticPencil
variable {K I n : Type*} [Field K] [Fintype I] [DecidableEq I] [Fintype n] [DecidableEq n]

omit [Fintype I] [DecidableEq I] in
private theorem line_base (y z : I → K) (p : MvPolynomial I K) :
    constantCoeff (restrictLine y z p) = MvPolynomial.eval y p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [restrictLine]
  | add p q h k => simp [map_add,h,k]
  | mul_X p i h => simp [restrictLine] at h ⊢; simp [h]

omit [Fintype I] [DecidableEq I] in
private theorem line_zero_direction (y : I → K) (p : MvPolynomial I K) :
    restrictLine y 0 p = C (MvPolynomial.eval y p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [restrictLine]
  | add p q h k => simp [map_add,h,k]
  | mul_X p i h => rw [map_mul,h,map_mul,map_mul]; simp [restrictLine]

omit [DecidableEq I] in
private theorem direction_linear (l y z : I → K) :
    restrictLine y z (linearForm l) = C (value l y) + X*C (value l z) := by
  simp [restrictLine,linearForm,value,MvPolynomial.coe_eval₂Hom,map_sum,Finset.mul_sum,
    Finset.sum_add_distrib,mul_add,mul_left_comm]

theorem line_directional_gradient (p : MvPolynomial I K) (y z : I → K) :
    coeff 1 (restrictLine y z p) =
      ∑ i, z i * MvPolynomial.eval y (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [restrictLine]
  | add p q h k => simp [map_add,h,k,mul_add,Finset.sum_add_distrib]
  | mul_X p j h =>
    have each (i : I) : MvPolynomial.eval y (MvPolynomial.pderiv i (p*MvPolynomial.X j)) =
        MvPolynomial.eval y (MvPolynomial.pderiv i p) * y j +
          (if i=j then MvPolynomial.eval y p else 0) := by
      by_cases e : i=j
      · subst i; simp; ring
      · simp [MvPolynomial.pderiv_X_of_ne (Ne.symm e),e,mul_comm]
    have coord : coeff 1 (restrictLine y z (MvPolynomial.X j)) = z j := by simp [restrictLine]
    rw [map_mul,coeff_one_mul,h,line_base,line_base,coord,MvPolynomial.eval_X]
    simp only [each,mul_add,←mul_assoc,mul_ite,mul_zero,Finset.sum_add_distrib,
      ←Finset.sum_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem invisible_direction (p : MvPolynomial I K) (b c : n → I → K) (D : n → n → I → K)
    (rep : p = regularDet b c D) (z : I → K) (hz : z ∈ (endpoints b c).ker)
    (internal : transfer D z = 0) (y : I → K) :
    ∑ i, z i * MvPolynomial.eval y (MvPolynomial.pderiv i p) = 0 := by
  obtain ⟨bz,cz⟩ := (endpoint_zero_iff b c z).mp hz
  have dz (i j : n) : value (D i j) z = 0 := congrFun (congrFun internal i) j
  have origin (l : I → K) : value l 0 = 0 := by simp [value]
  have eq : restrictLine y z p = restrictLine y 0 p := by
    rw [rep,regularDet,RingHom.map_det,RingHom.map_det]
    congr 1
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.fromBlocks,RingHom.mapMatrix_apply,Matrix.one_apply,direction_linear,bz,cz,dz,origin]
  rw [←line_directional_gradient,eq,line_zero_direction]
  simp

#print axioms line_directional_gradient
#print axioms invisible_direction
end QuinticPencil
