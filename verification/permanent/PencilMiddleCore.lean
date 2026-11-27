import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! The middle ten-dimensional quotient of a four-step nilpotent map,
expressed using split row and column inclusions. -/
noncomputable section
open Matrix
namespace PencilMiddle
variable {K n k u : Type*} [Field K]
  [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k] [Fintype u] [DecidableEq u]

theorem compressed_square (A : Matrix n n K) (M : Matrix k k K)
    (E : Matrix n k K) (F : Matrix k n K) (U : Matrix k u K) (V : Matrix u k K)
    (e : Matrix k n K) (f : Matrix n k K) (l : Matrix u k K) (v : Matrix k u K)
    (splitE : e*E=1) (splitF : F*f=1) (splitU : l*U=1) (splitV : V*v=1)
    (rep : A=E*M*F) (inter : F*E=U*V) (nil : A^4=0)
    (full : Fintype.card k ≤ A.rank) (kdim : Fintype.card k=15) (udim : Fintype.card u=10) :
    (V*M*U)^2=0 ∧ (V*M*U).rank=5 := by
  let B := V*M*U
  have rankM : M.rank = Fintype.card k := by
    apply le_antisymm (Matrix.rank_le_card_width _)
    rw [rep] at full
    exact full.trans ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _))
  have unit : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp
    (Matrix.mulVec_surjective_iff_isUnit.mp (Matrix.mulVec_surjective_iff_rank_eq_card.mpr rankM))
  have left : (l*M⁻¹*e)*(E*M*U)=1 := by
    calc (l*M⁻¹*e)*(E*M*U) = l*(M⁻¹*(e*E)*M)*U := by simp only [Matrix.mul_assoc]
         _ = 1 := by rw [splitE,Matrix.mul_one,Matrix.nonsing_inv_mul _ unit,Matrix.mul_one,splitU]
  have right : (V*M*F)*(f*M⁻¹*v)=1 := by
    calc (V*M*F)*(f*M⁻¹*v) = V*(M*(F*f)*M⁻¹)*v := by simp only [Matrix.mul_assoc]
         _ = 1 := by rw [splitF,Matrix.mul_one,Matrix.mul_nonsing_inv _ unit,Matrix.mul_one,splitV]
  have factor : A^4 = (E*M*U)*B^2*(V*M*F) := by
    calc A^4 = E*M*(F*E)*M*(F*E)*M*(F*E)*M*F := by
           rw [rep]; simp only [pow_succ,pow_zero,Matrix.one_mul,Matrix.mul_assoc]
         _ = _ := by rw [inter]; simp only [B,pow_succ,pow_zero,Matrix.one_mul,Matrix.mul_assoc]
  have z : B^2=0 := by
    calc B^2 = ((l*M⁻¹*e)*(E*M*U))*B^2*((V*M*F)*(f*M⁻¹*v)) := by
           rw [left,right,Matrix.one_mul,Matrix.mul_one]
         _ = (l*M⁻¹*e)*((E*M*U)*B^2*(V*M*F))*(f*M⁻¹*v) := by simp only [Matrix.mul_assoc]
         _ = 0 := by rw [←factor,nil,Matrix.mul_zero,Matrix.zero_mul]
  refine ⟨z,?_⟩
  have rv : Fintype.card u ≤ V.rank := by
    have h := Matrix.rank_mul_le_left V v
    rwa [splitV,Matrix.rank_one] at h
  have ru : Fintype.card u ≤ U.rank := by
    have h := Matrix.rank_mul_le_right l U
    rwa [splitU,Matrix.rank_one] at h
  have vm := Matrix.rank_mul_ge V M
  have bottom := Matrix.rank_mul_ge (V*M) U
  have top := Matrix.rank_mul_ge B B
  rw [←sq,z,Matrix.rank_zero,zero_add,udim] at top
  change B.rank=5
  change (V*M).rank+U.rank ≤ B.rank+Fintype.card k at bottom
  omega

#print axioms compressed_square
end PencilMiddle
