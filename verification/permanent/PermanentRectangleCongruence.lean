import PermanentRectangleMatrices

/-! Polynomial identities for the integral change of basis of the rectangle. -/

open Matrix
namespace PermanentFive.Rectangle
variable {R : Type*} [CommRing R] (s t : R)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 36000000 in
private theorem right_product : original s t * change s t = timesChange s t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply,Fin.sum_univ_succ,original,change,timesChange] <;> ring

set_option maxRecDepth 24000 in
set_option maxHeartbeats 36000000 in
private theorem left_product : (change s t).transpose * timesChange s t = split s t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply,Fin.sum_univ_succ,Matrix.transpose_apply,change,timesChange,split] <;> ring

theorem gram_congruence : (change s t).transpose * original s t * change s t = split s t := by
  rw [Matrix.mul_assoc,right_product,left_product]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 36000000 in
theorem change_right_inverse : change s t * inverseTwelve s t = (12 : R) • (1 : Mat R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply,Fin.sum_univ_succ,change,inverseTwelve,Matrix.one_apply] <;> ring

#print axioms gram_congruence
#print axioms change_right_inverse
end PermanentFive.Rectangle
