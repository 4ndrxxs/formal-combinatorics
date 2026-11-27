import PermanentFractionFreeRank
import PermanentOrderThreeSpectrum

/-! Integral certificate for a smooth order-4 permanent zero of Hessian rank 11. -/
noncomputable section
set_option maxHeartbeats 50000000
set_option maxRecDepth 50000
open Matrix PermanentFive QuinticPencil PermanentBorder
namespace PermanentOrderFour
private def point (u : CellOf (Fin 4)) : ℤ := ![![1, 1, 0, 0], ![1, -1, 0, 0], ![1, 2, 1, 1], ![1, 2, 1, 1]] u.1 u.2
private def pick : Fin 11 → CellOf (Fin 4) := ![(0,0), (0,1), (0,2), (0,3), (1,0), (1,1), (1,2), (1,3), (2,0), (2,1), (2,2)]
private def coefficients : Matrix (Fin 11) (CellOf (Fin 4)) ℤ := Matrix.of fun i u ↦
  ![![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 1]], ![![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 1]], ![![0, 0, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 1]], ![![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, -1], ![0, 0, 0, -1]], ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, -1], ![1, 0, 0, -1]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 0, -2], ![0, 1, 0, -2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, -1], ![0, 0, 1, -1]]] i u.1 u.2
private def inverseNumerator : Matrix (Fin 11) (Fin 11) ℤ := Matrix.of fun i j ↦
  ![![16, 16, 12, -12, 16, 8, 4, -4, 8, -56, -32], ![16, 16, 12, -12, 40, -16, 4, -4, 32, -80, -32], ![12, 12, 9, -9, 12, -12, -3, 3, -24, -12, -24], ![-12, -12, -9, 9, -12, 12, 3, -3, 0, 36, 24], ![16, 40, 12, -12, 16, -16, 4, -4, -40, -56, -32], ![8, -16, -12, 12, -16, 16, -4, 4, -32, -16, 32], ![4, 4, -3, 3, 4, -4, 1, -1, 8, 4, -8], ![-4, -4, 3, -3, -4, 4, -1, 1, 16, 20, 8], ![8, 32, -24, 0, -40, -32, 8, 16, -128, 32, 32], ![-56, -80, -12, 36, -56, -16, 4, 20, 32, 208, 64], ![-32, -32, -24, 24, -32, 32, -8, 8, 32, 64, 64]] i j
private def entries : Matrix (CellOf (Fin 4)) (CellOf (Fin 4)) ℤ := Matrix.of fun u v ↦
  ![![![![0, 0, 0, 0], ![0, 2, 4, 4], ![0, 0, -1, -1], ![0, 0, -1, -1]], ![![0, 0, 0, 0], ![2, 0, 2, 2], ![0, 0, 1, 1], ![0, 0, 1, 1]], ![![0, 0, 0, 0], ![4, 2, 0, 4], ![-1, 1, 0, 1], ![-1, 1, 0, 1]], ![![0, 0, 0, 0], ![4, 2, 4, 0], ![-1, 1, 1, 0], ![-1, 1, 1, 0]]], ![![![0, 2, 4, 4], ![0, 0, 0, 0], ![0, 0, 1, 1], ![0, 0, 1, 1]], ![![2, 0, 2, 2], ![0, 0, 0, 0], ![0, 0, 1, 1], ![0, 0, 1, 1]], ![![4, 2, 0, 4], ![0, 0, 0, 0], ![1, 1, 0, 3], ![1, 1, 0, 3]], ![![4, 2, 4, 0], ![0, 0, 0, 0], ![1, 1, 3, 0], ![1, 1, 3, 0]]], ![![![0, 0, -1, -1], ![0, 0, 1, 1], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![-1, 1, 0, 1], ![1, 1, 0, 3], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![-1, 1, 1, 0], ![1, 1, 3, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]], ![![![0, 0, -1, -1], ![0, 0, 1, 1], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![-1, 1, 0, 1], ![1, 1, 0, 3], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![-1, 1, 1, 0], ![1, 1, 3, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]] u.1 u.2 v.1 v.2

private theorem table_values : table point=entries := by decide +kernel
private theorem all_columns : (1:ℤ) • entries=entries.submatrix id pick*coefficients := by decide +kernel
private theorem inverse_minor : inverseNumerator*entries.submatrix pick pick=(48:ℤ) • 1 := by decide +kernel
private theorem smooth_cell : cofactor point (0:Fin 4) 0=-2 := by decide +kernel

theorem over_field_11 (K : Type*) [Field K] (two_ne : (2:K)≠0) (three_ne : (3:K)≠0) : PermanentOrderThree.AtOrder K 4 11 := by
  have val : integralValue point=0 := by decide +kernel
  refine ⟨castPoint K point,by rw [cast_value,val,Int.cast_zero],?_,?_⟩
  · intro bad
    rw [cast_cofactor] at bad
    have e := congrArg (fun A : Matrix (Fin 4) (Fin 4) K ↦ A 0 0) bad
    change (Int.castRingHom K) (cofactor point 0 0)=0 at e
    rw [smooth_cell] at e
    have hn : ((-2:ℤ):K)≠0 := by convert (neg_ne_zero.mpr two_ne) using 1; norm_num
    exact hn e
  · rw [cast_hessian,table_values]
    exact rank_certificate_scalars entries pick coefficients inverseNumerator 48 1
      all_columns inverse_minor (by convert (mul_ne_zero (pow_ne_zero 4 two_ne) three_ne) using 1; norm_num) (by norm_num)

theorem witness_11 (K : Type*) [Field K] [CharZero K] : PermanentOrderThree.AtOrder K 4 11 :=
  over_field_11 K (by norm_num) (by norm_num)

#print axioms over_field_11
end PermanentOrderFour
