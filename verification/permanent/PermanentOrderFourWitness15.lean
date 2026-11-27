import PermanentFractionFreeRank
import PermanentOrderThreeSpectrum

/-! Integral certificate for a smooth order-4 permanent zero of Hessian rank 15. -/
noncomputable section
set_option maxHeartbeats 50000000
set_option maxRecDepth 50000
open Matrix PermanentFive QuinticPencil PermanentBorder
namespace PermanentOrderFour
private def point (u : CellOf (Fin 4)) : ℤ := ![![1, 0, 1, 1], ![0, 1, 1, -2], ![1, 1, 0, 0], ![0, 1, 1, 1]] u.1 u.2
private def pick : Fin 15 → CellOf (Fin 4) := ![(0,0), (0,1), (0,2), (0,3), (1,0), (1,1), (1,2), (1,3), (2,0), (2,1), (2,2), (2,3), (3,0), (3,1), (3,2)]
private def coefficients : Matrix (Fin 15) (CellOf (Fin 4)) ℤ := Matrix.of fun i u ↦
  ![![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 2]], ![![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, -3]], ![![0, 0, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, -1]], ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, -1]], ![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, -1]], ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, -1]], ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 0, -1]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, -1]]] i u.1 u.2
private def inverseNumerator : Matrix (Fin 15) (Fin 15) ℤ := Matrix.of fun i j ↦
  ![![-48, 84, 36, 36, 0, 36, 36, -60, -48, -48, 0, 12, 0, 12, 12], ![84, -147, -57, -72, -12, -54, -54, 108, 84, 84, 0, -12, 0, -21, -27], ![36, -57, -27, -36, -4, -14, -30, 48, 36, 36, 0, 0, -8, -7, -9], ![36, -72, -36, -48, -8, -16, -24, 48, 48, 48, 0, 0, -4, -8, -12], ![0, -12, -4, -8, 0, 0, 0, 0, 0, 12, 4, 8, 0, 0, 0], ![36, -54, -14, -16, 0, -36, -12, 36, 36, 24, -4, -8, 0, -18, -6], ![36, -54, -30, -24, 0, -12, -36, 36, 36, 36, 0, 0, 0, -6, -18], ![-60, 108, 48, 48, 0, 36, 36, -48, -60, -60, 0, 0, 0, 24, 24], ![-48, 84, 36, 48, 0, 36, 36, -60, -48, -48, 0, 0, 0, 12, 12], ![-48, 84, 36, 48, 12, 24, 36, -60, -48, -48, 0, 0, 0, 12, 12], ![0, 0, 0, 0, 4, -4, 0, 0, 0, 0, 0, 0, 8, -8, 0], ![12, -12, 0, 0, 8, -8, 0, 0, 0, 0, 0, 0, 4, -4, 0], ![0, 0, -8, -4, 0, 0, 0, 0, 0, 0, 8, 4, 0, 0, 0], ![12, -21, -7, -8, 0, -18, -6, 24, 12, 12, -8, -4, 0, -3, 3], ![12, -27, -9, -12, 0, -6, -18, 24, 12, 12, 0, 0, 0, 3, -3]] i j
private def entries : Matrix (CellOf (Fin 4)) (CellOf (Fin 4)) ℤ := Matrix.of fun u v ↦
  ![![![![0, 0, 0, 0], ![0, 0, 1, 1], ![0, -1, -1, 2], ![0, 0, -2, 1]], ![![0, 0, 0, 0], ![0, 0, 1, 1], ![-1, 0, 0, 0], ![0, 0, -2, 1]], ![![0, 0, 0, 0], ![1, 1, 0, 1], ![-1, 0, 0, 0], ![-2, -2, 0, 1]], ![![0, 0, 0, 0], ![1, 1, 1, 0], ![2, 0, 0, 0], ![1, 1, 1, 0]]], ![![![0, 0, 1, 1], ![0, 0, 0, 0], ![0, 2, 1, 1], ![0, 0, 1, 1]], ![![0, 0, 1, 1], ![0, 0, 0, 0], ![2, 0, 1, 1], ![0, 0, 1, 1]], ![![1, 1, 0, 1], ![0, 0, 0, 0], ![1, 1, 0, 1], ![1, 1, 0, 1]], ![![1, 1, 1, 0], ![0, 0, 0, 0], ![1, 1, 1, 0], ![1, 1, 1, 0]]], ![![![0, -1, -1, 2], ![0, 2, 1, 1], ![0, 0, 0, 0], ![0, -1, 1, 1]], ![![-1, 0, 0, 0], ![2, 0, 1, 1], ![0, 0, 0, 0], ![-1, 0, -2, 1]], ![![-1, 0, 0, 0], ![1, 1, 0, 1], ![0, 0, 0, 0], ![1, -2, 0, 1]], ![![2, 0, 0, 0], ![1, 1, 1, 0], ![0, 0, 0, 0], ![1, 1, 1, 0]]], ![![![0, 0, -2, 1], ![0, 0, 1, 1], ![0, -1, 1, 1], ![0, 0, 0, 0]], ![![0, 0, -2, 1], ![0, 0, 1, 1], ![-1, 0, -2, 1], ![0, 0, 0, 0]], ![![-2, -2, 0, 1], ![1, 1, 0, 1], ![1, -2, 0, 1], ![0, 0, 0, 0]], ![![1, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 0], ![0, 0, 0, 0]]]] u.1 u.2 v.1 v.2

private theorem table_values : table point=entries := by decide +kernel
private theorem all_columns : (1:ℤ) • entries=entries.submatrix id pick*coefficients := by decide +kernel
private theorem inverse_minor : inverseNumerator*entries.submatrix pick pick=(24:ℤ) • 1 := by decide +kernel
private theorem smooth_cell : cofactor point (0:Fin 4) 0=-1 := by decide +kernel

theorem over_field_15 (K : Type*) [Field K] (two_ne : (2:K)≠0) (three_ne : (3:K)≠0) : PermanentOrderThree.AtOrder K 4 15 := by
  have val : integralValue point=0 := by decide +kernel
  refine ⟨castPoint K point,by rw [cast_value,val,Int.cast_zero],?_,?_⟩
  · intro bad
    rw [cast_cofactor] at bad
    have e := congrArg (fun A : Matrix (Fin 4) (Fin 4) K ↦ A 0 0) bad
    change (Int.castRingHom K) (cofactor point 0 0)=0 at e
    rw [smooth_cell] at e
    have hn : ((-1:ℤ):K)≠0 := by norm_num
    exact hn e
  · rw [cast_hessian,table_values]
    exact rank_certificate_scalars entries pick coefficients inverseNumerator 24 1
      all_columns inverse_minor (by convert (mul_ne_zero (pow_ne_zero 3 two_ne) three_ne) using 1; norm_num) (by norm_num)

theorem witness_15 (K : Type*) [Field K] [CharZero K] : PermanentOrderThree.AtOrder K 4 15 :=
  over_field_15 K (by norm_num) (by norm_num)

#print axioms over_field_15
end PermanentOrderFour
