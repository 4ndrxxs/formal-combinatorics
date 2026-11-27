import PermanentFractionFreeRank
import PermanentOrderThreeSpectrum

/-! Integral certificate for a smooth order-4 permanent zero of Hessian rank 16. -/
noncomputable section
set_option maxHeartbeats 50000000
set_option maxRecDepth 50000
open Matrix PermanentFive QuinticPencil PermanentBorder
namespace PermanentOrderFour
private def point (u : CellOf (Fin 4)) : ℤ := ![![1, 1, -1, 1], ![1, 0, -1, -1], ![1, -1, 1, 1], ![-1, 1, -1, 0]] u.1 u.2
private def pick : Fin 16 → CellOf (Fin 4) := ![(0,0), (0,1), (0,2), (0,3), (1,0), (1,1), (1,2), (1,3), (2,0), (2,1), (2,2), (2,3), (3,0), (3,1), (3,2), (3,3)]
private def coefficients : Matrix (Fin 16) (CellOf (Fin 4)) ℤ := Matrix.of fun i u ↦
  ![![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1]]] i u.1 u.2
private def inverseNumerator : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of fun i j ↦
  ![![10, 1, -4, 7, 7, 3, 5, -4, 4, 11, -2, -5, -1, -8, 11, -3], ![1, -14, -7, 10, 13, 6, -1, -13, 1, 20, 7, -2, -7, -8, 11, -9], ![-4, -7, -26, 23, -7, 3, -5, -2, -22, 19, 8, -1, 1, -4, 1, -9], ![7, 10, 23, -38, -17, -21, 11, 26, 7, -22, 13, 4, -13, 25, -13, 18], ![7, 13, -7, -17, -38, -18, -4, 26, -23, -13, 13, -11, -10, 25, -22, 21], ![3, 6, 3, -21, -18, -15, 0, 15, -9, -12, 3, -3, -9, 21, -3, 12], ![5, -1, -5, 11, -4, 0, 10, -2, -1, 1, -1, 5, -2, 5, 10, -3], ![-4, -13, -2, 26, 26, 15, -2, -29, 2, 19, -10, 2, 13, -22, 19, -15], ![4, 1, -22, 7, -23, -9, -1, 2, -26, -1, -8, -5, -7, 4, -19, 3], ![11, 20, 19, -22, -13, -12, 1, 19, -1, -14, 5, -10, -11, 20, -5, 3], ![-2, 7, 8, 13, 13, 3, -1, -10, -8, 5, -14, 1, -7, -2, 5, -3], ![-5, -2, -1, 4, -11, -3, 5, 2, -5, -10, 1, 10, -1, -5, -1, 0], ![-1, -7, 1, -13, -10, -9, -2, 13, -7, -11, -7, -1, -14, 8, -20, 6], ![-8, -8, -4, 25, 25, 21, 5, -22, 4, 20, -2, -5, 8, -17, 20, -21], ![11, 11, 1, -13, -22, -3, 10, 19, -19, -5, 5, -1, -20, 20, -14, 12], ![-3, -9, -9, 18, 21, 12, -3, -15, 3, 3, -3, 0, 6, -21, 12, -15]] i j
private def entries : Matrix (CellOf (Fin 4)) (CellOf (Fin 4)) ℤ := Matrix.of fun u v ↦
  ![![![![0, 0, 0, 0], ![0, -1, 1, 2], ![0, 1, -1, -1], ![0, -2, 1, 1]], ![![0, 0, 0, 0], ![-1, 0, -1, -2], ![1, 0, 1, 0], ![-2, 0, 0, 0]], ![![0, 0, 0, 0], ![1, -1, 0, 2], ![-1, 1, 0, 1], ![1, 0, 0, -1]], ![![0, 0, 0, 0], ![2, -2, 2, 0], ![-1, 0, 1, 0], ![1, 0, -1, 0]]], ![![![0, -1, 1, 2], ![0, 0, 0, 0], ![0, -1, 1, -2], ![0, 0, 0, 2]], ![![-1, 0, -1, -2], ![0, 0, 0, 0], ![-1, 0, -1, 0], ![0, 0, 2, 0]], ![![1, -1, 0, 2], ![0, 0, 0, 0], ![1, -1, 0, 0], ![0, 2, 0, 0]], ![![2, -2, 2, 0], ![0, 0, 0, 0], ![-2, 0, 0, 0], ![2, 0, 0, 0]]], ![![![0, 1, -1, -1], ![0, -1, 1, -2], ![0, 0, 0, 0], ![0, 0, -1, -1]], ![![1, 0, 1, 0], ![-1, 0, -1, 0], ![0, 0, 0, 0], ![0, 0, 0, -2]], ![![-1, 1, 0, 1], ![1, -1, 0, 0], ![0, 0, 0, 0], ![-1, 0, 0, 1]], ![![-1, 0, 1, 0], ![-2, 0, 0, 0], ![0, 0, 0, 0], ![-1, -2, 1, 0]]], ![![![0, -2, 1, 1], ![0, 0, 0, 2], ![0, 0, -1, -1], ![0, 0, 0, 0]], ![![-2, 0, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, -2], ![0, 0, 0, 0]], ![![1, 0, 0, -1], ![0, 2, 0, 0], ![-1, 0, 0, 1], ![0, 0, 0, 0]], ![![1, 0, -1, 0], ![2, 0, 0, 0], ![-1, -2, 1, 0], ![0, 0, 0, 0]]]] u.1 u.2 v.1 v.2

private theorem table_values : table point=entries := by decide +kernel
private theorem all_columns : (1:ℤ) • entries=entries.submatrix id pick*coefficients := by decide +kernel
private theorem inverse_minor : inverseNumerator*entries.submatrix pick pick=(36:ℤ) • 1 := by decide +kernel
private theorem smooth_cell : cofactor point (0:Fin 4) 0=-3 := by decide +kernel

theorem over_field_16 (K : Type*) [Field K] (two_ne : (2:K)≠0) (three_ne : (3:K)≠0) : PermanentOrderThree.AtOrder K 4 16 := by
  have val : integralValue point=0 := by decide +kernel
  refine ⟨castPoint K point,by rw [cast_value,val,Int.cast_zero],?_,?_⟩
  · intro bad
    rw [cast_cofactor] at bad
    have e := congrArg (fun A : Matrix (Fin 4) (Fin 4) K ↦ A 0 0) bad
    change (Int.castRingHom K) (cofactor point 0 0)=0 at e
    rw [smooth_cell] at e
    have hn : ((-3:ℤ):K)≠0 := by convert (neg_ne_zero.mpr three_ne) using 1; norm_num
    exact hn e
  · rw [cast_hessian,table_values]
    exact rank_certificate_scalars entries pick coefficients inverseNumerator 36 1
      all_columns inverse_minor (by convert (mul_ne_zero (pow_ne_zero 2 two_ne) (pow_ne_zero 2 three_ne)) using 1; norm_num) (by norm_num)

theorem witness_16 (K : Type*) [Field K] [CharZero K] : PermanentOrderThree.AtOrder K 4 16 :=
  over_field_16 K (by norm_num) (by norm_num)

#print axioms over_field_16
end PermanentOrderFour
