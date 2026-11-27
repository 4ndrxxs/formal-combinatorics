import PermanentFractionFreeRank
import PermanentOrderThreeSpectrum

/-! Integral certificate for a smooth order-4 permanent zero of Hessian rank 13. -/
noncomputable section
set_option maxHeartbeats 50000000
set_option maxRecDepth 50000
open Matrix PermanentFive QuinticPencil PermanentBorder
namespace PermanentOrderFour
private def point (u : CellOf (Fin 4)) : ℤ := ![![0, 0, 0, -1], ![0, 1, 1, -1], ![0, 1, -1, 0], ![1, 0, 1, -1]] u.1 u.2
private def pick : Fin 13 → CellOf (Fin 4) := ![(0,0), (0,1), (0,2), (0,3), (1,0), (1,1), (1,2), (1,3), (2,0), (2,1), (2,3), (3,0), (3,1)]
private def coefficients : Matrix (Fin 13) (CellOf (Fin 4)) ℤ := Matrix.of fun i u ↦
  ![![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, -1, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 1, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, -1, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 1, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, -1, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 0, 0]]] i u.1 u.2
private def inverseNumerator : Matrix (Fin 13) (Fin 13) ℤ := Matrix.of fun i j ↦
  ![![-1, 0, 1, 1, 1, 0, -1, 3, 0, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0], ![1, 0, -1, -1, -1, 0, 1, -1, 0, 0, 2, -2, 0], ![1, 0, -1, -5, 1, -6, -3, -5, 2, -2, 2, -4, 2], ![1, 0, -1, 1, -1, 0, 1, -1, 0, 0, 0, 0, 2], ![0, 0, 0, -6, 0, -8, -4, -4, 0, -4, -2, -2, 2], ![-1, 0, 1, -3, 1, -4, -1, -3, 0, -4, -2, -2, 0], ![3, -2, -1, -5, -1, -4, -3, -9, 2, -2, 2, -6, 4], ![0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, -2], ![0, 0, 0, -2, 0, -4, -4, -2, 0, 0, 0, -2, 2], ![0, 2, 2, 2, 0, -2, -2, 2, 0, 0, 0, 2, -2], ![2, 0, -2, -4, 0, -2, -2, -6, 2, -2, 2, -4, 0], ![0, 0, 0, 2, 2, 2, 0, 4, -2, 2, -2, 0, 0]] i j
private def entries : Matrix (CellOf (Fin 4)) (CellOf (Fin 4)) ℤ := Matrix.of fun u v ↦
  ![![![![0, 0, 0, 0], ![0, 1, -1, 1], ![0, -2, -1, 1], ![0, 1, -1, 0]], ![![0, 0, 0, 0], ![1, 0, 0, -1], ![-2, 0, -1, 1], ![1, 0, 0, 0]], ![![0, 0, 0, 0], ![-1, 0, 0, 1], ![-1, -1, 0, 1], ![-1, 0, 0, 0]], ![![0, 0, 0, 0], ![1, -1, 1, 0], ![1, 1, 1, 0], ![0, 0, 0, 0]]], ![![![0, 1, -1, 1], ![0, 0, 0, 0], ![0, -1, 0, 0], ![0, 1, -1, 0]], ![![1, 0, 0, -1], ![0, 0, 0, 0], ![-1, 0, -1, 0], ![1, 0, 0, 0]], ![![-1, 0, 0, 1], ![0, 0, 0, 0], ![0, -1, 0, 0], ![-1, 0, 0, 0]], ![![1, -1, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]], ![![![0, -2, -1, 1], ![0, -1, 0, 0], ![0, 0, 0, 0], ![0, -1, -1, 0]], ![![-2, 0, -1, 1], ![-1, 0, -1, 0], ![0, 0, 0, 0], ![-1, 0, 0, 0]], ![![-1, -1, 0, 1], ![0, -1, 0, 0], ![0, 0, 0, 0], ![-1, 0, 0, 0]], ![![1, 1, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]], ![![![0, 1, -1, 0], ![0, 1, -1, 0], ![0, -1, -1, 0], ![0, 0, 0, 0]], ![![1, 0, 0, 0], ![1, 0, 0, 0], ![-1, 0, 0, 0], ![0, 0, 0, 0]], ![![-1, 0, 0, 0], ![-1, 0, 0, 0], ![-1, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]] u.1 u.2 v.1 v.2

private theorem table_values : table point=entries := by decide +kernel
private theorem all_columns : (1:ℤ) • entries=entries.submatrix id pick*coefficients := by decide +kernel
private theorem inverse_minor : inverseNumerator*entries.submatrix pick pick=(4:ℤ) • 1 := by decide +kernel
private theorem smooth_cell : cofactor point (0:Fin 4) 0=-1 := by decide +kernel

theorem over_field_13 (K : Type*) [Field K] (two_ne : (2:K)≠0) : PermanentOrderThree.AtOrder K 4 13 := by
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
    exact rank_certificate_scalars entries pick coefficients inverseNumerator 4 1
      all_columns inverse_minor (by convert (pow_ne_zero 2 two_ne) using 1; norm_num) (by norm_num)

theorem witness_13 (K : Type*) [Field K] [CharZero K] : PermanentOrderThree.AtOrder K 4 13 :=
  over_field_13 K (by norm_num)

#print axioms over_field_13
end PermanentOrderFour
