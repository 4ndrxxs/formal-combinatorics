import PermanentFieldWitness

/-! A smooth characteristic-three point of order four with Hessian rank 11. -/
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 50000000
open Matrix PermanentFive QuinticPencil PermanentBorder
namespace PermanentOrderFour
private def point (u : CellOf (Fin 4)) : ZMod 3 := ![![1, 0, 0, 0], ![0, 1, 1, 1], ![0, 1, 1, 1], ![0, 1, 1, 1]] u.1 u.2
private def pick : Fin 11 → CellOf (Fin 4) := ![(0,0), (0,1), (1,0), (1,1), (1,2), (1,3), (2,1), (2,2), (2,3), (3,1), (3,2)]
private def coordinates : Matrix (Fin 11) (CellOf (Fin 4)) (ZMod 3) := Matrix.of fun i u ↦
  ![![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 2]], ![![0, 1, 1, 1], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 2]], ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 0], ![0, 0, 0, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 0], ![0, 0, 0, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 0, 2]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 2]]] i u.1 u.2
private def inverseMinor : Matrix (Fin 11) (Fin 11) (ZMod 3) := Matrix.of fun i j ↦
  ![![1, 0, 0, 0, 0, 2, 0, 0, 2, 2, 2], ![0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 1, 0, 2, 0, 2], ![0, 0, 0, 1, 0, 0, 0, 1, 2, 2, 0], ![2, 0, 0, 0, 0, 1, 2, 2, 2, 1, 1], ![0, 0, 0, 1, 0, 2, 0, 1, 0, 0, 2], ![0, 0, 0, 0, 1, 2, 1, 0, 0, 2, 0], ![2, 0, 0, 2, 2, 2, 0, 0, 1, 1, 1], ![2, 0, 0, 0, 2, 1, 0, 2, 1, 1, 2], ![2, 0, 0, 2, 0, 1, 2, 0, 1, 2, 1]] i j
private def entries : Matrix (CellOf (Fin 4)) (CellOf (Fin 4)) (ZMod 3) := Matrix.of fun u v ↦
  ![![![![0, 0, 0, 0], ![0, 2, 2, 2], ![0, 2, 2, 2], ![0, 2, 2, 2]], ![![0, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0]], ![![0, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0]], ![![0, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0], ![2, 0, 0, 0]]], ![![![0, 2, 2, 2], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 1], ![0, 0, 1, 1]], ![![2, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 0, 1], ![0, 1, 0, 1]], ![![2, 0, 0, 0], ![0, 0, 0, 0], ![0, 1, 1, 0], ![0, 1, 1, 0]]], ![![![0, 2, 2, 2], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 0, 0, 0], ![0, 0, 1, 1], ![0, 0, 0, 0], ![0, 0, 1, 1]], ![![2, 0, 0, 0], ![0, 1, 0, 1], ![0, 0, 0, 0], ![0, 1, 0, 1]], ![![2, 0, 0, 0], ![0, 1, 1, 0], ![0, 0, 0, 0], ![0, 1, 1, 0]]], ![![![0, 2, 2, 2], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 0, 0, 0], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 0, 0]], ![![2, 0, 0, 0], ![0, 1, 0, 1], ![0, 1, 0, 1], ![0, 0, 0, 0]], ![![2, 0, 0, 0], ![0, 1, 1, 0], ![0, 1, 1, 0], ![0, 0, 0, 0]]]] u.1 u.2 v.1 v.2
private theorem table_ok : hessTable point=entries := by decide +kernel
private theorem spanning : entries=entries.submatrix id pick*coordinates := by decide +kernel
private theorem inverse_ok : inverseMinor*entries.submatrix pick pick=1 := by decide +kernel

theorem characteristic_three_11 (K : Type*) [Field K] (three_zero : (3:K)=0) :
    PermanentOrderThree.AtOrder K 4 11 := by
  let _ : CharP K 3 := (CharP.charP_iff_prime_eq_zero (by decide : Nat.Prime 3)).mpr (by simpa using three_zero)
  exact transfer_witness (ZMod.castHom (dvd_refl 3) K) point entries pick coordinates inverseMinor 1 1
    (by decide +kernel) (by decide +kernel) table_ok spanning inverse_ok
#print axioms characteristic_three_11
end PermanentOrderFour
