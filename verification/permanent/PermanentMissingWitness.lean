import PermanentWitnesses

/-! A six-by-six Hessian minor that survives the removal of one entry from
three complete rows. It has two diagonal blocks equal to four times the
off-diagonal adjacency matrix on three points. -/

noncomputable section
namespace PermanentFive
open Matrix QuinticPencil

def rowHole (c : Cell) : ℤ := if c = (0,0) then 0 else rowPoint c
private def holeRows : Fin 6 → Cell := ![(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)]
private def holeCols : Fin 6 → Cell := ![(4,1),(4,2),(4,3),(3,1),(3,2),(3,3)]
private def holeMinor : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of fun i j ↦
  if i.val / 3 = j.val / 3 ∧ i.val % 3 ≠ j.val % 3 then 4 else 0

set_option maxRecDepth 15000 in
set_option maxHeartbeats 4000000 in
private theorem hole_entries : ∀ i j : Fin 6,
    secondAt rowHole (holeRows i) (holeCols j) = holeMinor i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 15000 in
set_option maxHeartbeats 4000000 in
private theorem hole_det : holeMinor.det = 16384 := by decide +kernel

theorem row_hole_rank (K : Type*) [Field K] [CharZero K] :
    6 ≤ (hessian (per K Idx) ((Int.castRingHom K) ∘ rowHole)).rank :=
  integer_hessian_rank K _ _ _ holeMinor hole_entries (by rw [hole_det]; decide)

#print axioms row_hole_rank
end PermanentFive
