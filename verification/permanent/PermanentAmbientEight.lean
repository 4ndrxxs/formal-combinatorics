import PermanentPrincipal
import PermanentTwelveShapes

/-! Rank-eight ambient Hessian tests supported on thirteen-cell boards. -/

noncomputable section
open Matrix QuinticPencil
namespace PermanentFive
variable (K : Type*) [Field K]

def HasAmbientEight (S : Finset Cell) : Prop :=
  ∃ z : Cell → K, (∀ i ∉ S, z i = 0) ∧ 8 ≤ (hessian (per K Idx) z).rank

def boardPoint (S : Finset Cell) (i : Cell) : ℤ := if i ∈ S then 1 else 0

theorem ambient_eight_of_integers [CharZero K] (S : Finset Cell) (r c : Fin 8 → Cell)
    (A : Matrix (Fin 8) (Fin 8) ℤ) (entries : ∀ i j, secondAt (boardPoint S) (r i) (c j) = A i j)
    (nonsingular : A.det ≠ 0) : HasAmbientEight K S := by
  refine ⟨(Int.castRingHom K) ∘ boardPoint S,?_,integer_hessian_rank K _ r c A entries nonsingular⟩
  intro i hi
  simp [boardPoint,hi]

end PermanentFive
