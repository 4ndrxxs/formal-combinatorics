import PermanentThreeRowsRigid
import PermanentBoardRigidity

/-! At the largest remaining endpoint dimension the actual kernel is the
whole coordinate space on three rows or on three columns. -/

noncomputable section
open Matrix Module Equiv MvPolynomial QuinticPencil
namespace PermanentFive
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

private def Singular (x : Cell → K) : Prop :=
  ∀ i, MvPolynomial.eval x (pderiv i (per K Idx)) = 0

private theorem top_three (u : Cell) : u ∈ shapeModel 11 ↔ u.1.val < 3 := by
  obtain ⟨i,j⟩ := u
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem top_rigid : BoardRigidity (Singular (K:=K)) (shapeModel 11) := by
  intro L sing free
  obtain ⟨w,hw,one⟩ := free (fun _ ↦ 1)
  intro x hx u outside
  exact three_rows_rigid L (fun y hy i ↦ (grad_formula y i).symm.trans (sing y hy i)) w hw
    (fun i j hi ↦ one (i,j) ((top_three _).mpr hi)) x hx u.1 u.2
    (Nat.le_of_not_lt (fun h ↦ outside ((top_three _).mpr h)))

private theorem only_fifteen (i : Fin 12) : (shapeModel i).card = 15 → i = 11 := by
  fin_cases i <;> decide +kernel

/-- A size-twenty-one normalized pencil with endpoint dimension fifteen
has as its actual kernel one full three-row or three-column coordinate space. -/
theorem fifteen_kernel_equals_strip (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (small : Fintype.card n ≤ 20)
    (dim : finrank K (endpoints b c).ker = 15) :
    ∃ S : Finset Cell, SameBoard (shapeModel 11) S ∧ (endpoints b c).ker = boardSpace K S := by
  let L := (endpoints b c).ker
  obtain ⟨S,card,free,paths⟩ := PermanentDegeneration.coordinate_paths L weight weight_injective
  obtain ⟨i,orb⟩ := normalized_pivot_shape standardGridWeights b c D rep small S card free paths
  have eq : i = 11 := only_fifteen i (orb.card_eq.symm.trans (card.trans dim))
  subst i
  have rigid := BoardRigidity.orbit (Singular (K:=K))
    (fun e act y hy i ↦ ((transport e (act.rename K) y).1 i).symm.trans (hy _)) top_rigid orb
  have cut : L ≤ boardSpace K S := rigid L
    (fun x hx ↦ (normalized_partial_kernel (per_homogeneous K Idx) b c D rep x hx).1) free
  exact ⟨S,orb,eq_board_of_free S L cut free⟩

#print axioms fifteen_kernel_equals_strip
end PermanentFive
