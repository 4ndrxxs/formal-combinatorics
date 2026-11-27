import PermanentBoardRigidity
import PermanentTwoRowsRankRigid

/-! In dimension ten the actual common kernel is a whole pair of coordinate
rows or a whole pair of coordinate columns. The proof uses the universal
cubic minor identities in the lower Hessian block. -/

noncomputable section
open Matrix Module Equiv QuinticPencil
namespace PermanentFive
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

private theorem top_two (u : Cell) : u ∈ shapeModel 8 ↔ u.1.val < 2 := by
  obtain ⟨i,j⟩ := u
  fin_cases i <;> fin_cases j <;> decide +kernel

private def SmallRank (x : Cell → K) : Prop := (hessian (per K Idx) x).rank ≤ 5

private theorem two_rigid : BoardRigidity (SmallRank (K:=K)) (shapeModel 8) := by
  intro L small free
  obtain ⟨w,hw,top⟩ := free ((Int.castRingHom K) ∘ twoRowPoint)
  intro x hx u outside
  exact two_rows_rank_rigid w x (fun i j hi ↦ top (i,j) ((top_two _).mpr hi))
    (fun a ↦ small _ (L.add_mem hw (L.smul_mem a hx))) u.1 u.2
    (Nat.le_of_not_lt (fun h ↦ outside ((top_two _).mpr h)))

private theorem only_ten (i : Fin 12) : (shapeModel i).card = 10 → i = 8 := by
  fin_cases i <;> decide +kernel

/-- At endpoint dimension ten and size at most twenty-one the kernel itself
is a coordinate space of two full parallel input lines. -/
theorem ten_kernel_equals_strip (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (small : Fintype.card n ≤ 20)
    (dim : finrank K (endpoints b c).ker = 10) :
    ∃ S : Finset Cell, SameBoard (shapeModel 8) S ∧ (endpoints b c).ker = boardSpace K S := by
  let L := (endpoints b c).ker
  obtain ⟨S,card,free,paths⟩ := PermanentDegeneration.coordinate_paths L weight weight_injective
  obtain ⟨i,orb⟩ := normalized_pivot_shape standardGridWeights b c D rep small S card free paths
  have eq : i = 8 := only_ten i (orb.card_eq.symm.trans (card.trans dim))
  subst i
  have rigid := BoardRigidity.orbit (SmallRank (K:=K))
    (fun e act y hy ↦ by
      change (hessian (per K Idx) y).rank ≤ 5
      rw [← (transport e (act.rename K) y).2]
      exact hy) two_rigid orb
  have cut : L ≤ boardSpace K S := rigid L (fun x hx ↦ by
    have h := (normalized_partial_kernel (per_homogeneous K Idx) b c D rep x hx).2
    rw [dim] at h
    change 25 + (hessian (per K Idx) x).rank ≤ Fintype.card n + 10 at h
    change (hessian (per K Idx) x).rank ≤ 5
    omega) free
  exact ⟨S,orb,eq_board_of_free S L cut free⟩

#print axioms ten_kernel_equals_strip
end PermanentFive
