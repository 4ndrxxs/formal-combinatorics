import PermanentFifteenExclusion

/-! The refined endpoint dimension and rank bounds for an arbitrary
size-twenty-one affine representation. -/
noncomputable section
open Matrix Module QuinticPencil
namespace PermanentFive
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

theorem endpoint_rank_interval (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (size : Fintype.card n=20) :
    14 ≤ finrank K (endpoints b c).range ∧ finrank K (endpoints b c).range ≤ 20 := by
  obtain ⟨lo,hi⟩ := endpoint_dimension_interval b c D rep size
  have sum := (endpoints b c).finrank_range_add_finrank_ker
  rw [Module.finrank_pi,show Fintype.card Cell=25 by decide] at sum
  omega

theorem affine_endpoint_interval (A : Matrix n n K) (F : Cell → Matrix n n K)
    (rep : per K Idx = (affineMatrix A F).det) (size : Fintype.card n = 21) :
    ∃ (b c : Fin A.rank → Cell → K) (D : Fin A.rank → Fin A.rank → Cell → K),
      per K Idx = regularDet b c D ∧
      (5 ≤ finrank K (endpoints b c).ker ∧ finrank K (endpoints b c).ker ≤ 11) ∧
      (14 ≤ finrank K (endpoints b c).range ∧ finrank K (endpoints b c).range ≤ 20) := by
  have reg := polynomial_regularity (affineMatrix A F) rep
  have origin : (MvPolynomial.eval 0).mapMatrix (affineMatrix A F) = A := by
    ext i j
    simp [affineMatrix,Matrix.sum_apply]
  rw [origin] at reg
  obtain ⟨b,c,D,normal⟩ := normalize_regular A F reg rep (d:=3) (per_homogeneous K Idx)
  have dim : Fintype.card (Fin A.rank)=20 := by rw [Fintype.card_fin]; omega
  exact ⟨b,c,D,normal,endpoint_dimension_interval b c D normal dim,endpoint_rank_interval b c D normal dim⟩

#print axioms affine_endpoint_interval
end PermanentFive
