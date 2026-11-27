import PermanentFifteenNilpotence
import PencilTransferRank
import NilpotentRankProfile

/-! On the rank-ten open subset of a fifteen-dimensional endpoint kernel,
the internal transfer has exactly five nilpotent Jordan chains of length
four, as witnessed by the ranks of its successive powers. -/

noncomputable section
open Matrix Module LinearMap QuinticPencil
namespace PermanentFive
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

theorem fifteen_transfer_rank_profile (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (size : Fintype.card n = 20)
    (dim : finrank K (endpoints b c).ker = 15) (z : Cell → K) (hz : z ∈ (endpoints b c).ker)
    (large : 10 ≤ (hessian (per K Idx) z).rank) :
    (transfer D z).rank = 15 ∧ ((transfer D z)^2).rank = 10 ∧
    ((transfer D z)^3).rank = 5 ∧ (transfer D z)^4 = 0 := by
  let A := transfer D z
  let M := A.toLin'
  have lo := hessian_rank_le_transfer_power (s:=3) (per_homogeneous K Idx) b c D rep z hz
  have r3 : 5 ≤ (A^3).rank := by change _ ≤ 2*(A^3).rank at lo; omega
  have fourth : A^4 = 0 := fifteen_transfer_fourth_zero b c D rep size.le dim z hz
  have stop : M^4 = 0 := by
    change A.toLin'^4 = 0
    rw [←Matrix.toLin'_pow,fourth]
    exact map_zero _
  have ranks (j : ℕ) : finrank K (M^j).range = (A^j).rank := by
    change finrank K (A.toLin'^j).range = _
    rw [←Matrix.toLin'_pow]
    rfl
  obtain ⟨a,b',c'⟩ := NilpotentProfile.four_step_profile M ((Module.finrank_pi K).trans size) stop
    ((ranks 3).symm ▸ r3)
  exact ⟨a,(ranks 2).symm.trans b',(ranks 3).symm.trans c',fourth⟩

theorem fifteen_has_full_transfer_profile (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (size : Fintype.card n = 20)
    (dim : finrank K (endpoints b c).ker = 15) :
    ∃ z ∈ (endpoints b c).ker, (transfer D z).rank = 15 ∧ ((transfer D z)^2).rank = 10 ∧
      ((transfer D z)^3).rank = 5 ∧ (transfer D z)^4 = 0 := by
  obtain ⟨z,hz,large⟩ := fifteen_kernel_has_rank_ten b c D rep size.le dim
  exact ⟨z,hz,fifteen_transfer_rank_profile b c D rep size dim z hz large⟩

#print axioms fifteen_transfer_rank_profile
#print axioms fifteen_has_full_transfer_profile
end PermanentFive
