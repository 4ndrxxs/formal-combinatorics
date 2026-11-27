import PermanentSimultaneous
import PermanentBlockCover
import PermanentRowPairBlock
import PermanentColPairBlock
import PermanentCrossPairBlock
import PermanentMixedBlock
import PermanentTenBlock

/-! The unrestricted determinantal complexity of the generic permanent of
order five is at least twenty over every characteristic-zero field. -/

noncomputable section
open Matrix MvPolynomial Module QuinticPencil
namespace PermanentFive
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

theorem determinantal_lower_bound_twenty (A : Matrix n n K) (F : Cell → Matrix n n K)
    (rep : per K Idx = (affineMatrix A F).det) : 20 ≤ Fintype.card n := by
  obtain ⟨S,ambient,restricted⟩ := simultaneous_coordinate_bounds A F rep
  by_cases small : S.card ≤ 13
  · have block := small_covered_block S small (coordinate_matching_bound S _ ambient)
      (row_pair_block K) (col_pair_block K) (cross_pair_block K) (mixed_block K)
    exact block.bound _ restricted
  · obtain ⟨test,maximum⟩ := large_coordinate_test S _ ambient (by omega)
    have ten := row_hole_rank_ten K
    omega

#print axioms determinantal_lower_bound_twenty
end PermanentFive
