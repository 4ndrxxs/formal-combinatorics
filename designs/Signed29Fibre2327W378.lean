import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case2327x378
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance : Fact (Nat.Prime 179) := ⟨by decide⟩
private def W2327x378 (x:ZMod 179) : ℤ := ([0, 0, 0, 18, 30, 23, 18, 58, 30, 36, 23, 32, 48, 19, 88, 41, 60, 87, 36, 9, 53, 76, 62, 52, 48, 46, 19, 54, 88, 79, 41, 40, 60, 50, 87, 81, 66, 84, 9, 37, 53, 85, 17, 43, 62, 59, 82, 6, 78, 57, 46, 16, 49, 20, 54, 55, 29, 27, 79, 86, 71, 12, 40, 5, 1, 42, 80, 44, 28, 70, 22, 69, 66, 35, 25, 64, 39, 31, 37, 61, 83, 72, 26, 4, 17, 21, 43, 8, 3, 74, 59, 77, 82, 58, 6, 32, 78, 11, 57, 68, 76, 52, 16, 24, 49, 10, 50, 81, 84, 7, 85, 13, 29, 65, 27, 75, 20, 55, 86, 56, 71, 5, 12, 14, 70, 69, 35, 34, 1, 61, 42, 63, 80, 67, 44, 77, 28, 2, 11, 68, 22, 24, 10, 51, 7, 13, 65, 75, 25, 56, 64, 14, 39, 34, 31, 63, 67, 47, 2, 38, 83, 51, 72, 45, 26, 73, 4, 33, 47, 38, 21, 45, 73, 33, 8, 15, 3, 15, 74] : List ℤ).getD x.val 0
private theorem W2327x378Levels : ∀x:ZMod 179,(89:ℤ)∣(if x=0 then (0:ℤ) else 1)+W2327x378 (14 • x)-W2327x378 x := by
  have done : ∀x:ZMod 179,(89:ℤ)∣(if x=0 then (0:ℤ) else 1)+W2327x378 ((14:ZMod 179)*x)-W2327x378 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((14:ℕ):ZMod 179)=14 by decide]; exact done x

theorem fibre_2327_378 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=2327) :
    ¬∃f:G→ℤ,IsSDS 378 1 f := by
  apply long_prime_pair_transfer G 13 179 (by decide) hg
  exact long_sign_exclusion 13 179 29 14 64 124 14 89 378 1 52 ⟨29,1,9,267⟩ ⟨29,0,9,267⟩
    (by decide) W2327x378 W2327x378Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_2327_378
end Case2327x378

end Signed39.Contraction
