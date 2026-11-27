import SignedLongLocal

namespace Signed39.Contraction

set_option maxRecDepth 32000
set_option maxHeartbeats 9000000

section Case537x88
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 179) := ⟨by decide⟩
private def W537x88 (x:ZMod 179) : ℤ := ([0, 0, 0, 88, 28, 63, 88, 66, 28, 87, 63, 18, 27, 83, 5, 62, 56, 10, 87, 44, 2, 65, 46, 7, 27, 37, 83, 86, 5, 50, 62, 67, 56, 17, 10, 40, 26, 25, 44, 82, 2, 20, 4, 52, 46, 61, 35, 59, 55, 71, 37, 9, 22, 78, 86, 81, 33, 43, 50, 15, 1, 29, 67, 64, 84, 57, 45, 47, 38, 6, 68, 11, 26, 3, 53, 36, 72, 23, 82, 51, 30, 85, 48, 69, 4, 73, 52, 49, 74, 75, 61, 60, 35, 66, 59, 18, 55, 34, 71, 16, 65, 7, 9, 58, 22, 39, 17, 40, 25, 54, 20, 24, 33, 31, 43, 70, 78, 81, 15, 76, 1, 64, 29, 19, 6, 11, 3, 8, 84, 51, 57, 41, 45, 21, 47, 60, 38, 79, 34, 16, 68, 58, 39, 12, 54, 24, 31, 70, 53, 76, 36, 19, 72, 8, 23, 41, 21, 32, 79, 77, 30, 12, 85, 42, 48, 80, 69, 13, 32, 77, 73, 42, 80, 13, 49, 14, 74, 14, 75] : List ℤ).getD x.val 0
private theorem W537x88Levels : ∀x:ZMod 179,(89:ℤ)∣(if x=0 then (0:ℤ) else 1)+W537x88 (361 • x)-W537x88 x := by
  have done : ∀x:ZMod 179,(89:ℤ)∣(if x=0 then (0:ℤ) else 1)+W537x88 ((3:ZMod 179)*x)-W537x88 x := by decide +kernel
  intro x; rw [nsmul_eq_mul,show ((361:ℕ):ZMod 179)=3 by decide]; exact done x

theorem fibre_537_88 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=537) :
    ¬∃f:G→ℤ,IsSDS 88 13 f := by
  apply long_prime_pair_transfer G 3 179 (by decide) hg
  exact long_sign_exclusion 3 179 25 361 60 90 1 89 88 13 84 ⟨5,2,24,178⟩ ⟨5,0,24,178⟩
    (by decide) W537x88 W537x88Levels (by decide +kernel) (by decide +kernel)
#print axioms fibre_537_88
end Case537x88

end Signed39.Contraction
