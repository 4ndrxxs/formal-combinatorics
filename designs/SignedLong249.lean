import SignedLongTransfer

namespace Signed39.Contraction
namespace Long249

set_option maxRecDepth 16384
set_option maxHeartbeats 7500000

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 83) := ⟨by decide⟩

private def w0 (x:ZMod 83) : ℤ := ([0, 0, 0, 10, 39, 15, 10, 33, 39, 20, 13, 17, 8, 6, 33, 25, 37, 26, 20, 36, 13, 2, 17, 22, 8, 28, 4, 30, 31, 29, 23, 3, 37, 27, 26, 7, 18, 21, 34, 16, 11, 1, 2, 12, 15, 35, 22, 19, 6, 25, 28, 36, 4, 24, 30, 32, 31, 5, 29, 7, 23, 16, 3, 12, 35, 19, 27, 38, 24, 32, 5, 9, 18, 14, 21, 38, 34, 9, 14, 40, 11, 40, 1] : List ℤ).getD x.val 0
private theorem w0_levels : ∀x:ZMod 83,(41:ℤ)∣(if x=0 then (0:ℤ) else 1)+w0 (247 • x)-w0 x := by decide +kernel

private theorem product_N15911 : ¬∃f:ZMod 3×ZMod 83→ℤ,IsSDS 76 1 f :=
  long_sign_exclusion 3 83 25 247 41 55 4 41 76 1 18 ⟨5,2,38,82⟩ ⟨5,0,38,82⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N15911 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=249) :
    ¬∃f:G→ℤ,IsSDS 76 1 f := long_prime_pair_transfer G 3 83 (by decide) h product_N15911

private theorem product_N15916 : ¬∃f:ZMod 3×ZMod 83→ℤ,IsSDS 97 4 f :=
  long_sign_exclusion 3 83 31 247 41 55 4 41 97 4 33 ⟨31,1,27,41⟩ ⟨31,0,27,41⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N15916 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=249) :
    ¬∃f:G→ℤ,IsSDS 97 4 f := long_prime_pair_transfer G 3 83 (by decide) h product_N15916

private theorem product_N15920 : ¬∃f:ZMod 3×ZMod 83→ℤ,IsSDS 112 28 f :=
  long_sign_exclusion 3 83 28 247 41 55 4 41 112 28 84 ⟨2,2,42,82⟩ ⟨7,1,36,41⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N15920 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=249) :
    ¬∃f:G→ℤ,IsSDS 112 28 f := long_prime_pair_transfer G 3 83 (by decide) h product_N15920

private theorem product_N15925 : ¬∃f:ZMod 3×ZMod 83→ℤ,IsSDS 121 10 f :=
  long_sign_exclusion 3 83 37 247 41 55 4 41 121 10 51 ⟨37,1,39,41⟩ ⟨37,0,39,41⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N15925 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=249) :
    ¬∃f:G→ℤ,IsSDS 121 10 f := long_prime_pair_transfer G 3 83 (by decide) h product_N15925

private theorem product_N15953 : ¬∃f:ZMod 3×ZMod 83→ℤ,IsSDS 169 22 f :=
  long_sign_exclusion 3 83 49 247 41 55 4 41 169 22 75 ⟨7,2,36,41⟩ ⟨7,0,36,41⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N15953 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=249) :
    ¬∃f:G→ℤ,IsSDS 169 22 f := long_prime_pair_transfer G 3 83 (by decide) h product_N15953

private theorem product_N15962 : ¬∃f:ZMod 3×ZMod 83→ℤ,IsSDS 193 1 f :=
  long_sign_exclusion 3 83 64 247 41 55 4 41 193 1 21 ⟨2,6,42,82⟩ ⟨2,0,42,82⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N15962 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=249) :
    ¬∃f:G→ℤ,IsSDS 193 1 f := long_prime_pair_transfer G 3 83 (by decide) h product_N15962

private theorem product_N15967 : ¬∃f:ZMod 3×ZMod 83→ℤ,IsSDS 193 109 f :=
  long_sign_exclusion 3 83 28 247 41 55 4 41 193 109 165 ⟨2,2,42,82⟩ ⟨7,1,36,41⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N15967 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=249) :
    ¬∃f:G→ℤ,IsSDS 193 109 f := long_prime_pair_transfer G 3 83 (by decide) h product_N15967

private theorem product_N15977 : ¬∃f:ZMod 3×ZMod 83→ℤ,IsSDS 217 34 f :=
  long_sign_exclusion 3 83 61 247 41 55 4 41 217 34 93 ⟨61,1,23,41⟩ ⟨61,0,23,41⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N15977 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=249) :
    ¬∃f:G→ℤ,IsSDS 217 34 f := long_prime_pair_transfer G 3 83 (by decide) h product_N15977

#print axioms case_N15911

end Long249
end Signed39.Contraction
