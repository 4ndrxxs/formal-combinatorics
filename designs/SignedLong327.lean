import SignedLongTransfer

namespace Signed39.Contraction
namespace Long327

set_option maxRecDepth 16384
set_option maxHeartbeats 7500000

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 109) := ⟨by decide⟩

private def w0 (x:ZMod 109) : ℤ := ([0, 0, 0, 2, 0, 5, 2, 14, 0, 4, 5, 7, 2, 23, 14, 7, 15, 18, 4, 15, 5, 16, 22, 24, 2, 10, 11, 6, 14, 26, 7, 19, 15, 9, 18, 19, 4, 25, 3, 25, 5, 12, 16, 3, 22, 9, 24, 13, 17, 1, 10, 20, 11, 8, 6, 12, 14, 17, 26, 16, 7, 23, 19, 18, 15, 1, 24, 22, 18, 26, 19, 9, 4, 25, 25, 12, 3, 21, 13, 13, 20, 8, 12, 17, 16, 23, 3, 1, 22, 26, 9, 10, 24, 21, 13, 20, 17, 23, 1, 11, 10, 21, 20, 8, 11, 21, 8, 6, 6] : List ℤ).getD x.val 0
private theorem w0_levels : ∀x:ZMod 109,(27:ℤ)∣(if x=0 then (0:ℤ) else 1)+w0 (307 • x)-w0 x := by decide +kernel

private theorem product_N29170 : ¬∃f:ZMod 3×ZMod 109→ℤ,IsSDS 77 2 f :=
  long_sign_exclusion 3 109 25 307 49 83 13 27 77 2 27 ⟨5,2,16,54⟩ ⟨5,0,16,54⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N29170 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=327) :
    ¬∃f:G→ℤ,IsSDS 77 2 f := long_prime_pair_transfer G 3 109 (by decide) h product_N29170

private def w1 (x:ZMod 109) : ℤ := ([0, 0, 0, 0, 0, 8, 0, 5, 0, 0, 8, 0, 0, 0, 5, 8, 4, 3, 0, 4, 8, 5, 3, 1, 7, 7, 6, 7, 5, 1, 8, 0, 4, 6, 3, 4, 5, 2, 8, 3, 6, 5, 5, 8, 3, 6, 1, 6, 4, 1, 7, 3, 6, 7, 7, 5, 3, 2, 8, 6, 4, 2, 5, 3, 4, 2, 1, 4, 3, 1, 4, 6, 1, 2, 7, 5, 8, 2, 6, 7, 3, 7, 5, 4, 1, 2, 8, 6, 8, 1, 6, 8, 1, 2, 2, 1, 4, 2, 1, 4, 3, 2, 3, 5, 6, 2, 7, 7, 7] : List ℤ).getD x.val 0
private theorem w1_levels : ∀x:ZMod 109,(9:ℤ)∣(if x=0 then (0:ℤ) else 1)+w1 (256 • x)-w1 x := by decide +kernel

private theorem product_N29200 : ¬∃f:ZMod 3×ZMod 109→ℤ,IsSDS 167 83 f :=
  long_sign_exclusion 3 109 28 256 66 56 15 9 167 83 165 ⟨2,2,8,36⟩ ⟨7,1,6,27⟩
    (by decide) w1 w1_levels (by decide +kernel) (by decide +kernel)
theorem case_N29200 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=327) :
    ¬∃f:G→ℤ,IsSDS 167 83 f := long_prime_pair_transfer G 3 109 (by decide) h product_N29200

private theorem product_N29203 : ¬∃f:ZMod 3×ZMod 109→ℤ,IsSDS 173 26 f :=
  long_sign_exclusion 3 109 49 307 49 83 13 27 173 26 93 ⟨7,2,25,27⟩ ⟨7,0,25,27⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N29203 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=327) :
    ¬∃f:G→ℤ,IsSDS 173 26 f := long_prime_pair_transfer G 3 109 (by decide) h product_N29203

private theorem product_N29259 : ¬∃f:ZMod 3×ZMod 109→ℤ,IsSDS 254 35 f :=
  long_sign_exclusion 3 109 73 307 49 83 13 27 254 35 108 ⟨73,1,14,27⟩ ⟨73,0,14,27⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N29259 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=327) :
    ¬∃f:G→ℤ,IsSDS 254 35 f := long_prime_pair_transfer G 3 109 (by decide) h product_N29259

private theorem product_N29281 : ¬∃f:ZMod 3×ZMod 109→ℤ,IsSDS 284 92 f :=
  long_sign_exclusion 3 109 64 256 66 56 15 9 284 92 174 ⟨2,6,8,36⟩ ⟨2,0,8,36⟩
    (by decide) w1 w1_levels (by decide +kernel) (by decide +kernel)
theorem case_N29281 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=327) :
    ¬∃f:G→ℤ,IsSDS 284 92 f := long_prime_pair_transfer G 3 109 (by decide) h product_N29281

private theorem product_N29306 : ¬∃f:ZMod 3×ZMod 109→ℤ,IsSDS 314 167 f :=
  long_sign_exclusion 3 109 49 307 49 83 13 27 314 167 234 ⟨7,2,25,27⟩ ⟨7,0,25,27⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N29306 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=327) :
    ¬∃f:G→ℤ,IsSDS 314 167 f := long_prime_pair_transfer G 3 109 (by decide) h product_N29306

#print axioms case_N29170

end Long327
end Signed39.Contraction
