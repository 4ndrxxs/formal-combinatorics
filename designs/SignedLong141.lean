import SignedLongTransfer

namespace Signed39.Contraction
namespace Long141

set_option maxRecDepth 16384
set_option maxHeartbeats 7500000

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 47) := ⟨by decide⟩

private def w0 (x:ZMod 47) : ℤ := ([0, 0, 5, 3, 10, 0, 8, 14, 15, 6, 5, 17, 13, 13, 19, 3, 20, 7, 11, 2, 10, 17, 22, 19, 18, 21, 18, 9, 1, 12, 8, 21, 2, 20, 12, 14, 16, 4, 7, 16, 15, 9, 22, 11, 4, 6, 1] : List ℤ).getD x.val 0
private theorem w0_levels : ∀x:ZMod 47,(23:ℤ)∣(if x=0 then (0:ℤ) else 1)+w0 (136 • x)-w0 x := by decide +kernel

private theorem product_N4550 : ¬∃f:ZMod 3×ZMod 47→ℤ,IsSDS 64 16 f :=
  long_sign_exclusion 3 47 16 136 28 39 15 23 64 16 48 ⟨2,4,32,46⟩ ⟨2,0,32,46⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N4550 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=141) :
    ¬∃f:G→ℤ,IsSDS 64 16 f := long_prime_pair_transfer G 3 47 (by decide) h product_N4550

private theorem product_N4560 : ¬∃f:ZMod 3×ZMod 47→ℤ,IsSDS 85 1 f :=
  long_sign_exclusion 3 47 28 136 28 39 15 23 85 1 15 ⟨2,2,32,46⟩ ⟨7,1,18,23⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N4560 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=141) :
    ¬∃f:G→ℤ,IsSDS 85 1 f := long_prime_pair_transfer G 3 47 (by decide) h product_N4560

private theorem product_N4562 : ¬∃f:ZMod 3×ZMod 47→ℤ,IsSDS 100 25 f :=
  long_sign_exclusion 3 47 25 136 28 39 15 23 100 25 60 ⟨5,2,24,46⟩ ⟨5,0,24,46⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N4562 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=141) :
    ¬∃f:G→ℤ,IsSDS 100 25 f := long_prime_pair_transfer G 3 47 (by decide) h product_N4562

private theorem product_N4569 : ¬∃f:ZMod 3×ZMod 47→ℤ,IsSDS 109 61 f :=
  long_sign_exclusion 3 47 16 136 28 39 15 23 109 61 93 ⟨2,4,32,46⟩ ⟨2,0,32,46⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N4569 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=141) :
    ¬∃f:G→ℤ,IsSDS 109 61 f := long_prime_pair_transfer G 3 47 (by decide) h product_N4569

private theorem product_N4583 : ¬∃f:ZMod 3×ZMod 47→ℤ,IsSDS 121 10 f :=
  long_sign_exclusion 3 47 37 136 28 39 15 23 121 10 39 ⟨37,1,17,23⟩ ⟨37,0,17,23⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N4583 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=141) :
    ¬∃f:G→ℤ,IsSDS 121 10 f := long_prime_pair_transfer G 3 47 (by decide) h product_N4583

private theorem product_N4585 : ¬∃f:ZMod 3×ZMod 47→ℤ,IsSDS 121 46 f :=
  long_sign_exclusion 3 47 25 136 28 39 15 23 121 46 81 ⟨5,2,24,46⟩ ⟨5,0,24,46⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N4585 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=141) :
    ¬∃f:G→ℤ,IsSDS 121 46 f := long_prime_pair_transfer G 3 47 (by decide) h product_N4585

#print axioms case_N4550

end Long141
end Signed39.Contraction
