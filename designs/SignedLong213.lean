import SignedLongTransfer

namespace Signed39.Contraction
namespace Long213

set_option maxRecDepth 16384
set_option maxHeartbeats 7500000

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 71) := ⟨by decide⟩

private def w0 (x:ZMod 71) : ℤ := ([0, 0, 19, 24, 3, 7, 8, 0, 22, 13, 26, 25, 27, 27, 19, 31, 6, 12, 32, 4, 10, 24, 9, 21, 11, 14, 11, 2, 3, 17, 15, 20, 25, 14, 31, 7, 16, 5, 23, 16, 29, 6, 8, 12, 28, 20, 5, 2, 30, 18, 33, 1, 30, 23, 21, 32, 22, 28, 1, 18, 34, 17, 4, 13, 9, 34, 33, 29, 15, 10, 26] : List ℤ).getD x.val 0
private theorem w0_levels : ∀x:ZMod 71,(35:ℤ)∣(if x=0 then (0:ℤ) else 1)+w0 (202 • x)-w0 x := by decide +kernel

private theorem product_N11021 : ¬∃f:ZMod 3×ZMod 71→ℤ,IsSDS 52 4 f :=
  long_sign_exclusion 3 71 16 202 58 65 16 35 52 4 30 ⟨2,4,46,70⟩ ⟨2,0,46,70⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N11021 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=213) :
    ¬∃f:G→ℤ,IsSDS 52 4 f := long_prime_pair_transfer G 3 71 (by decide) h product_N11021

private def w1 (x:ZMod 71) : ℤ := ([0, 0, 0, 0, 2, 1, 0, 0, 2, 0, 1, 0, 2, 0, 0, 1, 4, 4, 0, 1, 3, 0, 0, 3, 2, 2, 3, 0, 2, 4, 1, 4, 4, 2, 1, 1, 2, 3, 3, 1, 3, 2, 0, 4, 4, 1, 3, 4, 4, 3, 2, 4, 3, 2, 3, 1, 2, 4, 4, 4, 3, 4, 2, 3, 1, 1, 2, 3, 1, 3, 1] : List ℤ).getD x.val 0
private theorem w1_levels : ∀x:ZMod 71,(5:ℤ)∣(if x=0 then (0:ℤ) else 1)+w1 (199 • x)-w1 x := by decide +kernel

private theorem product_N11037 : ¬∃f:ZMod 3×ZMod 71→ℤ,IsSDS 97 22 f :=
  long_sign_exclusion 3 71 25 199 5 52 7 5 97 22 69 ⟨5,2,4,10⟩ ⟨5,0,4,10⟩
    (by decide) w1 w1_levels (by decide +kernel) (by decide +kernel)
theorem case_N11037 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=213) :
    ¬∃f:G→ℤ,IsSDS 97 22 f := long_prime_pair_transfer G 3 71 (by decide) h product_N11037

private theorem product_N11038 : ¬∃f:ZMod 3×ZMod 71→ℤ,IsSDS 100 43 f :=
  long_sign_exclusion 3 71 19 202 58 65 16 35 100 43 96 ⟨19,1,26,35⟩ ⟨19,0,26,35⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N11038 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=213) :
    ¬∃f:G→ℤ,IsSDS 100 43 f := long_prime_pair_transfer G 3 71 (by decide) h product_N11038

private def w2 (x:ZMod 71) : ℤ := ([0, 0, 0, 1, 0, 0, 1, 0, 3, 2, 0, 5, 4, 0, 0, 1, 3, 4, 5, 4, 2, 1, 5, 0, 4, 6, 5, 6, 0, 2, 3, 4, 5, 6, 2, 3, 5, 1, 4, 6, 2, 4, 1, 1, 5, 4, 1, 2, 6, 3, 6, 3, 6, 4, 6, 1, 6, 5, 2, 3, 3, 5, 4, 2, 5, 3, 6, 2, 3, 2, 1] : List ℤ).getD x.val 0
private theorem w2_levels : ∀x:ZMod 71,(7:ℤ)∣(if x=0 then (0:ℤ) else 1)+w2 (190 • x)-w2 x := by decide +kernel

private theorem product_N11041 : ¬∃f:ZMod 3×ZMod 71→ℤ,IsSDS 112 1 f :=
  long_sign_exclusion 3 71 37 190 37 68 10 7 112 1 18 ⟨37,1,6,7⟩ ⟨37,0,6,7⟩
    (by decide) w2 w2_levels (by decide +kernel) (by decide +kernel)
theorem case_N11041 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=213) :
    ¬∃f:G→ℤ,IsSDS 112 1 f := long_prime_pair_transfer G 3 71 (by decide) h product_N11041

private theorem product_N11050 : ¬∃f:ZMod 3×ZMod 71→ℤ,IsSDS 121 64 f :=
  long_sign_exclusion 3 71 19 202 58 65 16 35 121 64 117 ⟨19,1,26,35⟩ ⟨19,0,26,35⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N11050 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=213) :
    ¬∃f:G→ℤ,IsSDS 121 64 f := long_prime_pair_transfer G 3 71 (by decide) h product_N11050

private theorem product_N11066 : ¬∃f:ZMod 3×ZMod 71→ℤ,IsSDS 160 13 f :=
  long_sign_exclusion 3 71 49 202 58 65 16 35 160 13 54 ⟨7,2,66,70⟩ ⟨7,0,66,70⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N11066 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=213) :
    ¬∃f:G→ℤ,IsSDS 160 13 f := long_prime_pair_transfer G 3 71 (by decide) h product_N11066

private theorem product_N11075 : ¬∃f:ZMod 3×ZMod 71→ℤ,IsSDS 169 40 f :=
  long_sign_exclusion 3 71 43 202 58 65 16 35 169 40 93 ⟨43,1,32,35⟩ ⟨43,0,32,35⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N11075 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=213) :
    ¬∃f:G→ℤ,IsSDS 169 40 f := long_prime_pair_transfer G 3 71 (by decide) h product_N11075

private theorem product_N11079 : ¬∃f:ZMod 3×ZMod 71→ℤ,IsSDS 172 97 f :=
  long_sign_exclusion 3 71 25 199 5 52 7 5 172 97 144 ⟨5,2,4,10⟩ ⟨5,0,4,10⟩
    (by decide) w1 w1_levels (by decide +kernel) (by decide +kernel)
theorem case_N11079 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=213) :
    ¬∃f:G→ℤ,IsSDS 172 97 f := long_prime_pair_transfer G 3 71 (by decide) h product_N11079

private theorem product_N11091 : ¬∃f:ZMod 3×ZMod 71→ℤ,IsSDS 196 67 f :=
  long_sign_exclusion 3 71 43 202 58 65 16 35 196 67 120 ⟨43,1,32,35⟩ ⟨43,0,32,35⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N11091 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=213) :
    ¬∃f:G→ℤ,IsSDS 196 67 f := long_prime_pair_transfer G 3 71 (by decide) h product_N11091

private theorem product_N11103 : ¬∃f:ZMod 3×ZMod 71→ℤ,IsSDS 205 157 f :=
  long_sign_exclusion 3 71 16 202 58 65 16 35 205 157 183 ⟨2,4,46,70⟩ ⟨2,0,46,70⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N11103 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=213) :
    ¬∃f:G→ℤ,IsSDS 205 157 f := long_prime_pair_transfer G 3 71 (by decide) h product_N11103

private theorem product_N11105 : ¬∃f:ZMod 3×ZMod 71→ℤ,IsSDS 208 16 f :=
  long_sign_exclusion 3 71 64 202 58 65 16 35 208 16 60 ⟨2,6,46,70⟩ ⟨2,0,46,70⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N11105 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=213) :
    ¬∃f:G→ℤ,IsSDS 208 16 f := long_prime_pair_transfer G 3 71 (by decide) h product_N11105

#print axioms case_N11021

end Long213
end Signed39.Contraction
