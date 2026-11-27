import SignedLongTransfer

namespace Signed39.Contraction
namespace Long393

set_option maxRecDepth 16384
set_option maxHeartbeats 7500000

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 131) := ⟨by decide⟩

private def w0 (x:ZMod 131) : ℤ := ([0, 0, 0, 58, 63, 19, 58, 34, 63, 51, 19, 9, 56, 47, 34, 12, 61, 23, 51, 31, 17, 27, 9, 43, 56, 38, 47, 44, 32, 15, 12, 37, 61, 2, 21, 53, 49, 25, 29, 40, 17, 4, 27, 6, 7, 5, 41, 26, 54, 3, 38, 16, 45, 39, 44, 28, 32, 24, 13, 48, 10, 52, 35, 20, 59, 1, 2, 60, 21, 36, 53, 11, 49, 14, 23, 31, 29, 43, 40, 46, 15, 37, 4, 55, 25, 42, 6, 8, 7, 26, 5, 16, 41, 30, 24, 50, 54, 22, 3, 60, 36, 11, 14, 33, 45, 46, 39, 55, 42, 8, 28, 18, 30, 50, 22, 62, 13, 33, 48, 57, 10, 18, 52, 62, 35, 57, 20, 64, 59, 64, 1] : List ℤ).getD x.val 0
private theorem w0_levels : ∀x:ZMod 131,(65:ℤ)∣(if x=0 then (0:ℤ) else 1)+w0 (391 • x)-w0 x := by decide +kernel

private theorem product_N43003 : ¬∃f:ZMod 3×ZMod 131→ℤ,IsSDS 49 1 f :=
  long_sign_exclusion 3 131 16 391 65 87 28 65 49 1 21 ⟨2,4,66,130⟩ ⟨2,0,66,130⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N43003 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=393) :
    ¬∃f:G→ℤ,IsSDS 49 1 f := long_prime_pair_transfer G 3 131 (by decide) h product_N43003

private theorem product_N43009 : ¬∃f:ZMod 3×ZMod 131→ℤ,IsSDS 88 13 f :=
  long_sign_exclusion 3 131 25 391 65 87 28 65 88 13 72 ⟨5,2,106,130⟩ ⟨5,0,106,130⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N43009 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=393) :
    ¬∃f:G→ℤ,IsSDS 88 13 f := long_prime_pair_transfer G 3 131 (by decide) h product_N43009

private def w1 (x:ZMod 131) : ℤ := ([0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 2, 0, 4, 3, 0, 0, 0, 4, 0, 0, 0, 2, 3, 2, 0, 1, 0, 4, 1, 3, 0, 3, 4, 0, 1, 0, 2, 1, 2, 0, 2, 0, 4, 1, 4, 3, 1, 3, 0, 3, 1, 2, 4, 1, 4, 2, 1, 4, 3, 4, 2, 3, 1, 3, 4, 3, 2, 4, 2, 4, 3, 1, 3, 2, 3, 2, 0, 2, 1, 4, 1, 1, 4, 2, 1, 4, 4, 1, 3, 4, 3, 4, 3, 1, 2, 3, 4, 3, 2, 3, 3, 3, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 1, 2, 4, 1, 4, 3, 1, 3, 2, 4, 2, 1, 2, 2, 2, 1] : List ℤ).getD x.val 0
private theorem w1_levels : ∀x:ZMod 131,(5:ℤ)∣(if x=0 then (0:ℤ) else 1)+w1 (220 • x)-w1 x := by decide +kernel

private theorem product_N43036 : ¬∃f:ZMod 3×ZMod 131→ℤ,IsSDS 184 1 f :=
  long_sign_exclusion 3 131 61 220 53 67 52 5 184 1 24 ⟨61,1,3,5⟩ ⟨61,0,3,5⟩
    (by decide) w1 w1_levels (by decide +kernel) (by decide +kernel)
theorem case_N43036 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=393) :
    ¬∃f:G→ℤ,IsSDS 184 1 f := long_prime_pair_transfer G 3 131 (by decide) h product_N43036

private theorem product_N43040 : ¬∃f:ZMod 3×ZMod 131→ℤ,IsSDS 193 46 f :=
  long_sign_exclusion 3 131 49 391 65 87 28 65 193 46 135 ⟨7,2,21,65⟩ ⟨7,0,21,65⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N43040 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=393) :
    ¬∃f:G→ℤ,IsSDS 193 46 f := long_prime_pair_transfer G 3 131 (by decide) h product_N43040

private theorem product_N43041 : ¬∃f:ZMod 3×ZMod 131→ℤ,IsSDS 193 64 f :=
  long_sign_exclusion 3 131 43 391 65 87 28 65 193 64 159 ⟨43,1,54,65⟩ ⟨43,0,54,65⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N43041 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=393) :
    ¬∃f:G→ℤ,IsSDS 193 64 f := long_prime_pair_transfer G 3 131 (by decide) h product_N43041

private theorem product_N43042 : ¬∃f:ZMod 3×ZMod 131→ℤ,IsSDS 196 4 f :=
  long_sign_exclusion 3 131 64 391 65 87 28 65 196 4 42 ⟨2,6,66,130⟩ ⟨2,0,66,130⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N43042 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=393) :
    ¬∃f:G→ℤ,IsSDS 196 4 f := long_prime_pair_transfer G 3 131 (by decide) h product_N43042

private theorem product_N43045 : ¬∃f:ZMod 3×ZMod 131→ℤ,IsSDS 196 40 f :=
  long_sign_exclusion 3 131 52 391 65 87 28 65 196 40 126 ⟨2,2,66,130⟩ ⟨13,1,47,65⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N43045 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=393) :
    ¬∃f:G→ℤ,IsSDS 196 40 f := long_prime_pair_transfer G 3 131 (by decide) h product_N43045

private theorem product_N43082 : ¬∃f:ZMod 3×ZMod 131→ℤ,IsSDS 268 139 f :=
  long_sign_exclusion 3 131 43 391 65 87 28 65 268 139 234 ⟨43,1,54,65⟩ ⟨43,0,54,65⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N43082 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=393) :
    ¬∃f:G→ℤ,IsSDS 268 139 f := long_prime_pair_transfer G 3 131 (by decide) h product_N43082

private theorem product_N43095 : ¬∃f:ZMod 3×ZMod 131→ℤ,IsSDS 289 16 f :=
  long_sign_exclusion 3 131 91 391 65 87 28 65 289 16 81 ⟨7,1,21,65⟩ ⟨13,1,47,65⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N43095 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=393) :
    ¬∃f:G→ℤ,IsSDS 289 16 f := long_prime_pair_transfer G 3 131 (by decide) h product_N43095

private theorem product_N43114 : ¬∃f:ZMod 3×ZMod 131→ℤ,IsSDS 316 169 f :=
  long_sign_exclusion 3 131 49 391 65 87 28 65 316 169 258 ⟨7,2,21,65⟩ ⟨7,0,21,65⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N43114 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=393) :
    ¬∃f:G→ℤ,IsSDS 316 169 f := long_prime_pair_transfer G 3 131 (by decide) h product_N43114

private theorem product_N43117 : ¬∃f:ZMod 3×ZMod 131→ℤ,IsSDS 337 1 f :=
  long_sign_exclusion 3 131 112 391 65 87 28 65 337 1 27 ⟨2,4,66,130⟩ ⟨7,1,21,65⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N43117 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=393) :
    ¬∃f:G→ℤ,IsSDS 337 1 f := long_prime_pair_transfer G 3 131 (by decide) h product_N43117

private theorem product_N43122 : ¬∃f:ZMod 3×ZMod 131→ℤ,IsSDS 337 181 f :=
  long_sign_exclusion 3 131 52 391 65 87 28 65 337 181 267 ⟨2,2,66,130⟩ ⟨13,1,47,65⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N43122 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=393) :
    ¬∃f:G→ℤ,IsSDS 337 181 f := long_prime_pair_transfer G 3 131 (by decide) h product_N43122

private theorem product_N43123 : ¬∃f:ZMod 3×ZMod 131→ℤ,IsSDS 337 262 f :=
  long_sign_exclusion 3 131 25 391 65 87 28 65 337 262 321 ⟨5,2,106,130⟩ ⟨5,0,106,130⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N43123 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=393) :
    ¬∃f:G→ℤ,IsSDS 337 262 f := long_prime_pair_transfer G 3 131 (by decide) h product_N43123

private theorem product_N43139 : ¬∃f:ZMod 3×ZMod 131→ℤ,IsSDS 352 52 f :=
  long_sign_exclusion 3 131 100 391 65 87 28 65 352 52 144 ⟨2,2,66,130⟩ ⟨5,2,106,130⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N43139 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=393) :
    ¬∃f:G→ℤ,IsSDS 352 52 f := long_prime_pair_transfer G 3 131 (by decide) h product_N43139

private theorem product_N43143 : ¬∃f:ZMod 3×ZMod 131→ℤ,IsSDS 361 34 f :=
  long_sign_exclusion 3 131 109 391 65 87 28 65 361 34 117 ⟨109,1,8,65⟩ ⟨109,0,8,65⟩
    (by decide) w0 w0_levels (by decide +kernel) (by decide +kernel)
theorem case_N43143 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (h:Fintype.card G=393) :
    ¬∃f:G→ℤ,IsSDS 361 34 f := long_prime_pair_transfer G 3 131 (by decide) h product_N43143

#print axioms case_N43003

end Long393
end Signed39.Contraction
