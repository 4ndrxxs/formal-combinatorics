import SignedPowerOrbit

namespace Signed39.Shape

open Finset Contraction Template

local instance : Fact (Nat.Prime 47) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

private def tag (i:ZMod 47) : Bool := [1,2,3,4,6,7,8,9,12,14,16,17,18,21,24,25,27,28,32,34,36,37,42].contains i.val

theorem no_47_norm_1269 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    {k l:ℤ} {m:ℕ} (hg:Fintype.card G=47*m) (cop:Nat.Coprime 47 m) (hn:k-l=1269) :
    ¬∃f:G→ℤ,IsSDS k l f := by
  classical
  rintro ⟨f,hf⟩
  obtain ⟨K,hK,⟨E⟩⟩:=split_prime_factor hg cop
  let g:ZMod 47×Additive K→ℤ:=fun x=>f (E x)
  have h:IsSDS k l g:=pullback hf E
  obtain ⟨c,_,_,mu,flat⟩:=centered_row_corr h (s:=27) hn
  obtain ⟨L,mem,_⟩:=power_two_cover (q:=3) 3 23 23 35 (5:ZMod 47) tag
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) _ mu flat
  have none : twoForms 23 35 ((47:ℤ)*(3:ℤ)^3-(3:ℤ)^3)=[] := by decide +kernel
  exact List.not_mem_nil (none ▸ mem : L∈[])

theorem no_86339_1274_5 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=86339) :
    ¬∃f:G→ℤ,IsSDS 1274 5 f := no_47_norm_1269 G (m:=1837) hg (by decide) (by decide)

theorem no_93013_1273_4 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=93013) :
    ¬∃f:G→ℤ,IsSDS 1273 4 f := no_47_norm_1269 G (m:=1979) hg (by decide) (by decide)

#print axioms no_47_norm_1269
#print axioms no_86339_1274_5
#print axioms no_93013_1273_4

end Signed39.Shape
