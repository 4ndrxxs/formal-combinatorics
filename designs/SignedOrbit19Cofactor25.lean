import SignedPowerOrbit

namespace Signed39.Shape

open Finset Contraction Template

local instance : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def tag (i:ZMod 19) : Bool := [1,4,5,6,7,9,11,16,17].contains i.val
private def forms : List (List ℤ) := [[9,-5,-5,-5,-5,-5,-5,-5,-5,-5,4,4,4,4,4,4,4,4,4],[0,-5,-5,-5,-5,-5,-5,-5,-5,-5,5,5,5,5,5,5,5,5,5],[-9,-4,-4,-4,-4,-4,-4,-4,-4,-4,5,5,5,5,5,5,5,5,5],[9,4,4,4,4,4,4,4,4,4,-5,-5,-5,-5,-5,-5,-5,-5,-5],[0,5,5,5,5,5,5,5,5,5,-5,-5,-5,-5,-5,-5,-5,-5,-5],[-9,5,5,5,5,5,5,5,5,5,-4,-4,-4,-4,-4,-4,-4,-4,-4]]

private theorem cover (u : ZMod 19→ℤ) (mu:mass u=0) (flat:∀t,corr u t=(if t=0 then 475 else 0)-25) :
    ∃L∈forms,∀F:ℤ→ℤ,(∑i,F (u i))=(L.map F).sum := by
  obtain ⟨L,hL,out⟩:=power_two_cover (q:=5) 2 9 9 21 (2:ZMod 19) tag
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) u mu flat
  have eq : twoForms 9 21 ((19:ℤ)*(5:ℤ)^2-(5:ℤ)^2)=forms := by decide +kernel
  exact ⟨L,eq ▸ hL,out⟩

theorem no_2869_481_6 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=2869) :
    ¬∃f:G→ℤ,IsSDS 481 6 f := exclusion G 19 151 25 481 6 7 8 1 forms hg
  (by decide) (by decide) (by decide) (by decide) (by decide) cover (by decide +kernel)

#print axioms no_2869_481_6

theorem no_5301_476_1 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=5301) :
    ¬∃f:G→ℤ,IsSDS 476 1 f := exclusion G 19 279 25 476 1 4 235 16 forms hg
  (by decide) (by decide) (by decide) (by decide) (by decide) cover (by decide +kernel)

#print axioms no_5301_476_1

end Signed39.Shape
