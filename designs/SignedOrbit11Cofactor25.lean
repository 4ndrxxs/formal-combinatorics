import SignedPowerOrbit

namespace Signed39.Shape

open Finset Contraction Template

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def tag (i:ZMod 11) : Bool := [1,3,4,5,9].contains i.val
private def forms : List (List ℤ) := [[0,-5,-5,-5,-5,-5,5,5,5,5,5],[15,-2,-2,-2,-2,-2,-1,-1,-1,-1,-1],[15,-1,-1,-1,-1,-1,-2,-2,-2,-2,-2],[-15,1,1,1,1,1,2,2,2,2,2],[-15,2,2,2,2,2,1,1,1,1,1],[0,5,5,5,5,5,-5,-5,-5,-5,-5]]

private theorem cover (u : ZMod 11→ℤ) (mu:mass u=0) (flat:∀t,corr u t=(if t=0 then 275 else 0)-25) :
    ∃L∈forms,∀F:ℤ→ℤ,(∑i,F (u i))=(L.map F).sum := by
  obtain ⟨L,hL,out⟩:=power_two_cover (q:=5) 2 5 5 15 (2:ZMod 11) tag
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) u mu flat
  have eq : twoForms 5 15 ((11:ℤ)*(5:ℤ)^2-(5:ℤ)^2)=forms := by decide +kernel
  exact ⟨L,eq ▸ hL,out⟩

theorem no_473_300_25 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=473) :
    ¬∃f:G→ℤ,IsSDS 300 25 f := exclusion G 11 43 25 300 25 10 4 1 forms hg
  (by decide) (by decide) (by decide) (by decide) (by decide) cover (by decide +kernel)

#print axioms no_473_300_25

theorem no_869_609_334 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=869) :
    ¬∃f:G→ℤ,IsSDS 609 334 f := exclusion G 11 79 25 609 334 49 36 5 forms hg
  (by decide) (by decide) (by decide) (by decide) (by decide) cover (by decide +kernel)

#print axioms no_869_609_334

theorem no_1375_277_2 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=1375) :
    ¬∃f:G→ℤ,IsSDS 277 2 f := exclusion G 11 125 25 277 2 5 91 8 forms hg
  (by decide) (by decide) (by decide) (by decide) (by decide) cover (by decide +kernel)

#print axioms no_1375_277_2

theorem no_1661_276_1 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg:Fintype.card G=1661) :
    ¬∃f:G→ℤ,IsSDS 276 1 f := exclusion G 11 151 25 276 1 4 55 4 forms hg
  (by decide) (by decide) (by decide) (by decide) (by decide) cover (by decide +kernel)

#print axioms no_1661_276_1

end Signed39.Shape
