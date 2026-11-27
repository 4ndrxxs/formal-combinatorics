import SignedPowerOrbit

namespace Signed39.Shape

open Finset Contraction Template

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
set_option maxRecDepth 32000
set_option maxHeartbeats 8000000

private def tag27 (i:ZMod 11) : Bool := [1, 3, 4, 5, 9].contains i.val
private def forms27 : List (List ℤ) := [[10, -5, -5, -5, -5, -5, 3, 3, 3, 3, 3], [15, -3, -3, -3, -3, -3, 0, 0, 0, 0, 0], [-10, -3, -3, -3, -3, -3, 5, 5, 5, 5, 5], [15, 0, 0, 0, 0, 0, -3, -3, -3, -3, -3], [-15, 0, 0, 0, 0, 0, 3, 3, 3, 3, 3], [10, 3, 3, 3, 3, 3, -5, -5, -5, -5, -5], [-15, 3, 3, 3, 3, 3, 0, 0, 0, 0, 0], [-10, 5, 5, 5, 5, 5, -3, -3, -3, -3, -3]]

private theorem cover27 (u:ZMod 11→ℤ) (mu:mass u=0) (flat:∀t,corr u t=(if t=0 then 297 else 0)-27) :
    ∃L∈forms27,∀F:ℤ→ℤ,(∑i,F (u i))=(L.map F).sum := by
  obtain ⟨L,hL,out⟩:=power_two_cover (q:=3) 3 5 5 16 (2:ZMod 11) tag27
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide) u mu flat
  have eq : twoForms 5 16 ((11:ℤ)*(3:ℤ)^3-(3:ℤ)^3)=forms27 := by decide +kernel
  exact ⟨L,eq ▸ hL,out⟩

theorem shape_11_27 (G:Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (m:ℕ) (k l c inv w:ℤ) (hg:Fintype.card G=11*m) (cop:Nat.Coprime 11 m)
    (hn:k-l=297) (sq:(11*c)^2=k-l+(11:ℤ)*m*l) (hi:11*inv=1+(m:ℤ)*w)
    (bad:excludes 11 m 27 k l c inv forms27) : ¬∃f:G→ℤ,IsSDS k l f :=
  exclusion G 11 m 27 k l c inv w forms27 hg cop hn (by decide) sq hi cover27 bad

#print axioms shape_11_27

end Signed39.Shape
