import SignedBudgetCertificate

/-! Additional catalogue rows and two order-1169 cases excluded by residue capacities. The certified row-mass window bounds the finite reductions in this file. -/

namespace Signed39.CapacityCases

open Signed39.Contraction

theorem no_N11103 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg : Fintype.card G=213) :
    ¬ ∃ f : G → ℤ, IsSDS 205 157 f :=
  abelian_short_linear G 3 71 5 2 1 0 205 157 16 61 2 21 ⟨⟨4524,(-136),0,1⟩,[0,0,91],0⟩ hg (by decide +kernel)

theorem no_N11598 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg : Fintype.card G=217) :
    ¬ ∃ f : G → ℤ, IsSDS 100 44 f :=
  abelian_short_linear G 7 31 6 0 1 0 100 44 8 14 4 9 ⟨⟨0,(-72),45,1⟩,[182,0,0,170,0,0,0],0⟩ hg (by decide +kernel)

theorem no_N11607 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg : Fintype.card G=217) :
    ¬ ∃ f : G → ℤ, IsSDS 121 65 f :=
  abelian_short_linear G 7 31 6 0 1 0 121 65 8 17 4 9 ⟨⟨(-4),(-1),1,0⟩,[4,0,0,4,0,0,0],0⟩ hg (by decide +kernel)

theorem no_N23274 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg : Fintype.card G=295) :
    ¬ ∃ f : G → ℤ, IsSDS 49 4 f :=
  abelian_short_linear G 5 59 6 1 1 0 49 4 9 7 2 7 ⟨⟨0,(-101),21,8⟩,[0,24,84,0,0],0⟩ hg (by decide +kernel)

theorem no_N34503 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg : Fintype.card G=355) :
    ¬ ∃ f : G → ℤ, IsSDS 46 1 f :=
  abelian_short_linear G 5 71 6 2 1 0 46 1 9 4 2 7 ⟨⟨(-12),(-80),15,7⟩,[12,0,0,54,0],0⟩ hg (by decide +kernel)

theorem no_N41317 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg : Fintype.card G=385) :
    ¬ ∃ f : G → ℤ, IsSDS 100 1 f :=
  abelian_short_linear G 11 35 9 1 1 0 100 1 9 2 8 13 ⟨⟨(-462),(-55),30,7⟩,[462,0,0,0,0,0,0,0,0,0,0],0⟩ hg (by decide +kernel)

theorem no_N51481 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg : Fintype.card G=429) :
    ¬ ∃ f : G → ℤ, IsSDS 397 349 f :=
  abelian_short_linear G 3 143 5 1 1 0 397 349 16 129 2 21 ⟨⟨0,(-280),0,1⟩,[19311,19344,19591],0⟩ hg (by decide +kernel)

theorem no_N62935 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg : Fintype.card G=473) :
    ¬ ∃ f : G → ℤ, IsSDS 192 16 f :=
  abelian_short_linear G 11 43 12 2 1 0 192 16 16 8 10 29 ⟨⟨0,(-52440),11115,2392⟩,[0,0,0,0,0,0,0,61180,0,0,0],0⟩ hg (by decide +kernel)

theorem no_1169_57_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg : Fintype.card G=1169) :
    ¬ ∃ f : G → ℤ, IsSDS 57 1 f :=
  abelian_short_linear G 7 167 6 1 1 0 57 1 8 5 4 9 ⟨⟨(-1199),(-180),78,5⟩,[1199,360,759,212,0,39,0],0⟩ hg (by decide +kernel)

theorem no_1169_1156_1100 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G] (hg : Fintype.card G=1169) :
    ¬ ∃ f : G → ℤ, IsSDS 1156 1100 f :=
  abelian_short_linear G 7 167 6 0 1 0 1156 1100 8 162 4 9 ⟨⟨23547,(-26),0,(-1)⟩,[0,0,0,0,0,0,8684],0⟩ hg (by decide +kernel)

#print axioms no_1169_57_1

end Signed39.CapacityCases
