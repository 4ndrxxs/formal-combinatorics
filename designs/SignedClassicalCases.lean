import SignedMultiplierOrbits

/-! Concrete instances of the classical squarefree multiplier test on a three-element fibre.
The earlier solverz results already exclude these cyclic cases. -/

namespace Signed39.Contraction

private def w23 : List ℤ := [0,0,4,10,8,0,3,3,1,9,4,5,7,6,7,10,5,1,2,6,8,2,9]

theorem multiplier_69_49_10 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=69) : ¬∃ f : G → ℤ, IsSDS 49 10 f :=
  abelian_semiprime_three G 23 13 9 11 49 10 27 (fun i=>w23.getD i 0)
    hG (by decide) (by decide) (by decide +kernel)

private def w59 : List ℤ := [0,0,0,28,22,8,28,24,22,27,8,3,21,20,24,7,15,5,27,12,1,23,25,9,21,16,13,26,17,18,7,6,15,2,5,3,20,14,12,19,1,9,23,4,25,6,2,10,14,19,16,4,13,10,26,11,17,11,18]

theorem multiplier_177_64_7 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=177) : ¬∃ f : G → ℤ, IsSDS 64 7 f :=
  abelian_semiprime_three G 59 19 12 29 64 7 36 (fun i=>w59.getD i 0)
    hG (by decide) (by decide) (by decide +kernel)

private def w71 : List ℤ := [0,0,24,34,13,7,23,0,2,33,31,15,12,12,24,6,26,17,22,29,20,34,4,21,1,14,1,32,13,27,30,5,15,14,6,7,11,10,18,11,9,26,23,17,28,5,10,32,25,8,3,16,25,18,21,22,2,28,16,8,19,27,29,33,4,19,3,9,30,20,31]

theorem multiplier_213_100_43 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=213) : ¬∃ f : G → ℤ, IsSDS 100 43 f :=
  abelian_semiprime_three G 71 19 6 35 100 43 96 (fun i=>w71.getD i 0)
    hG (by decide) (by decide) (by decide +kernel)

theorem multiplier_213_121_64 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=213) : ¬∃ f : G → ℤ, IsSDS 121 64 f :=
  abelian_semiprime_three G 71 19 6 35 121 64 117 (fun i=>w71.getD i 0)
    hG (by decide) (by decide) (by decide +kernel)

private def w107 : List ℤ := [0,0,0,52,3,16,52,10,3,51,19,33,2,21,13,15,6,42,51,11,19,9,33,40,2,35,21,50,13,48,18,39,6,32,45,29,1,4,11,20,22,7,12,34,36,14,40,46,5,23,35,41,24,25,50,49,16,10,48,30,18,15,42,8,9,37,32,47,45,39,29,26,1,17,4,34,14,43,20,41,22,49,7,30,12,8,37,47,36,26,17,31,43,38,46,27,5,44,23,31,38,27,44,28,24,28,25]

theorem multiplier_321_64_7 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=321) : ¬∃ f : G → ℤ, IsSDS 64 7 f :=
  abelian_semiprime_three G 107 19 24 53 64 7 48 (fun i=>w107.getD i 0)
    hG (by decide) (by decide) (by decide +kernel)

#print axioms multiplier_69_49_10

end Signed39.Contraction
