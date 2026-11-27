import Signed20ColdPrime11Part0
import Signed20ColdPrime11Part12
import Signed20ColdPrime11Part24
import Signed20ColdPrime11Part36
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_11_20 : divisorGrid 11 20 130 qInputs_11_20 keep_11_20 := by
  intro d
  fin_cases d
  · exact slice20x11x0
  · exact slice20x11x1
  · exact slice20x11x2
  · exact slice20x11x3
  · exact slice20x11x4
  · exact slice20x11x5
  · exact slice20x11x6
  · exact slice20x11x7
  · exact slice20x11x8
  · exact slice20x11x9
  · exact slice20x11x10
  · exact slice20x11x11
  · exact slice20x11x12
  · exact slice20x11x13
  · exact slice20x11x14
  · exact slice20x11x15
  · exact slice20x11x16
  · exact slice20x11x17
  · exact slice20x11x18
  · exact slice20x11x19
  · exact slice20x11x20
  · exact slice20x11x21
  · exact slice20x11x22
  · exact slice20x11x23
  · exact slice20x11x24
  · exact slice20x11x25
  · exact slice20x11x26
  · exact slice20x11x27
  · exact slice20x11x28
  · exact slice20x11x29
  · exact slice20x11x30
  · exact slice20x11x31
  · exact slice20x11x32
  · exact slice20x11x33
  · exact slice20x11x34
  · exact slice20x11x35
  · exact slice20x11x36
  · exact slice20x11x37
  · exact slice20x11x38
  · exact slice20x11x39


private def types_frontier_mixed_869_221_1 : List RowType := [((-11),33),((-11),55),((-11),77),((-9),35),((-9),57),((-9),79),((-7),19),((-7),41),((-7),63),((-5),29),((-5),51),((-5),73),((-3),21),((-3),43),((-3),65),((-1),17),((-1),39),((-1),61),(1,17),(1,39),(1,61),(3,21),(3,43),(3,65),(5,29),(5,51),(5,73),(7,19),(7,41),(7,63),(9,35),(9,57),(9,79),(11,33),(11,55),(11,77),(13,13),(13,35),(13,57),(13,79),(15,19),(15,41),(15,63),(17,29),(17,51),(17,73)]
private def stage_0_frontier_mixed_869_221_1 : Stage := [
  (((-11),33),⟨⟨7,(-8),0,1⟩,[0,0,0,8,0,8,0,0,0,0,0],0⟩),
  (((-11),55),⟨⟨(-1287),(-88),70,9⟩,[0,176,0,0,0,0,0,132,0,0,0],0⟩),
  (((-11),77),⟨⟨7,(-8),0,1⟩,[0,0,0,8,0,8,0,0,0,0,0],0⟩),
  (((-9),35),⟨⟨(-2289815),(-236368),71416,14639⟩,[0,472736,0,0,0,0,0,0,0,0,0],132⟩),
  (((-9),57),⟨⟨(-2289815),(-236368),71416,14639⟩,[0,472736,0,0,0,0,0,0,0,0,0],132⟩),
  (((-9),79),⟨⟨(-475475),(-20900),26600,2376⟩,[0,41800,0,0,0,0,0,0,0,0,0],0⟩),
  (((-7),19),⟨⟨(-207691),0,6004,23⟩,[0,0,0,0,0,0,0,0,0,0,0],10⟩),
  (((-7),41),⟨⟨(-1259181),(-59092),45504,4121⟩,[0,118184,55616,0,0,0,0,0,0,0,0],40⟩),
  (((-7),63),⟨⟨(-1259181),(-59092),45504,4121⟩,[0,118184,55616,0,0,0,0,0,0,0,0],40⟩),
  (((-5),29),⟨⟨(-4813391),(-198132),0,45683⟩,[0,0,0,1598960,0,0,0,2773848,410168,0,0],360⟩),
  (((-5),51),⟨⟨(-1027158),(-15642),39105,1881⟩,[0,31284,0,0,0,0,0,218988,0,0,0],25⟩),
  (((-5),73),⟨⟨(-1287),(-88),70,9⟩,[0,176,0,0,0,0,0,132,0,0,0],0⟩),
  (((-3),21),⟨⟨(-435369),(-22594),12877,2466⟩,[0,45188,0,135564,0,0,0,26070,0,0,0],12⟩),
  (((-3),43),⟨⟨(-1257443),(-45188),29704,5487⟩,[0,90376,0,444928,0,69520,0,0,173800,0,0],44⟩),
  (((-3),65),⟨⟨(-437107),0,18170,617⟩,[0,0,0,0,0,0,0,0,0,0,0],8⟩),
  (((-1),17),⟨⟨(-68651),0,0,539⟩,[0,0,0,0,0,0,0,0,0,0,0],4⟩),
  (((-1),39),⟨⟨(-68651),0,0,539⟩,[0,0,0,0,0,0,0,0,0,0,0],4⟩),
  (((-1),61),⟨⟨(-68651),0,0,539⟩,[0,0,0,0,0,0,0,0,0,0,0],4⟩),
  ((1,17),⟨⟨(-68651),0,0,539⟩,[0,0,0,0,0,0,0,0,0,0,0],4⟩),
  ((1,39),⟨⟨(-68651),0,0,539⟩,[0,0,0,0,0,0,0,0,0,0,0],4⟩),
  ((1,61),⟨⟨(-68651),0,0,539⟩,[0,0,0,0,0,0,0,0,0,0,0],4⟩),
  ((3,21),⟨⟨(-435369),(-22594),12877,2466⟩,[0,45188,0,135564,0,0,0,26070,0,0,0],12⟩),
  ((3,43),⟨⟨(-1257443),(-45188),29704,5487⟩,[0,90376,0,444928,0,69520,0,0,173800,0,0],44⟩),
  ((3,65),⟨⟨(-636977),(-24332),20856,2893⟩,[0,48664,0,145992,0,0,0,0,0,0,0],16⟩),
  ((5,29),⟨⟨(-4813391),(-198132),0,45683⟩,[0,0,0,1598960,0,0,0,2773848,410168,0,0],360⟩),
  ((5,51),⟨⟨(-1027158),(-15642),39105,1881⟩,[0,31284,0,0,0,0,0,218988,0,0,0],25⟩),
  ((5,73),⟨⟨(-148599),0,7110,141⟩,[0,0,0,0,0,0,0,0,0,0,0],2⟩),
  ((7,19),⟨⟨(-207691),0,6004,23⟩,[0,0,0,0,0,0,0,0,0,0,0],10⟩),
  ((7,41),⟨⟨(-207691),0,6004,23⟩,[0,0,0,0,0,0,0,0,0,0,0],10⟩),
  ((7,63),⟨⟨(-1259181),(-59092),45504,4121⟩,[0,118184,55616,0,0,0,0,0,0,0,0],40⟩),
  ((9,35),⟨⟨(-3555000),0,0,5000⟩,[0,0,0,0,0,0,0,0,0,0,0],711⟩),
  ((9,57),⟨⟨(-35035),(-1540),1960,176⟩,[0,3080,0,0,0,0,0,0,0,0,0],0⟩),
  ((9,79),⟨⟨(-475475),(-20900),26600,2376⟩,[0,41800,0,0,0,0,0,0,0,0,0],0⟩),
  ((11,55),⟨⟨(-35035),(-1540),1960,176⟩,[0,3080,0,0,0,0,0,0,0,0,0],0⟩),
  ((11,77),⟨⟨(-1287),(-88),70,9⟩,[0,176,0,0,0,0,0,132,0,0,0],0⟩),
  ((13,13),⟨⟨(-33891),0,0,165⟩,[0,0,0,0,0,0,0,0,0,0,0],7⟩),
  ((13,35),⟨⟨(-101673),(-31284),0,2937⟩,[0,62568,0,0,0,0,0,0,0,0,0],14⟩),
  ((13,57),⟨⟨(-10010),(-440),560,77⟩,[0,880,0,0,0,0,0,0,0,0,0],0⟩),
  ((13,79),⟨⟨(-739739),(-32516),41384,3696⟩,[0,65032,0,0,0,0,0,0,0,0,0],0⟩),
  ((15,19),⟨⟨(-2262007),(-5214),0,2101⟩,[0,0,0,0,0,0,0,72996,0,0,0],240⟩),
  ((15,41),⟨⟨(-75603),0,0,99⟩,[0,0,0,0,0,0,0,0,0,0,0],8⟩),
  ((15,63),⟨⟨(-289377),(-45188),7268,7377⟩,[0,90376,0,0,0,0,0,0,0,0,0],12⟩),
  ((17,29),⟨⟨(-13035),0,0,55⟩,[0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((17,51),⟨⟨(-13035),0,0,55⟩,[0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((17,73),⟨⟨(-13035),0,0,55⟩,[0,0,0,0,0,0,0,0,0,0,0],1⟩)]
private theorem frontier_mixed_869_221_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=869) : ¬∃ f : G → ℤ, IsSDS 221 1 f :=
  abelian_short_mixed G 11 79 14 4 2 5 221 1 20 3 8 29 36 5
    types_frontier_mixed_869_221_1 [stage_0_frontier_mixed_869_221_1] ⟨⟨(-10),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4829_229_9 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4829) : ¬∃ f : G → ℤ, IsSDS 229 9 f :=
  abelian_short_linear G 11 439 14 0 2 5 229 9 20 19 8 29
    ⟨⟨(-650000),(-546000),70875,19656⟩,[0,156000,0,0,260000,0,0,0,156000,0,728000],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4829_4640_4420 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4829) : ¬∃ f : G → ℤ, IsSDS 4640 4420 f :=
  abelian_short_linear G 11 439 14 0 2 5 4640 4420 20 420 8 29
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5401_225_5 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5401) : ¬∃ f : G → ℤ, IsSDS 225 5 f :=
  abelian_short_linear G 11 491 14 2 2 5 225 5 20 15 8 29
    ⟨⟨0,(-5973),644,183⟩,[0,0,4862,0,1408,2750,0,0,0,0,4158],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5401_5296_5076 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5401) : ¬∃ f : G → ℤ, IsSDS 5296 5076 f :=
  abelian_short_linear G 11 491 14 1 2 5 5296 5076 20 476 8 29
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_27005_221_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=27005) : ¬∃ f : G → ℤ, IsSDS 221 1 f :=
  abelian_short_linear G 11 2455 14 2 2 5 221 1 20 15 8 29
    ⟨⟨(-1331264),0,79422,(-18909)⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_27005_26896_26676 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=27005) : ¬∃ f : G → ℤ, IsSDS 26896 26676 f :=
  abelian_short_linear G 11 2455 14 1 2 5 26896 26676 20 2440 8 29
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_11_20_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=11*m)
    (hm : 11 < m) (hn : k-l=(11:ℤ)*20) : False := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have row := endpoint_case (s:=20) hf hg hn (by decide) hm grid_11_20
  simp only [keep_11_20,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=221 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_869_221_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=229 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4829_229_9 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4640 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4829_4640_4420 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=225 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5401_225_5 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=5296 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5401_5296_5076 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=221 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_27005_221_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=26896 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_27005_26896_26676 G hg ⟨f,hf⟩

end Signed39.Contraction
