import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def qInputs_13_16 : ℕ → Option QuotientInput
  | 29 => some ⟨29,13,7,0,16⟩
  | 51 => some ⟨17,13,2,0,16⟩
  | 87 => some ⟨29,13,7,0,16⟩
  | 101 => some ⟨101,13,25,0,16⟩
  | 113 => some ⟨113,13,28,0,16⟩
  | 173 => some ⟨173,13,43,0,16⟩
  | 519 => some ⟨173,13,43,0,16⟩
  | 1037 => some ⟨17,13,2,0,16⟩
  | 1557 => some ⟨173,13,43,0,16⟩
  | 2909 => some ⟨2909,13,727,0,16⟩
  | _ => none

private def keep_13_16 : List (ℕ × ℤ) := [(23,27),(27,23),(43,87),(43,204),(53,153),(53,192),(61,17),(61,576),(69,9),(69,48),(69,529),(81,64),(81,597),(103,3),(107,12),(107,1143),(129,29),(129,1264),(207,3),(207,16),(207,2291),(211,12),(211,2391),(309,1),(321,4),(321,3917),(621,1),(633,4),(633,7869),(727,3),(727,9116),(2181,1),(2181,28016)]

private theorem grid_13_16 : divisorGrid 13 16 112 qInputs_13_16 keep_13_16 := by decide +kernel

private theorem frontier_mixed_299_235_27 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=299) : ¬∃ f : G → ℤ, IsSDS 235 27 f :=
  abelian_short_linear G 13 23 13 1 2 6 235 27 16 7 11 27
    ⟨⟨1,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_351_231_23 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=351) : ¬∃ f : G → ℤ, IsSDS 231 23 f :=
  abelian_short_linear G 13 27 13 1 2 6 231 23 16 7 11 27
    ⟨⟨(-45),1,2,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_559_295_87 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=559) : ¬∃ f : G → ℤ, IsSDS 295 87 f :=
  abelian_short_linear G 13 43 13 1 2 6 295 87 16 17 11 27
    ⟨⟨(-29),0,1,0⟩,[0,0,2,0,0,0,0,0,0,0,4,2,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_559_412_204 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=559) : ¬∃ f : G → ℤ, IsSDS 412 204 f :=
  abelian_short_linear G 13 43 13 1 2 6 412 204 16 26 11 27
    ⟨⟨0,0,242,(-15)⟩,[0,0,2080,0,0,0,0,676,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_689_361_153 : List RowType := [(13,39),(15,17),(15,43),(17,29),(19,23),(19,49),(21,25),(21,51),(23,35),(25,27),(27,27),(29,35),(31,51)]
private def stage_0_frontier_mixed_689_361_153 : Stage := [
  ((13,39),⟨⟨0,0,0,(-286)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],31⟩),
  ((15,17),⟨⟨0,0,0,(-13460000)⟩,[0,0,225910000,0,0,0,0,0,0,0,1622985000,0,0],5601379⟩),
  ((15,43),⟨⟨(-13091),0,2014,(-103)⟩,[0,6890,0,13780,0,0,0,0,0,0,0,0,0],3⟩),
  ((19,49),⟨⟨0,0,43937,(-3091)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,71656],144⟩),
  ((21,25),⟨⟨0,(-4186),0,0⟩,[0,0,0,80288,10712,0,0,0,0,0,0,0,0],31⟩),
  ((21,51),⟨⟨(-1217463),0,42612,(-765)⟩,[0,0,0,231504,0,0,132288,0,0,0,0,0,0],104⟩),
  ((25,27),⟨⟨0,(-5148),0,0⟩,[0,90246,0,0,23816,0,0,0,0,0,0,0,0],25⟩),
  ((27,27),⟨⟨0,0,0,(-15378)⟩,[0,7878662,0,0,0,0,0,0,0,0,0,0,0],4929⟩),
  ((29,35),⟨⟨0,(-1040),0,0⟩,[0,0,0,0,0,0,0,0,9906,0,0,0,0],9⟩)]
private theorem frontier_mixed_689_361_153 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=689) : ¬∃ f : G → ℤ, IsSDS 361 153 f :=
  abelian_short_mixed G 13 53 13 1 2 6 361 153 16 25 11 27 49 12
    types_frontier_mixed_689_361_153 [stage_0_frontier_mixed_689_361_153] ⟨⟨64,(-7),3,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_689_400_192 : List RowType := [(16,22),(16,48),(18,38),(20,36),(22,42),(24,30),(26,26),(26,52),(28,30),(30,42),(36,48),(38,40)]
private def stage_0_frontier_mixed_689_400_192 : Stage := [
  ((16,22),⟨⟨0,(-44096),0,871⟩,[0,0,0,0,0,0,0,0,0,0,0,479544,0],114⟩),
  ((16,48),⟨⟨(-1448278),0,64395,(-890)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],43⟩),
  ((18,38),⟨⟨(-1554384),0,25599,(-93)⟩,[0,0,669708,0,0,0,0,0,0,0,0,0,0],143⟩),
  ((20,36),⟨⟨(-4680),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],1⟩),
  ((22,42),⟨⟨(-308672),0,6307,(-2)⟩,[48230,0,0,0,0,0,0,0,0,0,0,31694,0],19⟩),
  ((24,30),⟨⟨0,(-120),0,0⟩,[0,0,0,1244,0,0,0,0,0,0,0,0,0],1⟩),
  ((26,26),⟨⟨0,(-975),0,0⟩,[15886,0,0,0,0,0,0,0,0,0,0,0,0],14⟩),
  ((26,52),⟨⟨(-1196),0,66,(-1)⟩,[156,0,0,0,0,0,0,0,0,0,0,0,0],0⟩),
  ((28,30),⟨⟨0,0,0,(-10000)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],5659⟩),
  ((30,42),⟨⟨(-1482728),0,0,845⟩,[82680,0,0,0,217724,0,0,0,0,0,0,0,0],198⟩),
  ((36,48),⟨⟨0,0,0,(-4990000)⟩,[0,0,1196286000,0,0,0,0,0,0,0,508625000,0,0],2030431⟩),
  ((38,40),⟨⟨0,(-522262),0,12961⟩,[0,0,0,0,1785888,0,0,0,0,0,0,0,0],1672⟩)]
private theorem frontier_mixed_689_400_192 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=689) : ¬∃ f : G → ℤ, IsSDS 400 192 f :=
  abelian_short_mixed G 13 53 13 1 2 6 400 192 16 28 11 27 49 12
    types_frontier_mixed_689_400_192 [stage_0_frontier_mixed_689_400_192] ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_793_225_17 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=793) : ¬∃ f : G → ℤ, IsSDS 225 17 f :=
  abelian_short_linear G 13 61 13 2 2 6 225 17 16 9 11 27
    ⟨⟨0,(-24115),3975,1170⟩,[0,0,0,0,0,0,0,44096,0,0,0,24804,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_793_784_576 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=793) : ¬∃ f : G → ℤ, IsSDS 784 576 f :=
  abelian_short_linear G 13 61 13 0 2 6 784 576 16 52 11 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_897_217_9 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=897) : ¬∃ f : G → ℤ, IsSDS 217 9 f :=
  abelian_short_linear G 13 69 13 2 2 6 217 9 16 7 11 27
    ⟨⟨(-663),(-78),32,5⟩,[0,0,0,52,0,0,0,0,0,0,0,52,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_897_256_48 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=897) : ¬∃ f : G → ℤ, IsSDS 256 48 f :=
  abelian_short_linear G 13 69 13 1 2 6 256 48 16 16 11 27
    ⟨⟨(-24830000),0,825000,5499⟩,[0,0,0,0,0,0,6500000,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_897_737_529 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=897) : ¬∃ f : G → ℤ, IsSDS 737 529 f :=
  abelian_short_linear G 13 69 13 1 2 6 737 529 16 53 11 27
    ⟨⟨47,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1053_272_64 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1053) : ¬∃ f : G → ℤ, IsSDS 272 64 f :=
  abelian_short_linear G 13 81 13 0 2 6 272 64 16 20 11 27
    ⟨⟨1404,(-208),24,5⟩,[0,0,0,260,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1053_805_597 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1053) : ¬∃ f : G → ℤ, IsSDS 805 597 f :=
  abelian_short_linear G 13 81 13 0 2 6 805 597 16 61 11 27
    ⟨⟨55,(-1),0,0⟩,[10,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1339_211_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1339) : ¬∃ f : G → ℤ, IsSDS 211 3 f :=
  abelian_short_linear G 13 103 13 4 2 6 211 3 16 5 11 27
    ⟨⟨(-689),(-13),27,1⟩,[0,26,0,260,0,0,0,0,0,104,182,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1391_220_12 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1391) : ¬∃ f : G → ℤ, IsSDS 220 12 f :=
  abelian_short_linear G 13 107 13 3 2 6 220 12 16 10 11 27
    ⟨⟨0,(-12166033),1828792,663762⟩,[0,0,0,0,0,0,0,0,0,0,0,0,10185516],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1391_1351_1143 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1391) : ¬∃ f : G → ℤ, IsSDS 1351 1143 f :=
  abelian_short_linear G 13 107 13 0 2 6 1351 1143 16 97 11 27
    ⟨⟨(-963),(-2),11,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1677_237_29 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1677) : ¬∃ f : G → ℤ, IsSDS 237 29 f :=
  abelian_short_linear G 13 129 13 0 2 6 237 29 16 17 11 27
    ⟨⟨(-23),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1677_1472_1264 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1677) : ¬∃ f : G → ℤ, IsSDS 1472 1264 f :=
  abelian_short_linear G 13 129 13 0 2 6 1472 1264 16 112 11 27
    ⟨⟨108,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2691_211_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2691) : ¬∃ f : G → ℤ, IsSDS 211 3 f :=
  abelian_short_linear G 13 207 13 4 2 6 211 3 16 7 11 27
    ⟨⟨0,(-6617),855,218⟩,[0,0,0,3354,7592,4550,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2691_224_16 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2691) : ¬∃ f : G → ℤ, IsSDS 224 16 f :=
  abelian_short_linear G 13 207 13 0 2 6 224 16 16 16 11 27
    ⟨⟨(-26),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2691_2499_2291 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2691) : ¬∃ f : G → ℤ, IsSDS 2499 2291 f :=
  abelian_short_linear G 13 207 13 0 2 6 2499 2291 16 191 11 27
    ⟨⟨181,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2743_220_12 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2743) : ¬∃ f : G → ℤ, IsSDS 220 12 f :=
  abelian_short_linear G 13 211 13 1 2 6 220 12 16 14 11 27
    ⟨⟨0,(-442),60,19⟩,[0,1144,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2743_2599_2391 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2743) : ¬∃ f : G → ℤ, IsSDS 2599 2391 f :=
  abelian_short_linear G 13 211 13 1 2 6 2599 2391 16 197 11 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4017_209_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4017) : ¬∃ f : G → ℤ, IsSDS 209 1 f :=
  abelian_short_linear G 13 309 13 5 2 6 209 1 16 5 11 27
    ⟨⟨(-1105),(-182),54,5⟩,[0,364,0,364,0,0,0,676,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4173_212_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4173) : ¬∃ f : G → ℤ, IsSDS 212 4 f :=
  abelian_short_linear G 13 321 13 3 2 6 212 4 16 10 11 27
    ⟨⟨0,(-723411),49464,32461⟩,[0,401895,0,0,0,0,401895,0,643032,0,723411,0,643032],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4173_4125_3917 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4173) : ¬∃ f : G → ℤ, IsSDS 4125 3917 f :=
  abelian_short_linear G 13 321 13 0 2 6 4125 3917 16 311 11 27
    ⟨⟨(-321),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8073_209_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8073) : ¬∃ f : G → ℤ, IsSDS 209 1 f :=
  abelian_short_linear G 13 621 13 4 2 6 209 1 16 7 11 27
    ⟨⟨0,(-127),15,4⟩,[0,0,0,0,0,10,0,0,0,54,0,88,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8229_212_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8229) : ¬∃ f : G → ℤ, IsSDS 212 4 f :=
  abelian_short_linear G 13 633 13 1 2 6 212 4 16 14 11 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_8229_8077_7869 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=8229) : ¬∃ f : G → ℤ, IsSDS 8077 7869 f :=
  abelian_short_linear G 13 633 13 1 2 6 8077 7869 16 619 11 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_9451_211_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=9451) : ¬∃ f : G → ℤ, IsSDS 211 3 f :=
  abelian_short_linear G 13 727 13 1 2 6 211 3 16 13 11 27
    ⟨⟨3,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_9451_9324_9116 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=9451) : ¬∃ f : G → ℤ, IsSDS 9324 9116 f :=
  abelian_short_linear G 13 727 13 1 2 6 9324 9116 16 714 11 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_28353_209_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=28353) : ¬∃ f : G → ℤ, IsSDS 209 1 f :=
  abelian_short_linear G 13 2181 13 1 2 6 209 1 16 13 11 27
    ⟨⟨1,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_28353_28224_28016 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=28353) : ¬∃ f : G → ℤ, IsSDS 28224 28016 f :=
  abelian_short_linear G 13 2181 13 1 2 6 28224 28016 16 2168 11 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_13_16_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=13*m)
    (hm : 13 < m) (hn : k-l=(13:ℤ)*16) : False := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  have row := endpoint_case (s:=16) hf hg hn (by decide) hm grid_13_16
  simp only [keep_13_16,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=235 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_299_235_27 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=231 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_351_231_23 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=295 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_559_295_87 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=412 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_559_412_204 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=361 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_689_361_153 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=400 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_689_400_192 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=225 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_793_225_17 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=784 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_793_784_576 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=217 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_897_217_9 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=256 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_897_256_48 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=737 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_897_737_529 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=272 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1053_272_64 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=805 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1053_805_597 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=211 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1339_211_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=220 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1391_220_12 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1351 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1391_1351_1143 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=237 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1677_237_29 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1472 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1677_1472_1264 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=211 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2691_211_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=224 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2691_224_16 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2499 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2691_2499_2291 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=220 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2743_220_12 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2599 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2743_2599_2391 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=209 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4017_209_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=212 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4173_212_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4125 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4173_4125_3917 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=209 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8073_209_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=212 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8229_212_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=8077 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_8229_8077_7869 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=211 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_9451_211_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=9324 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_9451_9324_9116 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=209 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_28353_209_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=28224 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_28353_28224_28016 G hg ⟨f,hf⟩

end Signed39.Contraction
