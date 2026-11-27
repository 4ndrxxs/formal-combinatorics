import Signed25Grid17Part0
import Signed25Grid17Part12
import Signed25Grid17Part24
import Signed25Grid17Part36
import Signed25Grid17Part48
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_17_25 : divisorGrid 17 25 202 qInputs_17_25 keep_17_25 := by
  intro d
  fin_cases d
  · exact grid17x25Case0
  · exact grid17x25Case1
  · exact grid17x25Case2
  · exact grid17x25Case3
  · exact grid17x25Case4
  · exact grid17x25Case5
  · exact grid17x25Case6
  · exact grid17x25Case7
  · exact grid17x25Case8
  · exact grid17x25Case9
  · exact grid17x25Case10
  · exact grid17x25Case11
  · exact grid17x25Case12
  · exact grid17x25Case13
  · exact grid17x25Case14
  · exact grid17x25Case15
  · exact grid17x25Case16
  · exact grid17x25Case17
  · exact grid17x25Case18
  · exact grid17x25Case19
  · exact grid17x25Case20
  · exact grid17x25Case21
  · exact grid17x25Case22
  · exact grid17x25Case23
  · exact grid17x25Case24
  · exact grid17x25Case25
  · exact grid17x25Case26
  · exact grid17x25Case27
  · exact grid17x25Case28
  · exact grid17x25Case29
  · exact grid17x25Case30
  · exact grid17x25Case31
  · exact grid17x25Case32
  · exact grid17x25Case33
  · exact grid17x25Case34
  · exact grid17x25Case35
  · exact grid17x25Case36
  · exact grid17x25Case37
  · exact grid17x25Case38
  · exact grid17x25Case39
  · exact grid17x25Case40
  · exact grid17x25Case41
  · exact grid17x25Case42
  · exact grid17x25Case43
  · exact grid17x25Case44
  · exact grid17x25Case45
  · exact grid17x25Case46
  · exact grid17x25Case47
  · exact grid17x25Case48
  · exact grid17x25Case49



private theorem frontier_mixed_731_426_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=731) : ¬∃ f : G → ℤ, IsSDS 426 1 f :=
  abelian_short_linear G 17 43 20 1 5 8 426 1 25 2 16 47
    ⟨⟨(-194),(-8),5,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_799_529_104 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=799) : ¬∃ f : G → ℤ, IsSDS 529 104 f :=
  abelian_short_linear G 17 47 20 1 5 8 529 104 25 17 16 47
    ⟨⟨(-107),(-4),5,0⟩,[0,0,0,0,0,35,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_799_750_325 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=799) : ¬∃ f : G → ℤ, IsSDS 750 325 f :=
  abelian_short_linear G 17 47 20 1 5 8 750 325 25 30 16 47
    ⟨⟨20,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private def types_frontier_mixed_1003_577_152 : List RowType := [(3,33),(8,42),(13,53),(18,32),(23,47),(28,30),(33,49)]
private def stage_0_frontier_mixed_1003_577_152 : Stage := [
  ((3,33),⟨⟨0,(-58174),0,578⟩,[0,0,0,0,0,0,0,0,0,0,0,952850,0,0,0,0,0],115⟩),
  ((8,42),⟨⟨0,0,0,(-702183076)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],59185555⟩),
  ((13,53),⟨⟨(-2243711),0,38645,(-26)⟩,[0,265795,0,0,0,0,0,0,0,0,0,476425,0,0,0,0,0],70⟩),
  ((18,32),⟨⟨0,0,0,(-2397)⟩,[0,0,0,0,0,0,55165,0,0,0,0,0,0,0,0,0,0],196⟩),
  ((23,47),⟨⟨(-27081),0,0,17⟩,[0,3009,0,0,0,0,0,0,1003,0,0,0,0,0,0,0,0],3⟩),
  ((28,30),⟨⟨0,(-6018),0,68⟩,[0,0,0,0,0,0,0,0,0,0,0,106318,0,0,0,0,0],9⟩),
  ((33,49),⟨⟨0,0,0,(-3196)⟩,[0,0,0,0,0,0,653956,0,0,0,0,0,0,0,0,0,0],363⟩)]
private theorem frontier_mixed_1003_577_152 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1003) : ¬∃ f : G → ℤ, IsSDS 577 152 f :=
  abelian_short_mixed G 17 59 20 1 5 8 577 152 25 23 16 47 7 2
    types_frontier_mixed_1003_577_152 [stage_0_frontier_mixed_1003_577_152] ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1003_798_373 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1003) : ¬∃ f : G → ℤ, IsSDS 798 373 f :=
  abelian_short_linear G 17 59 20 1 5 8 798 373 25 36 16 47
    ⟨⟨31,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1139_450_25 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1139) : ¬∃ f : G → ℤ, IsSDS 450 25 f :=
  abelian_short_linear G 17 67 20 2 5 8 450 25 25 10 16 47
    ⟨⟨0,(-323),30,13⟩,[0,0,0,0,0,0,0,0,0,0,850,0,0,0,0,510,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1411_769_344 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1411) : ¬∃ f : G → ℤ, IsSDS 769 344 f :=
  abelian_short_linear G 17 83 20 1 5 8 769 344 25 41 16 47
    ⟨⟨(-114803584),0,2901745,(-22610)⟩,[0,0,0,0,0,0,0,0,0,25625800,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1411_786_361 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1411) : ¬∃ f : G → ℤ, IsSDS 786 361 f :=
  abelian_short_linear G 17 83 20 1 5 8 786 361 25 42 16 47
    ⟨⟨918690846,(-69145596),7604625,773500⟩,[0,7387350,0,162521700,0,0,0,0,88648200,0,118197600,0,0,36936750,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2159_441_16 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2159) : ¬∃ f : G → ℤ, IsSDS 441 16 f :=
  abelian_short_linear G 17 127 20 4 5 8 441 16 25 11 16 47
    ⟨⟨(-321776),(-13923),6825,1275⟩,[0,0,0,0,0,0,154700,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3247_457_32 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3247) : ¬∃ f : G → ℤ, IsSDS 457 32 f :=
  abelian_short_linear G 17 191 20 3 5 8 457 32 25 19 16 47
    ⟨⟨0,(-19142),6825,253⟩,[0,0,33490,0,0,0,0,27030,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3247_3058_2633 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3247) : ¬∃ f : G → ℤ, IsSDS 3058 2633 f :=
  abelian_short_linear G 17 191 20 1 5 8 3058 2633 25 172 16 47
    ⟨⟨12,(-11),10,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4267_478_53 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4267) : ¬∃ f : G → ℤ, IsSDS 478 53 f :=
  abelian_short_linear G 17 251 20 0 5 8 478 53 25 28 16 47
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4267_3793_3368 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4267) : ¬∃ f : G → ℤ, IsSDS 3793 3368 f :=
  abelian_short_linear G 17 251 20 0 5 8 3793 3368 25 223 16 47
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4607_450_25 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4607) : ¬∃ f : G → ℤ, IsSDS 450 25 f :=
  abelian_short_linear G 17 271 20 3 5 8 450 25 25 20 16 47
    ⟨⟨0,(-284546),66952,4352⟩,[0,142273,0,0,0,0,0,0,711365,0,0,0,0,1138184,0,142273,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4607_4377_3952 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4607) : ¬∃ f : G → ℤ, IsSDS 4377 3952 f :=
  abelian_short_linear G 17 271 20 1 5 8 4377 3952 25 251 16 47
    ⟨⟨(-263),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7939_441_16 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7939) : ¬∃ f : G → ℤ, IsSDS 441 16 f :=
  abelian_short_linear G 17 467 20 2 5 8 441 16 25 21 16 47
    ⟨⟨(-70856),(-2703),1500,59⟩,[0,0,0,0,22100,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_7939_7666_7241 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=7939) : ¬∃ f : G → ℤ, IsSDS 7666 7241 f :=
  abelian_short_linear G 17 467 20 1 5 8 7666 7241 25 446 16 47
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_9979_426_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=9979) : ¬∃ f : G → ℤ, IsSDS 426 1 f :=
  abelian_short_linear G 17 587 20 9 5 8 426 1 25 6 16 47
    ⟨⟨(-374),(-102),25,1⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10727_438_13 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10727) : ¬∃ f : G → ℤ, IsSDS 438 13 f :=
  abelian_short_linear G 17 631 20 1 5 8 438 13 25 22 16 47
    ⟨⟨(-33),0,1,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_10727_10417_9992 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=10727) : ¬∃ f : G → ℤ, IsSDS 10417 9992 f :=
  abelian_short_linear G 17 631 20 1 5 8 10417 9992 25 609 16 47
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_18071_426_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=18071) : ¬∃ f : G → ℤ, IsSDS 426 1 f :=
  abelian_short_linear G 17 1063 20 8 5 8 426 1 25 8 16 47
    ⟨⟨(-2792250),(-85476),62850,0⟩,[0,0,0,890375,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_19057_433_8 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=19057) : ¬∃ f : G → ℤ, IsSDS 433 8 f :=
  abelian_short_linear G 17 1121 20 1 5 8 433 8 25 23 16 47
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_19057_18708_18283 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=19057) : ¬∃ f : G → ℤ, IsSDS 18708 18283 f :=
  abelian_short_linear G 17 1121 20 1 5 8 18708 18283 25 1098 16 47
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_41191_426_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=41191) : ¬∃ f : G → ℤ, IsSDS 426 1 f :=
  abelian_short_linear G 17 2423 20 6 5 8 426 1 25 12 16 47
    ⟨⟨(-86250),(-27240),5221,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_56219_426_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=56219) : ¬∃ f : G → ℤ, IsSDS 426 1 f :=
  abelian_short_linear G 17 3307 20 5 5 8 426 1 25 14 16 47
    ⟨⟨0,0,17660,(-9539)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_56219_56169_55744 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=56219) : ¬∃ f : G → ℤ, IsSDS 56169 55744 f :=
  abelian_short_linear G 17 3307 20 1 5 8 56169 55744 25 3293 16 47
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_73559_426_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=73559) : ¬∃ f : G → ℤ, IsSDS 426 1 f :=
  abelian_short_linear G 17 4327 20 4 5 8 426 1 25 16 16 47
    ⟨⟨0,0,8666,(-8809)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_73559_73441_73016 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=73559) : ¬∃ f : G → ℤ, IsSDS 73441 73016 f :=
  abelian_short_linear G 17 4327 20 1 5 8 73441 73016 25 4311 16 47
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_93211_426_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=93211) : ¬∃ f : G → ℤ, IsSDS 426 1 f :=
  abelian_short_linear G 17 5483 20 3 5 8 426 1 25 18 16 47
    ⟨⟨8,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_93211_93025_92600 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=93211) : ¬∃ f : G → ℤ, IsSDS 93025 92600 f :=
  abelian_short_linear G 17 5483 20 1 5 8 93025 92600 25 5465 16 47
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_166039_426_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=166039) : ¬∃ f : G → ℤ, IsSDS 426 1 f :=
  abelian_short_linear G 17 9767 20 0 5 8 426 1 25 24 16 47
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_166039_165649_165224 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=166039) : ¬∃ f : G → ℤ, IsSDS 165649 165224 f :=
  abelian_short_linear G 17 9767 20 0 5 8 165649 165224 25 9743 16 47
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_17_25_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=17*m)
    (hm : 17 < m) (hn : k-l=(17:ℤ)*25) : False := by
  let : Fact (Nat.Prime 17) := ⟨by decide⟩
  have row := endpoint_case (s:=25) hf hg hn (by decide) hm grid_17_25
  simp only [keep_17_25,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=426 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_731_426_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=529 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_799_529_104 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=750 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_799_750_325 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=577 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1003_577_152 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=798 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1003_798_373 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=450 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1139_450_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=769 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1411_769_344 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=786 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1411_786_361 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=441 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2159_441_16 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=457 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3247_457_32 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3058 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3247_3058_2633 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=478 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4267_478_53 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3793 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4267_3793_3368 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=450 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4607_450_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4377 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4607_4377_3952 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=441 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7939_441_16 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=7666 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_7939_7666_7241 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=426 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_9979_426_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=438 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10727_438_13 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=10417 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_10727_10417_9992 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=426 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_18071_426_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=433 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_19057_433_8 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=18708 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_19057_18708_18283 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=426 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_41191_426_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=426 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_56219_426_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=56169 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_56219_56169_55744 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=426 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_73559_426_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=73441 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_73559_73441_73016 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=426 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_93211_426_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=93025 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_93211_93025_92600 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=426 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_166039_426_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=165649 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_166039_165649_165224 G hg ⟨f,hf⟩

end Signed39.Contraction
