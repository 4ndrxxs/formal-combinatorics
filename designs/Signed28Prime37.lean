import Signed28Grid37Part0
import Signed28Grid37Part12
import Signed28Grid37Part24
import Signed28Grid37Part36
import Signed28Grid37Part48
import Signed28Case5217W1040
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_37_28 : divisorGrid 37 28 335 qInputs_37_28 keep_37_28 := by
  intro d
  fin_cases d
  · exact grid37x28Case0
  · exact grid37x28Case1
  · exact grid37x28Case2
  · exact grid37x28Case3
  · exact grid37x28Case4
  · exact grid37x28Case5
  · exact grid37x28Case6
  · exact grid37x28Case7
  · exact grid37x28Case8
  · exact grid37x28Case9
  · exact grid37x28Case10
  · exact grid37x28Case11
  · exact grid37x28Case12
  · exact grid37x28Case13
  · exact grid37x28Case14
  · exact grid37x28Case15
  · exact grid37x28Case16
  · exact grid37x28Case17
  · exact grid37x28Case18
  · exact grid37x28Case19
  · exact grid37x28Case20
  · exact grid37x28Case21
  · exact grid37x28Case22
  · exact grid37x28Case23
  · exact grid37x28Case24
  · exact grid37x28Case25
  · exact grid37x28Case26
  · exact grid37x28Case27
  · exact grid37x28Case28
  · exact grid37x28Case29
  · exact grid37x28Case30
  · exact grid37x28Case31
  · exact grid37x28Case32
  · exact grid37x28Case33
  · exact grid37x28Case34
  · exact grid37x28Case35
  · exact grid37x28Case36
  · exact grid37x28Case37
  · exact grid37x28Case38
  · exact grid37x28Case39
  · exact grid37x28Case40
  · exact grid37x28Case41
  · exact grid37x28Case42
  · exact grid37x28Case43
  · exact grid37x28Case44
  · exact grid37x28Case45
  · exact grid37x28Case46
  · exact grid37x28Case47
  · exact grid37x28Case48
  · exact grid37x28Case49
  · exact grid37x28Case50
  · exact grid37x28Case51
  · exact grid37x28Case52
  · exact grid37x28Case53
  · exact grid37x28Case54
  · exact grid37x28Case55



private theorem frontier_mixed_1739_1048_12 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1739) : ¬∃ f : G → ℤ, IsSDS 1048 12 f :=
  abelian_short_linear G 37 47 31 1 2 18 1048 12 28 4 2 3
    ⟨⟨0,(-23),2,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2331_1496_460 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2331) : ¬∃ f : G → ℤ, IsSDS 1496 460 f :=
  abelian_short_linear G 37 63 31 0 2 18 1496 460 28 28 2 3
    ⟨⟨0,0,0,(-1)⟩,[0,0,4,0,0,0,0,0,64,0,100,0,0,0,0,0,0,0,324,0,0,0,0,0,576,0,0,0,0,0,0,0,0,0,0,4,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2331_1755_719 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2331) : ¬∃ f : G → ℤ, IsSDS 1755 719 f :=
  abelian_short_linear G 37 63 31 0 2 18 1755 719 28 35 2 3
    ⟨⟨(-15366645),(-223629),467630,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2997_1661_625 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2997) : ¬∃ f : G → ℤ, IsSDS 1661 625 f :=
  abelian_short_linear G 37 81 31 1 2 18 1661 625 28 37 2 3
    ⟨⟨361,0,0,(-1)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,80,0,168,0,0,0,0,0,0,0,0,0,728,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2997_1920_884 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2997) : ¬∃ f : G → ℤ, IsSDS 1920 884 f :=
  abelian_short_linear G 37 81 31 0 2 18 1920 884 28 44 2 3
    ⟨⟨34,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_3071_1111_75 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=3071) : ¬∃ f : G → ℤ, IsSDS 1111 75 f :=
  abelian_short_linear G 37 83 31 1 2 18 1111 75 28 13 2 3
    ⟨⟨(-2109),0,28,1⟩,[0,0,0,0,0,0,0,296,0,0,0,0,0,0,0,0,0,0,0,0,0,296,0,0,0,0,0,0,0,0,296,0,0,0,0,0,0],0⟩ hG (by decide +kernel)


private theorem frontier_mixed_9213_1061_25 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=9213) : ¬∃ f : G → ℤ, IsSDS 1061 25 f :=
  abelian_short_linear G 37 249 31 3 2 18 1061 25 28 13 2 3
    ⟨⟨(-88319),(-444),1044,23⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,3552,0,0,0,15096,0,37296,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_29119_1048_12 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=29119) : ¬∃ f : G → ℤ, IsSDS 1048 12 f :=
  abelian_short_linear G 37 787 31 6 2 18 1048 12 28 16 2 3
    ⟨⟨(-2750370000),(-486460000),35396000,16556479⟩,[2750370000,0,0,0,280650000,0,972920000,0,0,0,0,0,280650000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_29119_28983_27947 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=29119) : ¬∃ f : G → ℤ, IsSDS 28983 27947 f :=
  abelian_short_linear G 37 787 31 0 2 18 28983 27947 28 771 2 3
    ⟨⟨(-787),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_45547_1048_12 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=45547) : ¬∃ f : G → ℤ, IsSDS 1048 12 f :=
  abelian_short_linear G 37 1231 31 4 2 18 1048 12 28 20 2 3
    ⟨⟨(-44400),(-3182),364,45⟩,[44400,0,12728,0,12728,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_45547_45115_44079 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=45547) : ¬∃ f : G → ℤ, IsSDS 45115 44079 f :=
  abelian_short_linear G 37 1231 31 0 2 18 45115 44079 28 1211 2 3
    ⟨⟨(-1231),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_54871_1039_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=54871) : ¬∃ f : G → ℤ, IsSDS 1039 3 f :=
  abelian_short_linear G 37 1483 31 8 2 18 1039 3 28 11 2 3
    ⟨⟨(-108669),(-7696),1020,(-7)⟩,[0,15392,0,53280,0,38184,0,45584,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7104,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_87357_1040_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=87357) : ¬∃ f : G → ℤ, IsSDS 1040 4 f :=
  abelian_short_linear G 37 2361 31 6 2 18 1040 4 28 16 2 3
    ⟨⟨0,0,11,(-9)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_87357_87213_86177 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=87357) : ¬∃ f : G → ℤ, IsSDS 87213 86177 f :=
  abelian_short_linear G 37 2361 31 0 2 18 87213 86177 28 2345 2 3
    ⟨⟨(-2361),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_136641_1040_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=136641) : ¬∃ f : G → ℤ, IsSDS 1040 4 f :=
  abelian_short_linear G 37 3693 31 4 2 18 1040 4 28 20 2 3
    ⟨⟨0,0,2,(-5)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_136641_136201_135165 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=136641) : ¬∃ f : G → ℤ, IsSDS 136201 135165 f :=
  abelian_short_linear G 37 3693 31 0 2 18 136201 135165 28 3673 2 3
    ⟨⟨(-3693),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_164613_1037_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=164613) : ¬∃ f : G → ℤ, IsSDS 1037 1 f :=
  abelian_short_linear G 37 4449 31 8 2 18 1037 1 28 11 2 3
    ⟨⟨0,(-4366),225,49⟩,[0,0,0,0,0,1480,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_284863_1039_3 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=284863) : ¬∃ f : G → ℤ, IsSDS 1039 3 f :=
  abelian_short_linear G 37 7699 31 1 2 18 1039 3 28 25 2 3
    ⟨⟨1,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_284863_284052_283016 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=284863) : ¬∃ f : G → ℤ, IsSDS 284052 283016 f :=
  abelian_short_linear G 37 7699 31 0 2 18 284052 283016 28 7674 2 3
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_306989_1037_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=306989) : ¬∃ f : G → ℤ, IsSDS 1037 1 f :=
  abelian_short_linear G 37 8297 31 6 2 18 1037 1 28 15 2 3
    ⟨⟨0,0,625,(-497)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_306989_306916_305880 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=306989) : ¬∃ f : G → ℤ, IsSDS 306916 305880 f :=
  abelian_short_linear G 37 8297 31 0 2 18 306916 305880 28 8282 2 3
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_854589_1037_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=854589) : ¬∃ f : G → ℤ, IsSDS 1037 1 f :=
  abelian_short_linear G 37 23097 31 1 2 18 1037 1 28 25 2 3
    ⟨⟨1,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_854589_853776_852740 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=854589) : ¬∃ f : G → ℤ, IsSDS 853776 852740 f :=
  abelian_short_linear G 37 23097 31 0 2 18 853776 852740 28 23072 2 3
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_37_28_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=37*m)
    (hm : 37 < m) (hn : k-l=(37:ℤ)*28) : False := by
  let : Fact (Nat.Prime 37) := ⟨by decide⟩
  have row := endpoint_case (s:=28) hf hg hn (by decide) hm grid_37_28
  simp only [keep_37_28,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1048 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1739_1048_12 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1496 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2331_1496_460 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1755 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2331_1755_719 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1661 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2997_1661_625 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1920 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2997_1920_884 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1111 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_3071_1111_75 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1040 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5217_1040_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1061 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_9213_1061_25 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1048 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_29119_1048_12 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=28983 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_29119_28983_27947 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1048 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_45547_1048_12 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=45115 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_45547_45115_44079 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1039 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_54871_1039_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1040 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_87357_1040_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=87213 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_87357_87213_86177 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1040 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_136641_1040_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=136201 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_136641_136201_135165 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1037 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_164613_1037_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1039 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_284863_1039_3 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=284052 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_284863_284052_283016 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1037 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_306989_1037_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=306916 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_306989_306916_305880 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1037 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_854589_1037_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=853776 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_854589_853776_852740 G hg ⟨f,hf⟩

end Signed39.Contraction
