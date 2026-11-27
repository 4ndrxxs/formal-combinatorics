import Signed27Grid23Part0
import Signed27Grid23Part12
import Signed27Grid23Part24
import Signed27Grid23Part36
import Signed27Grid23Part48
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_23_27 : divisorGrid 23 27 255 qInputs_23_27 keep_23_27 := by
  intro d
  fin_cases d
  · exact grid23x27Case0
  · exact grid23x27Case1
  · exact grid23x27Case2
  · exact grid23x27Case3
  · exact grid23x27Case4
  · exact grid23x27Case5
  · exact grid23x27Case6
  · exact grid23x27Case7
  · exact grid23x27Case8
  · exact grid23x27Case9
  · exact grid23x27Case10
  · exact grid23x27Case11
  · exact grid23x27Case12
  · exact grid23x27Case13
  · exact grid23x27Case14
  · exact grid23x27Case15
  · exact grid23x27Case16
  · exact grid23x27Case17
  · exact grid23x27Case18
  · exact grid23x27Case19
  · exact grid23x27Case20
  · exact grid23x27Case21
  · exact grid23x27Case22
  · exact grid23x27Case23
  · exact grid23x27Case24
  · exact grid23x27Case25
  · exact grid23x27Case26
  · exact grid23x27Case27
  · exact grid23x27Case28
  · exact grid23x27Case29
  · exact grid23x27Case30
  · exact grid23x27Case31
  · exact grid23x27Case32
  · exact grid23x27Case33
  · exact grid23x27Case34
  · exact grid23x27Case35
  · exact grid23x27Case36
  · exact grid23x27Case37
  · exact grid23x27Case38
  · exact grid23x27Case39
  · exact grid23x27Case40
  · exact grid23x27Case41
  · exact grid23x27Case42
  · exact grid23x27Case43
  · exact grid23x27Case44
  · exact grid23x27Case45
  · exact grid23x27Case46
  · exact grid23x27Case47
  · exact grid23x27Case48
  · exact grid23x27Case49
  · exact grid23x27Case50
  · exact grid23x27Case51
  · exact grid23x27Case52
  · exact grid23x27Case53



private theorem frontier_mixed_1909_808_187 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1909) : ¬∃ f : G → ℤ, IsSDS 808 187 f :=
  abelian_short_linear G 23 83 24 1 1 0 808 187 27 26 3 7
    ⟨⟨(-690),(-253),105,4⟩,[0,0,0,0,0,0,0,690,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1909_1521_900 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1909) : ¬∃ f : G → ℤ, IsSDS 1521 900 f :=
  abelian_short_linear G 23 83 24 1 1 0 1521 900 27 57 3 7
    ⟨⟨1849,0,0,(-1)⟩,[0,0,455,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,87,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2461_1116_495 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2461) : ¬∃ f : G → ℤ, IsSDS 1116 495 f :=
  abelian_short_linear G 23 107 24 0 1 0 1116 495 27 48 3 7
    ⟨⟨260958,(-11477),855,104⟩,[7590,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2461_1369_748 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2461) : ¬∃ f : G → ℤ, IsSDS 1369 748 f :=
  abelian_short_linear G 23 107 24 0 1 0 1369 748 27 59 3 7
    ⟨⟨56,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2783_881_260 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2783) : ¬∃ f : G → ℤ, IsSDS 881 260 f :=
  abelian_short_linear G 23 121 24 0 1 0 881 260 27 37 3 7
    ⟨⟨(-4784),0,144,(-1)⟩,[276,0,0,276,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2783_1962_1341 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2783) : ¬∃ f : G → ℤ, IsSDS 1962 1341 f :=
  abelian_short_linear G 23 121 24 0 1 0 1962 1341 27 84 3 7
    ⟨⟨(-14904),0,1113,(-13)⟩,[0,0,0,0,0,0,4554,0,0,0,0,0,0,0,0,0,0,1978,0,0,1012,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6371_686_65 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6371) : ¬∃ f : G → ℤ, IsSDS 686 65 f :=
  abelian_short_linear G 23 277 24 0 1 0 686 65 27 28 3 7
    ⟨⟨0,(-4163),1482,59⟩,[0,0,0,0,0,0,0,0,11592,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6371_5769_5148 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6371) : ¬∃ f : G → ℤ, IsSDS 5769 5148 f :=
  abelian_short_linear G 23 277 24 0 1 0 5769 5148 27 249 3 7
    ⟨⟨8360836,(-77330),40515,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_20999_638_17 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=20999) : ¬∃ f : G → ℤ, IsSDS 638 17 f :=
  abelian_short_linear G 23 913 24 0 1 0 638 17 27 26 3 7
    ⟨⟨(-32),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_20999_20441_19820 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=20999) : ¬∃ f : G → ℤ, IsSDS 20441 19820 f :=
  abelian_short_linear G 23 913 24 0 1 0 20441 19820 27 887 3 7
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_51083_626_5 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=51083) : ¬∃ f : G → ℤ, IsSDS 626 5 f :=
  abelian_short_linear G 23 2221 24 2 1 0 626 5 27 22 3 7
    ⟨⟨1,0,0,(-1)⟩,[0,0,3,8,15,24,35,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_51083_50697_50076 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=51083) : ¬∃ f : G → ℤ, IsSDS 50697 50076 f :=
  abelian_short_linear G 23 2221 24 1 1 0 50697 50076 27 2199 3 7
    ⟨⟨(-2221),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_23_27_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=23*m)
    (hm : 23 < m) (hn : k-l=(23:ℤ)*27) : False := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  have row := endpoint_case (s:=27) hf hg hn (by decide) hm grid_23_27
  simp only [keep_23_27,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=808 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1909_808_187 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1521 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1909_1521_900 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1116 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2461_1116_495 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1369 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2461_1369_748 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=881 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2783_881_260 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1962 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2783_1962_1341 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=686 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6371_686_65 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=5769 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6371_5769_5148 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=638 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_20999_638_17 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=20441 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_20999_20441_19820 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=626 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_51083_626_5 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=50697 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_51083_50697_50076 G hg ⟨f,hf⟩

end Signed39.Contraction
