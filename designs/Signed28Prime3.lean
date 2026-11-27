import Signed28Grid3Part0
import Signed28Grid3Part12
import Signed28Grid3Part24
import Signed28Grid3Part36
import Signed28Grid3Part48
import Signed28Fibre1941W85
import Signed28Fibre177W169
import Signed28Fibre249W193
import SignedLongLocalCases
import Signed28Fibre327W167
import Signed28Fibre501W421
import Signed28Fibre177W100
import Signed28Fibre1437W85
import Signed28Fibre249W112
import Signed28Fibre141W85
import Signed28Fibre501W100
import Signed28Case2517W85
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_3_28 : divisorGrid 3 28 96 qInputs_3_28 keep_3_28 := by
  intro d
  fin_cases d
  · exact grid3x28Case0
  · exact grid3x28Case1
  · exact grid3x28Case2
  · exact grid3x28Case3
  · exact grid3x28Case4
  · exact grid3x28Case5
  · exact grid3x28Case6
  · exact grid3x28Case7
  · exact grid3x28Case8
  · exact grid3x28Case9
  · exact grid3x28Case10
  · exact grid3x28Case11
  · exact grid3x28Case12
  · exact grid3x28Case13
  · exact grid3x28Case14
  · exact grid3x28Case15
  · exact grid3x28Case16
  · exact grid3x28Case17
  · exact grid3x28Case18
  · exact grid3x28Case19
  · exact grid3x28Case20
  · exact grid3x28Case21
  · exact grid3x28Case22
  · exact grid3x28Case23
  · exact grid3x28Case24
  · exact grid3x28Case25
  · exact grid3x28Case26
  · exact grid3x28Case27
  · exact grid3x28Case28
  · exact grid3x28Case29
  · exact grid3x28Case30
  · exact grid3x28Case31
  · exact grid3x28Case32
  · exact grid3x28Case33
  · exact grid3x28Case34
  · exact grid3x28Case35
  · exact grid3x28Case36
  · exact grid3x28Case37
  · exact grid3x28Case38
  · exact grid3x28Case39
  · exact grid3x28Case40
  · exact grid3x28Case41
  · exact grid3x28Case42
  · exact grid3x28Case43
  · exact grid3x28Case44
  · exact grid3x28Case45
  · exact grid3x28Case46
  · exact grid3x28Case47
  · exact grid3x28Case48
  · exact grid3x28Case49
  · exact grid3x28Case50
  · exact grid3x28Case51
  · exact grid3x28Case52
  · exact grid3x28Case53
  · exact grid3x28Case54
  · exact grid3x28Case55



private theorem frontier_mixed_1941_1936_1852 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1941) : ¬∃ f : G → ℤ, IsSDS 1936 1852 f :=
  abelian_short_linear G 3 647 7 3 2 1 1936 1852 28 632 2 37
    ⟨⟨644,0,(-1),0⟩,[0,0,0],0⟩ hG (by decide +kernel)


private theorem frontier_mixed_2517_2500_2416 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2517) : ¬∃ f : G → ℤ, IsSDS 2500 2416 f :=
  abelian_short_linear G 3 839 7 4 2 1 2500 2416 28 822 2 37
    ⟨⟨(-1),0,0,0⟩,[0,0,1],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4677_85_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4677) : ¬∃ f : G → ℤ, IsSDS 85 1 f :=
  abelian_short_linear G 3 1559 7 2 2 1 85 1 28 23 2 37
    ⟨⟨(-35),0,1,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4677_4624_4540 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4677) : ¬∃ f : G → ℤ, IsSDS 4624 4540 f :=
  abelian_short_linear G 3 1559 7 2 2 1 4624 4540 28 1536 2 37
    ⟨⟨(-1),0,0,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5541_85_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5541) : ¬∃ f : G → ℤ, IsSDS 85 1 f :=
  abelian_short_linear G 3 1847 7 1 2 1 85 1 28 25 2 37
    ⟨⟨(-1),0,0,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5541_5476_5392 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5541) : ¬∃ f : G → ℤ, IsSDS 5476 5392 f :=
  abelian_short_linear G 3 1847 7 1 2 1 5476 5392 28 1822 2 37
    ⟨⟨(-1),0,0,0⟩,[0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_3_28_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=3*m)
    (hm : 3 < m) (hn : k-l=(3:ℤ)*28) : False := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have row := endpoint_case (s:=28) hf hg hn (by decide) hm grid_3_28
  simp only [keep_3_28,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=85 := by omega
    rw [hk,hL] at hf
    exact fibre_141_85 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=100 := by omega
    rw [hk,hL] at hf
    exact fibre_177_100 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=169 := by omega
    rw [hk,hL] at hf
    exact fibre_177_169 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=112 := by omega
    rw [hk,hL] at hf
    exact fibre_249_112 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=193 := by omega
    rw [hk,hL] at hf
    exact fibre_249_193 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=164 := by omega
    rw [hk,hL] at hf
    exact local_327_164 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=167 := by omega
    rw [hk,hL] at hf
    exact fibre_327_167 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=100 := by omega
    rw [hk,hL] at hf
    exact fibre_501_100 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=421 := by omega
    rw [hk,hL] at hf
    exact fibre_501_421 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=85 := by omega
    rw [hk,hL] at hf
    exact fibre_1437_85 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=85 := by omega
    rw [hk,hL] at hf
    exact fibre_1941_85 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1936 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1941_1936_1852 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=85 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2517_85_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2500 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2517_2500_2416 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=85 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4677_85_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4624 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4677_4624_4540 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=85 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5541_85_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=5476 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5541_5476_5392 G hg ⟨f,hf⟩

end Signed39.Contraction
