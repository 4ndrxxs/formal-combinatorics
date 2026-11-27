import Signed28Grid29Part0
import Signed28Grid29Part12
import Signed28Grid29Part24
import Signed28Grid29Part36
import Signed28Grid29Part48
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_29_28 : divisorGrid 29 28 297 qInputs_29_28 keep_29_28 := by
  intro d
  fin_cases d
  · exact grid29x28Case0
  · exact grid29x28Case1
  · exact grid29x28Case2
  · exact grid29x28Case3
  · exact grid29x28Case4
  · exact grid29x28Case5
  · exact grid29x28Case6
  · exact grid29x28Case7
  · exact grid29x28Case8
  · exact grid29x28Case9
  · exact grid29x28Case10
  · exact grid29x28Case11
  · exact grid29x28Case12
  · exact grid29x28Case13
  · exact grid29x28Case14
  · exact grid29x28Case15
  · exact grid29x28Case16
  · exact grid29x28Case17
  · exact grid29x28Case18
  · exact grid29x28Case19
  · exact grid29x28Case20
  · exact grid29x28Case21
  · exact grid29x28Case22
  · exact grid29x28Case23
  · exact grid29x28Case24
  · exact grid29x28Case25
  · exact grid29x28Case26
  · exact grid29x28Case27
  · exact grid29x28Case28
  · exact grid29x28Case29
  · exact grid29x28Case30
  · exact grid29x28Case31
  · exact grid29x28Case32
  · exact grid29x28Case33
  · exact grid29x28Case34
  · exact grid29x28Case35
  · exact grid29x28Case36
  · exact grid29x28Case37
  · exact grid29x28Case38
  · exact grid29x28Case39
  · exact grid29x28Case40
  · exact grid29x28Case41
  · exact grid29x28Case42
  · exact grid29x28Case43
  · exact grid29x28Case44
  · exact grid29x28Case45
  · exact grid29x28Case46
  · exact grid29x28Case47
  · exact grid29x28Case48
  · exact grid29x28Case49
  · exact grid29x28Case50
  · exact grid29x28Case51
  · exact grid29x28Case52
  · exact grid29x28Case53
  · exact grid29x28Case54
  · exact grid29x28Case55



private theorem frontier_mixed_1711_871_59 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1711) : ¬∃ f : G → ℤ, IsSDS 871 59 f :=
  abelian_short_linear G 29 59 28 1 2 14 871 59 28 11 14 27
    ⟨⟨(-1421959),0,30361,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,114460,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2407_1399_587 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2407) : ¬∃ f : G → ℤ, IsSDS 1399 587 f :=
  abelian_short_linear G 29 83 28 1 2 14 1399 587 28 41 14 27
    ⟨⟨0,0,25,(-1)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,174,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2407_1428_616 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2407) : ¬∃ f : G → ℤ, IsSDS 1428 616 f :=
  abelian_short_linear G 29 83 28 1 2 14 1428 616 28 42 14 27
    ⟨⟨(-96512),0,1920,(-13)⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,26100,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2987_948_136 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2987) : ¬∃ f : G → ℤ, IsSDS 948 136 f :=
  abelian_short_linear G 29 103 28 1 2 14 948 136 28 22 14 27
    ⟨⟨0,(-11774),2964,199⟩,[0,0,0,0,0,0,0,11832,0,0,0,0,0,0,0,0,0,0,22968,0,0,0,8584,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2987_2659_1847 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2987) : ¬∃ f : G → ℤ, IsSDS 2659 1847 f :=
  abelian_short_linear G 29 103 28 0 2 14 2659 1847 28 81 14 27
    ⟨⟨695971,(-22968),2100,137⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4031_1039_227 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4031) : ¬∃ f : G → ℤ, IsSDS 1039 227 f :=
  abelian_short_linear G 29 139 28 1 2 14 1039 227 28 33 14 27
    ⟨⟨0,(-31494),8569,447⟩,[0,0,0,0,0,0,0,0,64902,0,111360,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4031_3156_2344 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4031) : ¬∃ f : G → ℤ, IsSDS 3156 2344 f :=
  abelian_short_linear G 29 139 28 1 2 14 3156 2344 28 106 14 27
    ⟨⟨0,0,2401,(-30)⟩,[0,0,0,2900,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5742,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_5771_819_7 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=5771) : ¬∃ f : G → ℤ, IsSDS 819 7 f :=
  abelian_short_linear G 29 199 28 3 2 14 819 7 28 7 14 27
    ⟨⟨(-22185),(-348),364,33⟩,[0,0,0,0,0,1624,0,3712,0,6264,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23519_840_28 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23519) : ¬∃ f : G → ℤ, IsSDS 840 28 f :=
  abelian_short_linear G 29 811 28 0 2 14 840 28 28 28 14 27
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_23519_22735_21923 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=23519) : ¬∃ f : G → ℤ, IsSDS 22735 21923 f :=
  abelian_short_linear G 29 811 28 0 2 14 22735 21923 28 783 14 27
    ⟨⟨(-811),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_40397_813_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=40397) : ¬∃ f : G → ℤ, IsSDS 813 1 f :=
  abelian_short_linear G 29 1393 28 10 2 14 813 1 28 7 14 27
    ⟨⟨(-610720026),(-22265964),9984341,0⟩,[0,44550702,0,14850234,0,0,0,311854914,0,59400936,0,0,0,0,0,14850234,0,44550702,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_52867_819_7 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=52867) : ¬∃ f : G → ℤ, IsSDS 819 7 f :=
  abelian_short_linear G 29 1823 28 3 2 14 819 7 28 21 14 27
    ⟨⟨0,0,27,(-73)⟩,[0,0,0,0,0,0,0,0,0,0,0,3190,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_52867_52468_51656 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=52867) : ¬∃ f : G → ℤ, IsSDS 52468 51656 f :=
  abelian_short_linear G 29 1823 28 0 2 14 52468 51656 28 1802 14 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_100949_813_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=100949) : ¬∃ f : G → ℤ, IsSDS 813 1 f :=
  abelian_short_linear G 29 3481 28 8 2 14 813 1 28 11 14 27
    ⟨⟨(-123453),(-1856),1456,(-267)⟩,[0,39672,0,33872,0,18560,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,22736,0,35960],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_164633_816_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=164633) : ¬∃ f : G → ℤ, IsSDS 816 4 f :=
  abelian_short_linear G 29 5677 28 0 2 14 816 4 28 28 14 27
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_164633_163825_163013 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=164633) : ¬∃ f : G → ℤ, IsSDS 163825 163013 f :=
  abelian_short_linear G 29 5677 28 0 2 14 163825 163013 28 5649 14 27
    ⟨⟨(-5677),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_370069_813_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=370069) : ¬∃ f : G → ℤ, IsSDS 813 1 f :=
  abelian_short_linear G 29 12761 28 3 2 14 813 1 28 21 14 27
    ⟨⟨1,0,0,(-1)⟩,[0,0,0,8,0,24,0,48,0,80,0,0,0,0,0,0,0,0,0,0,0,0,48,0,24,0,8,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_370069_369664_368852 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=370069) : ¬∃ f : G → ℤ, IsSDS 369664 368852 f :=
  abelian_short_linear G 29 12761 28 0 2 14 369664 368852 28 12740 14 27
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_29_28_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=29*m)
    (hm : 29 < m) (hn : k-l=(29:ℤ)*28) : False := by
  let : Fact (Nat.Prime 29) := ⟨by decide⟩
  have row := endpoint_case (s:=28) hf hg hn (by decide) hm grid_29_28
  simp only [keep_29_28,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=871 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1711_871_59 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1399 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2407_1399_587 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1428 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2407_1428_616 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=948 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2987_948_136 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2659 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2987_2659_1847 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1039 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4031_1039_227 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=3156 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4031_3156_2344 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=819 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_5771_819_7 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=840 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23519_840_28 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=22735 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_23519_22735_21923 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=813 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_40397_813_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=819 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_52867_819_7 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=52468 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_52867_52468_51656 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=813 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_100949_813_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=816 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_164633_816_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=163825 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_164633_163825_163013 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=813 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_370069_813_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=369664 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_370069_369664_368852 G hg ⟨f,hf⟩

end Signed39.Contraction
