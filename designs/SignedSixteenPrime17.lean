import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def qInputs_17_16 : ℕ → Option QuotientInput
  | 53 => some ⟨53,17,13,0,16⟩
  | 137 => some ⟨137,17,34,0,16⟩
  | 421 => some ⟨421,17,105,0,16⟩
  | 1361 => some ⟨1361,17,34,0,16⟩
  | 2041 => some ⟨13,17,3,0,16⟩
  | 2857 => some ⟨2857,17,357,0,16⟩
  | 3809 => some ⟨13,17,3,0,16⟩
  | _ => none

private def keep_17_16 : List (ℕ × ℤ) := [(19,43),(43,19),(47,191),(47,208),(59,83),(59,508),(67,16),(83,59),(83,892),(149,4),(157,13),(157,2308),(271,16),(271,4079),(293,13),(293,4484),(409,1),(817,1),(829,4),(829,13621)]

private theorem grid_17_16 : divisorGrid 17 16 128 qInputs_17_16 keep_17_16 := by decide +kernel

private theorem frontier_mixed_323_315_43 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=323) : ¬∃ f : G → ℤ, IsSDS 315 43 f :=
  abelian_short_linear G 17 19 16 0 2 4 315 43 16 7 8 15
    ⟨⟨(-19),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_731_291_19 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=731) : ¬∃ f : G → ℤ, IsSDS 291 19 f :=
  abelian_short_linear G 17 43 16 1 2 4 291 19 16 7 8 15
    ⟨⟨(-56917000),(-7950250),2551750,500143⟩,[0,15900500,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_799_463_191 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=799) : ¬∃ f : G → ℤ, IsSDS 463 191 f :=
  abelian_short_linear G 17 47 16 1 2 4 463 191 16 23 8 15
    ⟨⟨0,0,243186062,(-22229884)⟩,[0,0,0,0,0,0,0,0,0,0,5748885677,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_799_480_208 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=799) : ¬∃ f : G → ℤ, IsSDS 480 208 f :=
  abelian_short_linear G 17 47 16 1 2 4 480 208 16 24 8 15
    ⟨⟨0,0,162,(-19)⟩,[0,0,0,1768,0,4012,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1003_355_83 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1003) : ¬∃ f : G → ℤ, IsSDS 355 83 f :=
  abelian_short_linear G 17 59 16 1 2 4 355 83 16 17 8 15
    ⟨⟨(-2703),(-170),96,5⟩,[0,0,0,0,0,68,0,1632,0,1428,0,0,68,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1003_780_508 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1003) : ¬∃ f : G → ℤ, IsSDS 780 508 f :=
  abelian_short_linear G 17 59 16 0 2 4 780 508 16 42 8 15
    ⟨⟨30,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1139_288_16 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1139) : ¬∃ f : G → ℤ, IsSDS 288 16 f :=
  abelian_short_linear G 17 67 16 2 2 4 288 16 16 8 8 15
    ⟨⟨0,(-87703),8844,5712⟩,[0,0,0,0,0,0,37587,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1411_331_59 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1411) : ¬∃ f : G → ℤ, IsSDS 331 59 f :=
  abelian_short_linear G 17 83 16 1 2 4 331 59 16 17 8 15
    ⟨⟨(-1785),(-170),78,5⟩,[0,0,0,612,0,0,476,0,0,0,0,476,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_1411_1164_892 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=1411) : ¬∃ f : G → ℤ, IsSDS 1164 892 f :=
  abelian_short_linear G 17 83 16 0 2 4 1164 892 16 66 8 15
    ⟨⟨56,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2533_276_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2533) : ¬∃ f : G → ℤ, IsSDS 276 4 f :=
  abelian_short_linear G 17 149 16 4 2 4 276 4 16 6 8 15
    ⟨⟨0,(-34155),3618,1474⟩,[0,0,0,0,4554,0,0,0,0,0,0,0,0,0,0,0,31878],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2669_285_13 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2669) : ¬∃ f : G → ℤ, IsSDS 285 13 f :=
  abelian_short_linear G 17 157 16 2 2 4 285 13 16 11 8 15
    ⟨⟨(-19024513),(-821202),386448,40256⟩,[1642404,1642404,0,2189872,0,1642404,0,0,0,0,0,6569616,0,1642404,0,8759488,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2669_2580_2308 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2669) : ¬∃ f : G → ℤ, IsSDS 2580 2308 f :=
  abelian_short_linear G 17 157 16 0 2 4 2580 2308 16 146 8 15
    ⟨⟨(-1),0,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4607_288_16 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4607) : ¬∃ f : G → ℤ, IsSDS 288 16 f :=
  abelian_short_linear G 17 271 16 0 2 4 288 16 16 16 8 15
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4607_4351_4079 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4607) : ¬∃ f : G → ℤ, IsSDS 4351 4079 f :=
  abelian_short_linear G 17 271 16 0 2 4 4351 4079 16 255 8 15
    ⟨⟨(-271),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4981_285_13 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4981) : ¬∃ f : G → ℤ, IsSDS 285 13 f :=
  abelian_short_linear G 17 293 16 0 2 4 285 13 16 15 8 15
    ⟨⟨(-19),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_4981_4756_4484 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=4981) : ¬∃ f : G → ℤ, IsSDS 4756 4484 f :=
  abelian_short_linear G 17 293 16 0 2 4 4756 4484 16 278 8 15
    ⟨⟨274,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_6953_273_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=6953) : ¬∃ f : G → ℤ, IsSDS 273 1 f :=
  abelian_short_linear G 17 409 16 5 2 4 273 1 16 5 8 15
    ⟨⟨(-595),(-34),16,1⟩,[0,68,0,0,0,340,0,0,0,68,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_13889_273_1 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=13889) : ¬∃ f : G → ℤ, IsSDS 273 1 f :=
  abelian_short_linear G 17 817 16 4 2 4 273 1 16 7 8 15
    ⟨⟨0,(-3723),260,131⟩,[0,0,0,0,0,0,0,6902,0,1836,0,2482,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_14093_276_4 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=14093) : ¬∃ f : G → ℤ, IsSDS 276 4 f :=
  abelian_short_linear G 17 829 16 1 2 4 276 4 16 14 8 15
    ⟨⟨0,(-1),0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_14093_13893_13621 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=14093) : ¬∃ f : G → ℤ, IsSDS 13893 13621 f :=
  abelian_short_linear G 17 829 16 0 2 4 13893 13621 16 815 8 15
    ⟨⟨(-829),1,0,0⟩,[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_17_16_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=17*m)
    (hm : 17 < m) (hn : k-l=(17:ℤ)*16) : False := by
  let : Fact (Nat.Prime 17) := ⟨by decide⟩
  have row := endpoint_case (s:=16) hf hg hn (by decide) hm grid_17_16
  simp only [keep_17_16,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=315 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_323_315_43 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=291 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_731_291_19 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=463 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_799_463_191 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=480 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_799_480_208 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=355 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1003_355_83 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=780 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1003_780_508 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=288 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1139_288_16 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=331 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1411_331_59 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1164 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1411_1164_892 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=276 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2533_276_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=285 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2669_285_13 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2580 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2669_2580_2308 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=288 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4607_288_16 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4351 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4607_4351_4079 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=285 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4981_285_13 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=4756 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_4981_4756_4484 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=273 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_6953_273_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=273 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_13889_273_1 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=276 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_14093_276_4 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=13893 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_14093_13893_13621 G hg ⟨f,hf⟩

end Signed39.Contraction
