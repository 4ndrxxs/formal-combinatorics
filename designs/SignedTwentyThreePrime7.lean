import Signed721Orbit
import SignedTwentyThreeCase581W289
import SignedTwentyThreeCase581W324
import SignedDivisorGrid
import SignedBudgetCertificate
import SignedExtendedClassification

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def qInputs_7_23 : ℕ → Option QuotientInput
  | 23 => some ⟨23,7,11,0,23⟩
  | 61 => some ⟨61,23,10,0,7⟩
  | 71 => some ⟨71,23,7,0,7⟩
  | 85 => some ⟨5,7,2,0,23⟩
  | 89 => some ⟨89,7,44,0,23⟩
  | 95 => some ⟨5,7,2,0,23⟩
  | 97 => some ⟨97,7,48,0,23⟩
  | 115 => some ⟨5,7,2,0,23⟩
  | 125 => some ⟨5,7,2,0,23⟩
  | 127 => some ⟨127,7,63,0,23⟩
  | 145 => some ⟨5,7,2,0,23⟩
  | 197 => some ⟨197,7,49,0,23⟩
  | 211 => some ⟨211,23,5,0,7⟩
  | 229 => some ⟨229,7,114,0,23⟩
  | 313 => some ⟨313,7,52,0,23⟩
  | 425 => some ⟨5,7,2,0,23⟩
  | 449 => some ⟨449,7,56,0,23⟩
  | 673 => some ⟨673,23,7,0,7⟩
  | 677 => some ⟨677,7,338,0,23⟩
  | 985 => some ⟨5,7,2,0,23⟩
  | 1349 => some ⟨71,23,7,0,7⟩
  | 1769 => some ⟨61,23,10,0,7⟩
  | 2245 => some ⟨5,7,2,0,23⟩
  | 2777 => some ⟨2777,7,1388,0,23⟩
  | 3365 => some ⟨5,7,2,0,23⟩
  | _ => none

private def keep_7_23 : List (ℕ × ℤ) := [(29,40),(83,128),(83,163),(103,8),(383,8),(383,2395)]

private theorem grid_7_23 : divisorGrid 7 23 119 qInputs_7_23 keep_7_23 := by decide +kernel

private theorem frontier_mixed_203_201_40 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=203) : ¬∃ f : G → ℤ, IsSDS 201 40 f :=
  abelian_short_linear G 7 29 11 1 1 0 201 40 23 13 2 13
    ⟨⟨(-14),1,0,0⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)



private def types_frontier_mixed_2681_169_8 : List RowType := [(13,31),(14,28),(15,31),(16,26),(17,27),(18,20),(18,34),(19,33),(20,24),(20,38),(21,21),(21,35),(22,38),(23,33),(24,34),(25,41),(26,40),(27,31),(27,45),(28,42),(29,45),(30,40),(31,41),(32,34),(32,48)]
private def stage_0_frontier_mixed_2681_169_8 : Stage := [
  ((13,31),⟨⟨(-3804722),0,0,4070⟩,[0,0,0,0,0,0,0],53⟩),
  ((14,28),⟨⟨0,(-4466),0,0⟩,[0,0,0,0,0,0,0],1⟩),
  ((16,26),⟨⟨0,(-18424),0,0⟩,[0,0,0,0,0,0,0],27⟩),
  ((18,20),⟨⟨0,0,0,(-2303)⟩,[0,0,0,0,0,0,0],72⟩),
  ((18,34),⟨⟨(-44922836),0,0,(-8596)⟩,[0,0,0,40054140,0,0,0],533⟩),
  ((21,21),⟨⟨(-93912),0,0,0⟩,[0,0,0,0,0,0,0],1⟩),
  ((21,35),⟨⟨0,(-6153),0,0⟩,[0,0,0,1953,4032,0,0],1⟩),
  ((23,33),⟨⟨0,(-30156),0,0⟩,[0,0,0,0,0,0,230748],13⟩),
  ((24,34),⟨⟨(-17909080),0,0,17290⟩,[0,0,0,0,9930424,0,0],129⟩),
  ((28,42),⟨⟨0,(-7364),0,0⟩,[0,0,0,3472,7168,0,0],1⟩),
  ((30,40),⟨⟨0,(-209167),131558,0⟩,[0,0,0,0,0,0,0],33⟩),
  ((32,48),⟨⟨(-3129876),0,0,1404⟩,[0,0,0,0,0,0,406746],47⟩)]
private theorem frontier_mixed_2681_169_8 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2681) : ¬∃ f : G → ℤ, IsSDS 169 8 f :=
  abelian_short_mixed G 7 383 11 1 1 0 169 8 23 21 2 13 219 4
    types_frontier_mixed_2681_169_8 [stage_0_frontier_mixed_2681_169_8] ⟨⟨(-755392),0,25056,0⟩,[0,0,0,106227,0,0,191808],0⟩ hG (by decide +kernel)

private theorem frontier_mixed_2681_2556_2395 (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hG : Fintype.card G=2681) : ¬∃ f : G → ℤ, IsSDS 2556 2395 f :=
  abelian_short_linear G 7 383 11 1 1 0 2556 2395 23 362 2 13
    ⟨⟨(-128510),717,0,(-1)⟩,[0,0,0,0,0,0,0],0⟩ hG (by decide +kernel)

theorem fixed_7_23_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=7*m)
    (hm : 7 < m) (hn : k-l=(7:ℤ)*23) : False := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have row := endpoint_case (s:=23) hf hg hn (by decide) hm grid_7_23
  simp only [keep_7_23,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=201 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_203_201_40 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=289 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_581_289_128 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=324 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_581_324_163 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=169 := by omega
    rw [hk,hL] at hf
    exact Signed39.Contraction.no_721_169_8 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=169 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2681_169_8 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2556 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2681_2556_2395 G hg ⟨f,hf⟩

end Signed39.Contraction
