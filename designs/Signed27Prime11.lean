import Signed27Grid11Part0
import Signed27Grid11Part12
import Signed27Grid11Part24
import Signed27Grid11Part36
import Signed27Grid11Part48
import SignedOrbit11Cofactor27
import Signed27Case913W441
import Signed27Case913W628
import Signed27Case1177W361
import Signed27Case1177W988
import Signed27Case1441W324
import Signed27Case1441W1369
import Signed27Case2629W328
import Signed27Case2629W2385
import SignedExtendedClassification
import SignedBudgetCertificate

namespace Signed39.Contraction

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grid_11_27 : divisorGrid 11 27 176 qInputs_11_27 keep_11_27 := by
  intro d
  fin_cases d
  · exact grid11x27Case0
  · exact grid11x27Case1
  · exact grid11x27Case2
  · exact grid11x27Case3
  · exact grid11x27Case4
  · exact grid11x27Case5
  · exact grid11x27Case6
  · exact grid11x27Case7
  · exact grid11x27Case8
  · exact grid11x27Case9
  · exact grid11x27Case10
  · exact grid11x27Case11
  · exact grid11x27Case12
  · exact grid11x27Case13
  · exact grid11x27Case14
  · exact grid11x27Case15
  · exact grid11x27Case16
  · exact grid11x27Case17
  · exact grid11x27Case18
  · exact grid11x27Case19
  · exact grid11x27Case20
  · exact grid11x27Case21
  · exact grid11x27Case22
  · exact grid11x27Case23
  · exact grid11x27Case24
  · exact grid11x27Case25
  · exact grid11x27Case26
  · exact grid11x27Case27
  · exact grid11x27Case28
  · exact grid11x27Case29
  · exact grid11x27Case30
  · exact grid11x27Case31
  · exact grid11x27Case32
  · exact grid11x27Case33
  · exact grid11x27Case34
  · exact grid11x27Case35
  · exact grid11x27Case36
  · exact grid11x27Case37
  · exact grid11x27Case38
  · exact grid11x27Case39
  · exact grid11x27Case40
  · exact grid11x27Case41
  · exact grid11x27Case42
  · exact grid11x27Case43
  · exact grid11x27Case44
  · exact grid11x27Case45
  · exact grid11x27Case46
  · exact grid11x27Case47
  · exact grid11x27Case48
  · exact grid11x27Case49
  · exact grid11x27Case50
  · exact grid11x27Case51
  · exact grid11x27Case52
  · exact grid11x27Case53











theorem fixed_11_27_false {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {m : ℕ} {k l : ℤ} {f : G → ℤ} (hf : IsSDS k l f) (hg : Fintype.card G=11*m)
    (hm : 11 < m) (hn : k-l=(11:ℤ)*27) : False := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have row := endpoint_case (s:=27) hf hg hn (by decide) hm grid_11_27
  simp only [keep_11_27,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
  rcases row with row|row|row|row|row|row|row|row
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=441 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_913_441_144 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=628 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_913_628_331 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=361 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1177_361_64 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=988 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1177_988_691 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=324 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1441_324_27 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=1369 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_1441_1369_1072 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=328 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2629_328_31 G hg ⟨f,hf⟩
  · obtain ⟨hm,hL⟩ := row
    subst m
    have hk : k=2385 := by omega
    rw [hk,hL] at hf
    exact frontier_mixed_2629_2385_2088 G hg ⟨f,hf⟩

end Signed39.Contraction
