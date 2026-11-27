import PermanentJetFrame
import PermanentAmbientEight
import PermanentBlockCover
import PermanentTwelveLayouts

/-! Two separate tests on a small board. A twelve-cell extension supplies
a simple zero, and a thirteen-cell board supplies a supported rank-eight test. -/

noncomputable section
open Finset Equiv QuinticPencil
namespace PermanentFive
variable {K : Type*} [Field K]

private def tested (K : Type*) [Field K] (T : Finset Cell) : Prop :=
  ∀ S ⊆ T, (S.card ≤ 12 → HasOddBlock K S) ∧ (S.card = 13 → HasAmbientEight K S)

private theorem tested_rule : CoverRule (tested K) := by
  constructor
  · intro S T h sub B hB
    exact h B (hB.trans sub)
  · intro S T h e act sub B hB
    let C := B.map e.symm.toEmbedding
    have inc : C ⊆ T := by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
      exact sub i (hB hi)
    have cc : C.card = B.card := Finset.card_map _
    obtain ⟨odd,ambient⟩ := h C inc
    constructor
    · intro small
      apply (odd (cc.trans_le small)).relabel e (act.rename (DualNumber K))
      exact fun i hi ↦ Finset.mem_map.mpr ⟨i,hi,rfl⟩
    · intro eq
      obtain ⟨z,support,rank⟩ := ambient (cc.trans eq)
      refine ⟨z ∘ e.symm,?_,?_⟩
      · intro i hi
        apply support
        exact fun hc ↦ hi (by simpa [C,Finset.mem_map_equiv] using hc)
      · rw [(transport e (act.rename K) z).2]
        exact rank

private theorem parent_test (odd : ∀ i, HasOddBlock K (twelveShape i))
    (ambient : ∀ t, HasAmbientEight K (thirteenShape t)) (t : Fin 4) :
    tested K (thirteenShape t) := by
  intro S sub
  have n := thirteenShape_card t
  constructor
  · intro small
    obtain ⟨x,hx,out⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show S.card < (thirteenShape t).card by omega)
    obtain ⟨i,r,c,layout⟩ := twelve_deletion t x hx
    apply (odd i).relabel (r.prodCongr c).symm (row_column_rename r.symm c.symm)
    exact fun j hj ↦ layout j (Finset.subset_erase.mpr ⟨sub,out⟩ hj)
  · intro eq
    have same := Finset.eq_of_subset_of_card_le sub (by omega)
    rw [same]
    exact ambient t

theorem small_twenty_tests (S : Finset Cell) (small : S.card ≤ 13)
    (matching : ∀ p : Perm Idx, (univ.filter (fun i ↦ p i ∈ PermanentCover.neighbors S i)).card ≤ 3)
    (odd : ∀ i, HasOddBlock K (twelveShape i))
    (ambient : ∀ t, HasAmbientEight K (thirteenShape t)) :
    (S.card ≤ 12 → HasOddBlock K S) ∧ (S.card = 13 → HasAmbientEight K S) := by
  have h := small_cover_property (tested_rule (K:=K)) S small matching
    (parent_test odd ambient 0) (parent_test odd ambient 1)
    (parent_test odd ambient 2) (parent_test odd ambient 3)
  exact h S (Finset.Subset.refl S)

#print axioms small_twenty_tests
end PermanentFive
