import PermanentWeightedEquiv
import PermanentWeightedSmall3
import PermanentWeightedSmall4
import PermanentWeightedSmall5

/-! A polynomial identity for the weighted Hessian row, valid without
inverting any weight or any integer. -/
noncomputable section
open Matrix Equiv Finset MvPolynomial QuinticPencil PermanentFive PermanentBorder
namespace PermanentArrow.Weighted
variable {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]

private theorem from_anchor {n : ℕ} [NeZero n] (c i j : Fin n) (s : Fin n→R) (v : CellOf (Fin n))
    (ci : c≠i) (cj : c≠j) (ij : i≠j)
    (anch : ∀ c i j : Fin n, c≠i → c≠j → i≠j → ∃ b : Perm (Fin n), b c=0 ∧ b i=1 ∧ b j=2)
    (fixed : ∀ (s : Fin n→R) (v : CellOf (Fin n)), Law 0 1 2 s v) : Law c i j s v := by
  obtain ⟨b,bc,bi,bj⟩ := anch c i j ci cj ij
  let a := b.prodCongr b
  have h : Law (b c) (b i) (b j) (s ∘ b.symm) (a v) := by rw [bc,bi,bj];exact fixed _ _
  have t := law_reindex b.symm (b c) (b i) (b j) s (a v) h
  change Law (b.symm (b c)) (b.symm (b i)) (b.symm (b j)) s (a.symm (a v)) at t
  simpa only [Equiv.symm_apply_apply] using t

private theorem small {n : ℕ} (lo : 3≤n) (hi : n≤5) (c i j : Fin n) (s : Fin n→R) (v : CellOf (Fin n))
    (ci : c≠i) (cj : c≠j) (ij : i≠j) : Law c i j s v := by
  interval_cases n
  · exact from_anchor c i j s v ci cj ij anchor_3 fixed_3
  · exact from_anchor c i j s v ci cj ij anchor_4 fixed_4
  · exact from_anchor c i j s v ci cj ij anchor_5 fixed_5

private theorem unused_index (c : I) (e f : CellOf I) (large : 5<Fintype.card I) :
    ∃ t : I, c≠t ∧ e.1≠t ∧ e.2≠t ∧ f.1≠t ∧ f.2≠t := by
  let s : Finset I := {c,e.1,e.2,f.1,f.2}
  have cap : s.card≤5 := by
    dsimp [s]
    calc
      _ ≤ _ := Finset.card_insert_le _ _
      _ ≤ _ := Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) 1
      _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) 1) 1
      _ = 5 := by simp
  obtain ⟨t,_,ht⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show s.card<(univ:Finset I).card from cap.trans_lt large)
  simp only [s,Finset.mem_insert,Finset.mem_singleton] at ht
  exact ⟨t,by tauto,by tauto,by tauto,by tauto,by tauto⟩

theorem all_weighted (c i j : I) (s : I→R) (v : CellOf I)
    (ci : c≠i) (cj : c≠j) (ij : i≠j) : Law c i j s v := by
  suffices h : ∀ (m : ℕ) (J : Type _) [Fintype J] [DecidableEq J], Fintype.card J=m →
      ∀ (c i j : J) (s : J→R) (v : CellOf J), c≠i → c≠j → i≠j → Law c i j s v by
    exact h _ I rfl c i j s v ci cj ij
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro J _ _ card c i j s v ci cj ij
    by_cases hm : m≤5
    · have cap := Finset.card_le_univ ({c,i,j}:Finset J)
      have card3 : ({c,i,j}:Finset J).card=3 := by simp [ci,cj,ij]
      rw [card3,card] at cap
      let b := Fintype.equivFinOfCardEq card
      let a := b.prodCongr b
      have base := small cap hm (b c) (b i) (b j) (s ∘ b.symm) (a v)
        (b.injective.ne ci) (b.injective.ne cj) (b.injective.ne ij)
      have t := law_reindex b.symm (b c) (b i) (b j) s (a v) base
      change Law (b.symm (b c)) (b.symm (b i)) (b.symm (b j)) s (a.symm (a v)) at t
      simpa only [Equiv.symm_apply_apply] using t
    · obtain ⟨t,ct,it,jt,a,k⟩ := unused_index c (i,j) v (by omega)
      let S := {x : J // x≠t}
      let b := Equiv.optionSubtypeNe t
      let c' : S := ⟨c,ct⟩
      let i' : S := ⟨i,it⟩
      let j' : S := ⟨j,jt⟩
      let v' : CellOf S := (⟨v.1,a⟩,⟨v.2,k⟩)
      have less : Fintype.card S<m := by
        rw [←card]
        exact Fintype.card_subtype_lt (x:=t) (by simp)
      let w := s ∘ b
      have oldLaw := ih _ less S rfl c' i' j' (w ∘ some) v'
        (fun h ↦ ci (congrArg Subtype.val h)) (fun h ↦ cj (congrArg Subtype.val h))
        (fun h ↦ ij (congrArg Subtype.val h))
      have lifted := leaf_law c' i' j' w v' oldLaw
      simpa [b,c',i',j',v',old] using law_reindex b (some c') (some i') (some j') s (old v') lifted

#print axioms all_weighted
end PermanentArrow.Weighted
