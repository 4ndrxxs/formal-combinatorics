import PermanentCover
import PermanentSymmetry

/-! Place the single omitted cell of a three-row support at a fixed corner. -/

noncomputable section
open Finset Equiv
namespace PermanentFive

private def topThree : Finset Idx := univ.filter (fun i ↦ i.val < 3)

private theorem align_rows (R : Finset Idx) (count : R.card=3) {r : Idx} (hr : r ∈ R) :
    ∃ q : Perm Idx, q 0 = r ∧ ∀ i : Idx, i.val < 3 → q i ∈ R := by
  have a : (topThree.erase 0).card = 2 := by decide +kernel
  have b : (R.erase r).card = 2 := by rw [card_erase_of_mem hr,count]
  obtain ⟨q,move⟩ := move_into (topThree.erase 0) (R.erase r) (by omega)
  let v := q.trans (Equiv.swap (q 0) r)
  have v0 : v 0 = r := by simp [v]
  refine ⟨v,v0,?_⟩
  intro i hi
  by_cases zero : i = 0
  · simpa only [zero,v0] using hr
  · have h := mem_erase.mp (move i (mem_erase.mpr ⟨zero,mem_filter.mpr ⟨mem_univ _,hi⟩⟩))
    simpa only [v,Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne
      (fun eq ↦ zero (q.injective eq)) h.1] using h.2

theorem almost_rows (S : Finset Cell) (R : Finset Idx) (count : R.card=3)
    (sub : S ⊆ R.product univ) (large : 14 ≤ S.card) :
    ∃ q v : Perm Idx, ∀ i j : Idx, i.val < 3 → (i,j) ≠ ((0,0) : Cell) → (q i,v j) ∈ S := by
  classical
  let box := R.product (univ : Finset Idx)
  let holes := box \ S
  have bc : box.card = 15 := by
    change (R ×ˢ (univ : Finset Idx)).card = 15
    rw [card_product,count,card_univ,Fintype.card_fin]
  have small : holes.card ≤ 1 := by
    dsimp only [holes]
    rw [card_sdiff_of_subset sub]
    change (R.product (univ : Finset Idx)).card - S.card ≤ 1
    change box.card - S.card ≤ 1
    omega
  obtain ⟨r,hr,c,unique⟩ : ∃ r ∈ R, ∃ c : Idx, ∀ i ∈ R, ∀ j : Idx,
      (i,j) ∉ S → (i,j) = (r,c) := by
    by_cases existsHole : holes.Nonempty
    · obtain ⟨⟨r,c⟩,hc⟩ := existsHole
      have hr := (mem_product.mp (mem_sdiff.mp hc).1).1
      refine ⟨r,hr,c,?_⟩
      intro i hi j missing
      exact (card_le_one.mp small) _ (mem_sdiff.mpr ⟨mem_product.mpr ⟨hi,mem_univ _⟩,missing⟩) _ hc
    · obtain ⟨r,hr⟩ := card_pos.mp (show 0 < R.card by omega)
      refine ⟨r,hr,0,?_⟩
      intro i hi j missing
      exact (existsHole ⟨(i,j),mem_sdiff.mpr ⟨mem_product.mpr ⟨hi,mem_univ _⟩,missing⟩⟩).elim
  obtain ⟨q,q0,inside⟩ := align_rows R count hr
  let v := Equiv.swap 0 c
  have v0 : v 0 = c := Equiv.swap_apply_left _ _
  refine ⟨q,v,?_⟩
  intro i j hi different
  by_contra missing
  have e := unique (q i) (inside i hi) (v j) missing
  exact different (Prod.ext (q.injective ((congrArg Prod.fst e).trans q0.symm))
    (v.injective ((congrArg Prod.snd e).trans v0.symm)))

#print axioms almost_rows
end PermanentFive
