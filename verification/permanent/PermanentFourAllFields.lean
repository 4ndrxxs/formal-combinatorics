import PermanentOrderFourSpectrum
import PermanentBinaryFixedOrder

/-! The complete order-four smooth spectrum over every field, together
with the zero-line constraint on all smooth points of rank below eight. -/
noncomputable section
open Matrix Equiv Finset PermanentFive PermanentBorder QuinticPencil PermanentOrderThree
namespace PermanentOrderFour
variable {K : Type*} [Field K]

private theorem strip_exists (z : Cell4 → K) (flat : PermanentBorder.value z=0)
    (smooth : grad z (3,3)≠0) (row : ∃ j, z (3,j)≠0) : BottomNonzero z := by
  unfold BottomNonzero
  by_contra! missing
  have e0 := missing 0 (by decide)
  have e1 := missing 1 (by decide)
  have e2 := missing 2 (by decide)
  rw [value_eq] at flat
  simp [Fin.sum_univ_succ,e0,e1,e2] at flat
  have e3 := flat.resolve_right smooth
  obtain ⟨j,nz⟩ := row
  fin_cases j <;> contradiction

theorem small_smooth_zero_line (two_ne : (2:K)≠0) (z : Cell4 → K)
    (flat : PermanentBorder.value z=0) (smooth : cofactor z≠0)
    (small : (hessian (per K F) z).rank≤7) :
    (∃ i, ∀ j, z (i,j)=0) ∨ ∃ j, ∀ i, z (i,j)=0 := by
  by_contra! neither
  obtain ⟨i,j,h⟩ : ∃ i j : F, grad z (i,j)≠0 := by
    by_contra! empty
    exact smooth (Matrix.ext fun r c ↦ (grad_eq z (r,c)).trans (empty r c))
  let r := Equiv.swap 3 i
  let c := Equiv.swap 3 j
  let x := z ∘ r.prodCongr c
  have hx : grad x (3,3)≠0 := by
    change grad (z ∘ r.prodCongr c) (3,3)≠0
    rw [renamed_grad _ (row_column_rename r c)]
    simpa [r,c] using h
  have zx : PermanentBorder.value x=0 := (renamed_value _ (row_column_rename r c) z).trans flat
  have rk : (H x).rank≤7 := by
    change (H (z ∘ r.prodCongr c)).rank≤7
    rwa [renamed_rank _ (row_column_rename r c),←hess_eq]
  apply no_small_chart two_ne x
  refine ⟨rk,hx,zx,strip_exists x zx hx ?_,?_⟩
  · obtain ⟨t,ht⟩ := neither.1 i
    exact ⟨c.symm t,by simpa [x,r] using ht⟩
  · apply strip_exists (transposePoint x)
    · rw [transposePoint,renamed_value _ transpose_rename,zx]
    · rw [transposePoint,renamed_grad _ transpose_rename]
      exact hx
    · obtain ⟨t,ht⟩ := neither.2 j
      exact ⟨r.symm t,by simpa [transposePoint,x,c] using ht⟩

theorem all_fields (s : ℕ) : AtOrder K 4 s ↔
    ((2:K)=0 ∧ s=8) ∨ ((2:K)≠0 ∧ (s=4 ∨ s=6 ∨ (8≤s ∧ s≤16 ∧ (s=16 → (3:K)≠0)))) := by
  by_cases binary : (2:K)=0
  · rw [DeterminantHessian.fixed_binary_smooth binary 4 s (by decide)]
    simp [binary]
  · rw [fixed_four_odd binary]
    simp [binary]

#print axioms small_smooth_zero_line
#print axioms all_fields
end PermanentOrderFour
