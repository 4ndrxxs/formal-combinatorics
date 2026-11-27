module

public import Quantum.OddLower

/-! The larger summand of an odd-order square uses the noninitial rows
    of two squares and their common first row along a diagonal. -/
@[expose] public section
namespace QuantumCertificate.Odd

abbrev uMask (m : ℕ) := fun x => !vMask m x

private theorem diagonal {m : ℕ} {i j : Fin (m+1)}
    (h : uMask m (.inr i,.inr j) = true) : i=j := by
  simpa [uMask,vMask,IndexedArray.cornerMask] using h

private theorem diagonal_on {m : ℕ} (i : Fin (m+1)) :
    uMask m (.inr i,.inr i) = true := by simp [uMask,vMask,IndexedArray.cornerMask]

def upper {m : ℕ} (a b : Full (m+1)) (h₀ : ∀ i, b.entry (0,i) = a.entry (0,i)) :
    IndexedArray (m+1) (uMask m) where
  entry
    | (.inl _,.inl _) => 0
    | (.inl i,.inr j) => a.entry (i.succ,j)
    | (.inr i,.inl j) => b.entry (j.succ,i)
    | (.inr i,.inr _) => a.entry (0,i)
  nz := by
    rintro ⟨⟨i,j⟩,ha⟩
    rcases i with i|i <;> rcases j with j|j
    · contradiction
    · exact a.nz ⟨(i.succ,j),rfl⟩
    · exact b.nz ⟨(j.succ,i),rfl⟩
    · exact a.nz ⟨(0,i),rfl⟩
  unit := by
    rintro ⟨⟨i,j⟩,ha⟩
    rcases i with i|i <;> rcases j with j|j
    · contradiction
    · exact a.unit ⟨(i.succ,j),rfl⟩
    · exact b.unit ⟨(j.succ,i),rfl⟩
    · exact a.unit ⟨(0,i),rfl⟩
  rows := by
    rintro (i|i) (j|j) (k|k) hj hk hn
    all_goals try contradiction
    · exact a.rows i.succ j k rfl rfl (fun e => hn (congrArg Sum.inr e))
    · exact b.cols i j.succ k.succ rfl rfl
        (Fin.succ_injective _ |>.ne (fun e => hn (congrArg Sum.inl e)))
    · change inner ℂ (b.entry (j.succ,i)) (a.entry (0,i)) = 0
      rw [← h₀ i]
      exact b.cols i j.succ 0 rfl rfl j.succ_ne_zero
    · change inner ℂ (a.entry (0,i)) (b.entry (k.succ,i)) = 0
      rw [← h₀ i]
      exact b.cols i 0 k.succ rfl rfl k.succ_ne_zero.symm
    · exact False.elim (hn (congrArg Sum.inr ((diagonal hj).symm.trans (diagonal hk))))
  cols := by
    rintro (i|i) (j|j) (k|k) hj hk hn
    all_goals try contradiction
    · exact b.rows i.succ j k rfl rfl (fun e => hn (congrArg Sum.inr e))
    · exact a.cols i j.succ k.succ rfl rfl
        (Fin.succ_injective _ |>.ne (fun e => hn (congrArg Sum.inl e)))
    · obtain rfl := diagonal hk
      exact a.cols k j.succ 0 rfl rfl j.succ_ne_zero
    · obtain rfl := diagonal hj
      exact a.cols j 0 k.succ rfl rfl k.succ_ne_zero.symm
    · exact False.elim (hn (congrArg Sum.inr ((diagonal hj).trans (diagonal hk).symm)))

theorem rays_upper {m : ℕ} (a b : Full (m+1)) (h₀ : ∀ i, b.entry (0,i) = a.entry (0,i)) :
    (upper a b h₀).rays = a.rays ∪ b.rays := by
  ext z
  constructor
  · rintro ⟨⟨⟨i,j⟩,h⟩,rfl⟩
    cases i <;> cases j
    · contradiction
    · exact Or.inl ⟨⟨_,rfl⟩,rfl⟩
    · exact Or.inr ⟨⟨_,rfl⟩,rfl⟩
    · exact Or.inl ⟨⟨_,rfl⟩,rfl⟩
  · rintro (⟨⟨⟨i,j⟩,h⟩,rfl⟩|⟨⟨⟨i,j⟩,h⟩,rfl⟩)
    · induction i using Fin.cases with
      | zero => exact ⟨⟨(.inr j,.inr j),diagonal_on j⟩,rfl⟩
      | succ i => exact ⟨⟨(.inl i,.inr j),rfl⟩,rfl⟩
    · induction i using Fin.cases with
      | zero =>
        refine ⟨⟨(.inr j,.inr j),diagonal_on j⟩,?_⟩
        apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
        exact ⟨1,by simp [upper,h₀ j]⟩
      | succ i => exact ⟨⟨(.inr j,.inl i),rfl⟩,rfl⟩

end QuantumCertificate.Odd
