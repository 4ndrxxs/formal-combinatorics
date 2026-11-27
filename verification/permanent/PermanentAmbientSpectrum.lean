import PermanentSmoothSpectrum

/-! The same ranks occur on the total affine spaces and on the zero
fibres, when the order may vary. -/
noncomputable section
open Matrix PermanentFive QuinticPencil
namespace PermanentBorder
variable {K : Type*} [Field K]
def AmbientOccurs (K : Type*) [Field K] (s : ℕ) : Prop :=
  ∃ n, ∃ z : CellOf (Fin n) → K, (hessian (per K (Fin n)) z).rank=s

theorem ambient_iff_zero_fibre (s : ℕ) : AmbientOccurs K s ↔ Occurs K s := by
  constructor
  · rintro ⟨n,z,rank⟩
    have gap := permanent_hessian_rank_gap z
    rw [rank] at gap
    by_cases two : (2:K)=0
    · apply (spectrum_of_two_eq_zero two s).2
      have e := even_hessian two z
      rw [rank] at e
      rcases gap with h|h|h
      · exact Or.inl h
      · exact Or.inr ⟨by omega,e⟩
      · exact Or.inr ⟨by omega,e⟩
    · exact (spectrum_of_two_ne_zero two s).2 gap
  · rintro ⟨n,z,_,rank⟩
    exact ⟨n,z,rank⟩
#print axioms ambient_iff_zero_fibre
end PermanentBorder
