import Statement
import Quantum.Hadamard.DeterminantRatioEstimateUnbalanced

open Hadamard.DeterminantRatio

theorem verifiedConferenceEstimates : ConferenceAudit.Estimates := by
  intro k C hk sym sqr dia off
  have hc : C.IsHermitian := by
    change C.conjTranspose=C
    ext i j
    change C j i=C i j
    exact congrArg (fun A : Matrix (Fin (k+1) ⊕ Fin (k+1)) (Fin (k+1) ⊕ Fin (k+1)) ℝ ↦ A i j) sym
  have sig : (completionSign : Fin (k+1) ⊕ Fin (k+1) → ℝ) = ConferenceAudit.signedDiagonal := by
    funext s; cases s <;> rfl
  have entry (i j) (h : i≠j) : C i j^2=1 := by rcases off i j h with h|h <;> rw [h] <;> norm_num
  have q : 2*((k:ℝ)+1)-1=2*(k:ℝ)+1 := by ring
  constructor
  · intro large
    have a := balanced_conference_four_fifths k hk (Fintype.card_fin _) (Fintype.card_fin _)
      (q ▸ large) hc sqr dia (fun i j h ↦ (entry i j h).le)
    simpa only [mul_assoc, sig] using a
  · intro large
    have a := balanced_conference_log_rate k hk (Fintype.card_fin _) (Fintype.card_fin _) large hc sqr dia entry
    simpa only [q, ewBound, sig] using a

#print axioms verifiedConferenceEstimates
#print axioms Hadamard.DeterminantRatio.balanced_conference_tendsto

theorem verifiedProportionEstimate : ConferenceAudit.ProportionEstimate := by
  intro k a b C count sym sqr dia off
  have hc : C.IsHermitian := by
    change C.conjTranspose=C
    ext i j
    change C j i=C i j
    exact congrArg (fun A : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ ↦ A i j) sym
  have sig : (completionSign : Fin a ⊕ Fin b → ℝ)=ConferenceAudit.signedDiagonal := by
    funext s; cases s <;> rfl
  have entry (i j) (h : i≠j) : C i j^2=1 := by rcases off i j h with h|h <;> rw [h] <;> norm_num
  have card : Fintype.card (Fin a)+Fintype.card (Fin b)=2*(k+1) := by simpa using count
  intro n W z d size
  have H := conference_proportion_log_rate k size card hc sqr dia entry
  have q : 2*((k:ℝ)+1)-1=2*(k:ℝ)+1 := by ring
  simpa only [n, W, z, d, q, ewBound, sig, Fintype.card_fin] using H

#print axioms verifiedProportionEstimate
#print axioms Hadamard.DeterminantRatio.conference_proportion_tendsto
