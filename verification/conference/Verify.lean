import Statement
import Quantum.Hadamard.DeterminantRatioEstimateUnbalanced
import Quantum.Hadamard.ConferenceBalancedMean
import Quantum.Hadamard.ProjectivePaleyDeterminant

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
    have a := balanced_conference_four_fifths_169 k (Fintype.card_fin _) (Fintype.card_fin _)
      (q ▸ large) hc sqr dia entry
    simpa only [ewBound, sig] using a
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

private theorem hermitian_of_transpose {I : Type*} {C : Matrix I I ℝ} (h : C.transpose=C) :
    C.IsHermitian := by
  change C.conjTranspose=C
  ext i j
  exact congrArg (fun A : Matrix I I ℝ ↦ A i j) h

private theorem ratio_eq {a b : ℕ} (k : ℕ) (C : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ) :
    |(C+Matrix.diagonal completionSign).det| / ewBound k = ConferenceAudit.completedRatio k C := by
  have sig : (completionSign : Fin a ⊕ Fin b → ℝ) = ConferenceAudit.signedDiagonal := by
    funext s; cases s <;> rfl
  simp only [sig, ewBound, ConferenceAudit.completedRatio]

theorem verifiedBalancedLimit : ConferenceAudit.BalancedLimit := by
  intro ι l k grow C sym square diag off
  have lim := balanced_conference_tendsto l k grow C (fun j ↦ hermitian_of_transpose (sym j))
    square diag (fun j i s ne ↦ by rcases off j i s ne with h|h <;> rw [h] <;> norm_num)
  simpa only [ratio_eq] using lim

theorem verifiedProportionLimit : ConferenceAudit.ProportionLimit := by
  intro ι l k a b z grow count proportion C sym square diag off
  have lim := conference_proportion_tendsto l k a b grow count proportion C
    (fun j ↦ hermitian_of_transpose (sym j)) square diag
    (fun j i s ne ↦ by rcases off j i s ne with h|h <;> rw [h] <;> norm_num)
  simpa only [ratio_eq] using lim

#print axioms verifiedBalancedLimit
#print axioms verifiedProportionLimit

open Hadamard.ConferenceAverage

theorem verifiedDiagonalGenerating : ConferenceAudit.DiagonalGenerating := by
  intro v q z C hq sym square trace
  exact absolute_generating C v q z (Fintype.card_fin _) hq (hermitian_of_transpose sym) square trace

theorem verifiedBalancedMean : ConferenceAudit.BalancedMean := by
  intro k C hk sym square zero q
  have kp : 0<(k:ℝ) := by exact_mod_cast hk
  have cp : 0<((2*(k+1)).choose (k+1):ℝ) := by exact_mod_cast Nat.centralBinom_pos (k+1)
  apply (le_div_iff₀ cp).mpr
  have tr : C.trace=0 := by simp [Matrix.trace, Matrix.diag, zero]
  have H := balanced_total_lower C (k+1) q (Fintype.card_fin _)
    (by dsimp [q]; linarith) (by dsimp [q]; push_cast; ring) (hermitian_of_transpose sym) square tr
  rw [← Finset.sum_filter, mul_comm ((q+1/q)^_) _]
  refine le_trans H (le_of_eq ?_)
  apply Finset.sum_congr
  · ext f
    simp [signClass, positiveCount]
    exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ f))
  · intro f hf
    rfl

theorem verifiedAboveLimitAtEveryOrder : ConferenceAudit.AboveLimitAtEveryOrder := by
  intro k C hk sym square zero _
  have tr : C.trace=0 := by simp [Matrix.trace, Matrix.diag, zero]
  obtain ⟨f, balance, det⟩ := exists_balanced_above_limit C k hk (Fintype.card_fin _)
    (hermitian_of_transpose sym) square tr
  refine ⟨fun i ↦ signValue (f i), fun i ↦ ?_, ?_, ?_⟩
  · change (signValue (f i):ℝ)=1 ∨ (signValue (f i):ℝ)= -1
    cases hb : f i <;> norm_num [signValue, hb]
  · have h (i) : (signValue (f i):ℝ)=1 ↔ f i=true := by
      cases hb : f i <;> norm_num [signValue, hb]
    change (Finset.univ.filter (fun i ↦ (signValue (f i):ℝ)=1)).card = k+1
    simpa only [h, positiveCount] using balance
  · convert det using 2
    ring

theorem verifiedAllBalanced110 : ConferenceAudit.AllBalanced110 := by
  intro k C s size sym square diag off balance
  have n : (110:ℝ) ≤ 2*((k:ℝ)+1) := by exact_mod_cast size
  have sig (i j) (h : i≠j) : C i j^2=1 := by
    rcases off i j h with h | h <;> rw [h] <;> norm_num
  have v := Hadamard.ProjectiveSigning.balanced_signs_on_indices_109 C s k
    (Fintype.card_fin _) balance (by linarith) (hermitian_of_transpose sym) square diag sig
  simpa only [ewBound] using v

#print axioms verifiedAllBalanced110

#print axioms verifiedDiagonalGenerating
#print axioms verifiedBalancedMean
#print axioms verifiedAboveLimitAtEveryOrder
