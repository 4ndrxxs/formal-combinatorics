module
public import Quantum.WeberMatching
public import Mathlib.Analysis.Convex.Birkhoff

/-! A positive entry in a doubly stochastic matrix extends to a positive
permutation. A projection with vanishing vector weight annihilates that vector. -/
@[expose] public section
noncomputable section
namespace WeberCompletion
open Finset
variable {I H : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem permutation_through {M : Matrix I I ℝ} (hm : M∈doublyStochastic ℝ I)
    {i j : I} (pos : 0<M i j) :
    ∃ σ : Equiv.Perm I, σ i=j ∧ ∀ a, 0<M a (σ a) := by
  classical
  obtain ⟨w,nonneg,_,sum⟩:=exists_eq_sum_perm_of_mem_doublyStochastic hm
  have formula (a b : I) : (∑ σ : Equiv.Perm I, if σ a=b then w σ else 0)=M a b := by
    have h:=congrArg (fun A : Matrix I I ℝ => A a b) sum
    simpa [Matrix.sum_apply,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,eq_comm] using h
  have exists_pos : ∃ σ : Equiv.Perm I, σ i=j ∧ 0<w σ := by
    by_contra! no
    have vanish : (∑ σ : Equiv.Perm I, if σ i=j then w σ else 0)=0 := by
      apply sum_eq_zero
      intro σ _
      by_cases e : σ i=j
      · simp [e,le_antisymm (no σ e) (nonneg σ)]
      · simp [e]
    exact (ne_of_gt pos) ((formula i j).symm.trans vanish)
  obtain ⟨σ,hσ,hw⟩:=exists_pos
  refine ⟨σ,hσ,fun a => ?_⟩
  rw [←formula]
  apply lt_of_lt_of_le hw
  have h:=single_le_sum (s:=univ) (f:=fun τ : Equiv.Perm I => if τ a=σ a then w τ else 0)
    (fun τ _ => by split <;> first | exact nonneg _ | exact le_rfl) (mem_univ σ)
  simpa using h

theorem weight_eq_norm {T : Op H} (proj : IsStarProjection T) (x : H) :
    weight x T=‖T x‖^2/‖x‖^2 := by
  have self : T.adjoint=T := proj.isSelfAdjoint.star_eq
  have twice : T (T x)=T x := congrArg (fun A : Op H => A x) proj.isIdempotentElem.eq
  have h := T.adjoint_inner_right x (T x)
  rw [self,twice,inner_self_eq_norm_sq_to_K] at h
  simp [weight,h,← Complex.ofReal_pow]

theorem annihilates_of_weight_zero {T : Op H} (proj : IsStarProjection T) {x : H}
    (hx : x≠0) (h : weight x T=0) : T x=0 := by
  rw [weight_eq_norm proj] at h
  have ne : ‖x‖^2≠0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have zero := (div_eq_zero_iff.mp h).resolve_right ne
  exact norm_eq_zero.mp (by nlinarith [zero])

end WeberCompletion
