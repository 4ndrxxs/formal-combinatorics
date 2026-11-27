module
public import Mathlib

/-! Extracting one supported permutation from a common vector state. -/
@[expose] public section
noncomputable section
open Finset
namespace WeberCompletion

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype I] [DecidableEq I]

abbrev Op (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] := H →L[ℂ] H

/-- Weber's quantum permutation matrix, with projections of arbitrary rank. -/
structure Magic (U : I → I → Op H) : Prop where
  projection : ∀ i j, IsStarProjection (U i j)
  row : ∀ i, ∑ j, U i j=1
  column : ∀ j, ∑ i, U i j=1

def weight (x : H) (T : Op H) : ℝ := (inner ℂ x (T x)).re / ‖x‖^2

theorem weight_of_fix {x : H} (hx : x≠0) {T : Op H} (fix : T x=x) : weight x T=1 := by
  rw [weight,fix,inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow,hx]

theorem weight_of_zero {x : H} {T : Op H} (ann : T x=0) : weight x T=0 := by simp [weight,ann]

theorem sum_weight (x : H) (U : I → Op H) :
    ∑ i, weight x (U i) = weight x (∑ i, U i) := by
  simp only [weight,ContinuousLinearMap.sum_apply,inner_sum,Complex.re_sum,Finset.sum_div]

theorem Magic.doubly_stochastic {U : I → I → Op H} (h : Magic U) {x : H} (hx : x≠0) :
    (fun i j => weight x (U i j) : Matrix I I ℝ) ∈ doublyStochastic ℝ I := by
  apply mem_doublyStochastic_iff_sum.mpr
  refine ⟨fun i j => div_nonneg ?_ (sq_nonneg _),fun i => ?_,fun j => ?_⟩
  · exact (ContinuousLinearMap.IsPositive.of_isStarProjection (h.projection i j)).re_inner_nonneg_right x
  · change ∑ j, weight x (U i j)=1
    rw [sum_weight,h.row]
    exact weight_of_fix hx rfl
  · change ∑ i, weight x (U i j)=1
    rw [sum_weight,h.column]
    exact weight_of_fix hx rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Hall's marriage theorem applied to the positive entries of a bistochastic matrix. -/
theorem supported_permutation {M : Matrix I I ℝ} (hm : M∈doublyStochastic ℝ I) :
    ∃ σ : Equiv.Perm I, ∀ i, 0<M i (σ i) := by
  classical
  have h := mem_doublyStochastic_iff_sum.mp hm
  let nb (i : I) := univ.filter fun j => M i j≠0
  have hall (S : Finset I) : S.card≤(S.biUnion nb).card := by
    have row (i : I) : ∑ j ∈ nb i, M i j=1 := by
      simpa [nb,Finset.sum_filter_of_ne] using h.2.1 i
    have left : ∑ i ∈ S, ∑ j ∈ nb i, M i j=(S.card:ℝ) := by simp [row]
    have right : ∑ i, ∑ j ∈ S.biUnion nb, M i j=((S.biUnion nb).card:ℝ) := by
      rw [Finset.sum_comm (s:=univ) (t:=S.biUnion nb) (f:=fun i j => M i j)]
      simp [h.2.2]
    have ineq : (S.card:ℝ)≤((S.biUnion nb).card:ℝ) := by
      rw [← left,← right]
      calc
        _ ≤ ∑ i ∈ S, ∑ j ∈ S.biUnion nb, M i j :=
          sum_le_sum (fun i hi => sum_le_sum_of_subset_of_nonneg (subset_biUnion_of_mem nb hi)
            (fun j _ _ => h.1 i j))
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ S)
          (fun i _ _ => sum_nonneg (fun j _ => h.1 i j))
    exact_mod_cast ineq
  obtain ⟨f,inj,mem⟩ := (all_card_le_biUnion_card_iff_exists_injective nb).mp hall
  refine ⟨Equiv.ofBijective f ⟨inj,Finite.injective_iff_surjective.mp inj⟩,fun i => ?_⟩
  exact lt_of_le_of_ne (h.1 i _) (mem_filter.mp (mem i)).2.symm

theorem forced_at_one {M : Matrix I I ℝ} (hm : M∈doublyStochastic ℝ I) {σ : Equiv.Perm I}
    (hs : ∀ i, 0<M i (σ i)) {i j : I} (h : M i j=1) : σ i=j := by
  classical
  by_contra ne
  have r := sum_row_of_mem_doublyStochastic hm i
  have e := univ.sum_erase_add (fun x => M i x) (mem_univ j)
  rw [r,h] at e
  have pos := single_le_sum (s:=univ.erase j) (fun x _ => nonneg_of_mem_doublyStochastic hm (i:=i) (j:=x))
    (a:=σ i) (by simp [ne])
  linarith [hs i]

end WeberCompletion
