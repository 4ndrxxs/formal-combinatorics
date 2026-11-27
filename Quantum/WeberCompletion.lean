module
public import Quantum.WeberAtoms
public import Quantum.WeberMatching

/-! Weber 2023, Problem 3.6: commuting entries prescribed at arbitrary positions of
a square operator matrix always have a commuting completion if they have a quantum
permutation completion. No dimensional or rank restriction is imposed on the Hilbert space. -/
@[expose] public section
noncomputable section
open Finset
namespace WeberCompletion

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype I] [DecidableEq I]

theorem local_choice (U : I → I → Op H) (h : Magic U) (s : Finset (I × I)) (F : Op H)
    (binary : ∀ e∈s, U e.1 e.2*F=0 ∨ U e.1 e.2*F=F) :
    ∃ σ : Equiv.Perm I, ∀ e∈s, U e.1 e.2*F=if σ e.1=e.2 then F else 0 := by
  classical
  by_cases empty : F=0
  · exact ⟨Equiv.refl _,fun e _ => by simp [empty]⟩
  obtain ⟨y,hn⟩ : ∃ y, F y≠0 := by
    by_contra! no
    exact empty (ContinuousLinearMap.ext no)
  let x := F y
  have hx : x≠0 := hn
  let M : Matrix I I ℝ := fun i j => weight x (U i j)
  have hm : M∈doublyStochastic ℝ I := h.doubly_stochastic hx
  obtain ⟨σ,good⟩ := supported_permutation hm
  refine ⟨σ,fun e mem => ?_⟩
  rcases binary e mem with ann | fix
  · have vec : U e.1 e.2 x=0 := congrArg (fun T : Op H => T y) ann
    have zero : M e.1 e.2=0 := weight_of_zero vec
    have ne : σ e.1≠e.2 := by
      intro eq
      have pos := good e.1
      rw [eq,zero] at pos
      exact lt_irrefl _ pos
    simp [ann,ne]
  · have vec : U e.1 e.2 x=x := congrArg (fun T : Op H => T y) fix
    have one : M e.1 e.2=1 := weight_of_fix hx vec
    simp [fix,forced_at_one hm good one]

variable {K : Type*} [Fintype K]

def assemble (F : K → Op H) (σ : K → Equiv.Perm I) (i j : I) :=
  select F (fun k => σ k i=j)

theorem assembled_magic {F : K → Op H} (part : Partition F) (σ : K → Equiv.Perm I) :
    Magic (assemble F σ) := by
  classical
  constructor
  · exact fun i j => part.select_projection _
  · intro i
    unfold assemble select
    rw [Finset.sum_comm]
    calc
      _ = ∑ k, F k := by
        apply sum_congr rfl
        intro k _
        rw [sum_eq_single (σ k i)] <;> simp_all [eq_comm]
      _ = 1 := part.total
  · intro j
    unfold assemble select
    rw [Finset.sum_comm]
    calc
      _ = ∑ k, F k := by
        apply sum_congr rfl
        intro k _
        rw [sum_eq_single ((σ k).symm j)]
        · simp
        · intro b _ ne
          have diff : σ k b ≠ j := fun eq => ne ((σ k).eq_symm_apply.mpr eq)
          simp [diff]
        · simp
      _ = 1 := part.total

theorem assembled_commute {F : K → Op H} (part : Partition F) (σ : K → Equiv.Perm I)
    (i j a b : I) : Commute (assemble F σ i j) (assemble F σ a b) := part.select_commute _ _

/-- The input is any completion of the specified mask. The conclusion agrees as
operators at every clue, and all entries of the replacement commute pairwise. -/
theorem commuting_completion (U : I → I → Op H) (h : Magic U) (s : Finset (I × I))
    (hc : ∀ e∈s, ∀ f∈s, Commute (U e.1 e.2) (U f.1 f.2)) :
    ∃ W : I → I → Op H, Magic W ∧
      (∀ e∈s, W e.1 e.2=U e.1 e.2) ∧ (∀ i j a b, Commute (W i j) (W a b)) := by
  classical
  let P (e : I × I) := U e.1 e.2
  obtain ⟨K,inst,F,part,binary,_⟩ := atom_decomposition s P (fun e _ => h.projection _ _) hc
  choose σ good using fun k : K => local_choice U h s (F k) (fun e he => binary e he k)
  refine ⟨assemble F σ,assembled_magic part σ,?_,assembled_commute part σ⟩
  intro e he
  calc
    _ = ∑ k, U e.1 e.2*F k := by
      unfold assemble select
      apply sum_congr rfl
      intro k _
      have z := good k e he
      by_cases eq : σ k e.1=e.2 <;> simpa [eq] using z.symm
    _ = _ := by rw [← Finset.mul_sum,part.total,mul_one]

/-- Equivalent formulation entirely in terms of the original partial data. -/
theorem weber_problem_3_6 (s : Finset (I × I)) (clue : I → I → Op H)
    (hc : ∀ e∈s, ∀ f∈s, Commute (clue e.1 e.2) (clue f.1 f.2)) :
    (∃ U, Magic U ∧ ∀ e∈s, U e.1 e.2=clue e.1 e.2) ↔
    (∃ W, Magic W ∧ (∀ e∈s, W e.1 e.2=clue e.1 e.2) ∧
      ∀ i j a b, Commute (W i j) (W a b)) := by
  constructor
  · rintro ⟨U,h,hu⟩
    obtain ⟨W,hw,he,c⟩ := commuting_completion U h s (by
      intro e h₁ f h₂
      rw [hu e h₁,hu f h₂]
      exact hc e h₁ f h₂)
    exact ⟨W,hw,fun e hz => (he e hz).trans (hu e hz),c⟩
  · rintro ⟨W,h,agree,_⟩
    exact ⟨W,h,agree⟩

#print axioms commuting_completion
#print axioms weber_problem_3_6
end WeberCompletion
