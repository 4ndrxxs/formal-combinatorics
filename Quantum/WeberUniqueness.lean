module
public import Quantum.WeberCompletion
public import Quantum.WeberWeights

/-! Uniqueness of a partial quantum permutation with commuting prescribed
projections. Every supported assignment on a joint Boolean atom contributes
an independent commuting completion. If there is only one assignment, even
a completion with arbitrary noncommuting entries agrees with it. -/
@[expose] public section
noncomputable section
namespace WeberCompletion
open Finset
variable {I K H : Type*} [Fintype I] [DecidableEq I] [Fintype K]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def Fits (s : Finset (I×I)) (clue : I→I→Op H) (F : Op H) (σ : Equiv.Perm I) : Prop :=
  ∀ e∈s, clue e.1 e.2*F=if σ e.1=e.2 then F else 0

def Solves (s : Finset (I×I)) (clue U : I→I→Op H) : Prop :=
  Magic U ∧ ∀ e∈s, U e.1 e.2=clue e.1 e.2

def CommSolves (s : Finset (I×I)) (clue U : I→I→Op H) : Prop :=
  Solves s clue U ∧ ∀ i j a b, Commute (U i j) (U a b)

theorem assemble_mul {F : K→Op H} (part : Partition F) (σ : K→Equiv.Perm I)
    (k : K) (i j : I) : assemble F σ i j * F k = if σ k i=j then F k else 0 := by
  classical
  unfold assemble select
  rw [sum_mul,sum_eq_single k]
  · by_cases h : σ k i=j <;> simp [h,(part.projection k).isIdempotentElem.eq]
  · intro a _ ne
    by_cases h : σ a i=j <;> simp [h,part.orthogonal a k ne]
  · simp

theorem assemble_fits {s : Finset (I×I)} {clue : I→I→Op H}
    {F : K→Op H} (part : Partition F) {σ : K→Equiv.Perm I}
    (fit : ∀ k, Fits s clue (F k) (σ k)) : CommSolves s clue (assemble F σ) := by
  classical
  refine ⟨⟨assembled_magic part σ,?_⟩,assembled_commute part σ⟩
  intro e he
  calc
    _ = ∑ k, clue e.1 e.2*F k := by
      unfold assemble select
      apply sum_congr rfl
      intro k _
      by_cases t : σ k e.1=e.2 <;> simpa [t] using (fit k e he).symm
    _ = _ := by rw [←Finset.mul_sum,part.total,mul_one]

theorem supported_fits {s : Finset (I×I)} {clue U : I→I→Op H} (h : Solves s clue U)
    {F : Op H} (binary : ∀ e∈s, clue e.1 e.2*F=0 ∨ clue e.1 e.2*F=F) (y : H) (hy : F y≠0)
    {σ : Equiv.Perm I} (pos : ∀ i, 0<weight (F y) (U i (σ i))) : Fits s clue F σ := by
  let M : Matrix I I ℝ := fun i j => weight (F y) (U i j)
  have hm : M∈doublyStochastic ℝ I := h.1.doubly_stochastic hy
  intro e he
  rcases binary e he with ann | fix
  · have vec : U e.1 e.2 (F y)=0 := by
      rw [h.2 e he]
      exact congrArg (fun T : Op H => T y) ann
    have ne : σ e.1≠e.2 := by
      intro eq
      have p := pos e.1
      rw [eq,weight_of_zero vec] at p
      exact lt_irrefl _ p
    simp [ann,ne]
  · have vec : U e.1 e.2 (F y)=F y := by
      rw [h.2 e he]
      exact congrArg (fun T : Op H => T y) fix
    have eq := forced_at_one (M:=M) hm pos (weight_of_fix hy vec : M e.1 e.2=1)
    simp [fix,eq]

theorem acts_on_atom {s : Finset (I×I)} {clue U : I→I→Op H} (h : Solves s clue U)
    {F : Op H} (binary : ∀ e∈s, clue e.1 e.2*F=0 ∨ clue e.1 e.2*F=F)
    {σ : Equiv.Perm I} (unique : F≠0 → ∀ τ, Fits s clue F τ → τ=σ) (i j : I) :
    U i j*F=if σ i=j then F else 0 := by
  classical
  ext y
  by_cases hy : F y=0
  · by_cases e : σ i=j <;> simp [e,ContinuousLinearMap.mul_apply,hy]
  have nz : F≠0 := fun h => hy (h ▸ rfl)
  let M : Matrix I I ℝ := fun a b => weight (F y) (U a b)
  have hm : M∈doublyStochastic ℝ I := h.1.doubly_stochastic hy
  have off {b : I} (ne : σ i≠b) : U i b (F y)=0 := by
    apply annihilates_of_weight_zero (h.1.projection i b) hy
    apply le_antisymm _ (nonneg_of_mem_doublyStochastic hm (i:=i) (j:=b))
    by_contra! pos
    obtain ⟨τ,hit,positive⟩ := permutation_through (i:=i) (j:=b) hm pos
    exact ne ((unique nz τ (supported_fits h binary y hy positive)) ▸ hit)
  by_cases eq : σ i=j
  · rw [if_pos eq]
    have total := congrArg (fun T : Op H => T (F y)) (h.1.row i)
    simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.one_apply] at total
    rw [sum_eq_single j] at total
    · exact total
    · exact fun b _ ne => off (eq ▸ ne.symm)
    · simp
  · simpa [eq,ContinuousLinearMap.mul_apply] using off eq

theorem solution_eq_assemble {s : Finset (I×I)} {clue U : I→I→Op H} (h : Solves s clue U)
    {F : K→Op H} (part : Partition F) (binary : ∀ e∈s,∀ k,clue e.1 e.2*F k=0 ∨ clue e.1 e.2*F k=F k)
    {σ : K→Equiv.Perm I} (unique : ∀ k, F k≠0 → ∀ τ, Fits s clue (F k) τ → τ=σ k) :
    U=assemble F σ := by
  classical
  funext i j
  calc
    U i j = ∑ k, U i j * F k := by rw [←Finset.mul_sum,part.total,mul_one]
    _ = _ := by
      unfold assemble select
      apply sum_congr rfl
      intro k _
      by_cases t : σ k i=j <;> simpa [t] using acts_on_atom h (fun e he => binary e he k) (unique k) i j

theorem commuting_unique_iff {s : Finset (I×I)} {clue : I→I→Op H}
    (hc : ∀ e∈s,∀ f∈s,Commute (clue e.1 e.2) (clue f.1 f.2)) :
    (∃! U, Solves s clue U) ↔ (∃! W, CommSolves s clue W) := by
  classical
  constructor
  · rintro ⟨U,h,unique⟩
    obtain ⟨W,m,agree,comm⟩ := (weber_problem_3_6 s clue hc).mp ⟨U,h⟩
    refine ⟨W,⟨⟨m,agree⟩,comm⟩,fun X hx => ?_⟩
    exact (unique X hx.1).trans (unique W ⟨m,agree⟩).symm
  · rintro ⟨W,h,unique⟩
    let P (e : I×I) := clue e.1 e.2
    obtain ⟨K,inst,F,part,binary,_⟩ := atom_decomposition s P
      (fun e he => by change IsStarProjection (clue e.1 e.2); rw [←h.1.2 e he]; exact h.1.1.projection e.1 e.2) hc
    have hw k : ∃ σ, Fits s clue (F k) σ := by
      have b (e : I×I) (he : e∈s) : W e.1 e.2*F k=0 ∨ W e.1 e.2*F k=F k := by
        rw [h.1.2 e he]
        exact binary e he k
      obtain ⟨σ,hσ⟩:=local_choice W h.1.1 s (F k) b
      exact ⟨σ,fun e he => (h.1.2 e he) ▸ hσ e he⟩
    choose σ fits using hw
    have equals : assemble F σ=W := unique _ (assemble_fits part fits)
    have localUnique (k : K) (nz : F k≠0) (τ : Equiv.Perm I) (fit : Fits s clue (F k) τ) : τ=σ k := by
      let σ' := Function.update σ k τ
      have alt : ∀ a, Fits s clue (F a) (σ' a) := by
        intro a
        by_cases eq : a=k
        · subst a
          simpa [σ'] using fit
        · simpa [σ',eq] using fits a
      have same := (unique _ (assemble_fits part alt)).trans equals.symm
      ext i
      by_contra ne
      have op := congrArg (fun B : I→I→Op H => B i (τ i) * F k) same
      have notEq : σ k i≠τ i := fun eq => ne eq.symm
      exact nz (by simpa [assemble_mul part,σ',notEq] using op)
    refine ⟨W,h.1,fun U hu => ?_⟩
    exact (solution_eq_assemble hu part binary localUnique).trans equals

#print axioms commuting_unique_iff
end WeberCompletion
