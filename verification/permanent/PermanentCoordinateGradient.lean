import PermanentSymmetry
import PermanentWitnesses

/-! Every coordinate covector occurs as the gradient of the generic
permanent. The construction and its proof work at every order and over
every field. -/

noncomputable section
open Matrix Module Equiv Finset MvPolynomial
namespace PermanentFive
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

def missingMatching (h : I) (u : I × I) : K := if u.1 = u.2 ∧ u.2 ≠ h then 1 else 0

private theorem matching_gradient (h : I) (e : I × I) :
    gradAt (missingMatching (K:=K) h) e = if e=(h,h) then 1 else 0 := by
  obtain ⟨a,j⟩ := e
  by_cases jh : j=h
  · subst j
    by_cases ah : a=h
    · subst a
      rw [ite_eq_left rfl]
      unfold gradAt
      rw [Finset.sum_eq_single (Equiv.refl I)]
      · simp only [Equiv.refl_apply,ite_true]
        apply Finset.prod_eq_one
        intro i hi
        simp [missingMatching,(Finset.mem_erase.mp hi).1]
      · intro p _ ne
        by_cases ph : p h=h
        · obtain ⟨i,ni⟩ : ∃ i, p i ≠ i := by
            by_contra! fix
            exact ne (Equiv.ext (fun i ↦ fix i))
          have ih : i ≠ h := fun eq ↦ ni (eq ▸ ph)
          rw [ite_eq_left ph]
          exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨ih,Finset.mem_univ _⟩)
            (by simp [missingMatching,ni])
        · simp [ph]
      · simp
    · rw [ite_eq_right (fun z ↦ ah (congrArg Prod.fst z))]
      unfold gradAt
      apply Finset.sum_eq_zero
      intro p _
      by_cases ph : p h = a
      · have na : p a ≠ a := fun bad ↦ ah (p.injective (bad.trans ph.symm))
        rw [ite_eq_left ph]
        exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨ah,Finset.mem_univ _⟩)
          (by simp [missingMatching,na])
      · simp [ph]
  · rw [ite_eq_right (fun z ↦ jh (congrArg Prod.snd z))]
    unfold gradAt
    apply Finset.sum_eq_zero
    intro p _
    by_cases hit : p j=a
    · rw [ite_eq_left hit]
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm jh,Finset.mem_univ _⟩)
        (by simp [missingMatching])
    · simp [hit]

theorem permanent_coordinate_gradient (u : I × I) :
    ∃ y : I × I → K, ∀ v, MvPolynomial.eval y (pderiv v (per K I)) = if v=u then 1 else 0 := by
  let c := Equiv.swap u.1 u.2
  let e := (Equiv.refl I).prodCongr c
  let w := missingMatching (K:=K) u.1
  have sends : e (u.1,u.1) = u := by ext <;> simp [e,c]
  refine ⟨w ∘ e.symm,fun v ↦ ?_⟩
  have tr := (transport e (row_column_rename (Equiv.refl I) c) w).1 (e.symm v)
  rw [Equiv.apply_symm_apply] at tr
  rw [tr,grad_formula,matching_gradient]
  have iff : e.symm v = (u.1,u.1) ↔ v = u := by rw [e.symm_apply_eq,sends]
  simp only [iff]

#print axioms permanent_coordinate_gradient
end PermanentFive
