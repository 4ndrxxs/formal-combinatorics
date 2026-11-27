import PermanentFive

/-! Relabelings of rows and columns, and transposition, preserve the
permanent and transport its derivative witnesses. -/

noncomputable section
open MvPolynomial Matrix Equiv
namespace PermanentFive
open QuinticPencil
variable {K I : Type*} [Fintype I] [DecidableEq I]

section
variable [CommRing K]

theorem row_column_rename (r c : Perm I) :
    rename (r.prodCongr c) (per K I) = per K I := by
  let M := PermanentCuts.generic K I
  have eq : rename (r.prodCongr c) (per K I) = ((M.submatrix id c).submatrix r id).permanent := by
    simp [per,Matrix.permanent,PermanentCuts.generic,M,Matrix.submatrix,Equiv.prodCongr]
  rw [eq,Matrix.permanent_permute_cols,Matrix.permanent_permute_rows]
  rfl

theorem transpose_rename : rename (Equiv.prodComm I I) (per K I) = per K I := by
  let M := PermanentCuts.generic K I
  have eq : rename (Equiv.prodComm I I) (per K I) = M.transpose.permanent := by
    simp [per,Matrix.permanent,PermanentCuts.generic,M]
  rw [eq,Matrix.permanent_transpose]
  rfl

theorem rename_comp {e g : Perm (I × I)} (he : rename e (per K I) = per K I)
    (hg : rename g (per K I) = per K I) : rename (e.trans g) (per K I) = per K I := by
  change rename (g ∘ e) (per K I) = _
  rw [← MvPolynomial.rename_rename,he,hg]

end

variable [Field K]

/-- Transport a coordinate singular-plane condition back along a symmetry. -/
theorem transport {J : Type*} [Fintype J] [DecidableEq J] {p : MvPolynomial J K} (e : Perm J)
    (sym : rename e p = p) (z : J → K) :
    (∀ i, MvPolynomial.eval (z ∘ e.symm) (pderiv (e i) p) = MvPolynomial.eval z (pderiv i p)) ∧
      (hessian p (z ∘ e.symm)).rank = (hessian p z).rank := by
  have ev (a : MvPolynomial J K) : MvPolynomial.eval (z ∘ e.symm) (rename e a) =
      MvPolynomial.eval z a := by
    rw [MvPolynomial.eval_rename]
    simp [Function.comp_assoc]
  constructor
  · intro i
    have h := MvPolynomial.pderiv_rename e.injective i p
    rw [sym] at h
    rw [h,ev]
  · have he : (hessian p (z ∘ e.symm)).submatrix e e = hessian p z := by
      ext i j
      have h := MvPolynomial.pderiv_rename e.injective j p
      rw [sym] at h
      simp only [hessian, Matrix.submatrix_apply, Matrix.of_apply,h,
        MvPolynomial.pderiv_rename e.injective,ev]
    rw [← Matrix.rank_submatrix (hessian p (z ∘ e.symm)) e e,he]

/-- A permutation carries a prescribed finite set into any set of at least
its cardinality. -/
theorem move_into {J : Type*} [Fintype J] [DecidableEq J] (A B : Finset J) (le : A.card ≤ B.card) :
    ∃ q : Perm J, ∀ i ∈ A, q i ∈ B := by
  classical
  obtain ⟨T,sub,hcard⟩ := Finset.exists_subset_card_eq le
  let g : (↥A) ≃ (↥T) := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let h : {i : J // i ∉ A} ≃ {i : J // i ∉ T} := Fintype.equivOfCardEq (by
    simp [Fintype.card_subtype_compl,hcard])
  let q := (Equiv.sumCompl (· ∈ A)).symm.trans ((g.sumCongr h).trans (Equiv.sumCompl (· ∈ T)))
  refine ⟨q,fun i hi ↦ ?_⟩
  have eq : q i = (g ⟨i,hi⟩).val := by simp [q,Equiv.sumCompl,hi]
  rw [eq]
  exact sub (g ⟨i,hi⟩).property

#print axioms transport
#print axioms move_into
end PermanentFive
