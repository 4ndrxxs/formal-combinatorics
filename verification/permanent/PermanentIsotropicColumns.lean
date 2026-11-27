import PermanentFractionFreeRank

/-! Any totally isotropic coordinate family larger than half the rank
has a nonzero linear combination in the radical. -/
noncomputable section
open Matrix Module
namespace PermanentOrderFour
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]

theorem isotropic_columns_kernel (H : Matrix I I K) (symm : H.IsSymm) (f : J → I)
    (zero : ∀ i j, H (f i) (f j)=0) (small : H.rank<2*Fintype.card J) :
    ∃ v : J → K, v≠0 ∧ (H.submatrix id f) *ᵥ v=0 := by
  classical
  let B := H.submatrix id f
  let E := H.mulVecLin.range
  let proj : E →ₗ[K] (J → K) := (LinearMap.funLeft K K f).comp E.subtype
  have contained : B.mulVecLin.range≤E := by
    change B.mulVecLin.range≤H.mulVecLin.range
    rw [Matrix.range_mulVecLin,Matrix.range_mulVecLin]
    apply Submodule.span_mono
    rintro _ ⟨j,rfl⟩
    exact ⟨f j,rfl⟩
  let liftB : (J → K) →ₗ[K] E := B.mulVecLin.codRestrict E
    (fun v ↦ contained ⟨v,rfl⟩)
  have toKer (v : J → K) : liftB v ∈ proj.ker := by
    apply funext
    intro j
    change (∑ t : J, H (f j) (f t)*v t)=0
    simp [zero]
  let liftKer := liftB.codRestrict proj.ker toKer
  by_contra! no
  have inj : Function.Injective B.mulVecLin := LinearMap.ker_eq_bot.mp
    (LinearMap.ker_eq_bot'.mpr (fun v hv ↦ by by_contra hn; exact no v hn hv))
  have injKer : Function.Injective liftKer := fun v w eq ↦
    inj (congrArg (fun t : proj.ker ↦ (t.val : I → K)) eq)
  have lower := LinearMap.finrank_le_finrank_of_injective injKer
  rw [Module.finrank_fintype_fun_eq_card] at lower
  have rows : (H.submatrix f id).mulVecLin=proj.comp H.mulVecLin.rangeRestrict := by
    ext1 v
    rfl
  have rangeEq := LinearMap.range_comp_of_range_eq_top proj H.mulVecLin.range_rangeRestrict
  have rh : finrank K proj.range=B.rank := by
    rw [←rangeEq,←rows]
    change (H.submatrix f id).rank=B.rank
    rw [←Matrix.rank_transpose B]
    have eq : B.transpose=H.submatrix f id := by
      ext i j
      exact symm.apply _ _
    rw [eq]
  have full : B.rank=Fintype.card J := by
    change finrank K B.mulVecLin.range=_
    rw [LinearMap.finrank_range_of_inj inj,Module.finrank_fintype_fun_eq_card]
  have dimensions := proj.finrank_range_add_finrank_ker
  rw [rh,full] at dimensions
  change _+_=H.rank at dimensions
  omega

#print axioms isotropic_columns_kernel
end PermanentOrderFour
