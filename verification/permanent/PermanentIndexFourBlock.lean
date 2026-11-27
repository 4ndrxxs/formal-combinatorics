import PermanentCoordinateIsotropy
import PermanentBlockCover

/-! A twelve-direction Hessian form whose totally isotropic spaces have dimension
at most four gives an obstruction on every subboard covered by its frame. -/

noncomputable section
open Matrix Module Equiv QuinticPencil
namespace PermanentFive
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

def HasIndexFourBlock (K : Type*) [Field K] (S : Finset Cell) : Prop :=
  ∃ (v : Fin 12 → Cell) (z : Cell → K), (∀ j ∈ S, ∃ i, v i = j) ∧
    ∀ J : Submodule K (Fin 12 → K),
      J ≤ ((hessian (per K Idx) z).submatrix v v).toBilin'.orthogonal J → finrank K J ≤ 4

theorem HasIndexFourBlock.mono {S T : Finset Cell} (h : HasIndexFourBlock K T)
    (sub : S ⊆ T) : HasIndexFourBlock K S := by
  obtain ⟨v,z,inside,index⟩ := h
  exact ⟨v,z,fun j hj ↦ inside j (sub hj),index⟩

theorem HasIndexFourBlock.relabel {S T : Finset Cell} (h : HasIndexFourBlock K T)
    (e : Perm Cell) (sym : MvPolynomial.rename e (per K Idx) = per K Idx)
    (sub : ∀ j ∈ S, e.symm j ∈ T) : HasIndexFourBlock K S := by
  obtain ⟨v,z,inside,index⟩ := h
  let p := per K Idx
  have ev (a : MvPolynomial Cell K) :
      MvPolynomial.eval (z ∘ e.symm) (MvPolynomial.rename e a) = MvPolynomial.eval z a := by
    rw [MvPolynomial.eval_rename]
    simp [Function.comp_assoc]
  have he : (hessian p (z ∘ e.symm)).submatrix e e = hessian p z := by
    ext1 i j
    have h := MvPolynomial.pderiv_rename e.injective j p
    rw [show MvPolynomial.rename e p = p from sym] at h
    simp only [hessian,Matrix.submatrix_apply,Matrix.of_apply,h,MvPolynomial.pderiv_rename e.injective,ev]
  refine ⟨e ∘ v,z ∘ e.symm,?_,?_⟩
  · intro j hj
    obtain ⟨i,eq⟩ := inside _ (sub j hj)
    exact ⟨i,by simp [eq]⟩
  · intro J iso
    apply index J
    change J ≤ ((hessian p (z ∘ e.symm)).submatrix (e ∘ v) (e ∘ v)).toBilin'.orthogonal J at iso
    rwa [← Matrix.submatrix_submatrix,he] at iso

theorem normalized_excludes_index_four_weighted (weights : GridWeights) [CharZero K] (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (small : Fintype.card n ≤ 20) (S : Finset Cell)
    (card : S.card = finrank K (endpoints b c).ker)
    (lift : ∀ z : Cell → K, ∃ x ∈ (endpoints b c).ker, ∀ i ∈ S, x i = z i)
    (paths : PermanentDegeneration.HasCoordinatePaths (endpoints b c).ker weights.cell S) :
    ¬ HasIndexFourBlock K S := by
  rintro ⟨v,z,cover,idx⟩
  obtain ⟨J,dim,iso⟩ := coordinate_frame_isotropy_weighted weights b c D rep S card lift paths v cover z
  have bound := idx J iso
  omega

theorem normalized_excludes_index_four [CharZero K] (b c : n → Cell → K) (D : n → n → Cell → K)
    (rep : per K Idx = regularDet b c D) (small : Fintype.card n ≤ 20) (S : Finset Cell)
    (card : S.card = finrank K (endpoints b c).ker)
    (lift : ∀ z : Cell → K, ∃ x ∈ (endpoints b c).ker, ∀ i ∈ S, x i = z i)
    (paths : PermanentDegeneration.HasCoordinatePaths (endpoints b c).ker weight S) :
    ¬ HasIndexFourBlock K S := by
  exact normalized_excludes_index_four_weighted standardGridWeights b c D rep small S card lift paths

#print axioms normalized_excludes_index_four
end PermanentFive
