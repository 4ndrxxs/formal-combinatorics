import PermanentRectangleIndex
import PermanentRectangleCongruence
import PermanentIndexFourBlock

/-! A pivot support covered by a three-by-four rectangle is incompatible with a
pencil of size at most twenty-one over the two-parameter field. -/

noncomputable section
open Matrix Module QuinticPencil
namespace PermanentFive.Rectangle
variable {K n : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]

theorem rectangle_index_le_four (J : Submodule (Ext K) (Fin 12 → Ext K))
    (iso : J ≤ ((hessian (per (Ext K) Idx) (value (paramS K) (paramT K) ∘ centreCode)).submatrix
      directions directions).toBilin'.orthogonal J) : finrank (Ext K) J ≤ 4 := by
  let s := paramS K
  let t := paramT K
  let P := change s t
  have surj : Function.Surjective P.toLin' := by
    change Function.Surjective P.mulVec
    apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
    refine ⟨(12 : Ext K)⁻¹ • inverseTwelve s t,?_⟩
    rw [Matrix.mul_smul,show P * inverseTwelve s t = (12 : Ext K) • 1 from change_right_inverse s t,
      smul_smul,inv_mul_cancel₀ (by norm_num),one_smul]
  let V := J.comap P.toLin'
  have all : J ≤ P.toLin'.range := by rw [LinearMap.range_eq_top.mpr surj]; exact le_top
  have dim := Submodule.finrank_map_le P.toLin' V
  rw [show V.map P.toLin' = J from Submodule.map_comap_eq_self all] at dim
  apply dim.trans (split_index_le_four V ?_)
  rw [hessian_original] at iso
  have law : (split s t).toBilin' = (original s t).toBilin'.comp P.toLin' P.toLin' := by
    rw [Matrix.toBilin'_comp,gram_congruence]
  change V ≤ (split s t).toBilin'.orthogonal V
  rw [law]
  exact fun x hx z hz ↦ iso hx (P.toLin' z) hz

def board : Finset Cell := Finset.univ.image directions

theorem rectangle_block (K : Type*) [Field K] [CharZero K] : HasIndexFourBlock (Ext K) board := by
  refine ⟨directions,value (paramS K) (paramT K) ∘ centreCode,?_,rectangle_index_le_four⟩
  intro j hj
  obtain ⟨i,_,eq⟩ := Finset.mem_image.mp hj
  exact ⟨i,eq⟩

theorem normalized_rectangle_bound (b c : n → Cell → Ext K) (D : n → n → Cell → Ext K)
    (rep : per (Ext K) Idx = regularDet b c D) (S : Finset Cell)
    (card : S.card = finrank (Ext K) (endpoints b c).ker)
    (lift : ∀ z : Cell → Ext K, ∃ x ∈ (endpoints b c).ker, ∀ i ∈ S, x i = z i)
    (paths : PermanentDegeneration.HasCoordinatePaths (endpoints b c).ker weight S)
    (e : Equiv.Perm Cell) (sym : MvPolynomial.rename e (per (Ext K) Idx) = per (Ext K) Idx)
    (cover : ∀ j ∈ S, ∃ i, e (directions i) = j) : 21 ≤ Fintype.card n := by
  by_contra! small
  apply normalized_excludes_index_four b c D rep (by omega) S card lift paths
  apply (rectangle_block K).relabel e sym
  intro j hj
  obtain ⟨i,eq⟩ := cover j hj
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by simp [← eq]⟩

#print axioms rectangle_index_le_four
#print axioms normalized_rectangle_bound
end PermanentFive.Rectangle
