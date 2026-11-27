import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Rank changes in the successive images of a nilpotent linear map. -/

noncomputable section
open LinearMap Module Matrix
namespace NilpotentProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Each successive rank drop is at least the rank of the last possibly
nonzero power, whose image is in every earlier image and in the kernel. -/
theorem step (M : E →ₗ[K] E) (t i : ℕ) (hi : i ≤ t) (zero : M^(t+1) = 0) :
    finrank K ((M^(i+1)).range) + finrank K ((M^t).range) ≤ finrank K ((M^i).range) := by
  let R := (M^i).range
  let C := (M^t).range
  let f := M.comp R.subtype
  have eq : f.range = (M^(i+1)).range := by
    rw [pow_succ']
    change f.range = (M.comp (M^i)).range
    simp only [f,LinearMap.range_comp,Submodule.range_subtype,R]
  have sub : C ≤ R := by
    have add : t = i+(t-i) := by omega
    change (M^t).range ≤ (M^i).range
    conv_lhs => rw [add,pow_add]
    exact LinearMap.range_comp_le_range _ _
  have kill (x : C) : M x.val = 0 := by
    obtain ⟨v,hv⟩ := x.property
    change (M^t) v = x.val at hv
    rw [←hv]
    change (M*(M^t)) v = 0
    rw [← pow_succ',zero]
    rfl
  let inc := (Submodule.inclusion sub).codRestrict f.ker (fun x ↦ kill x)
  have injective : Function.Injective inc :=
    fun x y h ↦ Subtype.ext (congrArg (fun z : f.ker ↦ z.val.val) h)
  have last := LinearMap.finrank_le_finrank_of_injective injective
  have dim := f.finrank_range_add_finrank_ker
  rw [eq] at dim
  change finrank K C ≤ finrank K f.ker at last
  change _ + finrank K C ≤ finrank K R
  omega

theorem four_step_profile (M : E →ₗ[K] E) (dim : finrank K E = 20)
    (zero : M^4 = 0) (large : 5 ≤ finrank K (M^3).range) :
    finrank K M.range = 15 ∧ finrank K (M^2).range = 10 ∧ finrank K (M^3).range = 5 := by
  have a := step M 3 0 (by decide) zero
  have b := step M 3 1 (by decide) zero
  have c := step M 3 2 (by decide) zero
  have first : finrank K (M^0).range = 20 := by
    rw [pow_zero]
    change finrank K (LinearMap.id (R:=K) (M:=E)).range = 20
    rw [LinearMap.range_id,finrank_top,dim]
  change finrank K (M^1).range + finrank K (M^3).range ≤ finrank K (M^0).range at a
  change finrank K (M^2).range + finrank K (M^3).range ≤ finrank K (M^1).range at b
  change finrank K (M^3).range + finrank K (M^3).range ≤ finrank K (M^2).range at c
  rw [first,pow_one] at a
  rw [pow_one] at b
  omega

#print axioms step
#print axioms four_step_profile
end NilpotentProfile
