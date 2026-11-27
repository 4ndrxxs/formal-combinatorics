import PencilChainFrame
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! A maximal last power gives a full frame of equal-length chains. -/

noncomputable section
open LinearMap Module Matrix Finset
namespace PencilChain
variable {K n k : Type*} [Field K] [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

omit [DecidableEq k] in
private theorem frame_mulVec (s : ℕ) (A : Matrix n n K) (V : Matrix n k K) (x : Fin s × k → K) :
    frame s A V *ᵥ x = ∑ j : Fin s, (A^j.val*V) *ᵥ (fun i ↦ x (j,i)) := by
  funext i
  simp [frame,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Finset.sum_apply]

theorem full_frame_of_last {s : ℕ} (length : s=2 ∨ s=4) (A : Matrix (Fin s × k) (Fin s × k) K)
    (nil : A^s = 0) (V : Matrix (Fin s × k) k K)
    (last : Function.Injective (A^(s-1)*V).mulVec) : (frame s A V).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  change Function.Injective (frame s A V).mulVecLin
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change (frame s A V) *ᵥ x = 0 at hx
  have level (r : ℕ) :
      (∑ j : Fin s, (A^(r+j.val)*V) *ᵥ (fun i ↦ x (j,i))) = 0 := by
    have ev := congrArg (fun w ↦ (A^r).mulVecLin w) hx
    rw [frame_mulVec,map_sum,map_zero] at ev
    simpa only [Matrix.mulVecLin_apply,Matrix.mulVec_mulVec,←Matrix.mul_assoc,←pow_add] using ev
  have van (r : ℕ) (h : s≤r) : A^r = 0 := pow_eq_zero_of_le h nil
  have kill (v : k → K) (h : (A^(s-1)*V)*ᵥ v = 0) : v=0 := last (h.trans (Matrix.mulVec_zero _).symm)
  rcases length with rfl | rfl
  · have z0 : (fun a ↦ x (0,a)) = 0 := kill _ (by
        simpa [Fin.sum_univ_succ,van] using level 1)
    have z1 : (fun a ↦ x (1,a)) = 0 := kill _ (by
        simpa [Fin.sum_univ_succ,van,z0] using level 0)
    funext v
    obtain ⟨j,i⟩ := v
    fin_cases j
    · exact congrFun z0 i
    · exact congrFun z1 i
  · have z0 : (fun a ↦ x (0,a)) = 0 := kill _ (by
        simpa [Fin.sum_univ_succ,van] using level 3)
    have z1 : (fun a ↦ x (1,a)) = 0 := kill _ (by
        simpa [Fin.sum_univ_succ,van,z0] using level 2)
    have z2 : (fun a ↦ x (2,a)) = 0 := kill _ (by
        simpa [Fin.sum_univ_succ,van,z0,z1] using level 1)
    have z3 : (fun a ↦ x (3,a)) = 0 := kill _ (by
        simpa [Fin.sum_univ_succ,van,z0,z1,z2] using level 0)
    funext v
    obtain ⟨j,i⟩ := v
    fin_cases j
    · exact congrFun z0 i
    · exact congrFun z1 i
    · exact congrFun z2 i
    · exact congrFun z3 i

theorem exists_full_frame {s : ℕ} (length : s=2 ∨ s=4) (A : Matrix (Fin s × k) (Fin s × k) K)
    (nil : A^s=0) (full : (A^(s-1)).rank = Fintype.card k) :
    ∃ V : Matrix (Fin s × k) k K, (frame s A V).det ≠ 0 := by
  let f := (A^(s-1)).mulVecLin
  have dimension : finrank K (k → K) = finrank K f.range := (Module.finrank_pi K).trans full.symm
  let e : (k → K) ≃ₗ[K] f.range := LinearEquiv.ofFinrankEq _ _ dimension
  obtain ⟨g,right⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  let v := g.comp e.toLinearMap
  let V := v.toMatrix'
  refine ⟨V,full_frame_of_last length A nil V ?_⟩
  have ident (x : k → K) : (A^(s-1)*V) *ᵥ x = (e x).val := by
    rw [←Matrix.mulVec_mulVec]
    have vx : V *ᵥ x = v x := LinearMap.congr_fun (Matrix.toLin'_toMatrix' v) x
    rw [vx]
    exact congrArg Subtype.val (LinearMap.congr_fun right (e x))
  intro x y h
  exact e.injective (Subtype.ext ((ident x).symm.trans (h.trans (ident y))))

#print axioms full_frame_of_last
#print axioms exists_full_frame
end PencilChain
