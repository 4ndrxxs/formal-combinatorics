import PermanentFourEntries
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! Euler's identity for the gradient and its characteristic-three
consequence for the order-four Hessian. -/
noncomputable section
open Matrix Module Finset MvPolynomial PermanentFive QuinticPencil PermanentBorder
namespace PermanentOrderFour
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem euler_hessian {d : ℕ} {p : MvPolynomial I K} (hom : p.IsHomogeneous d) (z : I → K) :
    (hessian p z) *ᵥ z = fun i ↦ ((d-1:ℕ):K)*eval z (pderiv i p) := by
  funext i
  have h := congrArg (eval z) (hom.pderiv (i:=i)).sum_X_mul_pderiv
  change ∑ j, eval z (pderiv i (pderiv j p))*z j=_
  calc _=∑ j, z j*eval z (pderiv j (pderiv i p)) := by
         apply Finset.sum_congr rfl
         intro j _
         rw [pderiv_comm,mul_comm]
       _=_ := by simpa [nsmul_eq_mul] using h

theorem nonzero_point (z : Cell4 → K) (smooth : cofactor z≠0) : z≠0 := by
  rintro rfl
  apply smooth
  ext i j
  change gradAt (0:Cell4 → K) (i,j)=0
  rw [grad_eq]
  simp [grad,three]

theorem characteristic_three_cap (three_zero : (3:K)=0) (z : Cell4 → K) (smooth : cofactor z≠0) :
    (hessian (per K F) z).rank≤15 := by
  let A := hessian (per K F) z
  have hom : (per K F).IsHomogeneous 4 := per_homogeneous K F
  have zero := euler_hessian hom z
  change A *ᵥ z=(fun i ↦ (3:K)*eval z (pderiv i (per K F))) at zero
  simp only [three_zero,zero_mul] at zero
  by_contra! big
  have top := Matrix.rank_le_card_width A
  have eq : A.rank=Fintype.card Cell4 := by change A.rank=16; change A.rank≤16 at top; change 15<A.rank at big; omega
  have surj : Function.Surjective A.mulVecLin := Matrix.mulVec_surjective_iff_rank_eq_card.mpr eq
  have inj : Function.Injective A.mulVecLin := (LinearMap.injective_iff_surjective).mpr surj
  apply nonzero_point z smooth
  apply inj
  exact zero.trans (map_zero A.mulVecLin).symm

#print axioms euler_hessian
#print axioms characteristic_three_cap
end PermanentOrderFour
