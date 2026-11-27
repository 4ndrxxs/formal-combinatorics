import QuinticRestricted
import PermanentFive
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Lift the normalized equation to an extension field and keep the
dimension information for its endpoint kernel. -/

noncomputable section
open Matrix Module MvPolynomial
namespace QuinticPencil
variable {K E I n : Type*} [Field K] [Field E] [Fintype I] [Fintype n] [DecidableEq n]

theorem endpoint_zero_iff (b c : n → I → K) (x : I → K) :
    x ∈ (endpoints b c).ker ↔ (∀ i, value (b i) x = 0) ∧ (∀ i, value (c i) x = 0) := by
  constructor
  · intro hx
    have a : dotProductEquiv K n ((Matrix.of b).mulVecLin x) = 0 :=
      congrArg Prod.fst (show endpoints b c x = 0 from hx)
    exact ⟨fun i ↦ congrFun ((dotProductEquiv K n).map_eq_zero_iff.mp a) i,
      fun i ↦ congrFun (congrArg Prod.snd (show endpoints b c x = 0 from hx)) i⟩
  · rintro ⟨a,d⟩
    apply Prod.ext
    · change dotProductEquiv K n ((Matrix.of b).mulVecLin x) = 0
      exact (dotProductEquiv K n).map_eq_zero_iff.mpr (funext a)
    · exact funext d

omit [Fintype I] in
private def projection (L : Submodule K (I → K)) (S : Finset I) : L →ₗ[K] (S → K) :=
  { toFun := fun x i ↦ x.val i.val
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

theorem extended_endpoint_dimension [Algebra K E] (b c : n → I → K) (S : Finset I)
    (card : S.card = finrank K (endpoints b c).ker)
    (lift : ∀ z : I → K, ∃ x ∈ (endpoints b c).ker, ∀ i ∈ S, x i = z i) :
    finrank E (endpoints (fun a i ↦ algebraMap K E (b a i)) (fun a i ↦ algebraMap K E (c a i))).ker
      ≤ S.card := by
  classical
  let L := (endpoints b c).ker
  have surj : Function.Surjective (projection L S) := by
    intro z
    obtain ⟨x,hx,eq⟩ := lift (fun j ↦ if h : j ∈ S then z ⟨j,h⟩ else 0)
    exact ⟨⟨x,hx⟩,funext fun i ↦ by simpa [projection,i.property] using eq i.val i.property⟩
  have inj : Function.Injective (projection L S) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_pi,Fintype.card_coe]; exact card.symm)).mpr surj
  let b' (a : n) (i : I) := algebraMap K E (b a i)
  let c' (a : n) (i : I) := algebraMap K E (c a i)
  let U := (endpoints b' c').ker
  have desc (f : Dual K E) (row : I → K) (x : I → E) :
      value row (fun j ↦ f (x j)) = f (value (fun j ↦ algebraMap K E (row j)) x) := by
    simp only [value,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Algebra.smul_def,map_smul]
    rfl
  have zero (x : U) (eq : projection U S x = 0) : x = 0 := by
    have ⟨left,right⟩ := (endpoint_zero_iff b' c' x.val).mp x.property
    apply Subtype.ext
    funext i
    apply Module.eval_apply_injective K
    apply LinearMap.ext
    intro f
    change f (x.val i) = f 0
    let z : I → K := fun j ↦ f (x.val j)
    have hx : z ∈ L := (endpoint_zero_iff b c z).mpr
      ⟨fun a ↦ (desc f (b a) x.val).trans ((congrArg f (left a)).trans f.map_zero),
       fun a ↦ (desc f (c a) x.val).trans ((congrArg f (right a)).trans f.map_zero)⟩
    have pr : projection L S ⟨z,hx⟩ = projection L S 0 := by
      funext j
      have e := congrFun eq j
      change x.val j.val = 0 at e
      change f (x.val j.val) = 0
      simp [e]
    have ends : z i = 0 := congrFun (congrArg Subtype.val (inj pr)) i
    simpa [z] using ends
  have injE : Function.Injective (projection U S) := (projection U S).ker_eq_bot.mp
    (LinearMap.ker_eq_bot'.mpr zero)
  have bounds := (projection U S).finrank_le_finrank_of_injective injE
  simpa only [Module.finrank_pi,Fintype.card_coe] using bounds

omit [DecidableEq n] in
theorem mapped_form (f : K →+* E) (b : I → K) :
    MvPolynomial.map f (linearForm b) = linearForm (fun i ↦ f (b i)) := by
  simp [linearForm]

theorem mapped_regular_det (f : K →+* E) (b c : n → I → K) (D : n → n → I → K) :
    MvPolynomial.map f (regularDet b c D) =
      regularDet (fun j i ↦ f (b j i)) (fun j i ↦ f (c j i)) (fun j k i ↦ f (D j k i)) := by
  unfold regularDet
  rw [RingHom.map_det]
  congr 1
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks,mapped_form,Matrix.one_apply,apply_ite]

end QuinticPencil
namespace PermanentFive
open QuinticPencil
theorem mapped_permanent {K E : Type*} [Field K] [Field E] (f : K →+* E) :
    MvPolynomial.map f (per K Idx) = per E Idx := by
  simp [per,Matrix.permanent,PermanentCuts.generic]

#print axioms QuinticPencil.extended_endpoint_dimension
#print axioms QuinticPencil.mapped_regular_det
#print axioms mapped_permanent
end PermanentFive
