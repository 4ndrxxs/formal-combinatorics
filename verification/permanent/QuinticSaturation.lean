import Mathlib.LinearAlgebra.QuadraticForm.Dual
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A saturated space of endpoints cancels the even second difference of
a homogeneous quintic in each direction of the common kernel. -/

namespace QuinticSaturation
open Module
variable {K V T : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [AddCommGroup T] [Module K T]

/-- A polarization of the cubic and quartic transfer identities. All
multiplications by endomorphisms retain their displayed order. -/
theorem even_difference_of_lift (B : V →ₗ[K] Dual K T) (C : V →ₗ[K] T) (D : V →ₗ[K] End K T)
    (cubic : ∀ x, B x (D x (C x)) = 0)
    (quartic : ∀ x, B x (D x (D x (C x))) = 0)
    (f : V → K) (quintic : ∀ x, f x = B x (D x (D x (D x (C x)))))
    (z : V) (bz : B z = 0) (cz : C z = 0)
    (y : V) (lift : ∃ w, (∀ v, B w v = B y (D z v)) ∧ C w = D z (C y)) :
    f (y+z) + f (y-z) = 2 * f y := by
  have first (x : V) : B x (D z (D x (C x))) + B x (D x (D z (C x))) = 0 := by
    have plus := quartic (x+z)
    have minus := quartic (x-z)
    simp only [map_add,map_sub,bz,cz,add_zero,sub_zero,LinearMap.add_apply,
      LinearMap.sub_apply] at plus minus
    have h : 2 * (B x (D z (D x (C x))) + B x (D x (D z (C x)))) = 0 := by
      linear_combination plus - minus
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  obtain ⟨w,bw,cw⟩ := lift
  have fp := first (y+w)
  have fm := first (y-w)
  have fw := first w
  have cp := cubic (y+w)
  have cm := cubic (y-w)
  have cy := cubic y
  simp only [map_add,map_sub,LinearMap.add_apply,LinearMap.sub_apply,bw,cw] at fp fm fw cp cm cy
  simp only [quintic,map_add,map_sub,bz,cz,add_zero,sub_zero,LinearMap.add_apply,
    LinearMap.sub_apply]
  linear_combination fp - fm - 2 * fw - cp - cm + 2 * cy

/-- Universal lifting gives cancellation at every centre. -/
theorem even_difference (B : V →ₗ[K] Dual K T) (C : V →ₗ[K] T) (D : V →ₗ[K] End K T)
    (cubic : ∀ x, B x (D x (C x)) = 0)
    (quartic : ∀ x, B x (D x (D x (C x))) = 0)
    (f : V → K) (quintic : ∀ x, f x = B x (D x (D x (D x (C x)))))
    (z : V) (bz : B z = 0) (cz : C z = 0)
    (lift : ∀ y, ∃ w, (∀ v, B w v = B y (D z v)) ∧ C w = D z (C y)) (y : V) :
    f (y+z) + f (y-z) = 2 * f y := by
  exact even_difference_of_lift B C D cubic quartic f quintic z bz cz y (lift y)

omit [CharZero K] in
/-- In the half-dimensional case a transferred pair of endpoints lifts
back to an input vector. The quadratic and cubic identities give both
orthogonality relations by polarization. -/
theorem lift_of_half_dimension [FiniteDimensional K T]
    (B : V →ₗ[K] Dual K T) (C : V →ₗ[K] T) (D : V →ₗ[K] End K T)
    (quadratic : ∀ x, B x (C x) = 0) (cubic : ∀ x, B x (D x (C x)) = 0)
    (full : finrank K (B.prod C).range = finrank K T)
    (z : V) (bz : B z = 0) (cz : C z = 0) (y : V) :
    ∃ w, (∀ v, B w v = B y (D z v)) ∧ C w = D z (C y) := by
  let G := LinearMap.dualProd K T
  let U := (B.prod C).range
  have nd : G.Nondegenerate :=
    (LinearMap.isSymm_dualProd K T).isRefl.nondegenerate_iff_separatingLeft.mpr
      ((LinearMap.separatingLeft_dualProd K T).mpr (Module.eval_apply_injective K))
  have one (x : V) : B x (D z (C x)) = 0 := by
    have h := cubic (x+z)
    simp only [map_add,bz,cz,add_zero,LinearMap.add_apply] at h
    linear_combination h - cubic x
  have iso : U ≤ G.orthogonal U := by
    rintro _ ⟨v,rfl⟩ _ ⟨w,rfl⟩
    change B v (C w) + B w (C v) = 0
    have h := quadratic (v+w)
    simp only [map_add,LinearMap.add_apply] at h
    linear_combination h - quadratic v - quadratic w
  have dim := G.finrank_add_finrank_orthogonal' U
  rw [nd.ker_eq_bot,inf_bot_eq,finrank_bot,add_zero,Module.finrank_prod,
    Subspace.dual_finrank_eq] at dim
  have hU : finrank K U = finrank K T := full
  have equal : U = G.orthogonal U := Submodule.eq_of_le_of_finrank_le iso (by omega)
  let pair : Dual K T × T := ((B y).comp (D z),D z (C y))
  have mem : pair ∈ G.orthogonal U := by
    rintro _ ⟨v,rfl⟩
    change B y (D z (C v)) + B v (D z (C y)) = 0
    have h := one (v+y)
    simp only [map_add,LinearMap.add_apply] at h
    linear_combination h - one v - one y
  rw [← equal] at mem
  obtain ⟨w,eq⟩ := mem
  exact ⟨w,fun v ↦ DFunLike.congr_fun (congrArg Prod.fst eq) v,congrArg Prod.snd eq⟩

#print axioms lift_of_half_dimension
#print axioms even_difference
end QuinticSaturation
