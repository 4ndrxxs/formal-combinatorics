import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The anisotropic remainder cannot enlarge a totally isotropic subspace of a hyperbolic sum. -/

noncomputable section
open Module LinearMap
namespace RationalSpecialization
variable {K V W Z : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W] [AddCommGroup Z] [Module K Z]

theorem hyperbolic_plane_bound (X Y : V →ₗ[K] W) (T : V →ₗ[K] Z)
    (joint : ∀ u, X u = 0 → Y u = 0 → T u = 0 → u = 0)
    (B : LinearMap.BilinForm K W) (perfect : B.Nondegenerate)
    (A : LinearMap.BilinForm K Z) (anis : ∀ z, A z z = 0 → z = 0)
    (J : Submodule K V)
    (pair : ∀ u ∈ J, ∀ v ∈ J, B (Y u) (X v) + B (Y v) (X u) + A (T u) (T v) = 0) :
    finrank K J ≤ finrank K W := by
  let Xj := X.comp J.subtype
  let Yk := Y.comp (J.subtype.comp Xj.ker.subtype)
  have xzero (u : Xj.ker) : X u.val.val = 0 := u.property
  have tzero (u : Xj.ker) : T u.val.val = 0 := by
    apply anis
    simpa [xzero u] using pair u.val.val u.val.property u.val.val u.val.property
  have injY : Function.Injective Yk := by
    intro u v eq
    apply sub_eq_zero.mp
    have hz : Yk (u-v) = 0 := by rw [map_sub,eq,sub_self]
    apply Subtype.ext
    apply Subtype.ext
    exact joint _ (xzero (u-v)) hz (tzero (u-v))
  have dimY : finrank K Xj.ker = finrank K Yk.range := (LinearEquiv.ofInjective Yk injY).finrank_eq
  have incl : Xj.range ≤ B.orthogonal Yk.range := by
    rintro _ ⟨v,rfl⟩ _ ⟨u,rfl⟩
    simpa [xzero u,tzero u,Xj,Yk] using pair u.val.val u.val.property v.val v.property
  have bound := Submodule.finrank_mono incl
  rw [LinearMap.BilinForm.finrank_orthogonal perfect,← dimY] at bound
  have avail := Yk.range.finrank_le
  rw [← dimY] at avail
  have sumdim := Xj.finrank_range_add_finrank_ker
  omega

#print axioms hyperbolic_plane_bound
end RationalSpecialization
