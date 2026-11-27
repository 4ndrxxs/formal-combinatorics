module
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Tactic

/-! An integer phase system has a global solution on the circle exactly when
its prescribed row phases kill all integral relations among the rows. -/
@[expose] public section
noncomputable section
namespace FractionalTorus
open LinearMap

abbrev Torus := Real.Angle
local instance : DivisibleBy Torus ℤ := by
  letI : Fact (0<2*Real.pi) := ⟨by positivity⟩
  exact inferInstanceAs (DivisibleBy (AddCircle (2*Real.pi)) ℤ)

theorem character_extension {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (A : X →ₗ[ℤ] Y) (t : X →ₗ[ℤ] Torus) :
    (∃ T : Y →ₗ[ℤ] Torus, T.comp A=t) ↔ ker A≤ker t := by
  constructor
  · rintro ⟨T,rfl⟩ x hx
    change T (A x)=0
    rw [show A x=0 from hx,map_zero]
  · intro h
    let f : range A →ₗ[ℤ] Torus :=
      ((ker A).liftQ t h).comp A.quotKerEquivRange.symm.toLinearMap
    have ex := (Module.Baer.of_divisible Torus).extension_property
      (range A).subtype Subtype.val_injective f
    obtain ⟨T,hT⟩ := ex
    refine ⟨T,?_⟩
    ext x
    have e := DFunLike.congr_fun hT (A.rangeRestrict x)
    have er : A.quotKerEquivRange.symm (A.rangeRestrict x)=(ker A).mkQ x :=
      A.quotKerEquivRange_symm_apply_image x _
    simpa [f,er] using e

abbrev lattice (I : Type*) := I →₀ ℤ
def evaluate {I Z : Type*} [AddCommGroup Z] (u : I → Z) : lattice I →ₗ[ℤ] Z :=
  Finsupp.linearCombination ℤ u

@[simp] theorem evaluate_single {I Z : Type*} [AddCommGroup Z]
    (u : I → Z) (i : I) (n : ℤ) : evaluate u (Finsupp.single i n)=n • u i := by
  simp [evaluate]

theorem integral_relations {I J : Type*} (rows : I → lattice J) (t : I → Torus) :
    (∃ v : J → Torus, ∀ i, evaluate v (rows i)=t i) ↔
      ∀ c : lattice I, evaluate rows c=0 → evaluate t c=0 := by
  constructor
  · rintro ⟨v,hv⟩
    have h : (evaluate v).comp (evaluate rows)=evaluate t := by
      apply Finsupp.lhom_ext'
      intro i
      ext
      simp [hv]
    exact (character_extension (evaluate rows) (evaluate t)).mp ⟨_,h⟩
  · intro hc
    obtain ⟨T,hT⟩ := (character_extension (evaluate rows) (evaluate t)).mpr hc
    let v := fun j => T (Finsupp.single j 1)
    have hv : evaluate v=T := by
      apply Finsupp.lhom_ext'
      intro j
      ext
      simp [v]
    refine ⟨v,fun i => ?_⟩
    have he := DFunLike.congr_fun hT (Finsupp.single i 1)
    simpa [hv] using he

#print axioms integral_relations

/-- The integral relation lattice always has a finite generating set. The
same finite set works for every possible assignment of target phases. -/
theorem finite_relations {I J : Type*} [Finite I] (rows : I → lattice J) :
    ∃ tests : Finset (lattice I),
      (∀ c ∈ tests, evaluate rows c=0) ∧
      ∀ t : I → Torus, (∀ c, evaluate rows c=0 → evaluate t c=0) ↔
        ∀ c ∈ tests, evaluate t c=0 := by
  classical
  let := Fintype.ofFinite I
  have hg : (ker (evaluate rows)).FG := IsNoetherian.noetherian _
  obtain ⟨tests,hs⟩ := hg
  have inKer {c : lattice I} (hc : c∈tests) : c∈ker (evaluate rows) := by
    rw [←hs]
    exact Submodule.subset_span hc
  refine ⟨tests,fun _ hc => inKer hc,fun t => ⟨fun h c hc => h c (inKer hc),?_⟩⟩
  intro h
  change ker (evaluate rows)≤ker (evaluate t)
  rw [←hs]
  exact Submodule.span_le.mpr h

#print axioms finite_relations
end FractionalTorus
