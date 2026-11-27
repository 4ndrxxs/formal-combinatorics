module
public import Quantum.DiagonalSixCount
public import Quantum.DiagonalSixExamples

/-! The exact ray spectrum of the diagonal quantum Latin squares of order six. -/
@[expose] public section
noncomputable section
namespace DiagonalSix
open Complex Matrix QuantumCertificate
open scoped BigOperators ComplexConjugate

theorem proj_smul (s : ℂ) (v : Space 6) : proj (s • v)=(s*conj s) • proj v := by
  ext i j
  simp [proj,Matrix.vecMulVec_apply,PiLp.smul_apply,smul_eq_mul]
  ring

theorem equal_proj_of_ray {v w : Space 6} (nv : v≠0) (nw : w≠0)
    (tv : (proj v).trace=1) (tw : (proj w).trace=1)
    (h : Projectivization.mk ℂ v nv=Projectivization.mk ℂ w nw) : proj v=proj w := by
  obtain ⟨s,hs⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have hp := congrArg proj hs
  rw [proj_smul] at hp
  have t := congrArg Matrix.trace hp
  simp only [Matrix.trace_smul,tw,tv,smul_eq_mul,mul_one] at t
  simpa [t] using hp.symm

theorem range_count {ι α β : Type} (f : ι → α) (g : ι → β)
    (h : ∀ i j, f i=f j ↔ g i=g j) : (Set.range f).ncard=(Set.range g).ncard := by
  classical
  let lift (a : α) (ha : a∈Set.range f) := g (Classical.choose ha)
  apply Set.ncard_congr lift
  · intro a ha; exact ⟨_,rfl⟩
  · intro a b ha hb eq
    exact (Classical.choose_spec ha).symm.trans (((h _ _).mpr eq).trans (Classical.choose_spec hb))
  · rintro _ ⟨i,rfl⟩
    let hi : f i∈Set.range f := ⟨i,rfl⟩
    exact ⟨f i,hi,(h _ _).mp (Classical.choose_spec hi)⟩

theorem spectrum_only (c : ℕ) (hc : DiagonalRealized 6 c) : c=6 ∨ c=8 ∨ c=10 ∨ c=12 := by
  classical
  obtain ⟨a,ac⟩ := hc
  let g := toModel a.entry a.rows a.cols a.main a.anti
  let idx : (Idx × Idx) ≃ Cell 6 := ord.prodCongr ord
  let f := a.ray ∘ idx
  let p (x : Idx × Idx) := g.p x.1 x.2
  have equiv (x y) : f x=f y ↔ p x=p y := by
    exact ⟨equal_proj_of_ray (a.nz _) (a.nz _) (g.trace x.1 x.2) (g.trace y.1 y.2),
      same_ray (a.nz _) (a.nz _) (g.trace x.1 x.2)⟩
  have sr : Set.range f=Set.range a.ray := Function.Surjective.range_comp idx.surjective _
  have sp : (g.allRays : Set M)=Set.range p := by
    simp only [Model.allRays,Finset.coe_image,Finset.coe_univ,Set.image_univ]
    rfl
  have ct := range_count f p equiv
  rw [sr,ac,← sp,Set.ncard_coe_finset] at ct
  rw [ct]
  exact g.count

theorem spectrum (c : ℕ) : DiagonalRealized 6 c ↔ c=6 ∨ c=8 ∨ c=10 ∨ c=12 := by
  refine ⟨spectrum_only c,?_⟩
  rintro (rfl | rfl | rfl | rfl)
  · exact Examples.order6
  · exact Examples.order8
  · exact Examples.order10
  · exact Examples.order12

#print axioms spectrum_only
#print axioms spectrum
end DiagonalSix
