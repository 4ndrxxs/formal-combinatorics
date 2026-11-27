module
public import Quantum.FractionalLCSOrbit
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finite.Basic

/-! A transitive p-group of context permutations forces a solution mod p. -/
@[expose] public section
noncomputable section
namespace TransitiveLCS
open Finset MulAction
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
variable {G C V : Type*} [Group G] [Fintype C] [Nonempty C] [MulAction G C]
  [MulAction.IsPretransitive G C]

def pull (g : G) (f : C → ZMod p) (c : C) := f (g⁻¹ • c)

theorem ones_mem_of_pgroup (gp : IsPGroup p G) (W : Submodule (ZMod p) (C → ZMod p))
    (hn : ∃ f ∈ W, f ≠ 0) (stable : ∀ (g : G) f, f∈W → pull g f∈W) :
    (fun _ : C => (1 : ZMod p)) ∈ W := by
  classical
  let _ : MulAction G W := {
    smul g f := ⟨pull g f.1,stable g _ f.2⟩
    one_smul f := by
      apply Subtype.ext; funext c
      change f.1 ((1:G)⁻¹ • c) = f.1 c
      simp
    mul_smul a b f := by
      apply Subtype.ext; funext c
      change f.1 ((a*b)⁻¹ • c) = f.1 (b⁻¹ • (a⁻¹ • c))
      simp [mul_smul] }
  obtain ⟨f,hf,hfn⟩ := hn
  have nonzero : (⟨f,hf⟩ : W) ≠ 0 := fun h => hfn (congrArg Subtype.val h)
  have ht : 0 < Module.finrank (ZMod p) W :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_,nonzero⟩
  have hcard : p ∣ Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K:=ZMod p),Nat.card_eq_fintype_card,ZMod.card]
    exact dvd_pow_self _ (Nat.ne_of_gt ht)
  have h0 : (0:W) ∈ fixedPoints G W := fun g => by apply Subtype.ext; rfl
  obtain ⟨v,hv,hv0⟩ := gp.exists_fixed_point_of_prime_dvd_card_of_fixed_point W hcard h0
  let base : C := Classical.choice inferInstance
  have constant (c : C) : v.1 c = v.1 base := by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G base c
    have h := congrFun (congrArg Subtype.val (hv g⁻¹)) base
    change v.1 ((g⁻¹)⁻¹ • base) = v.1 base at h
    simpa [hg] using h
  have hval : v.1 base ≠ 0 := by
    intro h
    apply hv0
    apply Subtype.ext
    funext c
    exact ((constant c).trans h).symm
  have scaled := W.smul_mem (v.1 base)⁻¹ v.2
  have he : (v.1 base)⁻¹ • v.1 = fun _ : C => (1:ZMod p) := by
    funext c
    change _ * v.1 c = _
    rw [constant c,inv_mul_cancel₀ hval]
  rwa [he] at scaled

def incidence [Fintype V] (edge : C→Finset V) : (V→ZMod p) →ₗ[ZMod p] (C→ZMod p) where
  toFun f c := ∑ v ∈ edge c, f v
  map_add' f h := by funext c; simp [Finset.sum_add_distrib]
  map_smul' t f := by funext c; simp [Finset.mul_sum]

/-- This holds for any nonempty finite incidence system with a p-group transitive
on its contexts, even without a geometric realization or transitivity on variables. -/
theorem incidence_soluble_of_pgroup [Fintype V] [DecidableEq V] [MulAction G V]
    (gp : IsPGroup p G) (edge : C→Finset V) (hn : ∃ c, (edge c).Nonempty)
    (symmetry : ∀ (g:G) c, edge (g • c) = (edge c).image (fun v => g • v)) :
    ∃ f : V→ZMod p, ∀ c, ∑ v ∈ edge c, f v = 1 := by
  classical
  let L := incidence (p:=p) edge
  have nzero : ∃ f ∈ LinearMap.range L, f ≠ 0 := by
    obtain ⟨c,v,hv⟩ := hn
    let δ (w : V) : ZMod p := if w=v then 1 else 0
    refine ⟨L δ,⟨δ,rfl⟩,?_⟩
    intro h
    have h' := congrFun h c
    simp [δ,L,incidence,hv] at h'
  have stable (g : G) (f : C→ZMod p) (hf : f ∈ LinearMap.range L) :
      pull g f ∈ LinearMap.range L := by
    obtain ⟨x,rfl⟩ := hf
    refine ⟨fun v => x (g⁻¹ • v),?_⟩
    funext c
    change (∑ v ∈ edge c, x (g⁻¹ • v)) = ∑ v ∈ edge (g⁻¹ • c), x v
    rw [symmetry,Finset.sum_image]
    exact (MulAction.injective g⁻¹).injOn
  obtain ⟨x,hx⟩ := ones_mem_of_pgroup gp (LinearMap.range L) nzero stable
  exact ⟨x,fun c => congrFun hx c⟩

#print axioms incidence_soluble_of_pgroup
end TransitiveLCS

