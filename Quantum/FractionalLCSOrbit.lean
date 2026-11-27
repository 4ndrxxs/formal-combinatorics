module
public import Quantum.Exact
public import Mathlib.Data.ZMod.Basic

/-! Finite ray-context arrangements obtained by translating one orthonormal basis. -/
@[expose] public section
noncomputable section
namespace TransitiveLCS
open QuantumCertificate Finset
open scoped BigOperators

abbrev Ray (p : ℕ) := Projectivization ℂ (Space p)
abbrev Unitary (p : ℕ) := Space p ≃ₗᵢ[ℂ] Space p
abbrev Basis (p : ℕ) := OrthonormalBasis (Fin p) ℂ (Space p)

def onRay {p : ℕ} (U : Unitary p) : Ray p → Ray p :=
  Projectivization.map U.toLinearEquiv.toLinearMap U.injective

def imageContext {p : ℕ} (U : Unitary p) (C : Finset (Ray p)) : Finset (Ray p) := by
  classical exact C.image (onRay U)

def basisRays {p : ℕ} (b : Basis p) : Finset (Ray p) := by
  classical exact univ.image fun j => Projectivization.mk ℂ (b j) (b.orthonormal.ne_zero j)

structure Arrangement (p : ℕ) where
  rays : Finset (Ray p)
  contexts : Finset (Finset (Ray p))
  orthonormal : ∀ C ∈ contexts, ∃ b : Basis p, basisRays b = C
  incidence : ∀ v, v ∈ rays ↔ ∃ C ∈ contexts, v ∈ C

def Arrangement.Symmetry {p : ℕ} (A : Arrangement p) (U : Unitary p) : Prop := by
  classical exact A.rays.image (onRay U) = A.rays ∧
    A.contexts.image (imageContext U) = A.contexts

def Arrangement.RayAndContextTransitive {p : ℕ} (A : Arrangement p) : Prop :=
  (∀ v ∈ A.rays, ∀ w ∈ A.rays, ∃ U : Unitary p, A.Symmetry U ∧ onRay U v = w) ∧
  (∀ C ∈ A.contexts, ∀ D ∈ A.contexts, ∃ U : Unitary p, A.Symmetry U ∧ imageContext U C = D)

def Arrangement.Classical {p : ℕ} (A : Arrangement p) : Prop :=
  ∃ x : Ray p → ZMod p, ∀ C ∈ A.contexts, ∑ v ∈ C, x v = 1

variable {p : ℕ} {G : Type*} [Fintype G] [AddCommGroup G]

/-- The translations have representatives by genuine unitaries on the ambient space. -/
structure Orbit (p : ℕ) (G : Type*) [Fintype G] [AddCommGroup G] where
  state : G → Space p
  nz : ∀ g, state g ≠ 0
  projective : Function.Injective fun g => Projectivization.mk ℂ (state g) (nz g)
  seed : Fin p → G
  seed_injective : Function.Injective seed
  basis : Basis p
  seed_basis : ∀ i, basis i = state (seed i)
  translate : G → Unitary p
  translate_state : ∀ g a, translate g (state a) = state (g+a)

namespace Orbit
variable (O : Orbit p G)

def ray (a : G) : Ray p := Projectivization.mk ℂ (O.state a) (O.nz a)
def rays : Finset (Ray p) := by classical exact univ.image O.ray
def context (a : G) : Finset (Ray p) := by
  classical exact univ.image fun i => O.ray (a + O.seed i)
def contexts : Finset (Finset (Ray p)) := by classical exact univ.image O.context

theorem onRay_translate (g a : G) : onRay (O.translate g) (O.ray a) = O.ray (g+a) := by
  unfold onRay ray
  rw [Projectivization.map_mk]
  congr 1
  exact O.translate_state g a

theorem imageContext_translate (g a : G) :
    imageContext (O.translate g) (O.context a) = O.context (g+a) := by
  classical
  rw [imageContext,context,context,image_image]
  apply image_congr
  intro i _
  simpa [Function.comp_def,add_assoc] using O.onRay_translate g (a+O.seed i)

theorem basis_context (a : G) : basisRays (O.basis.map (O.translate a)) = O.context a := by
  classical
  unfold basisRays context
  apply image_congr
  intro i _
  unfold ray
  dsimp only
  congr 1
  rw [OrthonormalBasis.map_apply,O.seed_basis,O.translate_state]

def arrangement [NeZero p] : Arrangement p where
  rays := O.rays
  contexts := O.contexts
  orthonormal := by
    classical
    intro C hC
    obtain ⟨a,_,rfl⟩ := mem_image.mp hC
    exact ⟨_,O.basis_context a⟩
  incidence := by
    classical
    intro v
    constructor
    · intro hv
      obtain ⟨a,_,rfl⟩ := mem_image.mp hv
      refine ⟨O.context (a-O.seed 0),mem_image.mpr ⟨_,mem_univ _,rfl⟩,
        mem_image.mpr ⟨0,mem_univ _,?_⟩⟩
      simp
    · rintro ⟨C,hC,hv⟩
      obtain ⟨a,_,rfl⟩ := mem_image.mp hC
      obtain ⟨i,_,rfl⟩ := mem_image.mp hv
      exact mem_image.mpr ⟨_,mem_univ _,rfl⟩

theorem symmetry [NeZero p] (g : G) : O.arrangement.Symmetry (O.translate g) := by
  classical
  change O.rays.image _ = O.rays ∧ O.contexts.image _ = O.contexts
  constructor
  · ext v
    simp only [rays,mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      exact ⟨_,(O.onRay_translate g a).symm⟩
    · rintro ⟨a,rfl⟩
      exact ⟨_,⟨a-g,rfl⟩,by simpa using O.onRay_translate g (a-g)⟩
  · ext C
    simp only [contexts,mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      exact ⟨_,(O.imageContext_translate g a).symm⟩
    · rintro ⟨a,rfl⟩
      exact ⟨_,⟨a-g,rfl⟩,by simpa using O.imageContext_translate g (a-g)⟩

theorem transitive [NeZero p] : O.arrangement.RayAndContextTransitive := by
  classical
  constructor
  · intro v hv w hw
    obtain ⟨a,_,rfl⟩ := mem_image.mp hv
    obtain ⟨b,_,rfl⟩ := mem_image.mp hw
    exact ⟨O.translate (b-a),O.symmetry _,by simpa using O.onRay_translate (b-a) a⟩
  · intro C hC D hD
    obtain ⟨a,_,rfl⟩ := mem_image.mp hC
    obtain ⟨b,_,rfl⟩ := mem_image.mp hD
    exact ⟨O.translate (b-a),O.symmetry _,by simpa using O.imageContext_translate (b-a) a⟩

theorem classical_impossible [NeZero p] (hcard : (Fintype.card G : ZMod p) ≠ 0) :
    ¬ O.arrangement.Classical := by
  classical
  rintro ⟨x,hx⟩
  have row (a : G) : ∑ i, x (O.ray (a+O.seed i)) = 1 := by
    have h := hx (O.context a) (mem_image.mpr ⟨a,mem_univ _,rfl⟩)
    change ∑ v ∈ univ.image (fun i => O.ray (a+O.seed i)), x v = 1 at h
    rw [sum_image] at h
    · exact h
    · intro i _ j _ h
      exact O.seed_injective (add_left_cancel (O.projective h))
  have col (i : Fin p) : ∑ a, x (O.ray (a+O.seed i)) = ∑ a, x (O.ray a) :=
    Equiv.sum_comp (Equiv.addRight (O.seed i)) (fun a => x (O.ray a))
  have allrows := Finset.sum_congr (s₁:=univ) rfl (fun a _ => row a)
  rw [sum_comm] at allrows
  simp_rw [col] at allrows
  exact hcard (by simpa [nsmul_eq_mul] using allrows.symm)

end Orbit
end TransitiveLCS

