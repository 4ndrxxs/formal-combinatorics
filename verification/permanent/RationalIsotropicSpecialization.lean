import RationalPlaneSpecialization
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-! Specialization preserves the existence of a totally isotropic linear space. -/

noncomputable section
open Polynomial Module Matrix
namespace RationalSpecialization
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

private theorem map_pairing {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T)
    (G : Matrix I I R) (p q : I → R) :
    f (G.toBilin' p q) = (f.mapMatrix G).toBilin' (f ∘ p) (f ∘ q) := by
  simp [Matrix.toBilin'_apply]

theorem reduction_isotropic (G : Matrix I I K[X])
    (U : Submodule (RatFunc K) (I → RatFunc K))
    (iso : U ≤ ((algebraMap K[X] (RatFunc K)).mapMatrix G).toBilin'.orthogonal U) :
    reduction U ≤ ((evalRingHom (0 : K)).mapMatrix G).toBilin'.orthogonal (reduction U) := by
  rintro x ⟨p,hp,ep⟩ y ⟨q,hq,eq⟩

  have pol : G.toBilin' q p = 0 := by
    apply RatFunc.algebraMap_injective K
    rw [map_pairing,map_zero]
    exact iso hp _ hq
  have ex : (evalRingHom (0 : K)) ∘ p = x := funext ep
  have ey : (evalRingHom (0 : K)) ∘ q = y := funext eq
  have z := congrArg (evalRingHom (0 : K)) pol
  rw [map_pairing,ex,ey,map_zero] at z
  exact z

theorem specialize_isotropic_plane (G : Matrix I I K[X]) (d : ℕ)
    (U : Submodule (RatFunc K) (I → RatFunc K)) (hd : d ≤ finrank (RatFunc K) U)
    (iso : U ≤ ((algebraMap K[X] (RatFunc K)).mapMatrix G).toBilin'.orthogonal U) :
    ∃ V : Submodule K (I → K), d ≤ finrank K V ∧
      V ≤ ((evalRingHom (0 : K)).mapMatrix G).toBilin'.orthogonal V :=
  ⟨reduction U,hd.trans (finrank_le_reduction U),reduction_isotropic G U iso⟩

#print axioms specialize_isotropic_plane
end RationalSpecialization
