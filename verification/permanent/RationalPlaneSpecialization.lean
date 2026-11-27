import RationalPrimitiveVector

/-! A rational subspace has an equally large space of reductions of polynomial vectors. -/

noncomputable section
open Polynomial Module
namespace RationalSpecialization
variable {K I : Type*} [Field K]

/-- Values at zero of all polynomial vectors belonging generically to a fixed space. -/
def reduction (U : Submodule (RatFunc K) (I → RatFunc K)) : Submodule K (I → K) where
  carrier := {x | ∃ p : I → K[X], (fun i ↦ algebraMap K[X] (RatFunc K) (p i)) ∈ U ∧
    ∀ i, (p i).eval 0 = x i}
  zero_mem' := by
    refine ⟨0,?_,by simp⟩
    rw [show (fun i : I ↦ algebraMap K[X] (RatFunc K) ((0 : I → K[X]) i)) = 0 by ext; simp]
    exact U.zero_mem
  add_mem' := by
    rintro x y ⟨p,hp,ep⟩ ⟨q,hq,eq⟩
    refine ⟨p+q,?_,?_⟩
    · rw [show (fun i ↦ algebraMap K[X] (RatFunc K) ((p+q) i)) =
          (fun i ↦ algebraMap K[X] (RatFunc K) (p i)) +
          (fun i ↦ algebraMap K[X] (RatFunc K) (q i)) by ext; simp]
      exact U.add_mem hp hq
    · intro i
      simp [ep,eq]
  smul_mem' := by
    rintro c x ⟨p,hp,ep⟩
    refine ⟨fun i ↦ C c * p i,?_,?_⟩
    · rw [show (fun i ↦ algebraMap K[X] (RatFunc K) (C c * p i)) =
          algebraMap K[X] (RatFunc K) (C c) • (fun i ↦ algebraMap K[X] (RatFunc K) (p i)) by
            ext; simp]
      exact U.smul_mem _ hp
    · intro i
      simp [ep,smul_eq_mul]

theorem reduction_mono {U V : Submodule (RatFunc K) (I → RatFunc K)} (h : U ≤ V) :
    reduction U ≤ reduction V := fun _ ⟨p,hp,ep⟩ ↦ ⟨p,h hp,ep⟩

variable [Fintype I]

/-- A rational plane specializes without losing independent directions over the residue field. -/
theorem finrank_le_reduction (U : Submodule (RatFunc K) (I → RatFunc K)) :
    finrank (RatFunc K) U ≤ finrank K (reduction U) := by
  classical
  suffices bound : ∀ n, ∀ V : Submodule (RatFunc K) (I → RatFunc K),
      n ≤ finrank (RatFunc K) V → n ≤ finrank K (reduction V) from bound _ U le_rfl
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro V dim
    have nV : V ≠ ⊥ := by rintro rfl; simp at dim
    obtain ⟨v,hv,nv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot nV
    obtain ⟨c,p,_,hp,j,hj⟩ := primitive_vector v nv
    let x : I → K := fun i ↦ (p i).eval 0
    have hx : x ∈ reduction V := by
      refine ⟨p,?_,fun _ ↦ rfl⟩
      rw [show (fun i ↦ algebraMap K[X] (RatFunc K) (p i)) = c • v by ext i; exact hp i]
      exact V.smul_mem c hv
    let h : V →ₗ[RatFunc K] RatFunc K := (LinearMap.proj j).comp V.subtype
    let W := h.ker.map V.subtype
    have eqdim : finrank (RatFunc K) h.ker = finrank (RatFunc K) W :=
      (Submodule.equivMapOfInjective V.subtype V.subtype_injective h.ker).finrank_eq
    have onedim := h.range.finrank_le
    rw [finrank_self] at onedim
    have ranknull := h.finrank_range_add_finrank_ker
    have plenty : n ≤ finrank (RatFunc K) W := by omega
    have incl : W ≤ V := by
      rintro _ ⟨u,_,rfl⟩
      exact u.property
    have killed {z : I → RatFunc K} (hz : z ∈ W) : z j = 0 := by
      obtain ⟨u,hu,rfl⟩ := hz
      exact hu
    have nx : x ∉ reduction W := by
      rintro ⟨q,hq,eq⟩
      have zero : q j = 0 := RatFunc.algebraMap_injective K ((killed hq).trans (map_zero _).symm)
      apply hj
      change x j = 0
      rw [← eq j,zero]
      simp
    have lt : reduction W < reduction V := lt_of_le_of_ne (reduction_mono incl)
      (fun e ↦ nx (e ▸ hx))
    exact (ih W plenty).trans_lt (Submodule.finrank_lt_finrank_of_lt lt)

#print axioms finrank_le_reduction
end RationalSpecialization
