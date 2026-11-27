module

public import Quantum.Exact
import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Order.Interval.Set.Infinite

/-! Finite families of complex rays can be made disjoint by an isometry.
Rotate the phase on one generic line. Every input ray then has an infinite
orbit with no repetitions as the phase varies around the circle. -/

@[expose] public section
namespace QuantumCertificate
open Complex Submodule
open scoped ComplexConjugate

noncomputable def phaseLinear {d : ℕ} (a : Space d) (z : Circle) :
    Space d →ₗ[ℂ] Space d :=
  LinearMap.id + ((z:ℂ)-1) • (innerSL ℂ a).toLinearMap.smulRight a

theorem phaseLinear_apply {d : ℕ} (a u : Space d) (z : Circle) :
    phaseLinear a z u = u + (((z : ℂ)-1) * inner ℂ a u) • a := by
  simp [phaseLinear, smul_smul]

noncomputable def phaseIsometry {d : ℕ} (a : Space d) (ha : ‖a‖ = 1) (z : Circle) :
    Space d →ₗᵢ[ℂ] Space d :=
  (phaseLinear a z).isometryOfInner (by
    intro x y
    simp only [phaseLinear_apply, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, map_mul, map_sub, map_one, inner_self_eq_one_of_norm_eq_one ha]
    rw [← inner_conj_symm x a]
    have hz : conj (z:ℂ) * (z:ℂ) = 1 := by rw [RCLike.conj_mul, Circle.norm_coe]; norm_num
    linear_combination (conj (inner ℂ a x) * inner ℂ a y) * hz)

private theorem generic_axis {d : ℕ} (hd : 2 ≤ d) {I : Type*} [Finite I] [Nonempty I]
    (u : I → Space d) (hu : ∀ i, u i ≠ 0) :
    ∃ a : Space d, ‖a‖ = 1 ∧ ∀ i, u i ∉ ℂ ∙ a ∧ inner ℂ a (u i) ≠ 0 := by
  classical
  let p : I ⊕ I → Submodule ℂ (Space d) :=
    Sum.elim (fun i => ℂ ∙ u i) (fun i => (ℂ ∙ u i)ᗮ)
  have proper (k : I ⊕ I) : p k ≠ ⊤ := by
    rcases k with i|i
    · intro h
      have hdim := finrank_span_singleton (K:=ℂ) (hu i)
      change ℂ ∙ u i = ⊤ at h
      rw [h] at hdim
      simp at hdim
      omega
    · change (ℂ ∙ u i)ᗮ ≠ ⊤
      simpa [Submodule.orthogonal_eq_top_iff, Submodule.span_singleton_eq_bot] using hu i
  obtain ⟨b,hb⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p proper
  have hb0 : b ≠ 0 := by
    intro h
    exact hb (.inl (Classical.arbitrary I)) (h ▸ Submodule.zero_mem _)
  let t : ℂ := (‖b‖ : ℂ)⁻¹
  have ht : t ≠ 0 := by simp [t, norm_ne_zero_iff.mpr hb0]
  refine ⟨t • b, by simp [t,norm_smul, Complex.norm_real, norm_ne_zero_iff.mpr hb0], ?_⟩
  intro i
  have ha : t • b ∉ ℂ ∙ u i := fun h =>
    hb (.inl i) (((ℂ ∙ u i).smul_mem_iff ht).mp h)
  constructor
  · intro hm
    obtain ⟨s,hs⟩ := Submodule.mem_span_singleton.mp hm
    have hs0 : s ≠ 0 := by intro h; rw [h,zero_smul] at hs; exact hu i hs.symm
    apply ha (Submodule.mem_span_singleton.mpr ⟨s⁻¹, ?_⟩)
    rw [← hs, inv_smul_smul₀ hs0]
  · have hb' : inner ℂ b (u i) ≠ 0 := fun h =>
      hb (.inr i) (Submodule.mem_orthogonal_singleton_iff_inner_left.mpr h)
    simp [inner_smul_left,ht,hb']

private theorem circle_infinite : Infinite Circle := by
  have := (Set.Icc_infinite Real.pi_pos).to_subtype
  apply Infinite.of_injective (fun x : Set.Icc (0:ℝ) Real.pi => Circle.exp x)
  intro x y h
  apply Subtype.ext
  exact Circle.exp_injOn_Icc (by linarith [Real.pi_pos]) x.property y.property h

private theorem phase_ray_injective {d : ℕ} (a u : Space d) (ha : ‖a‖ = 1)
    (hu : u ≠ 0) (hu' : u ∉ ℂ ∙ a) (hip : inner ℂ a u ≠ 0) :
    Function.Injective (fun z : Circle => Projectivization.mk ℂ (phaseIsometry a ha z u)
      (fun h => hu ((phaseIsometry a ha z).injective (h.trans (map_zero _).symm)))) := by
  intro z w h
  obtain ⟨s,hs⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  change s • phaseLinear a w u = phaseLinear a z u at hs
  rw [phaseLinear_apply, phaseLinear_apply] at hs
  let L := (ℂ ∙ a).mkQ
  have hLa : L a = 0 := (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self a)
  have hLu : L u ≠ 0 := fun h' => hu' ((Submodule.Quotient.mk_eq_zero _).mp h')
  have hs' := congrArg L hs
  simp only [map_smul, map_add, hLa, smul_zero, add_zero] at hs'
  have h1 : s = 1 := smul_left_injective ℂ hLu (hs'.trans (one_smul ℂ _).symm)
  subst s
  rw [one_smul] at hs
  have ha0 : a ≠ 0 := fun h' => by simp [h'] at ha
  have hc := smul_left_injective ℂ ha0 (add_left_cancel hs)
  apply Circle.ext
  exact sub_left_inj.mp ((mul_right_cancel₀ hip hc).symm)

/-- A complex-linear isometry can move finitely many nonzero rays away from
any finite target set when the complex dimension is at least two. -/
theorem exists_isometry_avoiding {d : ℕ} (hd : 2 ≤ d) {I : Type*} [Finite I] [Nonempty I]
    (u : I → Space d) (hu : ∀ i, u i ≠ 0)
    (s : Set (Projectivization ℂ (Space d))) (hs : s.Finite) :
    ∃ f : Space d →ₗᵢ[ℂ] Space d, ∀ i, Projectivization.mk ℂ (f (u i))
        (fun h => hu i (f.injective (h.trans (map_zero _).symm))) ∉ s := by
  classical
  obtain ⟨a,ha,h⟩ := generic_axis hd u hu
  let ray (i : I) (z : Circle) := Projectivization.mk ℂ (phaseIsometry a ha z (u i))
    (fun eq => hu i ((phaseIsometry a ha z).injective (eq.trans (map_zero _).symm)))
  have hfin (i : I) : (ray i ⁻¹' s).Finite :=
    hs.preimage (phase_ray_injective a (u i) ha (hu i) (h i).1 (h i).2).injOn
  let : Infinite Circle := circle_infinite
  obtain ⟨z,hz⟩ := (Set.finite_iUnion hfin).exists_notMem
  exact ⟨phaseIsometry a ha z, fun i hbad => hz (Set.mem_iUnion.mpr ⟨i,hbad⟩)⟩

#print axioms exists_isometry_avoiding
end QuantumCertificate
