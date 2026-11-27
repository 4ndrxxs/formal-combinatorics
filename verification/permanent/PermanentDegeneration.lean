import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Finset.Max

/-! A diagonal torus degeneration for linear spaces. Distinct nonnegative
weights and polynomial interpolation give a coordinate space of precisely
the same dimension. No topological limit or projectivity assumption is used. -/

noncomputable section
open Polynomial Module

namespace PermanentDegeneration

variable {K I : Type*} [Field K] [Fintype I]

private def Pivot (L : Submodule K (I → K)) (w : I → ℕ) (i : I) : Prop :=
  ∃ x ∈ L, x i = 1 ∧ ∀ j, w j < w i → x j = 0

private def pivots (L : Submodule K (I → K)) (w : I → ℕ) : Finset I := by
  classical exact Finset.univ.filter (Pivot L w)

private theorem mem_pivots {L : Submodule K (I → K)} {w : I → ℕ} {i : I} :
    i ∈ pivots L w ↔ Pivot L w i := by classical simp [pivots]

private theorem zero_of_zero_on_pivots (L : Submodule K (I → K)) (w : I → ℕ)
    (x : I → K) (hx : x ∈ L) (zero : ∀ i ∈ pivots L w, x i = 0) : x = 0 := by
  classical
  by_contra ne
  obtain ⟨j,hj⟩ := Function.ne_iff.mp ne
  let s := Finset.univ.filter fun i ↦ x i ≠ 0
  have hs : s.Nonempty := ⟨j,by simpa [s] using hj⟩
  obtain ⟨i,hi,hm⟩ := s.exists_min_image w hs
  have nz : x i ≠ 0 := (Finset.mem_filter.mp hi).2
  apply nz
  apply zero
  apply mem_pivots.mpr
  refine ⟨(x i)⁻¹ • x,L.smul_mem _ hx,by simp [nz],?_⟩
  intro j hj
  have z : x j = 0 := by
    by_contra h
    exact (not_lt_of_ge (hm j (by simpa [s] using h))) hj
  simp [z]

private theorem pivot_count (L : Submodule K (I → K)) (w : I → ℕ) :
    finrank K L ≤ (pivots L w).card := by
  let e : L →ₗ[K] (↥(pivots L w) → K) :=
    { toFun := fun x i ↦ x.val i
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have inj : Function.Injective e := by
    intro x y h
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply zero_of_zero_on_pivots L w _ (L.sub_mem x.property y.property)
    intro i hi
    exact sub_eq_zero.mpr (congrFun h ⟨i,hi⟩)
  exact (LinearMap.finrank_le_finrank_of_injective inj).trans_eq
    ((Module.finrank_pi K).trans (Fintype.card_coe _))

/-- All polynomials vanishing on the weighted translates of L vanish on
a single coordinate subspace of dimension dim L. -/
theorem coordinate_specialization [Infinite K] (L : Submodule K (I → K))
    (w : I → ℕ) (injective : Function.Injective w) :
    ∃ S : Finset I, S.card = finrank K L ∧
      ∀ (p : MvPolynomial I K),
        (∀ x ∈ L, ∀ t : K, t ≠ 0 → MvPolynomial.eval (fun j ↦ t^(w j) * x j) p = 0) →
        ∀ z : I → K, (∀ j ∉ S, z j = 0) → MvPolynomial.eval z p = 0 := by
  classical
  obtain ⟨S,subset,card⟩ := Finset.exists_subset_card_eq (pivot_count L w)
  refine ⟨S,card,?_⟩
  intro p invariant z supported
  have leading (i : S) : Pivot L w i := mem_pivots.mp (subset i.property)
  choose v hv one lower using leading
  let q (j : I) : K[X] := ∑ i : S, C (z i * v i j) * X^(w j - w i)
  have eval_at (t : K) (j : I) : (q j).eval t =
      ∑ i : S, (z i * v i j) * t^(w j - w i) := by
    change Polynomial.evalRingHom t (q j) = _
    simp [q, map_sum]
  have off (i : S) (j : I) (ne : (i : I) ≠ j) :
      (z i * v i j) * (0 : K)^(w j - w i) = 0 := by
    rcases lt_or_gt_of_ne (fun eq ↦ ne (injective eq)) with h | h
    · simp [zero_pow (Nat.sub_ne_zero_of_lt h)]
    · simp [lower i j h]
  have at_zero (j : I) : (q j).eval 0 = z j := by
    rw [eval_at]
    by_cases h : j ∈ S
    · let i : S := ⟨j,h⟩
      rw [Finset.sum_eq_single i]
      · simp [i,one]
      · intro k _ different
        exact off k j (fun eq ↦ different (Subtype.ext eq))
      · simp
    · rw [supported j h]
      exact Finset.sum_eq_zero fun i _ ↦ off i j (fun eq ↦ h (eq ▸ i.property))
  have away (t : K) (nt : t ≠ 0) : ∃ x ∈ L, ∀ j, (q j).eval t = t^(w j) * x j := by
    let x := ∑ i : S, (z i / t^(w i)) • v i
    refine ⟨x,L.sum_mem (fun i _ ↦ L.smul_mem _ (hv i)),?_⟩
    intro j
    rw [eval_at]
    simp only [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases le : w i ≤ w j
    · have factor : t^(w j) = t^(w j-w i) * t^(w i) := by rw [← pow_add, Nat.sub_add_cancel le]
      rw [factor]
      field_simp
    · simp [lower i j (lt_of_not_ge le)]
  let g := MvPolynomial.eval₂Hom Polynomial.C q p
  have along (t : K) : g.eval t = MvPolynomial.eval (fun j ↦ (q j).eval t) p := by
    change (Polynomial.evalRingHom t) (MvPolynomial.eval₂Hom Polynomial.C q p) = _
    rw [MvPolynomial.map_eval₂Hom]
    have cmp : (Polynomial.evalRingHom t).comp (Polynomial.C : K →+* K[X]) = RingHom.id K := by
      apply RingHom.ext
      intro a
      simp
    rw [cmp]
    rfl
  have nonzero (t : K) (nt : t ≠ 0) : g.eval t = 0 := by
    obtain ⟨x,hx,eq⟩ := away t nt
    simpa only [along,eq] using invariant x hx t nt
  have killed : X * g = 0 := Polynomial.funext fun t ↦ by
    by_cases eq : t = 0
    · simp [eq]
    · simp [nonzero t eq]
  have gz : g = 0 := (mul_eq_zero.mp killed).resolve_left Polynomial.X_ne_zero
  have endpt := along 0
  simpa only [gz,Polynomial.eval_zero,at_zero] using endpt.symm

#print axioms coordinate_specialization
end PermanentDegeneration
