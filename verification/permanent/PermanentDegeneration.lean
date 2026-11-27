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

/-- Interpolate arbitrary values on leading coordinates, starting with
the smallest weights. Adjusting a later pivot preserves every earlier value. -/
private theorem lift_pivots (L : Submodule K (I → K)) (w : I → ℕ)
    (inj : Function.Injective w) (S : Finset I) (sub : S ⊆ pivots L w) (z : I → K) :
    ∃ x ∈ L, ∀ i ∈ S, x i = z i := by
  classical
  have aux (A : Finset I) (incl : A ⊆ S) : ∃ x ∈ L, ∀ i ∈ A, x i = z i := by
    induction A using Finset.strongInductionOn with
    | _ A ih =>
      by_cases hA : A.Nonempty
      · obtain ⟨i,hi,top⟩ := A.exists_max_image w hA
        obtain ⟨x,hx,h⟩ := ih (A.erase i) (Finset.erase_ssubset hi)
          (fun j hj ↦ incl (Finset.mem_of_mem_erase hj))
        obtain ⟨v,hv,one,lower⟩ := mem_pivots.mp (sub (incl hi))
        refine ⟨x + (z i - x i) • v,L.add_mem hx (L.smul_mem _ hv),?_⟩
        intro j hj
        by_cases eq : j = i
        · subst j; simp [one]
        · have lt : w j < w i := lt_of_le_of_ne (top j hj) (fun e ↦ eq (inj e))
          simp [lower j lt,h j (Finset.mem_erase.mpr ⟨eq,hj⟩)]
      · exact ⟨0,L.zero_mem,fun j hj ↦ (hA ⟨j,hj⟩).elim⟩
  exact aux S (fun _ h ↦ h)

/-- Every vector on the coordinate plane is reached by a polynomial
trajectory lying in the diagonal translates away from zero. -/
def HasCoordinatePaths (L : Submodule K (I → K)) (w : I → ℕ) (S : Finset I) : Prop :=
  ∀ z : I → K, (∀ j ∉ S, z j = 0) → ∃ q : I → K[X],
    (∀ j, (q j).eval 0 = z j) ∧
    ∀ t : K, t ≠ 0 → ∃ x ∈ L, ∀ j, (q j).eval t = t^(w j) * x j

theorem coordinate_paths_with_leading (L : Submodule K (I → K))
    (w : I → ℕ) (injective : Function.Injective w) :
    ∃ S : Finset I, S.card = finrank K L ∧
      (∀ z : I → K, ∃ x ∈ L, ∀ i ∈ S, x i = z i) ∧
      (∀ i ∈ S, ∃ x ∈ L, x i = 1 ∧ ∀ j, w j < w i → x j = 0) ∧
      HasCoordinatePaths L w S := by
  classical
  obtain ⟨S,subset,card⟩ := Finset.exists_subset_card_eq (pivot_count L w)
  refine ⟨S,card,lift_pivots L w injective S subset,fun _ hi ↦ mem_pivots.mp (subset hi),?_⟩
  intro z supported
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
  exact ⟨q,at_zero,away⟩

theorem coordinate_paths (L : Submodule K (I → K))
    (w : I → ℕ) (injective : Function.Injective w) :
    ∃ S : Finset I, S.card = finrank K L ∧
      (∀ z : I → K, ∃ x ∈ L, ∀ i ∈ S, x i = z i) ∧ HasCoordinatePaths L w S := by
  obtain ⟨S,card,lift,_,paths⟩ := coordinate_paths_with_leading L w injective
  exact ⟨S,card,lift,paths⟩

/-- A set of distinct leading coordinates gives a surjection onto their values. -/
theorem lift_leading (L : Submodule K (I → K)) (w : I → ℕ) (inj : Function.Injective w)
    (S : Finset I) (leading : ∀ i ∈ S, ∃ x ∈ L, x i = 1 ∧ ∀ j, w j < w i → x j = 0)
    (z : I → K) : ∃ x ∈ L, ∀ i ∈ S, x i = z i :=
  lift_pivots L w inj S (fun i hi ↦ mem_pivots.mpr (leading i hi)) z

/-- The number of distinct leading coordinates is a lower bound for dimension. -/
theorem card_le_finrank_of_leading (L : Submodule K (I → K)) (w : I → ℕ)
    (inj : Function.Injective w) (S : Finset I)
    (leading : ∀ i ∈ S, ∃ x ∈ L, x i = 1 ∧ ∀ j, w j < w i → x j = 0) :
    S.card ≤ finrank K L := by
  classical
  let e : L →ₗ[K] (S → K) := LinearMap.pi fun j ↦ (LinearMap.proj (j : I)).comp L.subtype
  have onto : Function.Surjective e := by
    intro z
    obtain ⟨x,hx,eq⟩ := lift_leading L w inj S leading (fun j ↦ if h : j ∈ S then z ⟨j,h⟩ else 0)
    exact ⟨⟨x,hx⟩,funext fun j ↦ by simpa [e,j.property] using eq j.val j.property⟩
  simpa using e.finrank_le_finrank_of_surjective onto

omit [Fintype I] in
theorem specialization_of_paths [Infinite K] {L : Submodule K (I → K)} {w : I → ℕ} {S : Finset I}
    (paths : HasCoordinatePaths L w S) (p : MvPolynomial I K)
    (invariant : ∀ x ∈ L, ∀ t : K, t ≠ 0 → MvPolynomial.eval (fun j ↦ t^(w j) * x j) p = 0)
    (z : I → K) (supported : ∀ j ∉ S, z j = 0) : MvPolynomial.eval z p = 0 := by
  obtain ⟨q,at_zero,away⟩ := paths z supported
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

/-- The limiting coordinate plane also has a surjective coordinate
projection from the original linear space. -/
theorem coordinate_specialization_with_lift [Infinite K] (L : Submodule K (I → K))
    (w : I → ℕ) (injective : Function.Injective w) :
    ∃ S : Finset I, S.card = finrank K L ∧
      (∀ z : I → K, ∃ x ∈ L, ∀ i ∈ S, x i = z i) ∧
      ∀ (p : MvPolynomial I K),
        (∀ x ∈ L, ∀ t : K, t ≠ 0 → MvPolynomial.eval (fun j ↦ t^(w j) * x j) p = 0) →
        ∀ z : I → K, (∀ j ∉ S, z j = 0) → MvPolynomial.eval z p = 0 := by
  obtain ⟨S,card,lift,paths⟩ := coordinate_paths L w injective
  exact ⟨S,card,lift,specialization_of_paths paths⟩

/-- All polynomials vanishing on the weighted translates of L vanish on
a single coordinate subspace of dimension dim L. -/
theorem coordinate_specialization [Infinite K] (L : Submodule K (I → K))
    (w : I → ℕ) (injective : Function.Injective w) :
    ∃ S : Finset I, S.card = finrank K L ∧
      ∀ (p : MvPolynomial I K),
        (∀ x ∈ L, ∀ t : K, t ≠ 0 → MvPolynomial.eval (fun j ↦ t^(w j) * x j) p = 0) →
        ∀ z : I → K, (∀ j ∉ S, z j = 0) → MvPolynomial.eval z p = 0 := by
  obtain ⟨S,card,_,special⟩ := coordinate_specialization_with_lift L w injective
  exact ⟨S,card,special⟩

#print axioms coordinate_paths
#print axioms specialization_of_paths
#print axioms coordinate_specialization_with_lift
#print axioms coordinate_specialization
end PermanentDegeneration
