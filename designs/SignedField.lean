import SignedProduct

/-! Correlation and counting lemmas for the projective finite-field construction. -/

noncomputable section

namespace Signed39.FieldConstruction

open Finset

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem character_corr (hF : ringChar F ≠ 2) (t : F) :
    corr (quadraticChar F) t = (if t = 0 then (Fintype.card F:ℤ) else 0) - 1 := by
  classical
  let L := quadraticChar F
  by_cases ht : t = 0
  · subst t
    have sq (a : F) : L a * L a = if a = 0 then 0 else 1 := by
      split_ifs with h
      · simp [L,h]
      · simpa [L,pow_two] using quadraticChar_sq_one h
    change (∑ a : F, L a * L (a+0)) = _
    simp [sq, sum_ite]
    rw [show (univ.filter (fun a : F => ¬a = 0)) = univ.erase 0 by ext; simp]
    rw [card_erase_of_mem (mem_univ 0), card_univ, Nat.cast_sub (Fintype.card_pos_iff.mpr inferInstance)]
    rfl
  · have hj : jacobiSum L L = -L (-1) := by
      have h := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
      rwa [(quadraticChar_isQuadratic F).inv] at h
    have hsq : L t ^ 2 = 1 := quadraticChar_sq_one ht
    have hm : L (-1) ^ 2 = 1 := quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)
    rw [ite_eq_right ht, zero_sub]
    calc
      _ = ∑ y : F, L ((-t)*y)*L (((-t)*y)+t) :=
        (Fintype.sum_equiv (Equiv.mulLeft₀ (-t) (neg_ne_zero.mpr ht)) _ _ (fun _ => rfl)).symm
      _ = L (-1)*jacobiSum L L := by
        rw [jacobiSum, mul_sum]
        apply sum_congr rfl
        intro y _
        rw [show (-t)*y+t = t*(1-y) by ring, show (-t)*y = ((-1)*t)*y by ring]
        simp only [map_mul]
        linear_combination (L (-1)*L y*L (1-y))*hsq
      _ = -1 := by rw [hj]; nlinarith

theorem uniform_sum {X Y : Type} [Fintype X] [Fintype Y] (f : X → Y) (g : Y → ℤ) (c : ℕ)
    (hc : ∀ y, Nat.card {x // f x = y} = c) :
    (∑ x : X, g (f x)) = (c:ℤ) * ∑ y : Y, g y := by
  classical
  calc
    _ = ∑ p : (Σ y, {x // f x = y}), g p.1 :=
      Fintype.sum_equiv (Equiv.sigmaFiberEquiv f).symm _ _ (fun x => rfl)
    _ = _ := by
      rw [Fintype.sum_sigma, mul_sum]
      apply sum_congr rfl
      intro y _
      simp [← Nat.card_eq_fintype_card, hc]

omit [Fintype F] [DecidableEq F] in
theorem sum_linear {E D : Type} [AddCommGroup E] [Fintype E] [AddCommGroup D] [Fintype D]
    [Module F E] [Module F D] (f : E →ₗ[F] D) (hf : Function.Surjective f) (g : D → ℤ) :
    (∑ x : E, g (f x)) = (Nat.card f.ker : ℤ) * ∑ y : D, g y := by
  apply uniform_sum
  intro y
  exact Nat.card_congr (AddMonoidHom.fiberEquivKerOfSurjective (f := f.toAddMonoidHom) hf y)

omit [DecidableEq F] in
theorem kernel_card {E D : Type} [AddCommGroup E] [AddCommGroup D] [Module F E] [Module F D]
    [FiniteDimensional F E] [FiniteDimensional F D] (f : E →ₗ[F] D) (hf : Function.Surjective f) :
    Nat.card f.ker = (Fintype.card F)^(Module.finrank F E - Module.finrank F D) := by
  rw [Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card]
  congr 1
  have hr := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top] at hr
  omega

variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E]

omit [Fintype F] [DecidableEq F] [FiniteDimensional F E] in
theorem form_surjective (L : E →ₗ[F] F) (hL : L ≠ 0) : Function.Surjective L := by
  obtain ⟨a,ha⟩ : ∃ x, L x ≠ 0 := by contrapose! hL; ext x; simp [hL]
  intro y
  refine ⟨(y/L a) • a, ?_⟩
  simp [smul_eq_mul, ha]

def pairForm (L : E →ₗ[F] F) (a : E) : E →ₗ[F] F × F := L.prod (L.comp (LinearMap.mul F E a))

omit [Fintype F] [DecidableEq F] [FiniteDimensional F E] in
@[simp] theorem pair_apply (L : E →ₗ[F] F) (a x : E) : pairForm L a x = (L x, L (a*x)) := rfl

omit [Fintype F] [DecidableEq F] [FiniteDimensional F E] in
theorem pair_surjective (L : E →ₗ[F] F) (hL : L ≠ 0) (a : E)
    (ha : ∀ c : F, a ≠ algebraMap F E c) : Function.Surjective (pairForm L a) := by
  obtain ⟨z,hz⟩ := form_surjective L hL 1
  obtain ⟨y,hy,hya⟩ : ∃ y, L y = 0 ∧ L (a*y) ≠ 0 := by
    by_contra! H
    have prop (x : E) : L (a*x) = L x * L (a*z) := by
      have hy := H (x - (L x) • z) (by simp [hz])
      rw [mul_sub, mul_smul_comm, map_sub, map_smul, smul_eq_mul] at hy
      linear_combination hy
    let c := L (a*z)
    have nz := sub_ne_zero.mpr (ha c)
    have annih (x : E) : L ((a - algebraMap F E c)*x) = 0 := by
      rw [sub_mul, ← Algebra.smul_def, map_sub, prop, map_smul, smul_eq_mul]
      dsimp [c]
      ring
    have bad := annih ((a-algebraMap F E c)⁻¹*z)
    rw [← mul_assoc, mul_inv_cancel₀ nz, one_mul, hz] at bad
    exact one_ne_zero bad
  let y' := (L (a*y))⁻¹ • y
  have hy' : L y' = 0 := by simp [y',hy]
  have hya' : L (a*y') = 1 := by simp [y',smul_eq_mul,hya]
  let z' := z - L (a*z) • y'
  have hz' : L z' = 1 := by simp [z',hz,hy']
  have hza' : L (a*z') = 0 := by simp [z',mul_sub,hya']
  rintro ⟨u,v⟩
  exact ⟨u • z' + v • y', by simp [pair_apply, mul_add, hz', hza', hy', hya', smul_eq_mul]⟩

end Signed39.FieldConstruction
