import PaleyLinPhoa

/-! Power-indexed Jacobi products in rows (5) and (6) of Table 1.6 of
Momihara, Suda and Xiang. -/

noncomputable section

open Finset Hadamard.MSXCore Hadamard.NearBorder

namespace Hadamard.LinPhoa

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

private theorem square_ne_zero (x : SquareIndex F) : x.val ≠ 0 := by
  intro h
  have hx := x.property
  rw [h] at hx
  norm_num at hx

private def squareRestriction {m : ℕ} [NeZero m] (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val = (e k).val / (e l).val) (ψ : MulChar F ℂ) :
    AddChar (Fin m) ℂ where
  toFun k := ψ (e k).val
  map_zero_eq_one' := by
    have h := cyc 0 0
    rw [sub_self, div_self (square_ne_zero _)] at h
    rw [h, map_one]
  map_add_eq_mul' k l := by rw [enum_add e cyc, map_mul]

/-- The first half of the powers of a primitive field character restrict
bijectively to the characters of the nonzero squares. -/
private theorem power_index_equiv {m : ℕ} [NeZero m] (e : Fin m ≃ SquareIndex F)
    (cyc : ∀ k l, (e (k-l)).val = (e k).val / (e l).val) (χ : MulChar F ℂ)
    (primitive : orderOf χ = 2*m) :
    ∃ E : Fin m ≃ AddChar (Fin m) ℂ, E 0 = 0 ∧
      ∀ j k, E j k = (χ ^ j.val) (e k).val := by
  classical
  let f (j : Fin m) := squareRestriction e cyc (χ ^ j.val)
  have inj : Function.Injective f := by
    intro a b hab
    have doubled : χ ^ (2*a.val) = χ ^ (2*b.val) := by
      apply MulChar.ext
      intro u
      let s : SquareIndex F := ⟨(u:F)^2, quadraticChar_sq_one' u.ne_zero⟩
      have h := congrArg (fun θ : AddChar (Fin m) ℂ ↦ θ (e.symm s)) hab
      change (χ ^ a.val) (e (e.symm s)).val = (χ ^ b.val) (e (e.symm s)).val at h
      rw [e.apply_symm_apply] at h
      change (χ ^ a.val) ((u:F)^2) = (χ ^ b.val) ((u:F)^2) at h
      simp only [map_pow, MulChar.pow_apply_coe] at h
      simpa only [MulChar.pow_apply_coe, Nat.mul_comm 2, pow_mul] using h
    have ltOrder (j : Fin m) : 2*j.val ∈ Set.Iio (orderOf χ) := by
      change 2*j.val < orderOf χ
      rw [primitive]
      omega
    have h := pow_injOn_Iio_orderOf (ltOrder a) (ltOrder b) doubled
    apply Fin.ext
    omega
  let E := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card _).mpr ⟨inj, by simp⟩)
  refine ⟨E, ?_, fun _ _ ↦ rfl⟩
  apply AddChar.ext
  intro k
  change (χ ^ (0 : Fin m).val) (e k).val = 1
  rw [Fin.val_zero, pow_zero]
  exact MulChar.one_apply (isUnit_iff_ne_zero.mpr (square_ne_zero _))

private theorem prod_nonzero_fin_eq_Icc {m : ℕ} [NeZero m] (g : ℕ → ℂ) :
    (∏ j ∈ (univ : Finset (Fin m)).erase 0, g j.val) = ∏ j ∈ Icc 1 (m-1), g j := by
  classical
  refine prod_nbij Fin.val ?_ Fin.val_injective.injOn ?_ (by intros; rfl)
  · intro j hj
    have hj' : j ≠ 0 := (mem_erase.mp hj).1
    have ne : j.val ≠ 0 := fun h ↦ hj' (Fin.ext (by simpa using h))
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro j hj
    obtain ⟨h₁, h₂⟩ := mem_Icc.mp hj
    have hm := NeZero.pos m
    let t : Fin m := ⟨j, by omega⟩
    refine ⟨t, mem_erase.mpr ⟨?_, mem_univ _⟩, rfl⟩
    intro z
    have h := congrArg Fin.val z
    change j = 0 at h
    omega

private theorem reindex_power_product {m : ℕ} [NeZero m] (E : Fin m ≃ AddChar (Fin m) ℂ)
    (zero : E 0 = 0) (g : ℕ → ℂ) :
    (∏ θ ∈ (univ : Finset (AddChar (Fin m) ℂ)).erase 0, g (E.symm θ).val) =
      ∏ j ∈ Icc 1 (m-1), g j := by
  classical
  calc
    _ = ∏ j ∈ (univ : Finset (Fin m)).erase 0, g j.val := by
      apply prod_equiv E.symm
      · intro θ
        simp only [mem_erase, mem_univ, and_true]
        constructor
        · intro h z
          apply h
          rw [← E.apply_symm_apply θ, z, zero]
        · intro h z
          apply h
          rw [z, ← zero, E.symm_apply_apply]
      · intros; rfl
    _ = _ := prod_nonzero_fin_eq_Icc g

private def jacobiFactor (i : Bool) (ψ : MulChar F ℂ) : ℂ :=
  (Fintype.card F : ℂ) + 1 - (cosetSign i : ℂ) *
    (jacobiSum ψ (eta F) + jacobiSum (ψ * eta F) (eta F))

private def jacobiPrefactor (F : Type) [Fintype F] (i : Bool) : ℝ :=
  if i then ((Fintype.card F : ℝ)-1)^2 else ((Fintype.card F : ℝ)+1)^2+4

private theorem row_five_factor (ψ : MulChar F ℂ) :
    jacobiFactor true ψ = (Fintype.card F : ℂ) + 1 +
      jacobiSum (eta F * ψ) (eta F) + jacobiSum ψ (eta F) := by
  rw [jacobiFactor, mul_comm ψ (eta F)]
  norm_num [cosetSign]
  ring

private theorem row_six_factor (ψ : MulChar F ℂ) :
    jacobiFactor false ψ = (Fintype.card F : ℂ) + 1 -
      jacobiSum (eta F * ψ) (eta F) - jacobiSum ψ (eta F) := by
  rw [jacobiFactor, mul_comm ψ (eta F)]
  norm_num [cosetSign]
  ring

open scoped ComplexOrder

private theorem power_product_bound (q4 : Fintype.card F % 4 = 1) (lo : 29 ≤ Fintype.card F)
    (χ : MulChar F ℂ) (primitive : orderOf χ = Fintype.card F - 1) (i : Bool) :
    (((4/5 : ℝ) * (2*(Fintype.card F : ℝ)) *
      ((Fintype.card F : ℝ)-1)^(Fintype.card F/2) : ℝ) : ℂ) ≤
    (jacobiPrefactor F i : ℂ) *
      ∏ j ∈ Icc 1 ((Fintype.card F-3)/2), jacobiFactor i (χ^j) := by
  classical
  let n := (Fintype.card F-3)/2
  have hc : ringChar F ≠ 2 := by
    intro h
    have := FiniteField.even_card_of_char_two h
    omega
  obtain ⟨w, hw⟩ := quadraticChar_exists_neg_one (F:=F) hc
  have cardq : Fintype.card F = 2*(n+1)+1 := by dsimp [n]; omega
  obtain ⟨e, cyc⟩ := exists_square_enumeration (n:=n)
    ((square_index_card w hw).trans (by omega))
  obtain ⟨E, zero, powers⟩ := power_index_equiv e cyc χ (by rw [primitive]; omega)
  let liftChar (θ : AddChar (Fin (n+1)) ℂ) := χ ^ (E.symm θ).val
  have extendsOn (θ : AddChar (Fin (n+1)) ℂ) (k : Fin (n+1)) :
      liftChar θ (e k).val = θ k := by
    simpa only [liftChar, E.apply_symm_apply] using (powers (E.symm θ) k).symm
  have reindex : (∏ θ ∈ (univ : Finset (AddChar (Fin (n+1)) ℂ)).erase 0,
      jacobiFactor i (liftChar θ)) = ∏ j ∈ Icc 1 n, jacobiFactor i (χ^j) := by
    simpa only [liftChar, Nat.add_sub_cancel] using
      reindex_power_product E zero (fun j ↦ jacobiFactor i (χ^j))
  have bound := two_jacobi_bounds q4 lo e cyc liftChar extendsOn i
  change _ ≤ jacobiPrefactor F i *
    ‖∏ θ ∈ (univ : Finset (AddChar (Fin (n+1)) ℂ)).erase 0, jacobiFactor i (liftChar θ)‖ at bound
  rw [reindex] at bound
  have pref : 2*((orientation true*(if i then 0 else -2)-((n+1 : ℕ) : ℝ))^2+
      ((n+1 : ℕ) : ℝ)^2) = jacobiPrefactor F i := by
    rw [jacobiPrefactor, cardq]
    cases i <;> norm_num [orientation] <;> ring
  have detEq := array_jacobi_product hc q4 w hw i false true e cyc liftChar extendsOn
  rw [pref] at detEq
  change ((|(array true (sourcePair w i false e)).det| : ℝ) : ℂ) = (jacobiPrefactor F i : ℂ) *
    ∏ θ ∈ (univ : Finset (AddChar (Fin (n+1)) ℂ)).erase 0, jacobiFactor i (liftChar θ) at detEq
  rw [reindex] at detEq
  change _ ≤ (jacobiPrefactor F i : ℂ) * ∏ j ∈ Icc 1 n, jacobiFactor i (χ^j)
  rw [← detEq, Complex.real_le_real]
  have prefNonneg : 0 ≤ jacobiPrefactor F i := by
    unfold jacobiPrefactor
    split <;> positivity
  have mag := congrArg (norm (E:=ℂ)) detEq
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs, abs_of_nonneg prefNonneg] at mag
  exact bound.trans_eq mag.symm

/-- Both Jacobi products of MSX Table 1.6 are at least four fifths of the
Ehlich–Wojtas bound for every eligible field of order at least 29 and every
multiplicative character of order `q-1`. The complex order records that both
displayed products have zero imaginary part. -/
theorem msx_table_rows_five_six (q4 : Fintype.card F % 4 = 1) (lo : 29 ≤ Fintype.card F)
    (χ : MulChar F ℂ) (primitive : orderOf χ = Fintype.card F - 1) :
    let q := Fintype.card F
    let η := eta F
    let B : ℂ := (4/5) * (2*(q:ℂ)) * ((q:ℂ)-1)^(q/2)
    B ≤ ((q:ℂ)-1)^2 * ∏ j ∈ Icc 1 ((q-3)/2),
        ((q:ℂ)+1 + jacobiSum (η*χ^j) η + jacobiSum (χ^j) η) ∧
    B ≤ ((q:ℂ)^2+2*(q:ℂ)+5) * ∏ j ∈ Icc 1 ((q-3)/2),
        ((q:ℂ)+1 - jacobiSum (η*χ^j) η - jacobiSum (χ^j) η) := by
  let q := Fintype.card F
  have five := power_product_bound q4 lo χ primitive true
  have six := power_product_bound q4 lo χ primitive false
  simp only [row_five_factor] at five
  simp only [row_six_factor] at six
  have prefFive : (jacobiPrefactor F true : ℂ) = ((q:ℂ)-1)^2 := by simp [jacobiPrefactor, q]
  have prefSix : (jacobiPrefactor F false : ℂ) = (q:ℂ)^2+2*(q:ℂ)+5 := by
    simp [jacobiPrefactor, q]
    ring
  rw [prefFive] at five
  rw [prefSix] at six
  push_cast at five six
  exact ⟨five, six⟩

#print axioms msx_table_rows_five_six

end Hadamard.LinPhoa