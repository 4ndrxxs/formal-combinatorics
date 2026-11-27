import Quantum.Hadamard.Extension

/-! Cardinality and pairwise intersections of hyperplanes in finite projective geometry.
The cyclic model uses the multiplicative group of a finite extension modulo base scalars. -/
noncomputable section
namespace Hadamard.PG
open Finset

def corr {G : Type} [AddCommGroup G] [Fintype G] (f : G → ℤ) (t : G) : ℤ :=
  ∑ x, f x*f (x+t)

section Linear

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
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

end Linear

section Quotient
variable (F E : Type) [Field F] [Field E] [Algebra F E]

abbrev scalarUnits : Fˣ →* Eˣ := Units.map (algebraMap F E).toMonoidHom
abbrev Projective := Eˣ ⧸ (scalarUnits F E).range
abbrev project : Eˣ →* Projective F E := QuotientGroup.mk' (scalarUnits F E).range

def chooseRep (a : Projective F E) : Eˣ := (QuotientGroup.mk'_surjective (scalarUnits F E).range a).choose

theorem project_chooseRep (a : Projective F E) : project F E (chooseRep F E a) = a :=
  (QuotientGroup.mk'_surjective (scalarUnits F E).range a).choose_spec

variable {F E} [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E] [FiniteDimensional F E]

def sec (L : E →ₗ[F] F) (x : E) : ℤ := if L x = 0 then 1 else 0
omit [Fintype F] [Fintype E] [DecidableEq E] [FiniteDimensional F E] in
theorem sec_scale (L : E →ₗ[F] F) {c : F} (hc : c ≠ 0) (x : E) :
    sec L (algebraMap F E c * x) = sec L x := by
  simp [sec, ← Algebra.smul_def, smul_eq_mul, hc]


omit [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E] [FiniteDimensional F E] in
theorem descend_project (f : E → ℤ)
    (hi : ∀ (c : F), c ≠ 0 → ∀ x : E, f (algebraMap F E c * x) = f x) (x : Eˣ) :
    f (chooseRep F E (project F E x) : E) = f (x:E) := by
  let u := chooseRep F E (project F E x)
  have hp : project F E u = project F E x := project_chooseRep F E _
  have hr : u / x ∈ (scalarUnits F E).range := QuotientGroup.eq_iff_div_mem.mp hp
  obtain ⟨c,hc⟩ := hr
  have hu : scalarUnits F E c * x = u := by rw [hc, div_mul_cancel]
  change f (u : E) = _
  rw [← hu]
  exact hi c c.ne_zero x

def sectionOn (L : E →ₗ[F] F) (a : Projective F E) : ℤ := sec L (chooseRep F E a)


omit [Fintype F] [Fintype E] [DecidableEq E] [FiniteDimensional F E] in
@[simp] theorem section_project (L : E →ₗ[F] F) (u : Eˣ) : sectionOn L (project F E u) = sec L u :=
  descend_project _ (fun _ h => sec_scale L h) _

omit [Fintype F] [DecidableEq F] [FiniteDimensional F E] in
theorem sum_units_with_zero (f : E → ℤ) :
    (∑ u : Eˣ, f u) + f 0 = ∑ x : E, f x := by
  classical
  calc
    _ = (∑ x : {x : E // x ≠ 0}, f x) + f 0 := by
      congr 1
      exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)
    _ = _ := by
      rw [← sum_subtype (univ.erase 0) (by simp) f]
      exact sum_erase_add _ _ (mem_univ _)

omit [FiniteDimensional F E] in
theorem sum_project (f : Projective F E → ℤ) :
    (∑ u : Eˣ, f (project F E u)) = ((Fintype.card F:ℤ)-1) * ∑ a : Projective F E, f a := by
  classical
  have hu : (Nat.card Fˣ : ℤ) = (Fintype.card F:ℤ)-1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, Nat.cast_sub Fintype.card_pos]
    rfl
  rw [← hu]
  apply uniform_sum
  intro a
  have hc := Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective (f := project F E)
    (QuotientGroup.mk'_surjective _ ) a)
  rw [show (project F E).ker = (scalarUnits F E).range from QuotientGroup.ker_mk' _] at hc
  exact hc.trans (Nat.card_congr (MonoidHom.ofInjective
    (Units.map_injective (algebraMap F E).injective)).symm.toEquiv)

end Quotient

section Intersections
variable {F E : Type} [Field F] [Field E] [Algebra F E] [Fintype F] [DecidableEq F]
  [Fintype E] [DecidableEq E] [FiniteDimensional F E]

abbrev addWord (f : Projective F E → ℤ) : Additive (Projective F E) → ℤ :=
  fun x => f x.toMul

omit [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E] [FiniteDimensional F E] in
theorem nonscalar (a : Eˣ) (ha : project F E a ≠ 1) (c : F) : (a:E) ≠ algebraMap F E c := by
  intro h
  have hc : c ≠ 0 := by rintro rfl; simp at h
  apply ha
  apply (QuotientGroup.eq_one_iff a).mpr
  exact ⟨Units.mk0 c hc, Units.ext h.symm⟩

omit [FiniteDimensional F E] in
theorem lifted_corr (f : Projective F E → ℤ) (raw : E → ℤ)
    (hp : ∀ u : Eˣ, f (project F E u) = raw u) (a : Eˣ) :
    ((Fintype.card F : ℤ)-1) * corr (addWord f) (Additive.ofMul (project F E a)) +
      raw 0 * raw 0 = ∑ x : E, raw x * raw (a*x) := by
  have proj := sum_project (fun z => f z * f (z * project F E a))
  have units := sum_units_with_zero (fun x => raw x * raw (a*x))
  have hadd : corr (addWord f) (Additive.ofMul (project F E a)) =
      ∑ z : Projective F E, f z * f (z * project F E a) :=
    Fintype.sum_equiv Additive.toMul _ _ (fun _ => rfl)
  rw [hadd, ← proj]
  simp only [← map_mul, hp, Units.val_mul]
  simpa only [mul_comm (a:E), zero_mul] using units

omit [DecidableEq E] in
theorem raw_section_sq (L : E →ₗ[F] F) (hL : L ≠ 0) :
    (∑ x : E, sec L x * sec L x) = (Fintype.card F : ℤ)^(Module.finrank F E-1) := by
  have hs := form_surjective L hL
  calc
    _ = ∑ x : E, (if L x = 0 then 1 else 0 : ℤ) := by
      apply sum_congr rfl
      intro x _
      by_cases hx : L x = 0 <;> simp [sec,hx]
    _ = _ := by
      have H := sum_linear L hs (fun y => if y = 0 then 1 else 0)
      rw [kernel_card L hs] at H
      simpa using H

omit [DecidableEq E] in
theorem raw_section_pair (L : E →ₗ[F] F) (hL : L ≠ 0) (a : Eˣ) (ha : project F E a ≠ 1) :
    (∑ x : E, sec L x * sec L (a*x)) = (Fintype.card F : ℤ)^(Module.finrank F E-2) := by
  have hs := pair_surjective L hL a (nonscalar a ha)
  calc
    _ = ∑ x : E, (if pairForm L a x = 0 then 1 else 0 : ℤ) := by
      apply sum_congr rfl
      intro x _
      by_cases h : L x = 0 <;> by_cases h' : L (a*x) = 0 <;>
        simp [sec, h, h', Prod.ext_iff]
    _ = _ := by
      have H := sum_linear _ hs (fun y => if y = 0 then 1 else 0)
      rw [kernel_card _ hs, Module.finrank_prod] at H
      simpa using H

def geom (q n : ℕ) : ℕ := ∑ i ∈ range n, q^i

theorem cast_geom (q n : ℕ) : (geom q n : ℤ) = ∑ i ∈ range n, (q:ℤ)^i := by
  simp [geom]

theorem geom_int (q n : ℕ) : (geom q n : ℤ)*((q:ℤ)-1) = (q:ℤ)^n-1 := by
  rw [cast_geom, geom_sum_mul]

theorem section_corr (L : E →ₗ[F] F) (hL : L ≠ 0) (n : ℕ) (hm : Module.finrank F E = n+2)
    (z : Additive (Projective F E)) :
    corr (addWord (sectionOn L)) z =
      (if z = 0 then (Fintype.card F:ℤ)^n else 0) + (geom (Fintype.card F) n : ℤ) := by
  let q := Fintype.card F
  have hq : (q:ℤ)-1 ≠ 0 := by have h := Fintype.one_lt_card (α := F); omega
  have hg := geom_int q n
  have rawzero : sec L 0 = 1 := by simp [sec]
  by_cases hz : z = 0
  · subst z
    rw [ite_eq_left rfl]
    have H := lifted_corr (sectionOn L) (sec L) (section_project L) (1:Eˣ)
    rw [map_one, show Additive.ofMul (1 : Projective F E) = 0 from rfl] at H
    simp only [Units.val_one, one_mul, rawzero] at H
    rw [raw_section_sq L hL, hm, show n+2-1 = n+1 by omega, pow_succ] at H
    apply mul_left_cancel₀ hq
    linear_combination H - hg
  · rw [ite_eq_right hz, zero_add]
    let a := chooseRep F E z.toMul
    have ha : project F E a = z.toMul := project_chooseRep F E _
    have hne : project F E a ≠ 1 := fun h => hz (ha.symm.trans h)
    have H := lifted_corr (sectionOn L) (sec L) (section_project L) a
    rw [ha, show Additive.ofMul z.toMul = z from rfl] at H
    simp only [rawzero, one_mul] at H
    rw [raw_section_pair L hL a hne, hm, show n+2-2 = n by omega] at H
    apply mul_left_cancel₀ hq
    linear_combination H - hg
omit [FiniteDimensional F E] in
theorem projective_card :
    Nat.card (Projective F E) = geom (Fintype.card F) (Module.finrank F E) := by
  have hq : (Fintype.card F:ℤ)-1 ≠ 0 := by have h := Fintype.one_lt_card (α := F); omega
  have h := sum_project (F := F) (E := E) (fun _ => 1)
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  rw [Fintype.card_units, Nat.cast_sub Fintype.card_pos,
    Module.card_eq_pow_finrank (K := F) (V := E), Nat.cast_pow] at h
  have hg := geom_int (Fintype.card F) (Module.finrank F E)
  rw [Nat.card_eq_fintype_card]
  apply Nat.cast_injective (R := ℤ)
  apply mul_left_cancel₀ hq
  linear_combination -h - hg

end Intersections

theorem geom_succ (q n : ℕ) : geom q (n+1) = 1 + geom q n * q := by
  rw [geom, sum_range_succ']
  simp only [pow_zero, pow_succ, ← sum_mul, geom, add_comm]

end Hadamard.PG

