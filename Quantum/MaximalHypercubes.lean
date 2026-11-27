module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic

/-!
# Quantum Latin hypercubes of every dimension and every order at least four

The matrix block in a Fourier basis of unitaries separates the projective
points after a generic diagonal phase is inserted between successive axes.
-/

@[expose] public section
noncomputable section

namespace MaximalHypercubes

open Finset Complex Matrix
open scoped BigOperators ComplexConjugate Matrix

abbrev M := Matrix (Fin 2) (Fin 2) ℂ
abbrev A (r : ℕ) := M × (Fin r → ℂ)

def Gram {r : ℕ} (a b : A r) : ℂ :=
  2 * Matrix.trace (a.1ᴴ * b.1) + ∑ i, conj (a.2 i) * b.2 i

def IsUnitary {r : ℕ} (a : A r) : Prop :=
  a.1ᴴ * a.1 = 1 ∧ a.1 * a.1ᴴ = 1 ∧ ∀ i, conj (a.2 i) * a.2 i = 1

theorem unitary_one (r : ℕ) : IsUnitary (1 : A r) := by
  simp [IsUnitary]

theorem unitary_mul {r : ℕ} {a b : A r} (ha : IsUnitary a) (hb : IsUnitary b) :
    IsUnitary (a * b) := by
  rcases ha with ⟨ha, ha', hs⟩
  rcases hb with ⟨hb, hb', ht⟩
  refine ⟨?_, ?_, fun i => ?_⟩
  · change (a.1 * b.1)ᴴ * (a.1 * b.1) = 1
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc a.1ᴴ, ha, one_mul, hb]
  · change (a.1 * b.1) * (a.1 * b.1)ᴴ = 1
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc b.1, hb', one_mul, ha']
  · change conj (a.2 i * b.2 i) * (a.2 i * b.2 i) = 1
    rw [map_mul, mul_mul_mul_comm, hs, ht, one_mul]

theorem Gram_left {r : ℕ} (a b c : A r) (h : IsUnitary c) :
    Gram (c * a) (c * b) = Gram a b := by
  unfold Gram
  simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, conjTranspose_mul, map_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc c.1ᴴ, h.1, one_mul]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [mul_mul_mul_comm, h.2.2, one_mul]

theorem Gram_right {r : ℕ} (a b c : A r) (h : IsUnitary c) :
    Gram (a * c) (b * c) = Gram a b := by
  unfold Gram
  simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, conjTranspose_mul, map_mul]
  rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc b.1, h.2.1, mul_one]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [mul_mul_mul_comm, h.2.2, mul_one]

def phase {q : ℕ} [NeZero q] (x : Fin q) : ℂ :=
  ZMod.stdAddChar (ZMod.finEquiv q x)

theorem phase_injective (q : ℕ) [NeZero q] : Function.Injective (@phase q _) :=
  ZMod.injective_stdAddChar.comp (ZMod.finEquiv q).injective

theorem phase_unit {q : ℕ} [NeZero q] (x : Fin q) : conj (phase x) * phase x = 1 := by
  simp [phase, ZMod.stdAddChar_apply, Complex.conj_mul']

theorem phase_ne {q : ℕ} [NeZero q] (x : Fin q) : phase x ≠ 0 := by
  intro hx
  simpa [hx] using phase_unit x

def scale2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

theorem scale2_conj : conj scale2 = scale2 := by simp [scale2]

theorem scale2_sq : 2 * scale2 * scale2 = 1 := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  unfold scale2
  field_simp
  linear_combination -hs

theorem scale2_ne : scale2 ≠ 0 := by
  intro hz
  simpa [hz] using scale2_sq

def columns (w : ℂ) : M :=
  !![scale2, scale2 * w^2; scale2 * w, -(scale2 * w^3)]

def basisUnitary {r : ℕ} (i : Fin (r+4)) : A r :=
  (columns (phase i), fun k => phase i ^ (k.val+4))

theorem columns_unitary {w : ℂ} (hw : conj w * w = 1) :
    (columns w)ᴴ * columns w = 1 ∧ columns w * (columns w)ᴴ = 1 := by
  have hh : scale2 * scale2 + scale2 * scale2 = 1 := by linear_combination scale2_sq
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [columns, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
       scale2_conj, pow_succ] <;>
    grind

theorem basis_isUnitary {r : ℕ} (x : Fin (r+4)) : IsUnitary (basisUnitary x) := by
  have h := columns_unitary (phase_unit x)
  refine ⟨h.1, h.2, fun i => ?_⟩
  change conj (phase x ^ (i.val+4)) * phase x ^ (i.val+4) = 1
  rw [map_pow, ← mul_pow, phase_unit, one_pow]

theorem phase_pow_card {q : ℕ} [NeZero q] (x : Fin q) : phase x ^ q = 1 := by
  unfold phase
  rw [← AddChar.map_nsmul_eq_pow]
  simp [nsmul_eq_mul]

theorem fourier_gram {q : ℕ} [NeZero q] (x y : Fin q) :
    (∑ k : Fin q, conj (phase x) ^ k.val * phase y ^ k.val) =
      if x=y then (q : ℂ) else 0 := by
  simp_rw [← mul_pow]
  by_cases h : x = y
  · subst y
    simp [phase_unit]
  · rw [ite_eq_right h, Fin.sum_univ_eq_sum_range]
    have hne : conj (phase x) * phase y ≠ 1 := by
      intro he
      apply h
      apply phase_injective q
      have hn : conj (phase x) ≠ 0 := by simp [phase_ne]
      exact mul_left_cancel₀ hn ((phase_unit x).trans he.symm)
    have hp : (conj (phase x) * phase y)^q = 1 := by
      rw [mul_pow, ← map_pow, phase_pow_card, phase_pow_card, map_one, one_mul]
    have hg := geom_sum_mul (conj (phase x) * phase y) q
    rw [hp, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_right (sub_ne_zero.mpr hne)

theorem basis_gram {r : ℕ} (x y : Fin (r+4)) :
    Gram (basisUnitary x) (basisUnitary y) = if x=y then ((r+4 : ℕ) : ℂ) else 0 := by
  rw [← fourier_gram x y]
  simp only [Gram, basisUnitary, columns, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  simp [Fin.sum_univ_succ, scale2_conj]
  have h := scale2_sq
  grind

def interleaver {r : ℕ} (z : ℂ) : A r := (!![1,0;0,z], 1)

theorem interleaver_unitary {r : ℕ} {z : ℂ} (hz : conj z * z = 1) :
    IsUnitary (interleaver (r := r) z) := by
  refine ⟨?_, ?_, by simp [interleaver]⟩ <;>
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [interleaver, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, hz,
      mul_comm z]

def firstDet (a b : M) : ℂ := a 0 0 * b 1 0 - a 1 0 * b 0 0

def collisionPolynomial (a b : M) (w t : ℂ) : Polynomial ℂ :=
  (Polynomial.C (a 0 0) + Polynomial.X * Polynomial.C (w * a 0 1)) *
  (Polynomial.C (b 1 0) + Polynomial.X * Polynomial.C (t * b 1 1)) -
  (Polynomial.C (a 1 0) + Polynomial.X * Polynomial.C (w * a 1 1)) *
  (Polynomial.C (b 0 0) + Polynomial.X * Polynomial.C (t * b 0 1))

theorem collisionPolynomial_zero (a b : M) (w t : ℂ) :
    (collisionPolynomial a b w t).eval 0 = firstDet a b := by
  simp [collisionPolynomial, firstDet]

theorem collisionPolynomial_self (a : M) (w t : ℂ) :
    (collisionPolynomial a a w t).eval 1 = (t-w) * a.det := by
  simp [collisionPolynomial, Matrix.det_fin_two]
  ring

theorem collisionPolynomial_eval (a b : M) (w t z : ℂ) :
    firstDet ((a * !![1,0;0,z]) * columns w) ((b * !![1,0;0,z]) * columns t) =
       scale2^2 * (collisionPolynomial a b w t).eval z := by
  simp [firstDet, collisionPolynomial, columns, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- A finite family of nonzero complex polynomials misses a common unit phase.
The candidate phases are the roots of unity of an explicit finite order. -/
theorem avoid_polynomials {ι : Type*} [Fintype ι] (p : ι → Polynomial ℂ)
    (hp : ∀ i, p i ≠ 0) : ∃ z : ℂ, conj z * z = 1 ∧ ∀ i, (p i).eval z ≠ 0 := by
  classical
  let bad : Finset ℂ := Finset.univ.biUnion (fun i => (p i).roots.toFinset)
  let roots := Finset.univ.image (@phase (bad.card+1) _)
  have hc : bad.card < roots.card := by
    unfold roots
    rw [Finset.card_image_of_injective _ (phase_injective _)]
    simp
  have hn : ¬ roots ⊆ bad := fun h => hc.not_ge (Finset.card_le_card h)
  obtain ⟨z, hz, hbad⟩ := Finset.not_subset.mp hn
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
  refine ⟨phase j, phase_unit j, fun i he => hbad ?_⟩
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Multiset.mem_toFinset.mpr
    ((Polynomial.mem_roots (hp i)).mpr he)⟩

theorem det_ne {r : ℕ} {a : A r} (hu : IsUnitary a) : a.1.det ≠ 0 := by
  intro hz
  have h := congrArg Matrix.det hu.1
  simp [Matrix.det_mul, hz] at h

theorem extend_separated {r : ℕ} {ι : Type*} [Fintype ι] (p : ι → A r)
    (hu : ∀ i, IsUnitary (p i))
    (hs : Pairwise (fun a b => firstDet (p a).1 (p b).1 ≠ 0)) :
    ∃ z : ℂ, conj z * z = 1 ∧ Pairwise (fun a b : ι × Fin (r+4) =>
      firstDet (p a.1 * interleaver z * basisUnitary a.2).1
               (p b.1 * interleaver z * basisUnitary b.2).1 ≠ 0) := by
  classical
  let J := ι × Fin (r+4)
  let I := { s : J × J // s.1 ≠ s.2 }
  let P : I → Polynomial ℂ := fun s => collisionPolynomial (p s.val.1.1).1 (p s.val.2.1).1
    (phase s.val.1.2) (phase s.val.2.2)
  have hP (s : I) : P s ≠ 0 := by
    rcases s with ⟨⟨⟨a,x⟩, ⟨b,y⟩⟩, h⟩
    change collisionPolynomial (p a).1 (p b).1 (phase x) (phase y) ≠ 0
    intro he
    by_cases hab : a = b
    · subst b
      have hxy : y ≠ x := by
        intro e
        apply h
        simp [e]
      have hh := congrArg (Polynomial.eval 1) he
      rw [collisionPolynomial_self, Polynomial.eval_zero] at hh
      exact (mul_ne_zero (sub_ne_zero.mpr (fun eq => hxy (phase_injective _ eq)))
        (det_ne (hu a))) hh
    · apply hs hab
      simpa only [collisionPolynomial_zero, Polynomial.eval_zero] using
        congrArg (Polynomial.eval 0) he
  obtain ⟨z, hz, good⟩ := avoid_polynomials P hP
  refine ⟨z, hz, ?_⟩
  intro a b h
  change firstDet (((p a.1).1 * !![1,0;0,z]) * columns (phase a.2))
                  (((p b.1).1 * !![1,0;0,z]) * columns (phase b.2)) ≠ 0
  rw [collisionPolynomial_eval]
  exact mul_ne_zero (pow_ne_zero _ scale2_ne) (good (⟨(a,b), h⟩ : I))

abbrev Grid (q d : ℕ) := Fin d → Fin q

def tail {q d : ℕ} (a : Grid q (d+1)) : Grid q d := fun i => a i.succ

structure Good {r d : ℕ} (p : Grid (r+4) d → A r) : Prop where
  unitary : ∀ a, IsUnitary (p a)
  separated : Pairwise (fun a b => firstDet (p a).1 (p b).1 ≠ 0)
  line : ∀ (k : Fin d) a b, (∀ j, j ≠ k → a j = b j) →
    Gram (p a) (p b) = if a k = b k then ((r+4 : ℕ) : ℂ) else 0

theorem good_exists (r d : ℕ) : ∃ p : Grid (r+4) d → A r, Good p := by
  induction d with
  | zero =>
    refine ⟨fun _ => 1, fun _ => unitary_one _, ?_, fun k => Fin.elim0 k⟩
    exact fun a b h => (h (Subsingleton.elim a b)).elim
  | succ d ih =>
    obtain ⟨p,hp⟩ := ih
    obtain ⟨z, hz, hsep⟩ := extend_separated p hp.unitary hp.separated
    let c : A r := interleaver z
    have hc : IsUnitary c := interleaver_unitary hz
    refine ⟨fun a => p (tail a) * c * basisUnitary (a 0), ?_, ?_, ?_⟩
    · exact fun a => unitary_mul (unitary_mul (hp.unitary _) hc) (basis_isUnitary _)
    · intro a b hab
      apply hsep (i := (tail a,a 0)) (j := (tail b,b 0))
      intro he
      apply hab
      funext k
      exact Fin.cases (congrArg Prod.snd he)
        (fun u => congrFun (congrArg Prod.fst he) u) k
    · intro k
      refine Fin.cases ?_ (fun u => ?_) k
      · intro a b ho
        have ht : tail a = tail b := funext fun i => ho _ (Fin.succ_ne_zero i)
        rw [ht, Gram_left _ _ _ (unitary_mul (hp.unitary _) hc), basis_gram]
      · intro a b ho
        have h0 : a 0 = b 0 := ho _ (Fin.succ_ne_zero _).symm
        rw [h0, Gram_right _ _ _ (basis_isUnitary _), Gram_right _ _ _ hc]
        exact hp.line u (tail a) (tail b) fun i h => ho i.succ
          (fun he => h (Fin.succ_injective _ he))

theorem Gram_self {r : ℕ} {a : A r} (ha : IsUnitary a) :
    Gram a a = ((r+4 : ℕ) : ℂ) := by
  simp [Gram, ha.1, ha.2.2, Matrix.trace_one]
  ring

abbrev Space (q : ℕ) := EuclideanSpace ℂ (Fin q)

def unpack {r : ℕ} (a : A r) : Fin (r+4) → ℂ :=
  Fin.cons (2 * scale2 * a.1 0 0) (Fin.cons (2 * scale2 * a.1 1 0)
    (Fin.cons (2 * scale2 * a.1 0 1) (Fin.cons (2 * scale2 * a.1 1 1) a.2)))

theorem unpack_gram {r : ℕ} (a b : A r) :
    (∑ i, unpack b i * conj (unpack a i)) = Gram a b := by
  simp [Gram, unpack, Fin.sum_univ_succ, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose_apply, scale2_conj, map_ofNat, mul_comm (b.2 _)]
  have h := scale2_sq
  grind

def normalizer (q : ℕ) : ℂ := ((Real.sqrt q : ℝ) : ℂ)⁻¹

theorem normalizer_ne {q : ℕ} [NeZero q] : normalizer q ≠ 0 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  simp [normalizer, hq.ne']

theorem normalizer_sq (q : ℕ) : normalizer q * conj (normalizer q) = (q : ℂ)⁻¹ := by
  have hs : ((Real.sqrt q : ℝ) : ℂ)^2 = (q : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg q)
  simp [normalizer, ← sq, hs]

def vector {r : ℕ} (a : A r) : Space (r+4) :=
  WithLp.toLp 2 (fun i => normalizer (r+4) * unpack a i)

theorem vector_gram {r : ℕ} (a b : A r) :
    inner ℂ (vector a) (vector b) = ((r+4 : ℕ) : ℂ)⁻¹ * Gram a b := by
  rw [PiLp.inner_apply]
  change (∑ i, (normalizer (r+4) * unpack b i) * conj (normalizer (r+4) * unpack a i)) = _
  rw [← unpack_gram, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, mul_mul_mul_comm, normalizer_sq]

theorem order_ne (r : ℕ) : ((r+4 : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast (show r+4 ≠ 0 by omega)

theorem vector_ne {r : ℕ} {a : A r} (ha : IsUnitary a) : vector a ≠ 0 := by
  apply (inner_self_ne_zero (𝕜 := ℂ)).mp
  rw [vector_gram, Gram_self ha, inv_mul_cancel₀ (order_ne r)]
  exact one_ne_zero

theorem separated_rays {r d : ℕ} {p : Grid (r+4) d → A r} (hp : Good p) :
    Function.Injective (fun a =>
      Projectivization.mk ℂ (vector (p a)) (vector_ne (hp.unitary a))) := by
  intro a b hr
  by_contra hn
  apply hp.separated hn
  obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hr
  have h0 := congrArg (fun v : Space (r+4) => v 0) ht
  have h1 := congrArg (fun v : Space (r+4) => v (0 : Fin (r+3)).succ) ht
  change t * (normalizer (r+4) * (2 * scale2 * (p b).1 0 0)) =
      normalizer (r+4) * (2 * scale2 * (p a).1 0 0) at h0
  change t * (normalizer (r+4) * (2 * scale2 * (p b).1 1 0)) =
      normalizer (r+4) * (2 * scale2 * (p a).1 1 0) at h1
  have hh := @normalizer_ne (r+4) inferInstance
  have hs := scale2_ne
  unfold firstDet
  grind

/-- A proof of maximal cardinality uses an orthonormal basis on every coordinate
line and counts the actual projectivized nonzero vectors in the full array. -/
theorem maximal_hypercubes (q d : ℕ) (hq : 4 ≤ q) :
    ∃ (v : (Fin d → Fin q) → EuclideanSpace ℂ (Fin q))
      (nz : ∀ a, v a ≠ 0),
      (∀ (k : Fin d) a, ∃ b : OrthonormalBasis (Fin q) ℂ (EuclideanSpace ℂ (Fin q)),
        ⇑b = fun x => v (Function.update a k x)) ∧
      (Set.range (fun a => Projectivization.mk ℂ (v a) (nz a))).ncard = q^d := by
  classical
  obtain ⟨r, rfl⟩ : ∃ r, q = r+4 := ⟨q-4, by omega⟩
  obtain ⟨p, hp⟩ := good_exists r d
  refine ⟨fun a => vector (p a), fun a => vector_ne (hp.unitary a), ?_, ?_⟩
  · intro k a
    have hOrtho : Orthonormal ℂ (fun x => vector (p (Function.update a k x))) := by
      rw [orthonormal_iff_ite]
      intro x y
      rw [vector_gram, hp.line k _ _ (fun j hj => by simp [Function.update_of_ne hj])]
      simp only [Function.update_self]
      split <;> simp only [inv_mul_cancel₀ (order_ne r), mul_zero]
    refine ⟨OrthonormalBasis.mk hOrtho ?_, OrthonormalBasis.coe_mk _ _⟩
    exact (hOrtho.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge
  · rw [Set.ncard_range_of_injective (separated_rays hp)]
    simp [Nat.card_eq_fintype_card, Grid]

#print axioms maximal_hypercubes

end MaximalHypercubes
