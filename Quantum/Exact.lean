module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Tactic

/-! Exact certificates for quantum Latin squares over imaginary quadratic fields. -/

@[expose] public section

namespace QuantumCertificate

open Finset Complex
open scoped BigOperators ComplexConjugate

abbrev IQ := ℤ × ℤ
abbrev Space (n : ℕ) := EuclideanSpace ℂ (Fin n)
abbrev Cell (n : ℕ) := Fin n × Fin n

/-- The pair (a,b) stands for a + b i√d. -/
noncomputable def embed (d : ℕ) : IQ →+ ℂ where
  toFun a := ⟨a.1, a.2 * Real.sqrt d⟩
  map_zero' := by apply Complex.ext <;> simp
  map_add' a b := by apply Complex.ext <;> simp [add_mul]

def times (d : ℕ) (a b : IQ) : IQ :=
  (a.1 * b.1 - d * a.2 * b.2, a.1 * b.2 + a.2 * b.1)

def cstar (a : IQ) : IQ := (a.1, -a.2)

theorem embed_injective {d : ℕ} (hd : 0 < d) : Function.Injective (embed d) := by
  intro x y h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  change (x.1 : ℝ) = y.1 at hre
  change (x.2 : ℝ) * Real.sqrt d = y.2 * Real.sqrt d at him
  have hs : Real.sqrt (d : ℝ) ≠ 0 := by positivity
  apply Prod.ext
  · exact_mod_cast hre
  · exact_mod_cast (mul_right_cancel₀ hs him)

theorem embed_times (d : ℕ) (a b : IQ) :
    embed d (times d a b) = embed d a * embed d b := by
  have hs : Real.sqrt (d : ℝ) ^ 2 = d := Real.sq_sqrt (by positivity)
  apply Complex.ext
  · simp [embed, times, Complex.mul_re]
    nlinarith only [congrArg (fun t : ℝ => (a.2 : ℝ) * (b.2 : ℝ) * t) hs]
  · simp [embed, times, Complex.mul_im]
    ring

theorem embed_cstar (d : ℕ) (a : IQ) : embed d (cstar a) = conj (embed d a) := by
  apply Complex.ext <;> simp [embed, cstar]

@[simp] theorem embed_integer (d : ℕ) (z : ℤ) : embed d (z, 0) = (z : ℂ) := by
  apply Complex.ext <;> simp [embed]

def gram {n : ℕ} (d : ℕ) (u v : Fin n → IQ) : IQ :=
  ∑ x, times d (cstar (u x)) (v x)

noncomputable def vector {n : ℕ} (d M : ℕ) (u : Fin n → IQ) : Space n :=
  WithLp.toLp 2 (fun x => (Real.sqrt (M : ℝ) : ℂ)⁻¹ * embed d (u x))

theorem inner_vector {n : ℕ} (d M : ℕ) (u v : Fin n → IQ) :
    inner ℂ (vector d M u) (vector d M v) = (M : ℂ)⁻¹ * embed d (gram d u v) := by
  have hs : (Real.sqrt (M : ℝ) : ℂ) ^ 2 = M := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ M by positivity)
  rw [PiLp.inner_apply]
  change (∑ x, (((Real.sqrt (M : ℝ) : ℂ)⁻¹ * embed d (v x)) *
        conj ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * embed d (u x)))) = _
  rw [gram, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [embed_times, embed_cstar, map_mul, map_inv₀, Complex.conj_ofReal]
  rw [← hs, ← inv_pow]
  ring

def GramTest {n : ℕ} (d M : ℕ) (v : Fin n → Fin n → IQ) : Prop :=
  ∀ i j, gram d (v i) (v j) = if i = j then ((M : ℤ), 0) else (0, 0)

instance {n : ℕ} (d M : ℕ) (v : Fin n → Fin n → IQ) : Decidable (GramTest d M v) :=
  inferInstanceAs (Decidable (∀ i j : Fin n, gram d (v i) (v j) =
    if i = j then ((M : ℤ), 0) else (0, 0)))

theorem basis_of_test {n d M : ℕ} [NeZero n] (hM : 0 < M) (v : Fin n → Fin n → IQ)
    (h : GramTest d M v) :
    ∃ b : OrthonormalBasis (Fin n) ℂ (Space n), ⇑b = fun i => vector d M (v i) := by
  have hon : Orthonormal ℂ (fun i => vector d M (v i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [inner_vector, h i j]
    split
    · simp [Nat.ne_of_gt hM]
    · simp
  refine ⟨OrthonormalBasis.mk hon ?_, OrthonormalBasis.coe_mk _ _⟩
  exact (hon.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge

/-- Explicitly require a full orthonormal basis in both directions. Count
points of the actual complex projective space, so any global phase disappears. -/
def Realized (n c : ℕ) : Prop :=
  ∃ v : Fin n → Fin n → Space n, ∃ hn : ∀ i j, v i j ≠ 0,
    (∀ i, ∃ b : OrthonormalBasis (Fin n) ℂ (Space n), ⇑b = v i) ∧
    (∀ j, ∃ b : OrthonormalBasis (Fin n) ℂ (Space n), ⇑b = fun i => v i j) ∧
    (Set.range (fun p : Cell n => Projectivization.mk ℂ (v p.1 p.2) (hn p.1 p.2))).ncard = c

def Separated {n c : ℕ} (d : ℕ) (r : Fin c → Fin n → IQ) : Prop :=
  ∀ i j, i ≠ j → ∃ x y, times d (r i x) (r j y) ≠ times d (r i y) (r j x)

instance {n c : ℕ} (d : ℕ) (r : Fin c → Fin n → IQ) : Decidable (Separated d r) :=
  inferInstanceAs (Decidable (∀ i j : Fin c, i ≠ j → ∃ x y : Fin n,
    times d (r i x) (r j y) ≠ times d (r i y) (r j x)))

theorem of_certificate {n c d M : ℕ} [NeZero n] (hd : 0 < d) (hM : 0 < M)
    (r : Fin c → Fin n → IQ) (label : Cell n → Fin c)
    (cover : ∀ k, ∃ p, label p = k) (sep : Separated d r)
    (rows : ∀ i, GramTest d M (fun j => r (label (i,j))))
    (cols : ∀ j, GramTest d M (fun i => r (label (i,j)))) :
    Realized n c := by
  classical
  let v (i j : Fin n) := vector d M (r (label (i,j)))
  have rb (i) := basis_of_test hM _ (rows i)
  have cb (j) := basis_of_test hM _ (cols j)
  have hn (i j : Fin n) : v i j ≠ 0 := by
    obtain ⟨b,hb⟩ := rb i
    have hon := b.orthonormal
    rw [hb] at hon
    exact hon.ne_zero j
  have hrn (a : Fin c) : vector d M (r a) ≠ 0 := by
    obtain ⟨⟨i,j⟩,rfl⟩ := cover a
    exact hn i j
  let ray (a : Fin c) := Projectivization.mk ℂ (vector d M (r a)) (hrn a)
  have hinj : Function.Injective ray := by
    intro a b h
    by_contra hab
    obtain ⟨x,y,hxy⟩ := sep a b hab
    obtain ⟨t,ht⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
    have hs : (Real.sqrt (M : ℝ) : ℂ)⁻¹ ≠ 0 := by
      apply inv_ne_zero
      exact_mod_cast (show Real.sqrt (M : ℝ) ≠ 0 by positivity)
    have coord (k : Fin n) : t * embed d (r b k) = embed d (r a k) := by
      have hk := congrArg (fun w : Space n => w k) ht
      change t * (_ * embed d (r b k)) = _ * embed d (r a k) at hk
      apply mul_left_cancel₀ hs
      linear_combination hk
    apply hxy (embed_injective hd ?_)
    rw [embed_times, embed_times, ← coord x, ← coord y]
    ring
  refine ⟨v, hn, rb, cb, ?_⟩
  change (Set.range (ray ∘ label)).ncard = c
  rw [Function.Surjective.range_comp cover, Set.ncard_range_of_injective hinj]
  simp

end QuantumCertificate
