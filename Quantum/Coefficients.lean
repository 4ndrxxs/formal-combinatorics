module

public import Quantum.Exact
public import Mathlib.NumberTheory.Real.Irrational

/-! Finite certificates with independently normalized vectors. Multiplication,
conjugation and a faithful embedding of the coefficient representation into
the complex numbers suffice. -/

@[expose] public section

namespace QuantumCertificate

open Finset Complex
open scoped BigOperators ComplexConjugate

structure Coefficients (T : Type) [AddCommMonoid T] where
  eval : T →+ ℂ
  faithful : Function.Injective eval
  mul : T → T → T
  mul_eval : ∀ x y, eval (mul x y) = eval x * eval y
  bar : T → T
  bar_eval : ∀ x, eval (bar x) = conj (eval x)

namespace Coefficients

variable {T : Type} [AddCommMonoid T] (a : Coefficients T)

def dot {n : ℕ} (u v : Fin n → T) : T := ∑ k, a.mul (a.bar (u k)) (v k)

noncomputable def raw {n : ℕ} (u : Fin n → T) : Space n :=
  WithLp.toLp 2 (fun x => a.eval (u x))

theorem raw_inner {n : ℕ} (u v : Fin n → T) :
    inner ℂ (a.raw u) (a.raw v) = a.eval (a.dot u v) := by
  rw [PiLp.inner_apply, dot, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  change a.eval (v x) * conj (a.eval (u x)) = _
  rw [a.mul_eval, a.bar_eval, mul_comm]

private noncomputable def unitVec {n : ℕ} (x : Space n) : Space n := (‖x‖ : ℂ)⁻¹ • x

private theorem unitVec_norm {n : ℕ} {x : Space n} (hx : x ≠ 0) : ‖unitVec x‖ = 1 := by
  simp [unitVec, norm_smul, Complex.norm_real, norm_ne_zero_iff.mpr hx]

def Orthogonal {n : ℕ} (v : Fin n → Fin n → T) : Prop :=
  ∀ i j, i ≠ j → a.dot (v i) (v j) = 0

instance [DecidableEq T] {n : ℕ} (v : Fin n → Fin n → T) : Decidable (a.Orthogonal v) :=
  inferInstanceAs (Decidable (∀ i j : Fin n, i ≠ j → a.dot (v i) (v j) = 0))

def DistinctLines {n c : ℕ} (r : Fin c → Fin n → T) : Prop :=
  ∀ i j, i ≠ j → ∃ x y, a.mul (r i x) (r j y) ≠ a.mul (r i y) (r j x)

instance [DecidableEq T] {n c : ℕ} (r : Fin c → Fin n → T) : Decidable (a.DistinctLines r) :=
  inferInstanceAs (Decidable (∀ i j : Fin c, i ≠ j → ∃ x y : Fin n,
    a.mul (r i x) (r j y) ≠ a.mul (r i y) (r j x)))

private theorem basis_of_orthogonal {n : ℕ} [NeZero n] (v : Fin n → Fin n → T)
    (h : a.Orthogonal v) (hne : ∀ i, a.raw (v i) ≠ 0) :
    ∃ b : OrthonormalBasis (Fin n) ℂ (Space n), ⇑b = fun i => unitVec (a.raw (v i)) := by
  have hon : Orthonormal ℂ (fun i => unitVec (a.raw (v i))) := by
    refine ⟨fun i => unitVec_norm (hne i), ?_⟩
    intro i j hij
    simp [unitVec, inner_smul_left, inner_smul_right, a.raw_inner, h i j hij]
  refine ⟨OrthonormalBasis.mk hon ?_, OrthonormalBasis.coe_mk _ _⟩
  exact (hon.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge

theorem certify {n c : ℕ} [NeZero n] (r : Fin c → Fin n → T) (label : Cell n → Fin c)
    (cover : ∀ k, ∃ p, label p = k) (nz : ∀ k, ∃ x, r k x ≠ 0)
    (sep : a.DistinctLines r) (rows : ∀ i, a.Orthogonal (fun j => r (label (i,j))))
    (cols : ∀ j, a.Orthogonal (fun i => r (label (i,j)))) : Realized n c := by
  classical
  have hr (k : Fin c) : a.raw (r k) ≠ 0 := by
    intro h
    obtain ⟨x,hx⟩ := nz k
    exact hx (a.faithful (show a.eval (r k x) = a.eval 0 by
      rw [map_zero]; exact congrArg (fun w : Space n => w x) h))
  let v (i j : Fin n) := unitVec (a.raw (r (label (i,j))))
  have hn (i j : Fin n) : v i j ≠ 0 := by
    have h := unitVec_norm (hr (label (i,j)))
    intro hz
    change ‖v i j‖ = 1 at h
    simp [hz] at h
  let ray (k : Fin c) := Projectivization.mk ℂ (a.raw (r k)) (hr k)
  have hinj : Function.Injective ray := by
    intro i j h
    by_contra hij
    obtain ⟨x,y,hxy⟩ := sep i j hij
    obtain ⟨t,ht⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
    have hc (k : Fin n) : t * a.eval (r j k) = a.eval (r i k) :=
      congrArg (fun w : Space n => w k) ht
    apply hxy (a.faithful ?_)
    rw [a.mul_eval, a.mul_eval, ← hc x, ← hc y]
    ring
  refine ⟨v, hn, fun i => a.basis_of_orthogonal _ (rows i) (fun j => hr (label (i,j))),
    fun j => a.basis_of_orthogonal _ (cols j) (fun i => hr (label (i,j))), ?_⟩
  have hmap : (fun p : Cell n => Projectivization.mk ℂ (v p.1 p.2) (hn p.1 p.2)) =
      ray ∘ label := by
    funext p
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    exact ⟨_, rfl⟩
  rw [hmap, Function.Surjective.range_comp cover, Set.ncard_range_of_injective hinj]
  simp

end Coefficients

noncomputable def imaginaryModel (d : ℕ) (hd : 0 < d) : Coefficients IQ :=
  ⟨embed d, embed_injective hd, times d, embed_times d, cstar, embed_cstar d⟩

/-- Exact integer coefficients in the real quadratic field Q(√5). -/
noncomputable def goldenEval : IQ →+ ℂ where
  toFun z := ((z.1 : ℝ) + (z.2 : ℝ) * Real.sqrt 5 : ℝ)
  map_zero' := by simp
  map_add' x y := by simp [add_mul]; ring

def goldenMul (a b : IQ) : IQ :=
  (a.1*b.1 + 5*a.2*b.2, a.1*b.2 + a.2*b.1)

theorem goldenEval_injective : Function.Injective goldenEval := by
  intro a b h
  have hab := congrArg Complex.re h
  change (a.1 : ℝ) + a.2 * Real.sqrt 5 = b.1 + b.2 * Real.sqrt 5 at hab
  have hs : Irrational (Real.sqrt 5) := by
    simpa using (Nat.Prime.irrational_sqrt (show Nat.Prime 5 by decide))
  have he : a.2 = b.2 := by
    by_contra hh
    have hne : (a.2 : ℝ) - b.2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hh)
    apply hs
    refine ⟨((b.1 : ℚ) - a.1) / (a.2 - b.2), ?_⟩
    push_cast
    apply (div_eq_iff hne).mpr
    linarith
  rw [he] at hab
  exact Prod.ext (by exact_mod_cast (add_right_cancel hab)) he

noncomputable def goldenModel : Coefficients IQ where
  eval := goldenEval
  faithful := goldenEval_injective
  mul := goldenMul
  mul_eval a b := by
    apply Complex.ext
    · simp [goldenEval, goldenMul, Complex.mul_re]
      nlinarith only [congrArg (fun t : ℝ => (a.2 : ℝ) * (b.2 : ℝ) * t)
        (Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num))]
    · simp [goldenEval, Complex.mul_im]
  bar := id
  bar_eval a := by simp [goldenEval]

end QuantumCertificate
