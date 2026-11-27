module
public import Quantum.Coefficients
public import Quantum.Pivots

/-! Integer coordinates in ℚ(√d,i), for the order-six certificates. -/
@[expose] public section
namespace SmallSixNumbers

open QuantumCertificate Complex
open scoped ComplexConjugate

noncomputable def reval (d : ℕ) : IQ →+ ℝ where
  toFun z := z.1 + z.2 * Real.sqrt d
  map_zero' := by simp
  map_add' x y := by simp [add_mul]; ring

theorem reval_inj (d : ℕ) (hd : ¬IsSquare d) : Function.Injective (reval d) := by
  intro a b h
  change (a.1 : ℝ) + a.2 * Real.sqrt d = b.1 + b.2 * Real.sqrt d at h
  have he : a.2 = b.2 := by
    by_contra hh
    have hne : (a.2 : ℝ) - b.2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hh)
    apply irrational_sqrt_natCast_iff.mpr hd
    refine ⟨((b.1 : ℚ) - a.1) / (a.2 - b.2), ?_⟩
    push_cast
    apply (div_eq_iff hne).mpr
    linarith
  rw [he] at h
  exact Prod.ext (by exact_mod_cast (add_right_cancel h)) he

def rmul (d : ℕ) (a b : IQ) : IQ :=
  (a.1 * b.1 + d * a.2 * b.2, a.1 * b.2 + a.2 * b.1)

theorem reval_mul (d : ℕ) (a b : IQ) :
    reval d (rmul d a b) = reval d a * reval d b := by
  simp [reval, rmul]
  nlinarith only [congrArg (fun t : ℝ => (a.2 : ℝ) * (b.2 : ℝ) * t)
    (Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity))]

abbrev Quad := IQ × IQ

noncomputable def eval (d : ℕ) : Quad →+ ℂ where
  toFun z := ⟨reval d z.1, reval d z.2⟩
  map_zero' := by apply Complex.ext <;> simp
  map_add' x y := by apply Complex.ext <;> simp

def mul (d : ℕ) (a b : Quad) : Quad :=
  (rmul d a.1 b.1 - rmul d a.2 b.2, rmul d a.1 b.2 + rmul d a.2 b.1)

noncomputable def model (d : ℕ) (hd : ¬IsSquare d) : Coefficients Quad where
  eval := eval d
  faithful := by
    intro a b h
    exact Prod.ext (reval_inj d hd (congrArg Complex.re h))
      (reval_inj d hd (congrArg Complex.im h))
  mul := mul d
  mul_eval a b := by
    apply Complex.ext <;> simp [eval, mul, reval_mul, Complex.mul_re, Complex.mul_im]
  bar a := (a.1, -a.2)
  bar_eval a := by apply Complex.ext <;> simp [eval]

end SmallSixNumbers
