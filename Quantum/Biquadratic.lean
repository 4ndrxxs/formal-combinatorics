module

public import Quantum.Coefficients

/-! Integer arithmetic in the compositum of Q(√5) and Q(√−3). -/

@[expose] public section
namespace QuantumCertificate

open Complex
open scoped ComplexConjugate

abbrev BQ := IQ × IQ

noncomputable def j3 : ℂ := ⟨0, Real.sqrt 3⟩

private theorem j3_sq : j3 * j3 = -3 := by
  apply Complex.ext
  · simp [j3, Complex.mul_re]
  · simp [j3, Complex.mul_im]

private theorem j3_conj : conj j3 = -j3 := by
  apply Complex.ext <;> simp [j3]

noncomputable def biquadEval : BQ →+ ℂ where
  toFun z := goldenEval z.1 + j3 * goldenEval z.2
  map_zero' := by simp
  map_add' a b := by simp [mul_add]; ring

private theorem goldenReal (z : IQ) : (goldenEval z).im = 0 := rfl

private theorem goldenReal_inj {a b : IQ} (h : (goldenEval a).re = (goldenEval b).re) :
    a = b := goldenEval_injective (Complex.ext h (by simp [goldenReal]))

theorem biquadEval_injective : Function.Injective biquadEval := by
  intro a b h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [biquadEval, j3, Complex.mul_re, goldenReal] at hr
  simp [biquadEval, j3, Complex.mul_im, goldenReal] at hi
  exact Prod.ext (goldenReal_inj hr) (goldenReal_inj hi)

def biquadMul (a b : BQ) : BQ :=
  let s := goldenMul a.2 b.2
  (goldenMul a.1 b.1 - (s+s+s),
   goldenMul a.1 b.2 + goldenMul a.2 b.1)

def biquadBar (a : BQ) : BQ := (a.1, -a.2)

noncomputable def biquadModel : Coefficients BQ where
  eval := biquadEval
  faithful := biquadEval_injective
  mul := biquadMul
  mul_eval a b := by
    have hh (u v : IQ) : goldenEval (goldenMul u v) = goldenEval u * goldenEval v :=
      goldenModel.mul_eval u v
    simp [biquadEval, biquadMul, hh]
    linear_combination -(goldenEval a.2 * goldenEval b.2) * j3_sq
  bar := biquadBar
  bar_eval a := by
    have hh (u : IQ) : conj (goldenEval u) = goldenEval u := (goldenModel.bar_eval u).symm
    simp [biquadEval, biquadBar, map_mul, hh, j3_conj]

end QuantumCertificate
