module

public import Quantum.MaximalHypercubes
public import Quantum.PartialArray

/-! Fourier bases of unitaries with distinct off-diagonal quotients. -/

@[expose] public section
noncomputable section
namespace UniversalPuncture

open Finset Complex Matrix MaximalHypercubes
open scoped ComplexConjugate Matrix

def adjoint {r : ℕ} (a : A r) : A r := (a.1ᴴ, fun k => conj (a.2 k))

theorem adjoint_unitary {r : ℕ} {a : A r} (h : IsUnitary a) : IsUnitary (adjoint a) := by
  refine ⟨?_, ?_, fun i => ?_⟩
  · simpa [adjoint] using h.2.1
  · simpa [adjoint] using h.1
  · simpa [adjoint, mul_comm] using h.2.2 i

theorem adjoint_gram {r : ℕ} (a b : A r) :
    Gram (adjoint a) (adjoint b) = conj (Gram a b) := by
  simp only [Gram, adjoint, Matrix.conjTranspose_conjTranspose, map_add, map_mul,
    map_ofNat, map_sum, Complex.conj_conj]
  congr 1
  change 2 * _ = 2 * star _
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]

theorem mul_adjoint_eq_one {r : ℕ} {a : A r} (h : IsUnitary a) : a * adjoint a = 1 := by
  apply Prod.ext
  · exact h.2.1
  · funext i
    simpa [adjoint, mul_comm] using h.2.2 i

def twoColumns (s t : ℂ) : M :=
  !![scale2, scale2*t; scale2*s, -(scale2*s*t)]

theorem twoColumns_unitary {s t : ℂ} (hs : conj s*s=1) (ht : conj t*t=1) :
    (twoColumns s t)ᴴ * twoColumns s t = 1 ∧
    twoColumns s t * (twoColumns s t)ᴴ = 1 := by
  have h := scale2_sq
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [twoColumns, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      scale2_conj] <;> grind

def headFour {r : ℕ} (x : Fin 4) : Fin (r+4) := ⟨x.val, by omega⟩
def tailIndex {r : ℕ} (x : Fin r) : Fin (r+4) := ⟨x.val+4, by omega⟩
def frequencies {r : ℕ} (a : ℕ) (h : a+1 < r+4) : Fin 4 → Fin (r+4) :=
  ![0,⟨a, by omega⟩,1,⟨a+1,h⟩]

theorem frequency_permutation {r a : ℕ} (h1 : 1<a) (h2 : a+1<r+4) :
    ∃ e : Equiv.Perm (Fin (r+4)), ∀ k, e (headFour k) = frequencies a h2 k := by
  apply Equiv.Perm.exists_extending_pair
  · intro x y h
    exact Fin.ext (congrArg (fun u : Fin (r+4) => u.val) h)
  · intro x y he
    have := congrArg Fin.val he
    fin_cases x <;> fin_cases y <;> simp_all [frequencies]

def fourierUnit {r : ℕ} (a : ℕ) (e : Equiv.Perm (Fin (r+4))) (x : Fin (r+4)) : A r :=
  (twoColumns (phase x ^ a) (phase x), fun k => phase x ^ (e (tailIndex k)).val)

theorem fourierUnit_unitary {r : ℕ} (a : ℕ) (e : Equiv.Perm (Fin (r+4))) (x : Fin (r+4)) :
    IsUnitary (fourierUnit a e x) := by
  have hw : conj (phase x^a) * phase x^a = 1 := by rw [map_pow, ← mul_pow, phase_unit, one_pow]
  have h := twoColumns_unitary hw (phase_unit x)
  refine ⟨h.1,h.2,fun i=>?_⟩
  change conj (phase x^_) * phase x^_ = 1
  rw [map_pow, ← mul_pow, phase_unit, one_pow]

theorem fourierUnit_gram {r a : ℕ} {h2 : a+1<r+4} (e : Equiv.Perm (Fin (r+4)))
    (he : ∀ k, e (headFour k) = frequencies a h2 k) (x y : Fin (r+4)) :
    Gram (fourierUnit a e x) (fourierUnit a e y) = if x=y then ((r+4:ℕ):ℂ) else 0 := by
  rw [← fourier_gram x y,
    ← Equiv.sum_comp e (fun k => conj (phase x)^k.val * phase y^k.val)]
  change _ = ∑ k : Fin (r+4), conj (phase x)^(e k).val * phase y^(e k).val
  simp only [Fin.sum_univ_succ]
  have h (k : Fin 4) := congrArg Fin.val (he k)
  have H0 := h 0
  have H1 := h 1
  have H2 := h 2
  have H3 := h 3
  change (e 0).val = 0 at H0
  change (e (0 : Fin (r+3)).succ).val = a at H1
  change (e (0 : Fin (r+2)).succ.succ).val = 1 at H2
  change (e (0 : Fin (r+1)).succ.succ.succ).val = a+1 at H3
  rw [H0,H1,H2,H3]
  simp [Gram, fourierUnit, twoColumns, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, scale2_conj, pow_succ]
  have hh := scale2_sq
  change _ + ∑ k : Fin r, _ = _ + (_ + (_ + (_ + ∑ k : Fin r, _)))
  have ht (k : Fin r) : tailIndex k = k.succ.succ.succ.succ := rfl
  simp_rw [ht]
  grind

def delta {q : ℕ} [NeZero q] (i j : Fin q) : ZMod q := ZMod.finEquiv q i - ZMod.finEquiv q j

theorem delta_eq_zero {q : ℕ} [NeZero q] {i j : Fin q} : delta i j = 0 ↔ i=j := by
  rw [delta, sub_eq_zero, (ZMod.finEquiv q).injective.eq_iff]

theorem conj_phase {q : ℕ} [NeZero q] (i : Fin q) : conj (phase i) = (phase i)⁻¹ := by
  exact (Circle.coe_inv_eq_conj (ZMod.toCircle (ZMod.finEquiv q i))).symm

theorem char_delta {q : ℕ} [NeZero q] (i j : Fin q) :
    ZMod.stdAddChar (delta i j) = phase i * conj (phase j) := by
  rw [conj_phase]
  simp [delta,phase,sub_eq_add_neg,AddChar.map_add_eq_mul,AddChar.map_neg_eq_inv]

theorem char_mul {q : ℕ} [NeZero q] (x : ZMod q) (a : ℕ) :
    ZMod.stdAddChar ((a : ZMod q)*x) = ZMod.stdAddChar x ^ a := by
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]

theorem phase_pow_injective {q a : ℕ} [NeZero q] (hc : a.Coprime q) :
    Function.Injective (fun i : Fin q => phase i ^ a) := by
  intro i j he
  have h := ZMod.isUnit_iff_coprime a q |>.mpr hc
  apply (ZMod.finEquiv q).injective
  apply h.mul_left_cancel
  apply ZMod.injective_stdAddChar
  simpa only [char_mul,phase] using he

theorem char_pow_injective {q a : ℕ} [NeZero q] (hc : a.Coprime q) :
    Function.Injective (fun x : ZMod q => ZMod.stdAddChar x ^ a) := by
  intro x y he
  apply (ZMod.isUnit_iff_coprime a q |>.mpr hc).mul_left_cancel
  apply ZMod.injective_stdAddChar
  simpa only [char_mul] using he

def quotient {r : ℕ} (a : ℕ) (e : Equiv.Perm (Fin (r+4))) (i j : Fin (r+4)) :
    A r := fourierUnit a e i * adjoint (fourierUnit a e j)

theorem quotient_entries {r a : ℕ} (e : Equiv.Perm (Fin (r+4))) (i j : Fin (r+4)) :
    let t := ZMod.stdAddChar (delta i j)
    (quotient a e i j).1 0 0 = scale2^2 * (1+t) ∧
    (quotient a e i j).1 1 1 = scale2^2 * (1+t) * t^a ∧
    (quotient a e i j).1 1 0 = scale2^2 * (1-t) * phase i^a := by
  dsimp only
  rw [char_delta]
  simp only [quotient, fourierUnit, adjoint, Prod.fst_mul, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.conjTranspose_apply]
  simp [twoColumns, scale2_conj, mul_pow]
  constructor <;> (try constructor) <;> ring

theorem quotient_tail {r a : ℕ} (e : Equiv.Perm (Fin (r+4))) (i j : Fin (r+4)) (k : Fin r) :
    (quotient a e i j).2 k = (ZMod.stdAddChar (delta i j)) ^ (e (tailIndex k)).val := by
  simp [quotient, fourierUnit, adjoint, char_delta, mul_pow]

theorem proportional_coordinates {r : ℕ} {a b : A r} {z : ℂ} (h : z • vector b = vector a) :
    (∀ i j, z * b.1 i j = a.1 i j) ∧ ∀ k, z * b.2 k = a.2 k := by
  have hu (k : Fin (r+4)) : z * unpack b k = unpack a k := by
    have hh := congrArg (fun v : Space (r+4) => v k) h
    change z * (normalizer (r+4) * unpack b k) = normalizer (r+4) * unpack a k at hh
    have hn := @normalizer_ne (r+4) inferInstance
    grind
  refine ⟨?_,fun k=>hu (tailIndex k)⟩
  intro i j
  have h0 := hu 0
  have h1 := hu (0 : Fin (r+3)).succ
  have h2 := hu (0 : Fin (r+2)).succ.succ
  have h3 := hu (0 : Fin (r+1)).succ.succ.succ
  simp only [unpack, Fin.cons_zero, Fin.cons_succ] at h0 h1 h2 h3
  have hs := scale2_ne
  fin_cases i <;> fin_cases j <;> grind

/-- If the off-diagonal quotient vectors are proportional, their ordered
pairs of indices agree. This includes the even-order half-turn difference. -/
theorem quotient_separated {r a : ℕ} (hr : 0<r) (hc : a.Coprime (r+4))
    (e : Equiv.Perm (Fin (r+4))) {i j u v : Fin (r+4)} (hij : i ≠ j)
    {z : ℂ} (hz : z ≠ 0) (h : z • vector (quotient a e u v) = vector (quotient a e i j)) :
    i = u ∧ j = v := by
  obtain ⟨entries, tailEq⟩ := proportional_coordinates h
  obtain ⟨a00,a11,a10⟩ := quotient_entries (a := a) e i j
  obtain ⟨b00,b11,b10⟩ := quotient_entries (a := a) e u v
  have h0 := entries 0 0
  have h1 := entries 1 1
  have h2 := entries 1 0
  rw [a00,b00] at h0
  rw [a11,b11] at h1
  rw [a10,b10] at h2
  have hs := scale2_ne
  have hd : delta i j = delta u v := by
    by_cases ht : 1 + ZMod.stdAddChar (delta i j) = 0
    · apply ZMod.injective_stdAddChar
      grind
    · apply char_pow_injective hc
      dsimp only
      grind
  have ht : ZMod.stdAddChar (delta u v) ≠ 0 := by simp [ZMod.stdAddChar_apply]
  have htail := tailEq ⟨0,hr⟩
  rw [quotient_tail, quotient_tail, hd] at htail
  have hz1 : z = 1 := (mul_right_cancel₀ (pow_ne_zero _ ht)) (htail.trans (one_mul _).symm)
  subst z
  have hdiff : 1 - ZMod.stdAddChar (delta u v) ≠ 0 := by
    intro he
    apply hij
    apply delta_eq_zero.mp
    apply ZMod.injective_stdAddChar
    rw [hd, AddChar.map_zero_eq_one]
    exact (sub_eq_zero.mp he).symm
  have hi : i = u := by
    apply phase_pow_injective hc
    rw [one_mul, hd] at h2
    exact (mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 hs) hdiff) h2).symm
  subst u
  refine ⟨rfl,(ZMod.finEquiv _).injective ?_⟩
  exact sub_right_inj.mp hd

end UniversalPuncture
