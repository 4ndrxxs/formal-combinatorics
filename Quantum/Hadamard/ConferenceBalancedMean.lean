import Quantum.Hadamard.ConferenceDiagonalAverage

/-! A finite-order lower bound for the mean determinant at a balanced
diagonal. Central binomial coefficients give a bound for every term. -/

open scoped BigOperators Matrix Polynomial
open Finset Matrix

namespace Hadamard.ConferenceAverage

variable {I : Type*} [Fintype I] [DecidableEq I]

def positiveCount (f : I → Bool) := (Finset.univ.filter (fun i ↦ f i = true)).card

def signClass (k : ℕ) : Finset (I → Bool) :=
  Finset.univ.filter (fun f ↦ positiveCount f=k)

private theorem extract_class (w : (I → Bool) → ℝ) (k : ℕ) :
    (∑ f, Polynomial.C (w f) * Polynomial.X ^ positiveCount f).coeff k =
    ∑ f ∈ signClass (I:=I) k, w f := by
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, signClass,
    Finset.sum_filter, eq_comm]

theorem card_signClass (k : ℕ) : (signClass (I:=I) k).card = (Fintype.card I).choose k := by
  classical
  have poly : (∑ f : I → Bool, Polynomial.C (1:ℝ) * Polynomial.X ^ positiveCount f) =
      (1 + Polynomial.X) ^ Fintype.card I := by
    have w (f : I → Bool) : (∏ i, if f i then (Polynomial.X : ℝ[X]) else 1) =
        Polynomial.X ^ positiveCount f := by simp [positiveCount, Finset.prod_ite]
    have h := Fintype.prod_sum (fun (_ : I) (b : Bool) ↦ if b then (Polynomial.X : ℝ[X]) else 1)
    simpa only [w, map_one, one_mul, Fintype.sum_bool,
      ite_true, Bool.false_eq_true, ite_false, Finset.prod_const, Finset.card_univ, add_comm]
      using h.symm
  have h := congrArg (fun p : ℝ[X] ↦ p.coeff k) poly
  change (∑ f : I → Bool, Polynomial.C ((fun _ : I → Bool ↦ (1:ℝ)) f) *
    Polynomial.X ^ positiveCount f).coeff k = ((1+Polynomial.X : ℝ[X])^Fintype.card I).coeff k at h
  rw [extract_class, Polynomial.coeff_one_add_X_pow] at h
  simpa using h

theorem class_determinant_total (C : Matrix I I ℝ) (v k : ℕ) (q : ℝ)
    (card : Fintype.card I=2*v) (hq : 1<q) (hc : C.IsHermitian)
    (square : C*C=q • (1 : Matrix I I ℝ)) (trace : C.trace=0) :
    (∑ f ∈ signClass (I:=I) k, |(C+diagonal (fun i ↦ signValue (f i))).det|) =
      ((Polynomial.C (q-1)*(1+Polynomial.X)^2+4*Polynomial.X)^v).coeff k := by
  have poly : (∑ f : I → Bool, Polynomial.C |(C+diagonal (fun i ↦ signValue (f i))).det| *
      Polynomial.X ^ positiveCount f) = (Polynomial.C (q-1)*(1+Polynomial.X)^2+4*Polynomial.X)^v := by
    apply Polynomial.funext
    intro z
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
    simpa only [positiveCount, mul_comm (z^_) _] using absolute_generating C v q z card hq hc square trace
  have h := congrArg (fun p : ℝ[X] ↦ p.coeff k) poly
  exact (extract_class _ k).symm.trans h

private theorem central_coefficient (x : ℝ) (v : ℕ) :
    ((Polynomial.C x*(1+Polynomial.X)^2+4*Polynomial.X)^v).coeff v =
    ∑ j ∈ range (v+1), (4:ℝ)^j*x^(v-j)*(v.choose j : ℝ)*Nat.centralBinom (v-j) := by
  open Polynomial in
    rw [add_comm (C x*(1+X)^2), add_pow, finsetSum_coeff]
    apply sum_congr rfl
    intro j hj
    have jv : j≤v := by simpa using hj
    let r := v-j
    have term : ((4*X : ℝ[X])^j * (C x*(1+X)^2)^(v-j) * (v.choose j : ℝ[X])) =
        C ((4:ℝ)^j*x^r*(v.choose j : ℝ)) * ((1+X)^(2*r)*X^j) := by
      simp only [r, map_mul, map_pow, map_ofNat, map_natCast, mul_pow, pow_mul]
      ring
    rw [term, coeff_C_mul, coeff_mul_X_pow']
    simp only [jv, ite_true, coeff_one_add_X_pow]
    rfl

private theorem central_factor (v j : ℕ) (hv : 0<v) (hj : j≤v) :
    (Nat.centralBinom v : ℝ)*(1+1/(2*(v:ℝ)-1))^j ≤
      4^j*(Nat.centralBinom (v-j) : ℝ) := by
  let a : ℝ := 1+1/(2*(v:ℝ)-1)
  have vp : (1:ℝ)≤v := by exact_mod_cast hv
  have den : 0<2*(v:ℝ)-1 := by linarith
  have ap : 0<a := by dsimp [a]; positivity
  have step (u : ℕ) (hu : u<v) :
      a*(Nat.centralBinom (u+1):ℝ) ≤ 4*(Nat.centralBinom u:ℝ) := by
    have ur : (u:ℝ)+1≤v := by exact_mod_cast hu
    have dup : 0<2*(u:ℝ)+1 := by positivity
    have hh : a ≤ 2*((u:ℝ)+1)/(2*u+1) := by
      dsimp [a]
      apply (le_div_iff₀ dup).mpr
      field_simp [den.ne']
      nlinarith
    have recurrence : ((u:ℝ)+1)*(Nat.centralBinom (u+1):ℝ) =
        2*(2*(u:ℝ)+1)*(Nat.centralBinom u:ℝ) := by exact_mod_cast Nat.succ_mul_centralBinom_succ u
    calc
      _ ≤ (2*((u:ℝ)+1)/(2*u+1))*(Nat.centralBinom (u+1):ℝ) := by gcongr
      _ = _ := by field_simp; nlinarith [recurrence]
  change (Nat.centralBinom v : ℝ)*a^j ≤ _
  induction j with
  | zero => simp
  | succ j ih =>
    let u := v-(j+1)
    have sub : v-j=u+1 := by dsimp [u]; omega
    have small : u<v := by dsimp [u]; omega
    have prev := ih (by omega : j≤v)
    rw [sub] at prev
    calc
      (Nat.centralBinom v:ℝ)*a^(j+1) = ((Nat.centralBinom v:ℝ)*a^j)*a := by ring
      _ ≤ (4^j*(Nat.centralBinom (u+1):ℝ))*a := mul_le_mul_of_nonneg_right prev ap.le
      _ = (4:ℝ)^j*(a*(Nat.centralBinom (u+1):ℝ)) := by ring
      _ ≤ (4:ℝ)^j*(4*(Nat.centralBinom u:ℝ)) := mul_le_mul_of_nonneg_left (step u small) (by positivity)
      _ = _ := by dsimp [u]; ring

/-- A balanced diagonal has mean absolute determinant at least (q+1/q)^v
when q=2v-1. Its numerator is written as a finite sum, without a probability law. -/
theorem balanced_total_lower (C : Matrix I I ℝ) (v : ℕ) (q : ℝ)
    (card : Fintype.card I=2*v) (hq : 1<q) (qdef : q=2*(v:ℝ)-1)
    (hc : C.IsHermitian) (square : C*C=q • (1 : Matrix I I ℝ)) (trace : C.trace=0) :
    (Nat.centralBinom v:ℝ)*(q+1/q)^v ≤
      ∑ f ∈ signClass (I:=I) v, |(C+diagonal (fun i ↦ signValue (f i))).det| := by
  have hv : 0<v := by
    by_contra! h
    have zero : v=0 := by omega
    rw [zero] at qdef
    norm_num at qdef
    linarith
  have eq : q+1/q = (1+1/q)+(q-1) := by ring
  rw [class_determinant_total C v v q card hq hc square trace, central_coefficient, eq, add_pow, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have cf := central_factor v j hv (by simpa using hj)
  rw [←qdef] at cf
  have mult : 0 ≤ (q-1)^(v-j)*(v.choose j:ℝ) :=
    mul_nonneg (pow_nonneg (by linarith) _) (Nat.cast_nonneg _)
  calc
    _ = ((Nat.centralBinom v:ℝ)*(1+1/q)^j) * ((q-1)^(v-j)*(v.choose j:ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right cf mult
    _ = _ := by ring

/-- The finite lower bound exceeds the limiting balanced constant at every
admissible order, including the orders below the uniform spectral estimate. -/
private theorem above_limit (k : ℕ) (hk : 0<k) (q : ℝ) (param : q=2*(k:ℝ)+1) :
    (Real.exp (1/2)/2)*((2*q)*(q-1)^k) < (q+1/q)^(k+1) := by
  have kp : 0<(k:ℝ) := by exact_mod_cast hk
  have qp : 1<q := by linarith
  have qm : 0<q-1 := by linarith
  have q0 : 0<q := by linarith
  have q2 : 0<q^2 := by positivity
  let a := 1+1/(q-1)
  let b := 1+1/q^2
  have ha : 0<a := by dsimp [a]; positivity
  have hb : 0<b := by dsimp [b]; positivity
  have lowa : 1/q ≤ Real.log a := by
    convert Real.one_sub_inv_le_log_of_pos ha using 1
    dsimp [a]; field_simp; ring
  have lowb : 1/(q^2+1) ≤ Real.log b := by
    convert Real.one_sub_inv_le_log_of_pos hb using 1
    dsimp [b]; field_simp; ring
  have strict : 1/2 < (k:ℝ)*(1/q)+((k:ℝ)+1)*(1/(q^2+1)) := by
    have p2 : 0<q^2+1 := by positivity
    field_simp
    nlinarith [show 2*(k:ℝ) = q-1 by linarith, show (2*(k:ℝ)+1)*q^2=q*q^2 by rw [←param]]
  have logs : 1/2 < Real.log (a^k*b^(k+1)) := by
    rw [Real.log_mul (pow_pos ha _).ne' (pow_pos hb _).ne', Real.log_pow, Real.log_pow]
    push_cast
    exact strict.trans_le (add_le_add (mul_le_mul_of_nonneg_left lowa kp.le)
      (mul_le_mul_of_nonneg_left lowb (by linarith)))
  have expLt : Real.exp (1/2) < a^k*b^(k+1) := (Real.lt_log_iff_exp_lt (by positivity)).mp logs
  have ae : (q-1)*a=q := by dsimp [a]; field_simp; ring
  have be : q*b=q+1/q := by dsimp [b]; field_simp
  calc
    _ = (q*(q-1)^k)*Real.exp (1/2) := by ring
    _ < (q*(q-1)^k)*(a^k*b^(k+1)) :=
      mul_lt_mul_of_pos_left expLt (mul_pos q0 (pow_pos qm _))
    _ = (q*((q-1)*a)^k)*b^(k+1) := by rw [mul_pow]; ring
    _ = _ := by rw [ae, ←be, mul_pow, pow_succ' q]

/-- Some balanced sign diagonal gives a determinant strictly above sqrt(e)/2
times the Ehlich--Wojtas bound, at every order 2(k+1) with k positive. -/
theorem exists_balanced_above_limit (C : Matrix I I ℝ) (k : ℕ) (hk : 0<k)
    (card : Fintype.card I=2*(k+1)) (hc : C.IsHermitian)
    (square : C*C=(2*(k:ℝ)+1) • (1 : Matrix I I ℝ)) (trace : C.trace=0) :
    ∃ f : I → Bool, positiveCount f=k+1 ∧
      (Real.exp (1/2)/2) * ((2*(2*(k:ℝ)+1))*(2*k)^k) <
      |(C+diagonal (fun i ↦ signValue (f i))).det| := by
  classical
  let q := 2*(k:ℝ)+1
  have kp : 0<(k:ℝ) := by exact_mod_cast hk
  have hq : 1<q := by dsimp [q]; linarith
  have bound := balanced_total_lower C (k+1) q card hq (by dsimp [q]; push_cast; ring) hc square trace
  have strict := above_limit k hk q rfl
  have cp : 0 < (Nat.centralBinom (k+1):ℝ) := by exact_mod_cast Nat.centralBinom_pos (k+1)
  have total := (mul_lt_mul_of_pos_left strict cp).trans_le bound
  by_contra! fails
  let t := signClass (I:=I) (k+1)
  have cc : t.card = Nat.centralBinom (k+1) := by rw [show t=signClass (I:=I) (k+1) by rfl,card_signClass,card]; rfl
  have cap : (∑ f ∈ t, |(C+diagonal (fun i ↦ signValue (f i))).det|) ≤
      ∑ _f ∈ t, (Real.exp (1/2)/2)*((2*q)*(q-1)^k) := by
    apply Finset.sum_le_sum
    intro f hf
    have h := fails f (Finset.mem_filter.mp hf).2
    simpa [q] using h
  rw [Finset.sum_const, cc, nsmul_eq_mul] at cap
  exact (not_lt_of_ge cap) total

#print axioms class_determinant_total
#print axioms exists_balanced_above_limit
#print axioms balanced_total_lower

end Hadamard.ConferenceAverage
