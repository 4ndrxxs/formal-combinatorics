import Quantum.Hadamard.ConferenceCubicEstimate

/-! A third-moment bound using the nonnegative polynomial (x+a)(x-b)^2.
For a balanced conference block it improves the universal four-fifths
threshold to q ≥ 169. -/

open Finset
open scoped BigOperators

namespace Hadamard.DeterminantRatio

theorem third_moment_lower {I : Type*} [Fintype I] (x : I → ℝ) (a b s : ℝ)
    (mean : ∑ i, x i=0) (second : ∑ i, x i^2=s)
    (matchMoment : (Fintype.card I:ℝ)*a*b=s) (lo : ∀ i, -a≤x i) :
    -(a-b)*s ≤ ∑ i, x i^3 := by
  have pos : 0 ≤ ∑ i, (x i+a)*(x i-b)^2 := sum_nonneg fun i _ ↦
    mul_nonneg (by linarith [lo i]) (sq_nonneg _)
  have expand (i : I) : (x i+a)*(x i-b)^2 =
      x i^3 + (a-2*b)*x i^2 + (b^2-2*a*b)*x i + a*b^2 := by ring
  simp only [expand, sum_add_distrib, ←mul_sum, mean, second, mul_zero, add_zero,
    sum_const, card_univ, nsmul_eq_mul] at pos
  have last : a*((Fintype.card I:ℝ)*b^2) = s*b := by rw [←matchMoment]; ring
  rw [last] at pos
  linarith

theorem cubic_certificate_at_169 {I : Type*} [Fintype I] (x : I → ℝ) (v t : ℝ)
    (hv : 85≤v) (card : (Fintype.card I:ℝ)=v) (ht : 13≤t) (ts : t^2=2*v-1)
    (mean : ∑ i, x i=0) (second : ∑ i, x i^2=1-1/v) (lo : ∀ i, -(t/v)≤x i) :
    0 ≤ 29/1000 + (4*v-3)/(8*v^2) + (∑ i, x i^3)/3 -
      (37/100)*((2*v-1)/v^2)*(1-1/v) := by
  have vp : 0<v := by linarith
  have tp : 0<t := by linarith
  let a := t/v
  let b := (v-1)/(v*t)
  have matchMoment : (Fintype.card I:ℝ)*a*b=1-1/v := by
    rw [card]; dsimp [a,b]; field_simp
  have diff : a-b=1/t := by dsimp [a,b]; field_simp; nlinarith
  have cubic := third_moment_lower x a b (1-1/v) mean second matchMoment lo
  rw [diff] at cubic
  have small : (1:ℝ)/t ≤ 1/13 := (one_div_le_one_div_of_le (by norm_num) ht)
  have mom : 1-1/v≤1 := by
    have h : 0<1/v := by positivity
    linarith
  have lower : -(1:ℝ)/39 ≤ (∑ i, x i^3)/3 := by
    have h := mul_le_mul_of_nonneg_left mom (show 0≤1/t by positivity)
    linarith
  have rad : ((2*v-1)/v^2)*(1-1/v) ≤ 2/v := by
    calc
      _ ≤ ((2*v-1)/v^2)*1 := mul_le_mul_of_nonneg_left mom (div_nonneg (by linarith) (sq_nonneg _))
      _ ≤ 2/v := by field_simp; nlinarith
  have shift : 49/(100*v) ≤ (4*v-3)/(8*v^2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg vp.le (show 0≤8*v-300 by linarith)]
  have upper : (1:ℝ)/v ≤ 1/85 := one_div_le_one_div_of_le (by norm_num) hv
  have exactShift : 49/(100*v) - (37/100)*(2/v) = -(1/v)/4 := by field_simp; ring
  linarith [mul_le_mul_of_nonneg_left rad (by norm_num : (0:ℝ)≤37/100)]

#print axioms cubic_certificate_at_169

end Hadamard.DeterminantRatio
