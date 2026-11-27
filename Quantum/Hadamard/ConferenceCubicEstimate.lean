import Quantum.Hadamard.DeterminantRatioEstimateLimit

/-! A fourth-degree logarithmic estimate makes the third trace moment
an exact integer certificate for the four-fifths determinant bound. -/

noncomputable section
open scoped BigOperators
open Real Set Finset

namespace Hadamard.DeterminantRatio

private def fourthRemainder (t : ℝ) := Real.log (1+t)-t+t^2/2-t^3/3+t^4/4

private theorem fourth_derivative (t : ℝ) (ht : 0<1+t) :
    HasDerivAt fourthRemainder (t^4/(1+t)) t := by
  have D := ((((((hasDerivAt_id t).const_add (1:ℝ)).log ht.ne').sub (hasDerivAt_id t)).add
    ((hasDerivAt_pow 2 t).div_const 2)).sub ((hasDerivAt_pow 3 t).div_const 3))
  convert D.add ((hasDerivAt_pow 4 t).div_const 4) using 1 <;>
    first | rfl | (dsimp [fourthRemainder, Function.comp_def]; field_simp; ring)

/-- An explicit quartic minorant valid on the entire interval [-3/8,∞). -/
theorem conference_log_quartic {x : ℝ} (hx : -(3:ℝ)/8 ≤ x) :
    x-x^2/2+x^3/3-37*x^4/100 ≤ Real.log (1+x) := by
  rcases le_total 0 x with h | h
  · have d (t : ℝ) (ht : 0≤t) := fourth_derivative t (by linarith)
    have mono : MonotoneOn fourthRemainder (Set.Ici 0) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
        (fun t ht ↦ (d t ht).continuousAt.continuousWithinAt)
        (fun t ht ↦ (d t (interior_subset ht)).hasDerivWithinAt)
        (fun t ht ↦ by have ht' : 0≤t := interior_subset ht; positivity)
    have v := mono (show (0:ℝ)∈Set.Ici 0 by simp) h h
    simp [fourthRemainder] at v
    nlinarith [sq_nonneg (x^2)]
  · let f (t : ℝ) := fourthRemainder t - 8*t^5/25
    have d (t : ℝ) (ht : -(3:ℝ)/8≤t) :
        HasDerivAt f (-(t^4*(3+8*t))/(5*(1+t))) t := by
      have pos : 0<1+t := by linarith
      convert (fourth_derivative t pos).sub (((hasDerivAt_pow 5 t).const_mul 8).div_const 25)
        using 1
      dsimp [f,Function.comp_def]; field_simp; ring
    have anti : AntitoneOn f (Set.Ici (-(3:ℝ)/8)) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
        (fun t ht ↦ (d t ht).continuousAt.continuousWithinAt)
        (fun t ht ↦ (d t (interior_subset ht)).hasDerivWithinAt)
        (fun t ht ↦ by
          have ht' : -(3:ℝ)/8≤t := interior_subset ht
          exact div_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr (mul_nonneg (by positivity) (by linarith))) (by linarith))
    have v := anti hx (show (0:ℝ)∈Set.Ici (-(3:ℝ)/8) by norm_num) h
    simp [f,fourthRemainder] at v
    nlinarith [mul_nonneg (show 0≤x^4 by positivity) (show 0≤x+3/8 by linarith)]

private theorem log_one_sub_quadratic {u : ℝ} (hu : 0≤u) (lt : u<1) :
    Real.log (1-u) ≤ -u-u^2/2 := by
  let f (t : ℝ) := Real.log (1-t)+t+t^2/2
  have d (t : ℝ) (ht : t<1) : HasDerivAt f (-(t^2)/(1-t)) t := by
    have nz : 1-t≠0 := by linarith
    convert ((((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).log nz).add
      (hasDerivAt_id t) |>.add ((hasDerivAt_pow 2 t).div_const 2)) using 1 <;>
      first | rfl | (dsimp [f,Function.comp_def]; field_simp; ring)
  have anti : AntitoneOn f (Set.Iio 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iio _)
      (fun t ht ↦ (d t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (d t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht ↦ by
        have ht' : t<1 := interior_subset ht
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg t)) (by linarith))
  have H := anti (show (0:ℝ)∈Set.Iio 1 by norm_num) lt hu
  simp [f] at H
  linarith

private theorem log_eight_fifths_471 : Real.log ((8:ℝ)/5) ≤ 471/1000 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1+471/(1000*128))
    (by simpa [add_comm] using Real.add_one_le_exp ((471:ℝ)/(1000*128))) 128
  have e : Real.exp ((471:ℝ)/(1000*128))^128=Real.exp (471/1000) := by
    rw [←Real.exp_nat_mul]
    norm_num
  exact (show (8:ℝ)/5 ≤ (1+471/(1000*128))^128 by norm_num).trans (h.trans_eq e)

/-- The signed cubic trace together with the squared spectral radius suffices
to certify the product. Here v=k+1 is the size of the principal block. -/
theorem normalized_cubic_four_fifths {I : Type*} [Fintype I] (k : ℕ) (hk : 0<k)
    (x : I → ℝ) (mean : ∑ i, x i=0) (moment : ∑ i, x i^2=1-1/((k:ℝ)+1))
    (lo : ∀ i, -(3:ℝ)/8 ≤ x i) (radius2 : ℝ) (radius : ∀ i, x i^2≤radius2)
    (certificate : let v := (k:ℝ)+1
      0 ≤ 29/1000 + (4*v-3)/(8*v^2) + (∑ i, x i^3)/3 -
          (37/100)*radius2*(1-1/v)) :
    (8/5:ℝ)*(1-1/(2*((k:ℝ)+1)))*(1-1/((k:ℝ)+1))^k ≤ ∏ i, (1+x i) := by
  let v : ℝ := (k:ℝ)+1
  have kr : 0<(k:ℝ) := by exact_mod_cast hk
  have hv : 1<v := by dsimp [v]; linarith
  have vp : 0<v := by linarith
  have half : 1/(2*v)<1 := (div_lt_one (by positivity)).mpr (by linarith)
  have one : 1/v<1 := (div_lt_one vp).mpr hv
  have pa : 0<1-1/(2*v) := sub_pos.mpr half
  have pb : 0<1-1/v := sub_pos.mpr one
  have pc (i : I) : 0<1+x i := by linarith [lo i]
  have fourth : (∑ i, x i^4) ≤ radius2*(1-1/v) := by
    calc
      _ ≤ ∑ i, radius2*x i^2 := sum_le_sum fun i _ ↦ by
        calc
          _ = (x i)^2*(x i)^2 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (radius i) (sq_nonneg _)
      _ = _ := by rw [←mul_sum, moment]
  have low := sum_le_sum (s:=univ) (fun i _ ↦ conference_log_quartic (lo i))
  simp only [sum_add_distrib,sum_sub_distrib,←sum_div,←mul_sum,mean,moment] at low
  change (8/5:ℝ)*(1-1/(2*v))*(1-1/v)^k ≤ _
  apply (Real.log_le_log_iff (by positivity) (prod_pos fun i _ ↦ pc i)).mp
  rw [Real.log_mul (mul_ne_zero (by norm_num) pa.ne') (pow_ne_zero _ pb.ne'),
    Real.log_mul (by norm_num) pa.ne', Real.log_pow,Real.log_prod (fun i _ ↦ (pc i).ne')]
  have h1 := log_one_sub_quadratic (show 0≤1/(2*v) by positivity) half
  have h2 := mul_le_mul_of_nonneg_left (log_one_sub_quadratic (show 0≤1/v by positivity) one) kr.le
  have shift : -(1/(2*v))-(1/(2*v))^2/2+(k:ℝ)*(-(1/v)-(1/v)^2/2) =
      -1+1/(2*v)-(4*v-3)/(8*v^2) := by dsimp [v]; field_simp; ring
  change 0 ≤ 29/1000+(4*v-3)/(8*v^2)+(∑ i, x i^3)/3-(37/100)*radius2*(1-1/v) at certificate
  change 0-(1-1/v)/2+(∑ i, x i^3)/3-37*(∑ i, x i^4)/100 ≤ _ at low
  have half_eq : 1/(2*v)=(1/v)/2 := by field_simp
  linarith [log_eight_fifths_471]

#print axioms conference_log_quartic
#print axioms normalized_cubic_four_fifths

end Hadamard.DeterminantRatio
