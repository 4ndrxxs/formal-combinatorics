import Quantum.Hadamard.ConferenceCubicMatrix

/-! Rational shifted quadratic minorants for the log determinant. -/
noncomputable section
open Set Real
open scoped BigOperators

namespace Hadamard.DeterminantRatio.Shifted

def negK (x : ℝ) : ℝ :=
  1/2+x/3+x^2/4+x^3/5+x^4/6+x^5/7+x^6/8+x^7/(9*(1-x))

def posSix (x : ℝ) := x-x^2/2+x^3/3-x^4/4+x^5/5-x^6/6

def subThree (x : ℝ) := x+x^2/2+x^3/3

private theorem log_neg_eight {x : ℝ} (xp : 0≤x) (x1 : x<1) :
    -x-x^2*negK x ≤ Real.log (1-x) := by
  let g (t : ℝ) := Real.log (1-t)+t+t^2/2+t^3/3+t^4/4+t^5/5+t^6/6+t^7/7+t^8/8+
    t^9/(9*(1-t))
  have D (t : ℝ) (lt : t<1) : HasDerivAt g (t^9/(9*(1-t)^2)) t := by
    have nz : 1-t≠0 := by linarith
    have hsub := (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)
    convert (((((((((hsub.log nz).add (hasDerivAt_id t)).add ((hasDerivAt_pow 2 t).div_const 2)).add ((hasDerivAt_pow 3 t).div_const 3)).add ((hasDerivAt_pow 4 t).div_const 4)).add ((hasDerivAt_pow 5 t).div_const 5)).add ((hasDerivAt_pow 6 t).div_const 6)).add ((hasDerivAt_pow 7 t).div_const 7)).add ((hasDerivAt_pow 8 t).div_const 8)).add ((hasDerivAt_pow 9 t).div (hsub.const_mul 9) (mul_ne_zero (by norm_num) nz)) using 1 <;>
      first | rfl | (dsimp [g,Function.comp_def]; field_simp; ring)
  have cont (t : ℝ) (h : t∈Icc 0 x) := D t (lt_of_le_of_lt h.2 x1)
  have mono : MonotoneOn g (Icc 0 x) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t ht ↦ (cont t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (cont t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht ↦ by have hp : 0≤t := (interior_subset ht : t∈Icc 0 x).1; positivity)
  have h := mono (left_mem_Icc.mpr xp) (right_mem_Icc.mpr xp) xp
  simp only [g,sub_zero,Real.log_one,zero_pow (by decide : 2≠0),zero_pow (by decide : 3≠0),
    zero_pow (by decide : 4≠0),zero_pow (by decide : 5≠0),zero_pow (by decide : 6≠0),
    zero_pow (by decide : 7≠0),zero_pow (by decide : 8≠0),zero_pow (by decide : 9≠0),
    zero_div,add_zero] at h
  dsimp [negK]
  linarith only [h,show x^2*(1/2+x/3+x^2/4+x^3/5+x^4/6+x^5/7+x^6/8+x^7/(9*(1-x))) =
      x^2/2+x^3/3+x^4/4+x^5/5+x^6/6+x^7/7+x^8/8+x^9/(9*(1-x)) by ring]

theorem log_positive_six {x : ℝ} (xp : 0≤x) : posSix x≤Real.log (1+x) := by
  let g (t : ℝ) := Real.log (1+t)-t+t^2/2-t^3/3+t^4/4-t^5/5+t^6/6
  have D (t : ℝ) (hp : 0≤t) : HasDerivAt g (t^6/(1+t)) t := by
    have nz : 1+t≠0 := by linarith
    convert (((((((((hasDerivAt_id t).const_add (1:ℝ)).log nz).sub (hasDerivAt_id t)).add ((hasDerivAt_pow 2 t).div_const 2)).sub ((hasDerivAt_pow 3 t).div_const 3)).add ((hasDerivAt_pow 4 t).div_const 4)).sub ((hasDerivAt_pow 5 t).div_const 5)).add ((hasDerivAt_pow 6 t).div_const 6)) using 1 <;>
      first | rfl | (dsimp [g,Function.comp_def]; field_simp; ring)
  have mono : MonotoneOn g (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
      (fun t ht ↦ (D t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (D t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht ↦ by have hp : 0≤t := interior_subset ht; positivity)
  have h := mono (show (0:ℝ)∈Ici 0 by simp) xp xp
  simp [g] at h
  dsimp [posSix]
  linarith

theorem log_sub_upper {x : ℝ} (xp : 0≤x) (x1 : x<1) :
    Real.log (1-x)≤ -subThree x := by
  let g (t : ℝ) := Real.log (1-t)+t+t^2/2+t^3/3
  have D (t : ℝ) (hp : t<1) : HasDerivAt g (-(t^3)/(1-t)) t := by
    have nz : 1-t≠0 := by linarith
    have hsub := (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)
    convert ((((hsub.log nz).add (hasDerivAt_id t)).add ((hasDerivAt_pow 2 t).div_const 2)).add ((hasDerivAt_pow 3 t).div_const 3)) using 1 <;>
      first | rfl | (dsimp [g,Function.comp_def]; field_simp; ring)
  have cont (t : ℝ) (h : t∈Icc 0 x) := D t (lt_of_le_of_lt h.2 x1)
  have anti : AntitoneOn g (Icc 0 x) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun t ht ↦ (cont t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (cont t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht ↦ by
        have h := (interior_subset ht : t∈Icc 0 x)
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (pow_nonneg h.1 _)) (by linarith [h.2]))
  have h := anti (left_mem_Icc.mpr xp) (right_mem_Icc.mpr xp) xp
  simp [g] at h
  dsimp [subThree]
  linarith

private theorem log_positive_two {x : ℝ} (xp : 0≤x) :
    x-x^2/2≤Real.log (1+x) := by
  let g (t : ℝ) := Real.log (1+t)-t+t^2/2
  have D (t : ℝ) (hp : 0≤t) : HasDerivAt g (t^2/(1+t)) t := by
    have nz : 1+t≠0 := by linarith
    convert ((((hasDerivAt_id t).const_add (1:ℝ)).log nz).sub
      (hasDerivAt_id t)).add ((hasDerivAt_pow 2 t).div_const 2) using 1 <;>
      first | rfl | (dsimp [g,Function.comp_def]; field_simp; ring)
  have mono : MonotoneOn g (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
      (fun t ht ↦ (D t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (D t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht ↦ by have hp : 0≤t := interior_subset ht; positivity)
  have h := mono (show (0:ℝ)∈Ici 0 by simp) xp xp
  simp [g] at h
  linarith

theorem negK_mono {x z : ℝ} (hx : 0≤x) (xz : x≤z) (hz : z<1) : negK x≤negK z := by
  have den : 0<9*(1-z) := by linarith
  have zp : 0≤z := hx.trans xz
  unfold negK
  gcongr

theorem shifted_log_lower {y z : ℝ} (z0 : 0≤z) (z1 : z<1) (lo : -z≤y) :
    y-negK z*y^2≤Real.log (1+y) := by
  rcases le_total 0 y with h | h
  · have hK : (1/2:ℝ)≤negK z := calc
      _ = negK 0 := by norm_num [negK]
      _ ≤ _ := negK_mono le_rfl z0 z1
    linarith [log_positive_two h, mul_le_mul_of_nonneg_right hK (sq_nonneg y)]
  · have hz : -y≤z := by linarith
    have hK := negK_mono (neg_nonneg.mpr h) hz z1
    have L := log_neg_eight (neg_nonneg.mpr h) (lt_of_le_of_lt hz z1)
    rw [sub_neg_eq_add, neg_neg, neg_sq] at L
    linarith [mul_le_mul_of_nonneg_right hK (sq_nonneg y)]

theorem log_eight_fifths_upper : Real.log ((8:ℝ)/5)≤470005/1000000 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤470005/1000000) 9
  exact (show (8:ℝ)/5 ≤ ∑ i ∈ Finset.range 9, ((470005:ℝ)/1000000)^i/(i.factorial:ℝ) by
    norm_num [Finset.sum_range_succ,Nat.factorial]).trans h

def margin (v a b : ℝ) : ℝ :=
  v*(posSix b-b/(1+b)) - negK ((a+b)/(1+b))*(1-1/v+v*b^2)/(1+b)^2+
  subThree (1/(2*v))+(v-1)*subThree (1/v)-470005/1000000

theorem normalized_shifted {I : Type*} [Fintype I] (k : ℕ) (hk : 0<k)
    (card : Fintype.card I=k+1) (x : I → ℝ) (a b : ℝ)
    (ap : 0≤a) (a1 : a<1) (bp : 0≤b) (lo : ∀ i, -a≤x i)
    (mean : ∑ i, x i=0) (moment : ∑ i, x i^2=1-1/((k:ℝ)+1))
    (bound : 0 ≤ margin ((k:ℝ)+1) a b) :
    (8/5:ℝ)*(1-1/(2*((k:ℝ)+1)))*(1-1/((k:ℝ)+1))^k ≤ ∏ i, (1+x i) := by
  let v := (k:ℝ)+1
  let z := (a+b)/(1+b)
  let y (i : I) := (x i-b)/(1+b)
  have kr : 0<(k:ℝ) := by exact_mod_cast hk
  have hv : 1<v := by dsimp [v]; linarith
  have vp : 0<v := by linarith
  have hp : 0<1+b := by linarith
  have z0 : 0≤z := div_nonneg (by linarith) hp.le
  have z1 : z<1 := (div_lt_one hp).mpr (by linarith)
  have ylo (i : I) : -z≤y i := by
    change -((a+b)/(1+b))≤(x i-b)/(1+b)
    rw [←neg_div]
    exact div_le_div_of_nonneg_right (by linarith [lo i]) hp.le
  have cardR : (Fintype.card I:ℝ)=v := by dsimp [v]; exact_mod_cast card
  have sy : ∑ i, y i= -(v*b)/(1+b) := by
    simp [y,←Finset.sum_div,Finset.sum_sub_distrib,mean,cardR]
  have sy2 : ∑ i, y i^2=(1-1/v+v*b^2)/(1+b)^2 := by
    simp only [y,div_pow,←Finset.sum_div,show ∀ i, (x i-b)^2=x i^2-(2*b)*x i+b^2 by
      intro i; ring,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,mean,moment]
    simp [cardR,v]
  have posx (i : I) : 0<1+x i := by linarith [lo i]
  have inner (i : I) : posSix b+y i-negK z*(y i)^2 ≤ Real.log (1+x i) := by
    have h1 := log_positive_six bp
    have h2 := shifted_log_lower z0 z1 (ylo i)
    have py : 0<1+y i := by linarith [ylo i]
    have id : 1+x i=(1+b)*(1+y i) := by dsimp [y]; field_simp; ring
    rw [id,Real.log_mul hp.ne' py.ne']
    linarith
  have alls := Finset.sum_le_sum (s:=Finset.univ) (fun i _ ↦ inner i)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,cardR,sy,sy2] at alls
  have half : 1/(2*v)<1 := (div_lt_one (by positivity)).mpr (by linarith)
  have one : 1/v<1 := (div_lt_one vp).mpr hv
  have pa : 0<1-1/(2*v) := sub_pos.mpr half
  have pb : 0<1-1/v := sub_pos.mpr one
  change (8/5:ℝ)*(1-1/(2*v))*(1-1/v)^k ≤ _
  apply (Real.log_le_log_iff (by positivity) (Finset.prod_pos fun i _ ↦ posx i)).mp
  rw [Real.log_mul (mul_ne_zero (by norm_num) pa.ne') (pow_ne_zero _ pb.ne'),
    Real.log_mul (by norm_num) pa.ne', Real.log_pow,Real.log_prod (fun i _ ↦ (posx i).ne')]
  have p1 := log_sub_upper (show 0≤1/(2*v) by positivity) half
  have p2 := mul_le_mul_of_nonneg_left (log_sub_upper (show 0≤1/v by positivity) one) kr.le
  change 0≤v*(posSix b-b/(1+b)) - negK z*(1-1/v+v*b^2)/(1+b)^2+
    subThree (1/(2*v))+(v-1)*subThree (1/v)-470005/1000000 at bound
  have alt : (k:ℝ)=v-1 := by dsimp [v]; ring
  rw [alt] at p2 ⊢
  linarith only [log_eight_fifths_upper,p1,p2,alls,bound,
    show v*(posSix b-b/(1+b))=v*posSix b+ -(v*b)/(1+b) by ring,
    show negK z*((1-1/v+v*b^2)/(1+b)^2)=negK z*(1-1/v+v*b^2)/(1+b)^2 by ring]

#print axioms normalized_shifted

#print axioms shifted_log_lower
#print axioms log_eight_fifths_upper

end Hadamard.DeterminantRatio.Shifted
