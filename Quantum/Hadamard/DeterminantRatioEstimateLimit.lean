import Quantum.Hadamard.DeterminantRatioEstimateConference

/-! Quantitative convergence of balanced conference completions to the
Ehlich–Wojtas ratio `exp(1/2)/2`. -/

open scoped BigOperators
open Real Matrix

namespace Hadamard.DeterminantRatio

theorem quadratic_log_error {x δ : ℝ} (hx : |x| ≤ δ) (hd : δ ≤ 1/2) :
    |Real.log (1+x)-x+x^2/2| ≤ 2*δ*x^2 := by
  have ax : |x| < 1 := by linarith
  have H := Real.abs_log_sub_add_sum_range_le (x := -x) (by simpa using ax) 2
  norm_num [Finset.sum_range_succ, abs_neg] at H
  calc
    _ = |-x + x^2/2 + Real.log (1+x)| := congrArg abs (by ring)
    _ ≤ |x|^3/(1-|x|) := by simpa [add_comm] using H
    _ ≤ |x|^3/(1/2) := div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    _ = 2*|x| * x^2 := by rw [← sq_abs x]; ring
    _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg x)]

theorem linear_log_error {a : ℝ} (ha : 0 ≤ a) (hc : a ≤ 1/2) :
    |Real.log (1-a)+a| ≤ 2*a^2 := by
  have H := Real.abs_log_sub_add_sum_range_le (x := a) (by rw [abs_of_nonneg ha]; linarith) 1
  norm_num [Finset.sum_range_succ, abs_of_nonneg ha] at H
  calc
    _ ≤ a^2/(1-a) := by simpa [add_comm] using H
    _ ≤ a^2/(1/2) := div_le_div_of_nonneg_left (sq_nonneg a) (by norm_num) (by linarith)
    _ = _ := by ring

/-- An explicit logarithmic rate for one normalized half-Gram determinant.
The size of the error tends to zero uniformly as the spectral radius does. -/
theorem normalized_log_ratio_error {I : Type*} [Fintype I] (k : ℕ) (hk : 0 < k)
    (x : I → ℝ) (mean : ∑ i, x i = 0) (moment : ∑ i, x i^2 = 1-1/((k:ℝ)+1))
    {δ : ℝ} (hd : 0 ≤ δ) (hc : δ ≤ 1/2) (bound : ∀ i, |x i| ≤ δ) :
    |Real.log ((∏ i, (1+x i)) /
        (2*(1-1/(2*((k:ℝ)+1)))*(1-1/((k:ℝ)+1))^k)) - (1/2-Real.log 2)| ≤
      2*δ+2/((k:ℝ)+1) := by
  let v : ℝ := (k:ℝ)+1
  let a : ℝ := 1/(2*v)
  let b : ℝ := 1/v
  have kr : 1 ≤ (k:ℝ) := by exact_mod_cast hk
  have vpos : 0 < v := by dsimp [v]; positivity
  have ba : 0 ≤ a := by dsimp [a]; positivity
  have bb : 0 ≤ b := by dsimp [b]; positivity
  have ac : a ≤ 1/2 := by dsimp [a,v]; field_simp; linarith
  have bc : b ≤ 1/2 := by dsimp [b,v]; field_simp; linarith
  have xp (i : I) : 0 < 1+x i := by linarith [(abs_le.mp (bound i)).1]
  have pa : 0 < 1-a := by linarith
  have pb : 0 < 1-b := by linarith
  have ea := abs_le.mp (linear_log_error ba ac)
  have eb := abs_le.mp (linear_log_error bb bc)
  have ek (i : I) := quadratic_log_error (bound i) hc
  have su : |(∑i, Real.log (1+x i))+(1-b)/2| ≤ 2*δ*(1-b) := by
    calc
      _ = |∑i, (Real.log (1+x i)-x i+(x i)^2/2)| := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, mean, sub_zero, moment]
      _ ≤ ∑i, |Real.log (1+x i)-x i+(x i)^2/2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑i, 2*δ*x i^2 := Finset.sum_le_sum fun i _ ↦ ek i
      _ = _ := by rw [← Finset.mul_sum, moment]
  have se := abs_le.mp su
  have el := mul_le_mul_of_nonneg_left eb.1 (show 0≤(k:ℝ) by positivity)
  have er := mul_le_mul_of_nonneg_left eb.2 (show 0≤(k:ℝ) by positivity)
  have can : a+(k:ℝ)*b + b/2 = 1 := by dsimp [a,b,v]; field_simp; ring
  have small : 2*a^2 + (k:ℝ)*(2*b^2) ≤ 2/v := by dsimp [a,b,v]; field_simp; linarith
  have db : 0 ≤ δ*b := mul_nonneg hd bb
  change |Real.log ((∏i, (1+x i))/(2*(1-a)*(1-b)^k))-(1/2-Real.log 2)| ≤ 2*δ+2/v
  rw [Real.log_div (Finset.prod_pos fun i _ ↦ xp i).ne' (by positivity),
    Real.log_mul (mul_ne_zero (by norm_num) pa.ne') (pow_ne_zero _ pb.ne'),
    Real.log_mul (by norm_num) pa.ne', Real.log_pow, Real.log_prod (fun i _ ↦ (xp i).ne')]
  apply abs_le.mpr
  constructor <;> linarith

#print axioms normalized_log_ratio_error

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

private theorem upper_of_shift {E : Matrix I I ℝ} (herm : E.IsHermitian) {s : ℝ}
    (hp : (s • (1 : Matrix I I ℝ) - E).PosSemidef) (i : I) : herm.eigenvalues i ≤ s := by
  let u := herm.eigenvectorUnitary
  let α := Unitary.conjStarAlgAut ℝ (Matrix I I ℝ) (star u)
  have pos : (α (s • (1 : Matrix I I ℝ) - E)).PosSemidef :=
    hp.conjTranspose_mul_mul_same (u : Matrix I I ℝ)
  have diag : α E = diagonal herm.eigenvalues := herm.conjStarAlgAut_star_eigenvectorUnitary
  rw [map_sub, map_smul, map_one, diag, smul_one_eq_diagonal, diagonal_sub] at pos
  exact sub_nonneg.mp (posSemidef_diagonal_iff.mp pos i)

theorem conference_principal_abs {C : Matrix K K ℝ} {q : ℝ} (hq : 0 < q)
    (hc : C.IsHermitian) (square : C*C = q • (1 : Matrix K K ℝ))
    (f : I → K) (hf : Function.Injective f) (i : I) :
    |((hc.submatrix f).smul (show IsSelfAdjoint (2:ℝ) by simp)).eigenvalues i| ≤ 2*Real.sqrt q := by
  apply abs_le.mpr
  constructor
  · simpa [neg_mul] using conference_principal_lower hq hc square f hf i
  · have negSq : (-C)*(-C)=q • (1 : Matrix K K ℝ) := by simpa using square
    have p := (positive_conference_shift hq hc.neg negSq).submatrix f
    have eq : (Real.sqrt q • (1 : Matrix K K ℝ) + (-C)).submatrix f f =
        Real.sqrt q • (1 : Matrix I I ℝ) - C.submatrix f f := by
      ext i j
      by_cases ij : i=j
      · subst j; simp [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, sub_eq_add_neg]
      · simp [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, ij, hf.ne ij]
    rw [eq] at p
    have p2 := p.smul (show 0 ≤ (2:ℝ) by norm_num)
    rw [smul_sub, smul_smul] at p2
    exact upper_of_shift _ p2 i

private theorem gram_moments {E : Matrix I I ℝ} (k : ℕ) (card : Fintype.card I=k+1)
    (herm : E.IsHermitian) (diag : ∀ i, E i i=0) (off : ∀ i j, i≠j → E i j^2=4) :
    (∑ i, herm.eigenvalues i=0) ∧ (∑ i, (herm.eigenvalues i)^2=4*(k:ℝ)*((k:ℝ)+1)) := by
  constructor
  · calc
      _ = E.trace := herm.trace_eq_sum_eigenvalues.symm
      _ = _ := by simp [Matrix.trace, Matrix.diag, diag]
  · have row (i : I) : ∑ j, E i j * E j i = 4*(k:ℝ) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), diag i, zero_mul, add_zero]
      calc
        _ = ∑ _j ∈ Finset.univ.erase i, (4:ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hs : E j i=E i j := by simpa using herm.apply i j
          rw [hs, ← sq, off _ _ (Finset.mem_erase.mp hj).1.symm]
        _ = _ := by simp [Finset.card_erase_of_mem, card]; ring
    calc
      _ = (E^2).trace := (trace_sq_eq_sum_sq_eigenvalues herm).symm
      _ = ∑ i, ∑ j, E i j * E j i := by simp [Matrix.trace, Matrix.diag, sq, Matrix.mul_apply]
      _ = _ := by simp [row, card]; ring

/-- The bound at order `2*(k+1)`, indexed by the exponent of its power term. -/
def ewBound (k : ℕ) : ℝ := (2 * (2*((k:ℝ)+1)) - 2)*(2*((k:ℝ)+1)-2)^k

private theorem gram_ratio_identity {E : Matrix I I ℝ} (k : ℕ) (card : Fintype.card I=k+1)
    (herm : E.IsHermitian) :
    (((2*((k:ℝ)+1)) • (1 : Matrix I I ℝ) + E).det / ewBound k) =
      (∏ i, (1+herm.eigenvalues i/(2*((k:ℝ)+1)))) /
        (2*(1-1/(2*((k:ℝ)+1)))*(1-1/((k:ℝ)+1))^k) := by
  let v : ℝ := (k:ℝ)+1
  let n : ℝ := 2*v
  have vp : 0 < v := by dsimp [v]; positivity
  have np : 0 < n := by dsimp [n]; positivity
  have eq1 : n*(1-1/n)=n-1 := by field_simp
  have eq2 : n*(1-1/v)=n-2 := by dsimp [n]; field_simp
  have w : ewBound k = n^(k+1)*(2*(1-1/n)*(1-1/v)^k) := by
    change (2*n-2)*(n-2)^k=_
    rw [show 2*n-2=2*(n-1) by ring, ← eq1, ← eq2, mul_pow, pow_succ]
    ring
  have de : (n • (1 : Matrix I I ℝ)+E).det = n^(k+1)*(∏ i, (1+herm.eigenvalues i/n)) := by
    rw [det_shift_eq_prod herm]
    calc
      _ = ∏ i, (n*(1+herm.eigenvalues i/n)) := Finset.prod_congr rfl fun i _ ↦ by field_simp
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, card]
  change (n • (1 : Matrix I I ℝ)+E).det / ewBound k = _
  rw [de, w, mul_div_mul_left _ _ (pow_ne_zero _ np.ne')]

/-- Exact error for the log ratio of a single principal conference Gram block. -/
theorem conference_block_log_rate {C : Matrix K K ℝ} (k : ℕ) (hk : 0<k)
    (card : Fintype.card I=k+1) (hc : C.IsHermitian)
    (square : C*C=(2*(k:ℝ)+1) • (1 : Matrix K K ℝ)) (diag : ∀ i, C i i=0)
    (off : ∀ i j, i≠j → C i j^2=1) (f : I→K) (hf : Function.Injective f)
    (size : 16 ≤ 2*((k:ℝ)+1)) :
    |Real.log (((2*((k:ℝ)+1)) • (1 : Matrix I I ℝ) + (2:ℝ) • C.submatrix f f).det / ewBound k)
        -(1/2-Real.log 2)| ≤ 4*(Real.sqrt (2*(k:ℝ)+1)+1)/(2*((k:ℝ)+1)) := by
  let E := (2:ℝ) • C.submatrix f f
  let hE : E.IsHermitian := (hc.submatrix f).smul (show IsSelfAdjoint (2:ℝ) by simp)
  let n : ℝ := 2*((k:ℝ)+1)
  let q : ℝ := 2*(k:ℝ)+1
  have np : 0 < n := by dsimp [n]; positivity
  have qp : 0 < q := by dsimp [q]; positivity
  have nd : ∀ i, E i i=0 := by intro i; simp [E, Matrix.smul_apply, submatrix_apply, diag]
  have offE (i j : I) (hij : i≠j) : E i j^2=4 := by
    have h := off _ _ (hf.ne hij)
    change (2*C (f i) (f j))^2=4
    nlinarith
  obtain ⟨M,V⟩ := gram_moments k card hE nd offE
  have mean : ∑ i, hE.eigenvalues i/n = 0 := by rw [← Finset.sum_div, M, zero_div]
  have var : ∑ i, (hE.eigenvalues i/n)^2 = 1-1/((k:ℝ)+1) := by
    simp_rw [div_pow]; rw [← Finset.sum_div, V]; dsimp [n]; field_simp; ring
  let δ := 2*Real.sqrt q/n
  have bp (i : I) : |hE.eigenvalues i/n| ≤ δ := by
    rw [abs_div, abs_of_pos np]
    exact div_le_div_of_nonneg_right (conference_principal_abs qp hc square f hf i) np.le
  have dp : 0≤δ := by dsimp [δ]; positivity
  have dc : δ ≤ 1/2 := by
    apply (div_le_iff₀ np).mpr
    have nq : q=n-1 := by dsimp [n,q]; ring
    have big : 16≤n := size
    rw [←sq_le_sq₀ (by positivity) (by positivity)]
    nlinarith [Real.sq_sqrt qp.le, mul_nonneg np.le (show 0≤n-16 by linarith)]
  rw [gram_ratio_identity k card hE]
  have rate := normalized_log_ratio_error k hk _ mean var dp dc bp
  refine rate.trans_eq ?_
  dsimp [δ,n,q]; field_simp; ring

#print axioms conference_block_log_rate

theorem conference_block_pos {C : Matrix K K ℝ} (k : ℕ) (hk : 0<k)
    (hc : C.IsHermitian) (square : C*C=(2*(k:ℝ)+1) • (1 : Matrix K K ℝ))
    (f : I→K) (hf : Function.Injective f) :
    0 < ((2*((k:ℝ)+1)) • (1 : Matrix I I ℝ) + (2:ℝ) • C.submatrix f f).det := by
  have q1 : 1 < 2*(k:ℝ)+1 := by exact_mod_cast (show 1<2*k+1 by omega)
  let H := (hc.submatrix f).smul (show IsSelfAdjoint (2:ℝ) by simp)
  rw [det_shift_eq_prod H]
  have rad : 2*Real.sqrt (2*(k:ℝ)+1) < 2*((k:ℝ)+1) := by
    rw [← sq_lt_sq₀ (by positivity) (by positivity)]
    nlinarith [Real.sq_sqrt (show 0 ≤ 2*(k:ℝ)+1 by positivity),
      sq_pos_of_pos (show 0<(k:ℝ) by exact_mod_cast hk)]
  exact Finset.prod_pos fun i _ ↦ by
    linarith [conference_principal_lower (show 0<2*(k:ℝ)+1 by positivity) hc square f hf i]

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The actual determinant of every balanced completion satisfies the explicit
uniform logarithmic error at all conference orders of size at least sixteen. -/
theorem balanced_conference_log_rate {C : Matrix (I⊕J) (I⊕J) ℝ}
    (k : ℕ) (hk : 0<k) (ci : Fintype.card I=k+1) (cj : Fintype.card J=k+1)
    (size : 16 ≤ 2*((k:ℝ)+1)) (hc : C.IsHermitian)
    (square : C*C=(2*(k:ℝ)+1) • (1 : Matrix (I⊕J) (I⊕J) ℝ))
    (diag : ∀ i, C i i=0) (off : ∀ i j, i≠j → C i j^2=1) :
    |Real.log (|(C+diagonal completionSign).det| / ewBound k)-(1/2-Real.log 2)| ≤
      4*(Real.sqrt (2*(k:ℝ)+1)+1)/(2*((k:ℝ)+1)) := by
  have nd (i : I⊕J) : (-C) i i=0 := by simp [diag]
  have nof (i j : I⊕J) (h : i≠j) : (-C) i j^2=1 := by simpa using off i j h
  have ns : (-C)*(-C)=(2*(k:ℝ)+1) • (1 : Matrix (I⊕J) (I⊕J) ℝ) := by simpa using square
  let n : ℝ := 2*((k:ℝ)+1)
  let P := n • (1 : Matrix I I ℝ) + (2:ℝ) • C.submatrix Sum.inl Sum.inl
  let Q := n • (1 : Matrix J J ℝ) + (2:ℝ) • (-C).submatrix Sum.inr Sum.inr
  let M := C+diagonal completionSign
  have pp : 0<P.det := conference_block_pos k hk hc square _ Sum.inl_injective
  have qp : 0<Q.det := conference_block_pos k hk hc.neg ns _ Sum.inr_injective
  have wp : 0<ewBound k := by
    have kr : 0<(k:ℝ) := by exact_mod_cast hk
    dsimp [ewBound]; exact mul_pos (by linarith) (pow_pos (by linarith) _)
  have rateP := conference_block_log_rate k hk ci hc square diag off _ Sum.inl_injective size
  have rateQ := conference_block_log_rate k hk cj hc.neg ns nd nof _ Sum.inr_injective size
  let t : ℝ := 1/2-Real.log 2
  let err : ℝ := 4*(Real.sqrt (2*(k:ℝ)+1)+1)/n
  have p1 : |Real.log (P.det/ewBound k)-t|≤err := rateP
  have p2 : |Real.log (Q.det/ewBound k)-t|≤err := rateQ
  have g := conference_completion_gram hc square
  rw [show 2*(k:ℝ)+1+1=n by dsimp [n]; ring] at g
  have de : M.det^2=P.det*Q.det := by
    simpa only [sq, Matrix.det_mul, Matrix.det_transpose, Matrix.det_fromBlocks_zero₂₁] using congrArg Matrix.det g
  have ds : (|M.det|/ewBound k)^2=(P.det/ewBound k)*(Q.det/ewBound k) := by
    rw [div_pow, sq_abs, de]; ring
  have lh := congrArg Real.log ds
  rw [Real.log_pow, Real.log_mul (div_ne_zero pp.ne' wp.ne') (div_ne_zero qp.ne' wp.ne')] at lh
  norm_num at lh
  change |Real.log (|M.det|/ewBound k)-t|≤err
  obtain ⟨ll,lu⟩ := abs_le.mp p1
  obtain ⟨rl,ru⟩ := abs_le.mp p2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

#print axioms balanced_conference_log_rate

open Filter Topology

private theorem limit_from_rate {α : Type*} (l : Filter α) {q r : α → ℝ}
    (grow : Tendsto q l atTop) (pos : ∀ᶠ j in l, 0<r j)
    (rate : ∀ᶠ j in l, |Real.log (r j)-(1/2-Real.log 2)| ≤ 4*(Real.sqrt (q j)+1)/(q j+1)) :
    Tendsto r l (𝓝 (Real.exp (1/2)/2)) := by
  have inv : Tendsto (fun j ↦ (Real.sqrt (q j))⁻¹) l (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp grow)
  have upper : Tendsto (fun j ↦ 8/Real.sqrt (q j)) l (𝓝 0) := by
    simpa [div_eq_mul_inv] using inv.const_mul 8
  have logr : Tendsto (fun j ↦ Real.log (r j)) l (𝓝 (1/2-Real.log 2)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq]
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _) _ upper
    filter_upwards [rate, (tendsto_atTop.mp grow 1)] with j hr hj
    refine hr.trans ?_
    have hs : 1 ≤ Real.sqrt (q j) := Real.one_le_sqrt.mpr hj
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith [Real.sq_sqrt (show 0≤q j by linarith),
      mul_nonneg (Real.sqrt_nonneg (q j)) (show 0≤Real.sqrt (q j)-1 by linarith)]
  have el := (Real.continuous_exp.tendsto _).comp logr
  rw [Real.exp_sub, Real.exp_log (by norm_num : 0<(2:ℝ))] at el
  exact el.congr' (pos.mono fun j hj ↦ Real.exp_log hj)

/-- The limit holds along any diverging sequence of half-orders and for any
independent choice of symmetric conference matrix and balanced signs at each
order. The two finite coordinate sets parameterize an arbitrary balanced split. -/
theorem balanced_conference_tendsto {α : Type*} (l : Filter α) (k : α → ℕ)
    (grow : Tendsto k l atTop)
    (C : (j : α) → Matrix (Fin (k j+1)⊕Fin (k j+1)) (Fin (k j+1)⊕Fin (k j+1)) ℝ)
    (hc : ∀ j, (C j).IsHermitian)
    (square : ∀ j, C j*C j=(2*(k j:ℝ)+1) • 1)
    (diag : ∀ j i, C j i i=0) (off : ∀ j u v, u≠v → C j u v^2=1) :
    Tendsto (fun j ↦ |(C j+diagonal completionSign).det| / ewBound (k j))
      l (𝓝 (Real.exp (1/2)/2)) := by
  have kg : Tendsto (fun j ↦ (k j:ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp grow
  have qg : Tendsto (fun j ↦ 2*(k j:ℝ)+1) l atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(tendsto_atTop.mp kg b)] with j hj
    have kp : 0 ≤ (k j:ℝ) := by positivity
    linarith
  apply limit_from_rate l qg
  · filter_upwards [(tendsto_atTop.mp grow 337)] with j hj
    have h : 337 ≤ (k j:ℝ) := by exact_mod_cast hj
    have wp : 0<ewBound (k j) := by
      dsimp [ewBound]; exact mul_pos (by linarith) (pow_pos (by linarith) _)
    have bound := balanced_conference_four_fifths (k j) (by omega) (Fintype.card_fin _) (Fintype.card_fin _)
      (by linarith) (hc j) (square j) (diag j) (fun u v huv ↦ (off j u v huv).le)
    apply div_pos _ wp
    exact lt_of_lt_of_le (mul_pos (by norm_num : (0:ℝ)<4/5) wp)
      (by simpa only [ewBound, mul_assoc] using bound)
  · filter_upwards [(tendsto_atTop.mp grow 8)] with j hj
    have h : 8 ≤ (k j:ℝ) := by exact_mod_cast hj
    have rate := balanced_conference_log_rate (k j) (by omega) (Fintype.card_fin _)
      (Fintype.card_fin _) (by linarith) (hc j) (square j) (diag j) (off j)
    convert rate using 1; ring

#print axioms balanced_conference_tendsto

end Hadamard.DeterminantRatio
