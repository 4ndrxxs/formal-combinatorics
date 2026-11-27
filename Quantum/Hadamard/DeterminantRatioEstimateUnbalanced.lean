import Quantum.Hadamard.DeterminantRatioEstimateLimit

/-! The determinant depends asymptotically only on the proportion of positive
diagonal entries. The two coordinate sets in this file can have any sizes. -/

open scoped BigOperators
open Real Matrix

namespace Hadamard.DeterminantRatio

variable {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable [Fintype K] [DecidableEq K]

private theorem arbitrary_moments {E : Matrix I I ℝ} (herm : E.IsHermitian)
    (diag : ∀ i, E i i=0) (off : ∀ i j, i≠j → E i j^2=4) :
    (∑ i, herm.eigenvalues i=0) ∧
      (∑ i, (herm.eigenvalues i)^2=4*(Fintype.card I:ℝ)*((Fintype.card I:ℝ)-1)) := by
  constructor
  · calc
      _ = E.trace := herm.trace_eq_sum_eigenvalues.symm
      _ = _ := by simp [Matrix.trace, Matrix.diag, diag]
  · have entry (i j : I) : E i j*E j i=4-(if j=i then 4 else 0) := by
      by_cases eq : j=i
      · subst j; simp [diag]
      · have hs : E j i=E i j := by simpa using herm.apply i j
        rw [hs, ← sq, off _ _ (Ne.symm eq), ite_eq_right eq, sub_zero]
    have row (i : I) : ∑ j, E i j*E j i=4*((Fintype.card I:ℝ)-1) := by
      simp [entry, Finset.sum_sub_distrib]; ring
    calc
      _ = (E^2).trace := (trace_sq_eq_sum_sq_eigenvalues herm).symm
      _ = ∑ i, ∑ j, E i j*E j i := by simp [Matrix.trace, Matrix.diag, sq, Matrix.mul_apply]
      _ = _ := by simp [row]; ring

private theorem principal_log_deviation {C : Matrix K K ℝ} (k : ℕ) (size : 16≤2*((k:ℝ)+1))
    (hc : C.IsHermitian) (square : C*C=(2*(k:ℝ)+1) • (1 : Matrix K K ℝ))
    (diag : ∀ i, C i i=0) (off : ∀ i j, i≠j → C i j^2=1) (f : I→K) (hf : Function.Injective f) :
    let n := 2*((k:ℝ)+1)
    let a : ℝ := Fintype.card I
    let V := 4*a*(a-1)/n^2
    let δ := 2*Real.sqrt (2*(k:ℝ)+1)/n
    |Real.log (((n • (1 : Matrix I I ℝ)+(2:ℝ) • C.submatrix f f).det)/n^(Fintype.card I))+V/2| ≤
      2*δ*V := by
  intro n a V δ
  let q : ℝ := 2*(k:ℝ)+1
  let E := (2:ℝ) • C.submatrix f f
  let hE : E.IsHermitian := (hc.submatrix f).smul (show IsSelfAdjoint (2:ℝ) by simp)
  let x (i : I) := hE.eigenvalues i/n
  have np : 0<n := by dsimp [n]; positivity
  have qp : 0<q := by dsimp [q]; positivity
  have nd (i : I) : E i i=0 := by simp [E, Matrix.smul_apply, submatrix_apply, diag]
  have ofE (i j : I) (hij : i≠j) : E i j^2=4 := by
    have he := off _ _ (hf.ne hij)
    change (2*C (f i) (f j))^2=4
    nlinarith
  obtain ⟨M,S⟩ := arbitrary_moments hE nd ofE
  have mean : ∑ i, x i=0 := by dsimp [x]; rw [← Finset.sum_div, M, zero_div]
  have var : ∑ i, x i^2=V := by dsimp [x]; simp_rw [div_pow]; rw [← Finset.sum_div, S]
  have bnd (i : I) : |x i|≤δ := by
    dsimp only [x,δ]; rw [abs_div, abs_of_pos np]
    exact div_le_div_of_nonneg_right (conference_principal_abs qp hc square f hf i) np.le
  have dc : δ ≤ 1/2 := by
    apply (div_le_iff₀ np).mpr
    have nq : q=n-1 := by dsimp [n,q]; ring
    have big : 16≤n := size
    change 2*Real.sqrt q ≤ 1/2*n
    rw [←sq_le_sq₀ (by positivity) (by positivity)]
    nlinarith [Real.sq_sqrt qp.le, mul_nonneg np.le (show 0≤n-16 by linarith)]
  have xp (i : I) : 0<1+x i := by linarith [(abs_le.mp (bnd i)).1]
  have de : (n • (1 : Matrix I I ℝ)+E).det=n^(Fintype.card I)*∏ i, (1+x i) := by
    rw [det_shift_eq_prod hE]
    calc
      _ = ∏ i, (n*(1+x i)) := Finset.prod_congr rfl fun i _ ↦ by dsimp [x]; field_simp
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  change |Real.log ((n • (1 : Matrix I I ℝ)+E).det/n^(Fintype.card I))+V/2|≤_
  rw [de, mul_div_cancel_left₀ _ (pow_ne_zero _ np.ne'), Real.log_prod (fun i _ ↦ (xp i).ne')]
  calc
    _ = |∑ i, (Real.log (1+x i)-x i+(x i)^2/2)| := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, mean, sub_zero,
        ← Finset.sum_div Finset.univ (fun i ↦ (x i)^2) 2, var]
    _ ≤ ∑ i, |Real.log (1+x i)-x i+(x i)^2/2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2*δ*(x i)^2 := Finset.sum_le_sum fun i _ ↦ quadratic_log_error (bnd i) dc
    _ = _ := by rw [← Finset.mul_sum, var]

/-- The uniform error for arbitrary sign proportions. Empty sign classes are allowed. -/
theorem conference_proportion_log_rate {C : Matrix (I⊕J) (I⊕J) ℝ}
    (k : ℕ) (size : 16≤2*((k:ℝ)+1)) (card : Fintype.card I+Fintype.card J=2*(k+1))
    (hc : C.IsHermitian) (square : C*C=(2*(k:ℝ)+1) • (1 : Matrix (I⊕J) (I⊕J) ℝ))
    (diag : ∀ i, C i i=0) (off : ∀ i j, i≠j → C i j^2=1) :
    let n := 2*((k:ℝ)+1)
    let a := (Fintype.card I:ℝ)/n
    |Real.log (|(C+diagonal completionSign).det| / ewBound k)-(2*a*(1-a)-Real.log 2)| ≤
      (8*Real.sqrt (2*(k:ℝ)+1)+4)/n := by
  intro n prop
  let v : ℝ := (k:ℝ)+1
  let a : ℝ := Fintype.card I
  let b : ℝ := Fintype.card J
  let δ := 2*Real.sqrt (2*(k:ℝ)+1)/n
  let VA := 4*a*(a-1)/n^2
  let VB := 4*b*(b-1)/n^2
  let t : ℝ := 1/n
  let u : ℝ := 1/v
  let w := 2*(1-t)*(1-u)^k
  let N := n^(k+1)
  let M := C+diagonal completionSign
  let P := n • (1 : Matrix I I ℝ)+(2:ℝ) • C.submatrix Sum.inl Sum.inl
  let Q := n • (1 : Matrix J J ℝ)+(2:ℝ) • (-C).submatrix Sum.inr Sum.inr
  let p := P.det / n^(Fintype.card I)
  let q := Q.det / n^(Fintype.card J)
  have realcard : a+b=n := by dsimp [a,b,n]; exact_mod_cast card
  have kr : 1≤(k:ℝ) := by linarith
  have hk : 0<k := by exact_mod_cast kr
  have vp : 0<v := by dsimp [v]; positivity
  have np : 0<n := by dsimp [n]; positivity
  have Np : 0<N := pow_pos np _
  have dp : 0≤δ := by dsimp [δ]; positivity
  have ap : 0≤a := by dsimp [a]; positivity
  have bp : 0≤b := by dsimp [b]; positivity
  have td : 0 ≤ t := by dsimp [t]; positivity
  have ud : 0 ≤ u := by dsimp [u]; positivity
  have tc : t ≤ 1/2 := by dsimp [t,n]; field_simp; linarith
  have uc : u ≤ 1/2 := by dsimp [u,v]; field_simp; linarith
  have tp : 0<1-t := by linarith
  have up : 0<1-u := by linarith
  have wp : 0<w := by dsimp [w]; positivity
  have nd (i : I⊕J) : (-C) i i=0 := by simp [diag]
  have nof (i j : I⊕J) (h : i≠j) : (-C) i j^2=1 := by simpa using off i j h
  have ns : (-C)*(-C)=(2*(k:ℝ)+1) • (1 : Matrix (I⊕J) (I⊕J) ℝ) := by simpa using square
  have pp : 0<p := div_pos (conference_block_pos k hk hc square _ Sum.inl_injective) (pow_pos np _)
  have qp : 0<q := div_pos (conference_block_pos k hk hc.neg ns _ Sum.inr_injective) (pow_pos np _)
  have perP : |Real.log p+VA/2|≤2*δ*VA := principal_log_deviation k size hc square diag off _ Sum.inl_injective
  have perQ : |Real.log q+VB/2|≤2*δ*VB := principal_log_deviation k size hc.neg ns nd nof _ Sum.inr_injective
  have g := conference_completion_gram hc square
  rw [show 2*(k:ℝ)+1+1=n by dsimp [n]; ring] at g
  have de : M.det^2=P.det*Q.det := by
    simpa only [sq, Matrix.det_mul, Matrix.det_transpose, Matrix.det_fromBlocks_zero₂₁] using congrArg Matrix.det g
  have powN : n^(Fintype.card I)*n^(Fintype.card J)=N^2 := by
    dsimp [N]; rw [←pow_add, card,←pow_mul]; congr 1; omega
  have normS : (|M.det|/N)^2=p*q := by
    dsimp only [p,q]; rw [div_pow,sq_abs,de,div_mul_div_comm,powN]
  have nz : |M.det|/N≠0 := fun bad ↦ by
    rw [bad,zero_pow (by decide)] at normS
    exact (mul_pos pp qp).ne' normS.symm
  have lh := congrArg Real.log normS
  rw [Real.log_pow, Real.log_mul pp.ne' qp.ne'] at lh
  norm_num at lh
  have wEq : ewBound k=N*w := by
    have eq1 : n*(1-1/n)=n-1 := by field_simp
    have eq2 : n*(1-1/v)=n-2 := by change 2*v*(1-1/v)=2*v-2; field_simp
    change (2*n-2)*(n-2)^k=n^(k+1)*(2*(1-1/n)*(1-1/v)^k)
    rw [show 2*n-2=2*(n-1) by ring,←eq1,←eq2,mul_pow,pow_succ]; ring
  have lW : Real.log w=Real.log 2 + Real.log (1-t) + (k:ℝ)*Real.log (1-u) := by
    dsimp [w]; rw [Real.log_mul (mul_ne_zero (by norm_num) tp.ne') (pow_ne_zero _ up.ne'),
      Real.log_mul (by norm_num) tp.ne', Real.log_pow]
  have et := abs_le.mp (linear_log_error td tc)
  have eu := abs_le.mp (linear_log_error ud uc)
  have el := mul_le_mul_of_nonneg_left eu.1 (show 0≤(k:ℝ) by positivity)
  have er := mul_le_mul_of_nonneg_left eu.2 (show 0≤(k:ℝ) by positivity)
  have small : 2*t^2 + (k:ℝ)*(2*u^2) ≤ 4/n := by dsimp [t,u,n,v]; field_simp; linarith
  have boundV : VA+VB ≤ 4 := by
    calc
      _ = 4*(a*(a-1)+b*(b-1))/n^2 := by dsimp [VA,VB]; ring
      _ ≤ 4 := (div_le_iff₀ (sq_pos_of_pos np)).mpr (by rw [←realcard]; nlinarith [mul_nonneg ap bp])
  have weighted := mul_le_mul_of_nonneg_left boundV dp
  have main : t+(k:ℝ)*u-(VA+VB)/4=2*prop*(1-prop) := by
    have br : b=n-a := by linarith
    dsimp only [t,u,VA,VB,prop]
    change 1/n+(k:ℝ)*(1/v)-(4*a*(a-1)/n^2+4*b*(b-1)/n^2)/4=2*(a/n)*(1-a/n)
    rw [br]; dsimp [n,v]; field_simp; ring
  have err : (8*Real.sqrt (2*(k:ℝ)+1)+4)/n=4*δ+4/n := by dsimp [δ]; ring
  obtain ⟨pLo,pUp⟩ := abs_le.mp perP
  obtain ⟨qLo,qUp⟩ := abs_le.mp perQ
  change |Real.log (|M.det|/ewBound k)-(2*prop*(1-prop)-Real.log 2)| ≤ _
  rw [wEq,←div_div,Real.log_div nz wp.ne',lW,err,←main]
  apply abs_le.mpr
  constructor <;> linarith

#print axioms conference_proportion_log_rate

open Filter Topology

private theorem positive_ratio {C : Matrix (I⊕J) (I⊕J) ℝ} (k : ℕ) (hk : 0<k)
    (hc : C.IsHermitian) (square : C*C=(2*(k:ℝ)+1) • (1 : Matrix (I⊕J) (I⊕J) ℝ)) :
    0 < |(C+diagonal completionSign).det| / ewBound k := by
  have ns : (-C)*(-C)=(2*(k:ℝ)+1) • (1 : Matrix (I⊕J) (I⊕J) ℝ) := by simpa using square
  let n : ℝ := 2*((k:ℝ)+1)
  let M := C+diagonal completionSign
  let P := n • (1 : Matrix I I ℝ)+(2:ℝ) • C.submatrix Sum.inl Sum.inl
  let Q := n • (1 : Matrix J J ℝ)+(2:ℝ) • (-C).submatrix Sum.inr Sum.inr
  have pp : 0<P.det := conference_block_pos k hk hc square _ Sum.inl_injective
  have qp : 0<Q.det := conference_block_pos k hk hc.neg ns _ Sum.inr_injective
  have gram := conference_completion_gram hc square
  rw [show 2*(k:ℝ)+1+1=n by dsimp [n]; ring] at gram
  have de : M.det^2=P.det*Q.det := by
    simpa only [sq, Matrix.det_mul, Matrix.det_transpose, Matrix.det_fromBlocks_zero₂₁] using congrArg Matrix.det gram
  have nz : M.det≠0 := fun bad ↦ by
    rw [bad,zero_pow (by decide)] at de
    exact (mul_pos pp qp).ne' de.symm
  have kr : 0<(k:ℝ) := by exact_mod_cast hk
  apply div_pos (abs_pos.mpr nz)
  dsimp [ewBound]; exact mul_pos (by linarith) (pow_pos (by linarith) _)

/-- For every converging positive-sign proportion `α`, the determinant ratio
converges to `exp(2*α*(1-α))/2` along any diverging family of conference orders. -/
theorem conference_proportion_tendsto {ι : Type*} (l : Filter ι) (k a b : ι→ℕ)
    (grow : Tendsto k l atTop) (count : ∀ j, a j+b j=2*(k j+1))
    {α : ℝ} (hp : Tendsto (fun j ↦ (a j:ℝ)/(2*((k j:ℝ)+1))) l (𝓝 α))
    (C : (j : ι) → Matrix (Fin (a j)⊕Fin (b j)) (Fin (a j)⊕Fin (b j)) ℝ)
    (hc : ∀ j, (C j).IsHermitian) (square : ∀ j, C j*C j=(2*(k j:ℝ)+1) • 1)
    (diag : ∀ j i, C j i i=0) (off : ∀ j i s, i≠s → C j i s^2=1) :
    Tendsto (fun j ↦ |(C j+diagonal completionSign).det| / ewBound (k j))
      l (𝓝 (Real.exp (2*α*(1-α))/2)) := by
  let q (j : ι) : ℝ := 2*(k j:ℝ)+1
  let p (j : ι) : ℝ := (a j:ℝ)/(2*((k j:ℝ)+1))
  let r (j : ι) := |(C j+diagonal completionSign).det| / ewBound (k j)
  let center (j : ι) := 2*p j*(1-p j)-Real.log 2
  have kg : Tendsto (fun j ↦ (k j:ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp grow
  have qg : Tendsto q l atTop := by
    apply tendsto_atTop.mpr
    intro c
    filter_upwards [(tendsto_atTop.mp kg c)] with j hj
    have kp : 0≤(k j:ℝ) := by positivity
    dsimp [q]; linarith
  have inv : Tendsto (fun j ↦ (Real.sqrt (q j))⁻¹) l (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp qg)
  have upper : Tendsto (fun j ↦ 12/Real.sqrt (q j)) l (𝓝 0) := by
    simpa [div_eq_mul_inv] using inv.const_mul 12
  have dp : Tendsto (fun j ↦ Real.log (r j)-center j) l (𝓝 0) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq, sub_zero]
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _) _ upper
    filter_upwards [(tendsto_atTop.mp grow 8)] with j hj
    have kr : 8≤(k j:ℝ) := by exact_mod_cast hj
    have card : Fintype.card (Fin (a j))+Fintype.card (Fin (b j))=2*(k j+1) := by simpa using count j
    have er := conference_proportion_log_rate (k j) (by linarith) card (hc j) (square j) (diag j) (off j)
    have q1 : 1≤q j := by dsimp [q]; linarith
    have hs : 1≤Real.sqrt (q j) := Real.one_le_sqrt.mpr q1
    have bound : |Real.log (r j)-center j|≤(8*Real.sqrt (q j)+4)/(q j+1) := by
      simpa [q,r,center,p,show 2*(k j:ℝ)+1+1=2*((k j:ℝ)+1) by ring] using er
    refine bound.trans ?_
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith [Real.sq_sqrt (show 0≤q j by linarith),
      mul_nonneg (Real.sqrt_nonneg (q j)) (show 0≤Real.sqrt (q j)-1 by linarith)]
  have ct : Tendsto center l (𝓝 (2*α*(1-α)-Real.log 2)) :=
    ((tendsto_const_nhds.mul hp).mul (tendsto_const_nhds.sub hp)).sub_const _
  have lt : Tendsto (fun j ↦ Real.log (r j)) l (𝓝 (2*α*(1-α)-Real.log 2)) := by
    simpa only [sub_add_cancel,zero_add] using dp.add ct
  have el := (Real.continuous_exp.tendsto _).comp lt
  rw [Real.exp_sub,Real.exp_log (by norm_num : 0<(2:ℝ))] at el
  apply el.congr'
  filter_upwards [(tendsto_atTop.mp grow 1)] with j hj
  exact Real.exp_log (positive_ratio (k j) hj (hc j) (square j))

#print axioms conference_proportion_tendsto

end Hadamard.DeterminantRatio
