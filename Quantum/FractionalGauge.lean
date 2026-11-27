module
public import Quantum.FractionalTensor

/-! Commuting qubit observables in a four-element joint eigenbasis. -/
@[expose] public section
noncomputable section
namespace FractionalGauge
open Complex Matrix FractionalTensor
open scoped ComplexConjugate Matrix

private theorem va_square : va*va=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [va,vertical,Matrix.mul_apply,Fin.sum_univ_four,Matrix.one_apply]

private theorem hb_square : hb*hb=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hb,horizontal,Matrix.mul_apply,Fin.sum_univ_four,Matrix.one_apply]

private theorem neg_expect (v : V) (m : M) : expectation v (-m) = -expectation v m := by
  simp [expectation,ip,Matrix.neg_mulVec,dotProduct_neg]

theorem degenerate_left {d a b : ℝ} {B : M} (ha : a^2=1) (hb0 : b^2=1)
    (L : M → ℝ) (negL : ∀ M, L (-M)= - L M) (l0 : L va=0)
    (joint : ∀ x y, L (chooseObs va (vertical a b 0 0) x*chooseObs hb B y)=entry d x y) :
    d=0 := by
  have j0 := joint false false
  have j1 := joint false true
  have k0 := joint true false
  have k1 := joint true true
  simp only [chooseObs,entry,Bool.and_false,Bool.false_and,Bool.true_and,Bool.false_eq_true,
    ite_false,ite_true] at j0 j1 k0 k1 l0
  have vs : vertical (-1) (-1) 0 0 = -va := by ext i j; fin_cases i <;> fin_cases j <;> simp [va,vertical]
  have d1 : vertical 1 (-1) 0 0=va*hb := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [va,hb,vertical,horizontal,Matrix.mul_apply,Fin.sum_univ_four]
  have d2 : vertical (-1) 1 0 0= -(va*hb) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [va,hb,vertical,horizontal,Matrix.mul_apply,Fin.sum_univ_four]
  rcases sq_eq_one_iff.mp ha with rfl|rfl <;> rcases sq_eq_one_iff.mp hb0 with rfl|rfl
  · change L (va*B) = -d at k1
    linarith
  · rw [d1,Matrix.mul_assoc,hb_square,mul_one] at k0
    linarith
  · rw [d2,neg_mul,Matrix.mul_assoc,hb_square,mul_one,negL] at k0
    linarith
  · rw [vs,neg_mul,negL] at k0
    linarith

theorem degenerate_right {d a b : ℝ} {A : M} (ha : a^2=1) (hb0 : b^2=1)
    (L : M → ℝ) (negL : ∀ M, L (-M)= - L M) (l0 : L hb=0)
    (joint : ∀ x y, L (chooseObs va A x*chooseObs hb (horizontal a b 0 0) y)=entry d x y) :
    d=0 := by
  have j0 := joint false false
  have j1 := joint true false
  have k0 := joint false true
  have k1 := joint true true
  simp only [chooseObs,entry,Bool.and_false,Bool.false_and,Bool.true_and,Bool.false_eq_true,
    ite_false,ite_true] at j0 j1 k0 k1 l0
  have vs : horizontal (-1) (-1) 0 0 = -hb := by ext i j; fin_cases i <;> fin_cases j <;> simp [hb,horizontal]
  have d1 : horizontal 1 (-1) 0 0=va*hb := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [va,hb,vertical,horizontal,Matrix.mul_apply,Fin.sum_univ_four]
  have d2 : horizontal (-1) 1 0 0= -(va*hb) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [va,hb,vertical,horizontal,Matrix.mul_apply,Fin.sum_univ_four]
  rcases sq_eq_one_iff.mp ha with rfl|rfl <;> rcases sq_eq_one_iff.mp hb0 with rfl|rfl
  · change L (A*hb) = -d at k1
    linarith
  · rw [d1,← Matrix.mul_assoc,va_square,one_mul] at k0
    linarith
  · rw [d2,mul_neg,← Matrix.mul_assoc,va_square,one_mul,negL] at k0
    linarith
  · rw [vs,mul_neg,negL] at k0
    linarith

def phase (z : ℂ) := (‖z‖:ℂ)/z

theorem phase_norm {z : ℂ} (h : z≠0) : ‖phase z‖=1 := by
  simp [phase,h]

theorem phase_times {z : ℂ} (h : z≠0) : z*phase z=(‖z‖:ℂ) := by
  unfold phase
  field_simp

theorem bar_phase {z : ℂ} (h : z≠0) : conj (phase z)*phase z=1 := by
  rw [RCLike.conj_mul,phase_norm h]
  norm_num

private def diagGauge (q : V) : M := Matrix.diagonal q
private theorem gauge_unitary (q : V) (h : ∀ i, conj (q i)*q i=1) :
    diagGauge q*(diagGauge q)ᴴ=1 := by
  ext i j
  by_cases hij : i=j
  · subst j
    simpa [diagGauge,Matrix.mul_diagonal,Matrix.one_apply,mul_comm] using h i
  · simp [diagGauge,Matrix.mul_diagonal,hij]

private theorem gauge_entry (q : V) (m : M) (i j : Fin 4) :
    ((diagGauge q)ᴴ*m*(diagGauge q)) i j=conj (q i)*m i j*q j := by
  simp [diagGauge,Matrix.diagonal_mul,Matrix.mul_diagonal]

private theorem diagonal_fixed {q : V} (h : ∀ i, conj (q i)*q i=1) (e : V) :
    (diagGauge q)ᴴ*Matrix.diagonal e*(diagGauge q)=Matrix.diagonal e := by
  ext i j
  rw [gauge_entry]
  by_cases he : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    calc
      _ = (conj (q i)*q i)*e i := by ring
      _ = _ := by rw [h,one_mul]
  · simp [Matrix.diagonal_apply_ne _ he]

private theorem gauge_vertical {q : V} {a b r s : ℝ} {z w : ℂ} (unit : ∀ i, conj (q i)*q i=1)
    (h0 : conj (q 0)*z*q 2=r) (h1 : conj (q 1)*w*q 3=s) :
    (diagGauge q)ᴴ*vertical a b z w*(diagGauge q)=vertical a b r s := by
  have hd (i : Fin 4) (k : ℂ) : conj (q i)*k*q i=k := by
    calc
      _=(conj (q i)*q i)*k := by ring
      _=_ := by rw [unit,one_mul]
  have l0 := congrArg (starRingEnd ℂ) h0
  have l1 := congrArg (starRingEnd ℂ) h1
  simp [map_mul] at l0 l1
  ext i j
  rw [gauge_entry]
  fin_cases i <;> fin_cases j <;>
    simp [vertical,hd,h0,h1] <;> first | linear_combination l0 | linear_combination l1

private theorem gauge_horizontal {q : V} {a b r s : ℝ} {z w : ℂ} (unit : ∀ i, conj (q i)*q i=1)
    (h0 : conj (q 0)*z*q 1=r) (h1 : conj (q 2)*w*q 3=s) :
    (diagGauge q)ᴴ*horizontal a b z w*(diagGauge q)=horizontal a b r s := by
  have hd (i : Fin 4) (k : ℂ) : conj (q i)*k*q i=k := by
    calc
      _=(conj (q i)*q i)*k := by ring
      _=_ := by rw [unit,one_mul]
  have l0 := congrArg (starRingEnd ℂ) h0
  have l1 := congrArg (starRingEnd ℂ) h1
  simp [map_mul] at l0 l1
  ext i j
  rw [gauge_entry]
  fin_cases i <;> fin_cases j <;>
    simp [horizontal,hd,h0,h1] <;> first | linear_combination l0 | linear_combination l1

private theorem magnitude {z w : ℂ} (h : ‖z‖^2=‖w‖^2) : ‖z‖=‖w‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Two compatible binary planar block systems either degenerate on one side
or admit one common unitary change to two independent real factors. -/
theorem structured_cases {a b c d : ℝ} {z w u v : ℂ}
    (va2 : vertical a b z w * vertical a b z w=1)
    (hb2 : horizontal c d u v * horizontal c d u v=1)
    (comm : vertical a b z w*horizontal c d u v = horizontal c d u v*vertical a b z w) :
    (z=0 ∧ w=0 ∧ a^2=1 ∧ b^2=1) ∨ (u=0 ∧ v=0 ∧ c^2=1 ∧ d^2=1) ∨
      ∃ (T : M) (r s : ℝ), T*Tᴴ=1 ∧ a^2+r^2=1 ∧ c^2+s^2=1 ∧ r≠0 ∧ s≠0 ∧
       (fun i => Tᴴ*chooseObs va (vertical a b z w) i*T)=chooseObs va (vertical a a r r) ∧
       (fun i => Tᴴ*chooseObs hb (horizontal c d u v) i*T)=chooseObs hb (horizontal c c s s) := by
  have hv (i j : Fin 4) := congrFun (congrFun va2 i) j
  have hh (i j : Fin 4) := congrFun (congrFun hb2 i) j
  have hc (i j : Fin 4) := congrFun (congrFun comm i) j
  have az : a^2+‖z‖^2=1 := by
    have e := congrArg Complex.re (hv 0 0)
    simpa [vertical,Matrix.mul_apply,Fin.sum_univ_four,Complex.mul_conj,
      Complex.normSq_eq_norm_sq,pow_two] using e
  have bw : b^2+‖w‖^2=1 := by
    have e := congrArg Complex.re (hv 1 1)
    simpa [vertical,Matrix.mul_apply,Fin.sum_univ_four,Complex.mul_conj,
      Complex.normSq_eq_norm_sq,pow_two] using e
  have cu : c^2+‖u‖^2=1 := by
    have e := congrArg Complex.re (hh 0 0)
    simpa [horizontal,Matrix.mul_apply,Fin.sum_univ_four,Complex.mul_conj,
      Complex.normSq_eq_norm_sq,pow_two] using e
  have dv : d^2+‖v‖^2=1 := by
    have e := congrArg Complex.re (hh 2 2)
    simpa [horizontal,Matrix.mul_apply,Fin.sum_univ_four,Complex.mul_conj,
      Complex.normSq_eq_norm_sq,pow_two] using e
  by_cases Hz : z=0 ∧ w=0
  · rcases Hz with ⟨rfl,rfl⟩
    exact Or.inl ⟨rfl,rfl,by simpa using az,by simpa using bw⟩
  by_cases Hu : u=0 ∧ v=0
  · rcases Hu with ⟨rfl,rfl⟩
    exact Or.inr (Or.inl ⟨rfl,rfl,by simpa using cu,by simpa using dv⟩)
  have eab : a=b := by
    by_cases hu : u=0
    · have hv : v≠0 := fun he => Hu ⟨hu,he⟩
      have ee : (a:ℂ)*v=(b:ℂ)*v := by
        simpa [vertical,horizontal,Matrix.mul_apply,Fin.sum_univ_four,mul_comm] using hc 2 3
      exact_mod_cast mul_right_cancel₀ hv ee
    · have ee : (a:ℂ)*u=(b:ℂ)*u := by
        simpa [vertical,horizontal,Matrix.mul_apply,Fin.sum_univ_four,mul_comm] using hc 0 1
      exact_mod_cast mul_right_cancel₀ hu ee
  have ecd : c=d := by
    by_cases hz : z=0
    · have hw : w≠0 := fun he => Hz ⟨hz,he⟩
      have ee : (d:ℂ)*w=(c:ℂ)*w := by
        simpa [vertical,horizontal,Matrix.mul_apply,Fin.sum_univ_four,mul_comm] using hc 1 3
      exact_mod_cast (mul_right_cancel₀ hw ee).symm
    · have ee : (d:ℂ)*z=(c:ℂ)*z := by
        simpa [vertical,horizontal,Matrix.mul_apply,Fin.sum_univ_four,mul_comm] using hc 0 2
      exact_mod_cast (mul_right_cancel₀ hz ee).symm
  subst b; subst d
  have zw : ‖z‖=‖w‖ := magnitude (by linarith)
  have uv : ‖u‖=‖v‖ := magnitude (by linarith)
  have hz : z≠0 := by
    intro h; apply Hz; exact ⟨h,norm_eq_zero.mp (by simpa [h] using zw.symm)⟩
  have hw : w≠0 := fun h => hz (norm_eq_zero.mp (by simpa [h] using zw))
  have hu : u≠0 := by
    intro h; apply Hu; exact ⟨h,norm_eq_zero.mp (by simpa [h] using uv.symm)⟩
  have hV : v≠0 := fun h => hu (norm_eq_zero.mp (by simpa [h] using uv))
  have rect : z*v=u*w := by
    simpa [vertical,horizontal,Matrix.mul_apply,Fin.sum_univ_four] using hc 0 3
  have phases : phase z*phase v=phase u*phase w := by
    simp only [phase,div_mul_div_comm,rect,zw,←uv]
    ring
  let q : V := ![1,phase u,phase z,phase z*phase v]
  have unit (i : Fin 4) : conj (q i)*q i=1 := by
    fin_cases i <;> simp [q,bar_phase,hu,hz,map_mul]
    calc
      _ = (conj (phase z)*phase z)*(conj (phase v)*phase v) := by ring
      _ = _ := by rw [bar_phase hz,bar_phase hV,one_mul]
  have V0 : conj (q 0)*z*q 2=‖z‖ := by simpa [q] using phase_times hz
  have V1 : conj (q 1)*w*q 3=‖z‖ := by
    change conj (phase u)*w*(phase z*phase v)=_
    rw [phases]
    calc
      _ = (conj (phase u)*phase u)*(w*phase w) := by ring
      _ = _ := by rw [bar_phase hu,phase_times hw,zw,one_mul]
  have H0 : conj (q 0)*u*q 1=‖u‖ := by simpa [q] using phase_times hu
  have H1 : conj (q 2)*v*q 3=‖u‖ := by
    change conj (phase z)*v*(phase z*phase v)=_
    calc
      _ = (conj (phase z)*phase z)*(v*phase v) := by ring
      _ = _ := by rw [bar_phase hz,phase_times hV,uv,one_mul]
  let T := diagGauge q
  have ma : (fun i => Tᴴ*chooseObs va (vertical a a z w) i*T) =
      chooseObs va (vertical a a ‖z‖ ‖z‖) := by
    funext i
    cases i
    · exact gauge_vertical unit (by simp : conj (q 0)*0*q 2=(0:ℝ)) (by simp)
    · exact gauge_vertical unit V0 V1
  have mb : (fun i => Tᴴ*chooseObs hb (horizontal c c u v) i*T) =
      chooseObs hb (horizontal c c ‖u‖ ‖u‖) := by
    funext i
    cases i
    · exact gauge_horizontal unit (by simp : conj (q 0)*0*q 1=(0:ℝ)) (by simp)
    · exact gauge_horizontal unit H0 H1
  exact Or.inr (Or.inr ⟨T,‖z‖,‖u‖,gauge_unitary q unit,az,cu,
    norm_ne_zero_iff.mpr hz,norm_ne_zero_iff.mpr hu,ma,mb⟩)

/-- In the rank-one orthogonal readout problem the common noisy parameter
vanishes on each branch of the simultaneous normal form. -/
theorem structured_forces_zero {k a b c d : ℝ} {z w u v : ℂ}
    (va2 : vertical a b z w * vertical a b z w=1)
    (hb2 : horizontal c d u v * horizontal c d u v=1)
    (comm : vertical a b z w*horizontal c d u v = horizontal c d u v*vertical a b z w)
    (p : PairData k (chooseObs va (vertical a b z w)) (chooseObs hb (horizontal c d u v))) :
    k=0 := by
  rcases structured_cases va2 hb2 comm with ⟨rfl,rfl,ha,hb⟩|⟨rfl,rfl,hc,hd⟩|
    ⟨T,r,s,hT,_,_,hr,hs,ma,mb⟩
  · exact degenerate_left ha hb (expectation (p.state false)) (neg_expect _)
      (p.leftMean false false) (p.joint false)
  · exact degenerate_right hc hd (expectation (p.state false)) (neg_expect _)
      (p.rightMean false false) (p.joint false)
  · have h := p.change T hT
    rw [ma,mb] at h
    exact product_forces_zero hr hs h

#print axioms structured_forces_zero
end FractionalGauge
