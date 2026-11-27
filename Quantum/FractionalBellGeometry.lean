module
public import Quantum.FractionalBellOperators

/-! A sharp bound on an affine sign pattern of expectations of a single
Hermitian contraction, proved from an arbitrary grid's twelve bases. -/
@[expose] public section
noncomputable section
namespace FractionalBell
open QuantumCertificate FractionalBinary FractionalPositive FractionalProjectors
  FractionalTensor FractionalCorrelations FractionalSettings FractionalForms FractionalGauge
  Complex Matrix Finset
open scoped ComplexConjugate ComplexOrder Matrix BigOperators

structure Moments (t : ℝ) (H : M) (A B : Bool → M) : Prop where
  left : ∀ x, pairing H (A x)=0
  right : ∀ y, pairing H (B y)=0
  joint : ∀ x y, pairing H (A x*B y)=entry t x y

theorem Moments.change {t : ℝ} {H : M} {A B : Bool → M} (h : Moments t H A B)
    (T : M) (hu : T*Tᴴ=1) : Moments t (Tᴴ*H*T)
      (fun x => Tᴴ*A x*T) (fun y => Tᴴ*B y*T) where
  left x := (pairing_change _ hu _ _).trans (h.left x)
  right y := (pairing_change _ hu _ _).trans (h.right y)
  joint x y := by
    change pairing _ ((Tᴴ*A x*T)*(Tᴴ*B y*T))=_
    rw [conjugate_pair_mul _ hu,pairing_change _ hu,h.joint]

theorem moments_of_sites {p : Prob} (m : Model p) (H : M) (c d : ℝ)
    (measure : ∀ q, pairing H (m.effect q)=c+d*mask q) :
    Moments (4*d) H (FractionalSettings.A m) (FractionalSettings.B m) where
  left x := by
    cases x <;> norm_num [A,left,combo,four,cell,order,box,vSign,Fin.sum_univ_four,
      measure,mask,pattern,line] <;> ring
  right y := by
    cases y <;> norm_num [B,right,combo,four,cell,order,box,hSign,Fin.sum_univ_four,
      measure,mask,pattern,line] <;> ring
  joint x y := by
    rw [AB]
    cases x <;> cases y <;> norm_num [joint,combo,four,cell,order,box,jSign,
      Fin.sum_univ_four,measure,mask,pattern,line,entry] <;> ring

theorem circular_pair {H : M} (hh : Hᴴ=H) (x y : ℂ) :
    pairing H (lEq x*rEq y)=correlation x y (H 0 3) (H 1 2) := by
  have e (i j : Fin 4) : H j i=conj (H i j) := (congrFun (congrFun hh j) i).symm
  norm_num [pairing,Matrix.trace,Matrix.diag,lEq,rEq,vertical,horizontal,Matrix.mul_apply,
    Fin.sum_univ_four,e 0 3,e 1 2,correlation,Complex.mul_re,Complex.mul_im]
  ring

theorem circular_bound {t : ℝ} {H : M} {x y : ℂ} (C : Contract H) (hx : ‖x‖=1) (hy : ‖y‖=1)
    (m : Moments t H (fun i => lEq (setting x i)) (fun j => rEq (setting y j))) :
    2*t^2≤4 := by
  let p := H 0 3
  let q := H 1 2
  have observed (i j : Bool) : correlation (setting x i) (setting y j) p q=entry t i j :=
    (circular_pair C.herm _ _).symm.trans (m.joint i j)
  have det := correlation_determinant x y p q
  have m00 := observed false false
  have m01 := observed false true
  have m10 := observed true false
  have m11 := observed true true
  simp only [entry,setting,Bool.and_false,Bool.false_and,Bool.true_and,
    Bool.false_eq_true,ite_false,ite_true] at m00 m01 m10 m11
  rw [m00,m01,m10,m11] at det
  have sign : - (2*t^2)=4*x.im*y.im*(normSq q-normSq p) := by linarith only [det]
  have d : |normSq q - normSq p|≤1 := abs_le.mpr ⟨by
    linarith [Complex.normSq_nonneg q,show normSq p≤1 from C.entry 0 3],by
    linarith [Complex.normSq_nonneg p,show normSq q≤1 from C.entry 1 2]⟩
  have a : |x.im|≤1 := (Complex.abs_im_le_norm _).trans_eq hx
  have b : |y.im|≤1 := (Complex.abs_im_le_norm _).trans_eq hy
  calc
    2*t^2=|-(2*t^2)| := by rw [abs_neg,abs_of_nonneg (by positivity)]
    _=4 * |x.im| * |y.im| * |normSq q - normSq p| := by rw [sign]; norm_num [abs_mul]
    _≤4*1*1*1 := by gcongr
    _=4 := by norm_num

theorem product_bound {t a b r s : ℝ} {H : M} (C : Contract H)
    (ha : a^2+r^2=1) (hb0 : b^2+s^2=1)
    (m : Moments t H (chooseObs va (vertical a a r r)) (chooseObs hb (horizontal b b s s))) :
    2*t^2≤4 := by
  have obsA : (fun i => circularBasisᴴ * chooseObs va (vertical a a r r) i * circularBasis)=
      (fun i => lEq (setting (a+(r:ℂ)*I) i)) := by
    funext i
    cases i
    · simpa [chooseObs,va,setting] using circular_vertical 1 0
    · exact circular_vertical a r
  have obsB : (fun i => circularBasisᴴ * chooseObs hb (horizontal b b s s) i * circularBasis)=
      (fun i => rEq (setting (b+(s:ℂ)*I) i)) := by
    funext i
    cases i
    · simpa [chooseObs,hb,setting] using circular_horizontal 1 0
    · exact circular_horizontal b s
  have hn {u v : ℝ} (hc : u^2+v^2=1) : ‖(u:ℂ)+(v:ℂ)*I‖=1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [Complex.sq_norm]
    simpa [Complex.normSq_apply,pow_two] using hc
  have cut := m.change circularBasis circular_unitary
  rw [obsA,obsB] at cut
  exact circular_bound (C.change _ circular_unitary) (hn ha) (hn hb0) cut

theorem model_bound {p : Prob} (m : Model p) (H : M) (C : Contract H) (c d : ℝ)
    (measure : ∀ q, pairing H (m.effect q)=c+d*mask q) : 8*d^2≤1 := by
  have ca : A m true*hb=hb*A m true := by rw [←first_B m,AB,BA]
  have cb : B m true*va=va*B m true := by rw [←first_A m,AB,BA]
  have ta : (A m true*hb).trace=0 := by rw [←first_B m,AB,joint_trace]
  have tb : (B m true*va).trace=0 := by rw [←first_A m,BA,joint_trace]
  obtain ⟨a,b,z,w,vform⟩ := vertical_form _ (A_hermitian m true) ca (A_trace m true) ta
  obtain ⟨k,l,u,v,hform⟩ := horizontal_form _ (B_hermitian m true) cb (B_trace m true) tb
  have av : A m=chooseObs va (vertical a b z w) := by
    funext x; cases x; exact first_A m; exact vform
  have bh : B m=chooseObs hb (horizontal k l u v) := by
    funext x; cases x; exact first_B m; exact hform
  have obs := moments_of_sites m H c d measure
  rw [av,bh] at obs
  obtain dl|dr|prod := structured_cases (vform ▸ AA m true) (hform ▸ BB m true)
    (by rw [←vform,←hform,AB,BA])
  · obtain ⟨rfl,rfl,ha,hb'⟩ := dl
    have e := degenerate_left ha hb' (pairing H) (pairing_neg H) (obs.left false) obs.joint
    nlinarith
  · obtain ⟨rfl,rfl,ha,hb'⟩ := dr
    have e := degenerate_right ha hb' (pairing H) (pairing_neg H) (obs.right false) obs.joint
    nlinarith
  · obtain ⟨T,r,s,hT,hr,hs,_,_,ma,mb⟩ := prod
    have o := obs.change T hT
    rw [ma,mb] at o
    nlinarith [product_bound (C.change _ hT) hr hs o]

/-- Every Hermitian contraction on any four-dimensional SudoQ obeys the
sharp nonlinear contrast bound for this sign pattern. -/
theorem contrast_bound (v : Site → Space 4) (hg : Grid v) (H : M) (C : Contract H) (c d : ℝ)
    (measure : ∀ q, expectation (⇑(v q)) H=c+d*mask q) : 8*d^2≤1 := by
  obtain ⟨m,T,hT,hv⟩ := normalized_with_unitary (p:=fun q k => normSq (v q k)) v hg
    (fun _ _ => rfl)
  apply model_bound m (Tᴴ*H*T) (C.change T hT) c d
  intro q
  rw [hv,pairing_change _ hT,pairing_projection,measure]

theorem norm_grid {v : Site → Space 4} (hg : Grid v) (q : Site) : ‖v q‖=1 := by
  rcases q with ⟨r,c⟩
  let l : Fin 12 := ⟨r.val,by omega⟩
  have he : line l c=(r,c) := by fin_cases r <;> fin_cases c <;> rfl
  obtain ⟨B,hB⟩ := hg l
  rw [←he,←congrFun hB c]
  exact B.orthonormal.norm_eq_one c

theorem exp_add (v : V) (H K : M) : expectation v (H+K)=expectation v H+expectation v K := by
  simp [expectation,ip,Matrix.add_mulVec,dotProduct_add]
theorem exp_sub (v : V) (H K : M) : expectation v (H-K)=expectation v H-expectation v K := by
  simp [expectation,ip,Matrix.sub_mulVec,dotProduct_sub]

theorem separate_bound {t : ℝ} (h : Separate (family t)) : 2*t^2≤1 := by
  obtain ⟨v,hg,m⟩ := h
  obtain ⟨f,hf,born⟩ := m 0
  have hm (q : Site) : expectation (⇑(v q)) (projection (⇑f))=family t q 0 := by
    rw [projection_expect,←inner_conj_symm (v q) f,Complex.normSq_conj,born]
  have hu (q : Site) : expectation (⇑(v q)) 1=1 := by
    simp only [expectation,Matrix.one_mulVec,unit_ip (norm_grid hg q),Complex.one_re]
  have b := contrast_bound v hg _ (projective_contrast hf) (-1/2) (t/2) (fun q => by
    rw [exp_sub,exp_add,hm,hu,family_apply]; norm_num [weightSign]; ring)
  nlinarith

theorem generalized_bound {t : ℝ} (h : Generalized (family t)) : 8*t^2≤1 := by
  obtain ⟨v,E,hg,hp,hs,born⟩ := h
  apply contrast_bound v hg _ (contract_contrast E hp hs) 0 t
  intro q
  simp only [contrast,exp_sub,exp_add,born,family_apply]
  norm_num [weightSign]
  ring

#print axioms contrast_bound
#print axioms separate_bound
#print axioms generalized_bound
end FractionalBell

