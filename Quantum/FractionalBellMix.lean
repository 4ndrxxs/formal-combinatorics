module
public import Quantum.FractionalBell

/-! The full four-symbol Bell functional bounds ensembles of arbitrary POVMs
and is saturated by eight explicit classical Sudoku. -/
@[expose] public section
noncomputable section
namespace FractionalBell
open QuantumCertificate FractionalBinary FractionalProjectors FractionalTensor
  FractionalSettings Complex Matrix Finset
open scoped ComplexConjugate ComplexOrder Matrix BigOperators

theorem pairing_comm (H K : M) : pairing H K=pairing K H := by
  rw [pairing,pairing,Matrix.trace_mul_comm]
@[simp] theorem pairing_sub_left (H K L : M) : pairing (H-K) L=pairing H L-pairing K L := by
  simp [pairing,sub_mul]
@[simp] theorem pairing_add_left (H K L : M) : pairing (H+K) L=pairing H L+pairing K L := by
  simp [pairing,add_mul]

theorem self_nonneg {D : M} (h : Dᴴ=D) : 0≤pairing D D := by
  have p := (Matrix.posSemidef_conjTranspose_mul_self D).trace_nonneg
  rw [h] at p
  exact p.1

theorem Contract.trace_le {D : M} (C : Contract D) : pairing D D≤4 := by
  have p := C.defect.trace_nonneg.1
  simpa [pairing] using p

def bell {p : Prob} (m : Model p) :=
  A m false*(B m false+B m true)+A m true*(B m false-B m true)

theorem cross {p : Prob} (m : Model p) (i j : Bool) : Commute (A m i) (B m j) := by
  change _*_= _*_
  rw [AB,BA]

theorem bell_hermitian {p : Prob} (m : Model p) : (bell m)ᴴ=bell m := by
  simp [bell,A_hermitian,B_hermitian,
    ((cross m false false).add_right (cross m false true)).eq.symm,
    ((cross m true false).sub_right (cross m true true)).eq.symm]

theorem bell_square_trace {p : Prob} (m : Model p) : (bell m*bell m).trace=16 := by
  let U := B m false+B m true
  let V := B m false-B m true
  have hU (i : Bool) : Commute (A m i) U := (cross m i false).add_right (cross m i true)
  have hV (i : Bool) : Commute (A m i) V := (cross m i false).sub_right (cross m i true)
  have move (X Y Z T : M) (h : Commute Y Z) : (X*Y)*(Z*T)=(X*Z)*(Y*T) := by
    calc
      _=X*(Y*Z)*T := by simp [Matrix.mul_assoc]
      _=_ := by rw [h.eq]; simp [Matrix.mul_assoc]
  have square : U*U+V*V=(4:ℕ) • (1:M) := by
    dsimp [U,V]
    noncomm_ring [BB m false,BB m true]
  have anti : U*V+V*U=0 := by
    dsimp [U,V]
    noncomm_ring [BB m false,BB m true]
  have tr : ((A m true*A m false)*(V*U)).trace=((A m false*A m true)*(V*U)).trace := by
    let X := V*U
    have hX := (hV true).mul_right (hU true)
    change (A m true*A m false*X).trace=(A m false*A m true*X).trace
    calc
      _=(X*A m true*A m false).trace := Matrix.trace_mul_cycle _ _ _
      _=(A m true*X*A m false).trace := by rw [show X*A m true=A m true*X from hX.eq.symm]
      _=_ := Matrix.trace_mul_cycle _ _ _
  change ((A m false*U+A m true*V)*(A m false*U+A m true*V)).trace=16
  simp only [add_mul,mul_add,Matrix.trace_add,move _ _ _ _ (hU false).symm,
    move _ _ _ _ (hU true).symm,move _ _ _ _ (hV false).symm,
    move _ _ _ _ (hV true).symm,AA,one_mul,tr]
  have tw := congrArg Matrix.trace square
  have tc := congrArg (fun X : M => ((A m false*A m true)*X).trace) anti
  simp only [Matrix.trace_add,Matrix.trace_smul,Matrix.trace_one] at tw
  norm_num at tw
  simp [mul_add] at tc
  linear_combination tw+tc

theorem bell_bound {p : Prob} (m : Model p) (D : M) (C : Contract D) : |pairing D (bell m)|≤8 := by
  have hW := bell_hermitian m
  have sq : pairing (bell m) (bell m)=16 := by rw [pairing,bell_square_trace]; norm_num
  have pos := self_nonneg (D:=bell m+D+D) (by simp [hW,C.herm])
  have neg := self_nonneg (D:=bell m-D-D) (by simp [hW,C.herm])
  simp only [pairing_sub_left,pairing_sub,pairing_add_left,pairing_add,sq,
    pairing_comm (bell m) D] at pos neg
  exact abs_le.mpr ⟨by linarith [C.trace_le],by linarith [C.trace_le]⟩

def score (p : Prob) : ℝ := ∑ q, mask q*((p q 0+p q 1)-(p q 2+p q 3))

theorem bell_evaluation {p : Prob} (m : Model p) (D : M) (g : Site → ℝ)
    (born : ∀ q, pairing D (m.effect q)=g q) :
    pairing D (bell m)=∑ q, mask q*g q := by
  simp only [bell,mul_add,mul_sub,AB,pairing_add,pairing_sub]
  norm_num [joint,combo,four,cell,order,box,FractionalForms.vSign,jSign,
    Fintype.sum_prod_type,Fin.sum_univ_four,born,mask,pattern,line]
  ring

theorem score_bound {p : Prob} (h : Generalized p) : |score p|≤8 := by
  obtain ⟨v,E,hg,hp,hs,born⟩ := h
  obtain ⟨m,T,hT,hv⟩ := normalized_with_unitary (p:=fun q k => normSq (v q k)) v hg (fun _ _ => rfl)
  let D := contrast E
  have b := bell_bound m (Tᴴ*D*T) ((contract_contrast E hp hs).change T hT)
  rw [bell_evaluation m _ (fun q => (p q 0+p q 1)-(p q 2+p q 3)) (fun q => by
    rw [hv,pairing_change _ hT,pairing_projection]
    simp [D,contrast,exp_add,exp_sub,born])] at b
  exact b

theorem score_mix (r s : ℝ) (p q : Prob) : score (r • p+s • q)=r*score p+s*score q := by
  simp only [score,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,←Finset.sum_add_distrib]
  apply sum_congr rfl
  intro x _
  ring

theorem ensemble_bound {p : Prob} (h : p∈convexHull ℝ {p | Generalized p}) : |score p|≤8 := by
  have convex : Convex ℝ {p : Prob | |score p|≤8} := by
    intro p hp q hq r s hr hs hrs
    change |score p|≤8 at hp
    change |score q|≤8 at hq
    change |score (r • p+s • q)|≤8
    rw [score_mix]
    calc
      _≤|r*score p|+|s*score q| := abs_add_le _ _
      _=r*|score p|+s*|score q| := by rw [abs_mul,abs_mul,abs_of_nonneg hr,abs_of_nonneg hs]
      _≤r*8+s*8 := by gcongr
      _=8 := by linarith only [hrs]
  exact convexHull_min (fun _ hp => score_bound hp) convex h

theorem score_family (t : ℝ) : score (family t)=16*t := by
  norm_num [score,Fintype.sum_prod_type,Fin.sum_univ_four,family_apply,mask,pattern,weightSign]
  ring

theorem classical_to_generalized {p : Prob} (h : ArbitraryMeasurement p) : Generalized p := by
  obtain ⟨v,B,hg,born⟩ := h
  refine ⟨v,fun i => projection (⇑(B i)),hg,?_,basis_projection_sum B,?_⟩
  · intro i
    have hs := basis_projection_mul B i i
    simp only [ite_true] at hs
    have hpos := Matrix.posSemidef_conjTranspose_mul_self (projection (⇑(B i)))
    rwa [projection_hermitian,hs] at hpos
  · intro q k
    rw [projection_expect,←inner_conj_symm (v q) (B k),Complex.normSq_conj]
    simpa [OrthonormalBasis.repr_apply_apply] using born q k

def ClassicalGrid (p : Prob) : Prop :=
  ∃ f : Site → Fin 4, (∀ l, Function.Injective (fun j => f (line l j))) ∧
    ∀ q k, p q k=if f q=k then 1 else 0

theorem classical_is_quantum {p : Prob} (h : ClassicalGrid p) : ArbitraryMeasurement p := by
  obtain ⟨f,hf,born⟩ := h
  apply any_basis.mpr
  refine ⟨fun q => axis (f q),?_,?_⟩
  · intro l
    let e := Equiv.ofBijective (fun j => f (line l j)) (Finite.injective_iff_bijective.mp (hf l))
    exact ⟨(EuclideanSpace.basisFun (Fin 4) ℂ).reindex e.symm,funext fun j => by simp [e,axis]⟩
  · intro q k
    rw [born]
    by_cases he : f q=k <;> simp [axis,he]

def exampleRows : Fin 4 → Fin 4 → Fin 4 → Fin 4 :=
  ![![![0,1,2,3],![2,3,0,1],![1,2,3,0],![3,0,1,2]],
    ![![0,2,1,3],![3,1,2,0],![1,0,3,2],![2,3,0,1]],
    ![![0,2,1,3],![3,1,2,0],![2,3,0,1],![1,0,3,2]],
    ![![2,3,0,1],![0,1,2,3],![1,2,3,0],![3,0,1,2]]]

def ensembleGrid (neg : Bool) (i : Fin 8) (q : Site) : Fin 4 :=
  let k := exampleRows ⟨i.val/2,by omega⟩ q.1 q.2
  let a := if i.val%2=1 then ![1,0,3,2] k else k
  if neg then ![2,3,0,1] a else a

def gridTable (f : Site → Fin 4) : Prob := fun q k => if f q=k then 1 else 0

theorem endpoint_classical (neg : Bool) :
    family (if neg then -1/2 else 1/2)∈convexHull ℝ {p | ClassicalGrid p} := by
  have hG : ∀ b i l, Function.Injective (fun j => ensembleGrid b i (line l j)) := by decide +kernel
  have hb (i : Fin 8) : gridTable (ensembleGrid neg i)∈convexHull ℝ {p | ClassicalGrid p} :=
    subset_convexHull ℝ _ ⟨ensembleGrid neg i,hG neg i,fun _ _ => rfl⟩
  have hsum := (convex_convexHull ℝ {p | ClassicalGrid p}).sum_mem
    (t:=univ) (w:=fun _ : Fin 8 => (1/8:ℝ)) (z:=fun i => gridTable (ensembleGrid neg i))
    (fun _ _ => by norm_num) (by norm_num) (fun i _ => hb i)
  have exact_counts : ∀ b q k, (univ.filter (fun i => ensembleGrid b i q=k)).card=
      if (pattern q == decide (k.val<2)) != b then 3 else 1 := by decide +kernel
  have ident : (∑ i, (1/8:ℝ) • gridTable (ensembleGrid neg i))=
      family (if neg then -1/2 else 1/2) := by
    funext q k
    simp [gridTable,Finset.sum_apply,exact_counts,Finset.sum_ite]
    rw [family_apply]
    cases neg <;> cases h : pattern q <;> fin_cases k <;> norm_num [mask,h,weightSign]
  rwa [ident] at hsum

theorem classical_region {t : ℝ} (h : |t|≤1/2) :
    family t∈convexHull ℝ {p | ClassicalGrid p} := by
  have hs := abs_le.mp h
  have c := convex_convexHull ℝ {p | ClassicalGrid p} (endpoint_classical false)
    (endpoint_classical true) (show 0≤t+1/2 by linarith) (show 0≤1/2-t by linarith)
    (show t+1/2+(1/2-t)=1 by ring)
  have eq : (t+1/2) • family (1/2)+(1/2-t) • family (-1/2)=family t := by
    funext q k
    simp [family_apply]
    ring
  change (t+1/2) • family (1/2)+(1/2-t) • family (-1/2)∈_ at c
  rwa [eq] at c

theorem quantum_ensemble_iff (t : ℝ) :
    family t∈convexHull ℝ {p | Generalized p} ↔ |t|≤1/2 := by
  constructor
  · intro h
    have b := ensemble_bound h
    rw [score_family,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤16)] at b
    linarith
  · intro h
    exact (convexHull_mono (fun _ hp => classical_to_generalized (classical_is_quantum hp))) (classical_region h)

theorem classical_ensemble_iff (t : ℝ) :
    family t∈convexHull ℝ {p | ClassicalGrid p} ↔ |t|≤1/2 :=
  ⟨fun h => (quantum_ensemble_iff t).mp ((convexHull_mono
    (fun _ hp => classical_to_generalized (classical_is_quantum hp))) h),classical_region⟩

#print axioms bell_square_trace
#print axioms quantum_ensemble_iff
#print axioms classical_ensemble_iff
end FractionalBell

