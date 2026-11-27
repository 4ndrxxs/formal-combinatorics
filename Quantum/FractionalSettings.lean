module
public import Quantum.FractionalProjectors
public import Quantum.FractionalForms

/-! The four blocks of a SudoQ give compatible binary observables when the
two bits of the off-diagonal blocks are reversed. -/
@[expose] public section
noncomputable section
namespace FractionalSettings
open Complex Matrix Finset FractionalTensor FractionalGauge FractionalForms
open FractionalBinary FractionalPositive FractionalProjectors
open scoped ComplexConjugate Matrix BigOperators

def box (x y : Bool) : Fin 12 := if x then (if y then 11 else 10) else (if y then 9 else 8)
def order (x y : Bool) (k : Fin 4) : Fin 4 := if x=y then k else ![3,2,1,0] k
def cell (x y : Bool) (k : Fin 4) := line (box x y) (order x y k)
def four {p : Prob} (m : Model p) (x y : Bool) (k : Fin 4) := m.effect (cell x y k)

def combo (e : Fin 4 → M) (c : V) : M := ∑ k, c k • e k
def jSign : V := ![1,-1,-1,1]
def left {p : Prob} (m : Model p) (x y : Bool) := combo (four m x y) vSign
def right {p : Prob} (m : Model p) (x y : Bool) := combo (four m x y) hSign
def joint {p : Prob} (m : Model p) (x y : Bool) := combo (four m x y) jSign

private theorem combo_mul (e : Fin 4 → M) (u v : V)
    (h : ∀ i j, e i*e j=if i=j then e i else 0) :
    combo e u * combo e v=combo e (fun k => u k*v k) := by
  classical
  simp only [combo,sum_mul,mul_sum,Matrix.smul_mul,Matrix.mul_smul,h]
  apply sum_congr rfl
  intro i _
  rw [sum_eq_single i]
  · simp [smul_smul,mul_comm]
  · intro j _ hj
    simp [hj]
  · simp

private theorem prod4 {p : Prob} (m : Model p) (x y : Bool) (i j : Fin 4) :
    four m x y i*four m x y j=if i=j then four m x y i else 0 := by
  have inj := (by decide +kernel : ∀ a b, Function.Injective (order a b)) x y
  simpa [four,cell,inj.eq_iff] using m.product (box x y) (order x y i) (order x y j)

private theorem sum4 {p : Prob} (m : Model p) (x y : Bool) : ∑ i, four m x y i=1 := by
  have h := m.unitSum (box x y)
  cases x <;> cases y <;> simpa [four,cell,order,Fin.sum_univ_four,add_comm,add_left_comm,add_assoc] using h

private theorem left_same {p : Prob} (m : Model p) (x : Bool) : left m x false=left m x true := by
  have l (i : Fin 12) := m.unitSum i
  cases x
  · have a := l 0; have b := l 1
    norm_num [left,combo,four,cell,order,box,vSign,line,Fin.sum_univ_four] at a b ⊢
    linear_combination (norm := abel) a-b
  · have a := l 3; have b := l 2
    norm_num [left,combo,four,cell,order,box,vSign,line,Fin.sum_univ_four] at a b ⊢
    linear_combination (norm := abel) a-b

private theorem right_same {p : Prob} (m : Model p) (y : Bool) : right m false y=right m true y := by
  have l (i : Fin 12) := m.unitSum i
  cases y
  · have a := l 4; have b := l 5
    norm_num [right,combo,four,cell,order,box,hSign,line,Fin.sum_univ_four] at a b ⊢
    linear_combination (norm := abel) a-b
  · have a := l 7; have b := l 6
    norm_num [right,combo,four,cell,order,box,hSign,line,Fin.sum_univ_four] at a b ⊢
    linear_combination (norm := abel) a-b

def A {p : Prob} (m : Model p) (x : Bool) := left m x false
def B {p : Prob} (m : Model p) (y : Bool) := right m false y

theorem A_at {p : Prob} (m : Model p) (x y : Bool) : A m x=left m x y := by
  cases y; rfl; exact left_same m x
theorem B_at {p : Prob} (m : Model p) (x y : Bool) : B m y=right m x y := by
  cases x; rfl; exact right_same m y

theorem AB {p : Prob} (m : Model p) (x y : Bool) : A m x*B m y=joint m x y := by
  rw [A_at m x y,B_at m x y,left,right,joint,combo_mul _ _ _ (prod4 m x y)]
  congr 1
  funext i; fin_cases i <;> norm_num [vSign,hSign,jSign]

theorem BA {p : Prob} (m : Model p) (x y : Bool) : B m y*A m x=joint m x y := by
  rw [A_at m x y,B_at m x y,left,right,joint,combo_mul _ _ _ (prod4 m x y)]
  congr 1
  funext i; fin_cases i <;> norm_num [vSign,hSign,jSign]

theorem AA {p : Prob} (m : Model p) (x : Bool) : A m x*A m x=1 := by
  rw [A,left,combo_mul _ _ _ (prod4 m x false)]
  have t : (fun i => vSign i*vSign i)=(fun _ => (1:ℂ)) := by
    funext i; fin_cases i <;> norm_num [vSign]
  rw [t]
  simpa [combo] using sum4 m x false

theorem BB {p : Prob} (m : Model p) (y : Bool) : B m y*B m y=1 := by
  rw [B,right,combo_mul _ _ _ (prod4 m false y)]
  have t : (fun i => hSign i*hSign i)=(fun _ => (1:ℂ)) := by
    funext i; fin_cases i <;> norm_num [hSign]
  rw [t]
  simpa [combo] using sum4 m false y

theorem A_trace {p : Prob} (m : Model p) (x : Bool) : (A m x).trace=0 := by
  simp [A,left,combo,four,vSign,Fin.sum_univ_four,m.trace]
theorem B_trace {p : Prob} (m : Model p) (y : Bool) : (B m y).trace=0 := by
  simp [B,right,combo,four,hSign,Fin.sum_univ_four,m.trace]
theorem joint_trace {p : Prob} (m : Model p) (x y : Bool) : (joint m x y).trace=0 := by
  simp [joint,combo,four,jSign,Fin.sum_univ_four,m.trace]
theorem A_hermitian {p : Prob} (m : Model p) (x : Bool) : (A m x)ᴴ=A m x := by
  simp [A,left,combo,four,vSign,Fin.sum_univ_four,m.hermitian]
theorem B_hermitian {p : Prob} (m : Model p) (y : Bool) : (B m y)ᴴ=B m y := by
  simp [B,right,combo,four,hSign,Fin.sum_univ_four,m.hermitian]

private theorem ref4 {p : Prob} (m : Model p) (i : Fin 4) :
    four m false false i=projection (⇑(axis i)) := m.reference i

theorem first_A {p : Prob} (m : Model p) : A m false=va := by
  simp only [A,left,combo,ref4,Fin.sum_univ_four]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [vSign,projection,axis,Matrix.vecMulVec_apply,
    PiLp.single_apply,va,vertical]
theorem first_B {p : Prob} (m : Model p) : B m false=hb := by
  simp only [B,right,combo,ref4,Fin.sum_univ_four]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [hSign,projection,axis,Matrix.vecMulVec_apply,
    PiLp.single_apply,hb,horizontal]

private theorem exp_add (f : V) (m n : M) :
    expectation f (m+n)=expectation f m+expectation f n := by
  simp [expectation,ip,Matrix.add_mulVec,dotProduct_add]
private theorem exp_neg (f : V) (m : M) : expectation f (-m) = -expectation f m := by
  simp [expectation,ip,Matrix.neg_mulVec,dotProduct_neg]

private def noisy_data {ε : ℝ} (m : Model (noisy ε)) : PairData (1-2*ε) (A m) (B m) where
  state := m.state
  orth := m.orth
  leftMean i x := by
    cases x <;> cases i <;> norm_num [A,left,combo,four,cell,order,box,vSign,Fin.sum_univ_four,
      exp_add,exp_neg,m.born,noisy,noisyWeight,pattern,line,firstOutcome,first,second]
  rightMean i y := by
    cases y <;> cases i <;> norm_num [B,right,combo,four,cell,order,box,hSign,Fin.sum_univ_four,
      exp_add,exp_neg,m.born,noisy,noisyWeight,pattern,line,firstOutcome,first,second]
  joint i x y := by
    rw [AB]
    cases x <;> cases y <;> cases i <;>
      norm_num [joint,combo,four,cell,order,box,jSign,Fin.sum_univ_four,
        exp_add,exp_neg,m.born,noisy,noisyWeight,pattern,line,firstOutcome,first,second,entry] <;> ring

theorem epsilon_of_quantum {ε : ℝ} (h : ArbitraryMeasurement (noisy ε)) : ε=1/2 := by
  obtain ⟨m⟩ := normalized h
  have ca : A m true*hb=hb*A m true := by rw [←first_B m,AB,BA]
  have cb : B m true*va=va*B m true := by rw [←first_A m,AB,BA]
  have ta : (A m true*hb).trace=0 := by rw [←first_B m,AB,joint_trace]
  have tb : (B m true*va).trace=0 := by rw [←first_A m,BA,joint_trace]
  obtain ⟨a,b,z,w,vform⟩ := vertical_form _ (A_hermitian m true) ca (A_trace m true) ta
  obtain ⟨c,d,u,v,hform⟩ := horizontal_form _ (B_hermitian m true) cb (B_trace m true) tb
  have av : A m=chooseObs va (vertical a b z w) := by
    funext x; cases x; exact first_A m; exact vform
  have bh : B m=chooseObs hb (horizontal c d u v) := by
    funext x; cases x; exact first_B m; exact hform
  have p := noisy_data m
  rw [av,bh] at p
  have e := structured_forces_zero (vform ▸ AA m true) (hform ▸ BB m true)
    (by rw [←vform,←hform,AB,BA]) p
  linarith

#print axioms epsilon_of_quantum
end FractionalSettings
