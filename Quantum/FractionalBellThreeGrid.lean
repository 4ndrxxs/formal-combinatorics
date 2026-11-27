module
public import Quantum.FractionalBlockPolytope

/-! A ternary, rational product SudoQ and its scalar CHSH functional.
All row, column and block Grams and the witness value are finite integer
identities. Vectors are expressed in measurement coordinates. -/
@[expose] public section
noncomputable section
namespace FractionalBellThree
open QuantumSudoku FractionalLayouts FractionalBlockBell FractionalPolygons.Sudoku
  Complex Matrix Finset
open scoped BigOperators ComplexConjugate

abbrev F := Fin 3
abbrev Two := Fin 2
abbrev P := BigProb F
def id5 : F → F → ℤ := !![5,0,0;0,5,0;0,0,5]
def rot : F → F → ℤ := !![4,3,0;-3,4,0;0,0,5]
def rotT : F → F → ℤ := !![4,-3,0;3,4,0;0,0,5]
def localA (x : F) := if x=1 then rot else id5
def localB (y : F) := if y=0 then rot else if y=1 then rotT else id5
def tag (a : Two) : F := ⟨a.val,by omega⟩
def aDigit (q : Site F) : F := q.1.2+q.1.1+q.2.1
def bDigit (q : Site F) : F := q.2.2+q.1.1+q.2.1
def productEntry (q : Site F) (k : Index F) : ℤ :=
  localA q.1.1 (aDigit q) k.1 * localB q.2.1 (bDigit q) k.2

def raw (q : Site F) (k : Index F) : ℤ :=
  if k=(0,0) then 3*productEntry q (0,0)+4*productEntry q (1,1)
  else if k=(1,1) then -4*productEntry q (0,0)+3*productEntry q (1,1)
  else 5*productEntry q k

def v (r c : Index F) : H F := WithLp.toLp 2 (fun k => (raw (r,c) k:ℂ)/125)
def data (q : Site F) (k : Index F) : ℝ := (raw q k:ℝ)^2/15625
def zeroSymbol : Index F := (0,0)

theorem v_rational : RationalEntries v := fun r c k => ⟨(raw (r,c) k:ℚ)/125,by simp [v]⟩
theorem born (q : Site F) (k : Index F) : normSq (v q.1 q.2 k)=data q k := by
  norm_num [v,data,Complex.normSq_div,Complex.normSq_intCast,Complex.normSq_ofNat]
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem gramZ : ∀ d : Direction, ∀ a i j : Index F,
    (∑ k, raw (arrange d (a,j)) k * raw (arrange d (a,i)) k)=
      if i=j then 15625 else 0 := by intro d; cases d <;> decide +kernel

theorem v_valid : Valid v := by
  have lines (d : Direction) (a i j : Index F) :
      inner ℂ (v (arrange d (a,i)).1 (arrange d (a,i)).2)
        (v (arrange d (a,j)).1 (arrange d (a,j)).2)=if i=j then 1 else 0 := by
    have g : (∑ k, (raw (arrange d (a,j)) k:ℂ) * (raw (arrange d (a,i)) k:ℂ))=
        if i=j then 15625 else 0 := by exact_mod_cast gramZ d a i j
    have term (x y : ℤ) : ((x:ℂ)/125)*conj ((y:ℂ)/125)=((x:ℂ)*(y:ℂ))/15625 := by
      norm_num [map_ofNat]; ring
    rw [PiLp.inner_apply]
    change (∑ k, ((raw (arrange d (a,j)) k:ℂ)/125)*conj ((raw (arrange d (a,i)) k:ℂ)/125))=_
    rw [show (∑ k, ((raw (arrange d (a,j)) k:ℂ)/125)*conj ((raw (arrange d (a,i)) k:ℂ)/125))=
        (∑ k, ((raw (arrange d (a,j)) k:ℂ)*(raw (arrange d (a,i)) k:ℂ)))/15625 by
      simp only [term,Finset.sum_div],g]
    split <;> norm_num
  exact ⟨fun r => basis_of_gram _ (lines .row r),fun c => basis_of_gram _ (lines .column c),
    fun x y => basis_of_gram _ (lines .block (x,y))⟩

def binpos (xy : Index Two) (rc : Index F) : Site F :=
  arrange .block ((tag xy.1,tag xy.2),rc)
def pay (x y : Two) (a b : F) : ℤ :=
  if (decide (a=1) ^^ decide (b=1)) ^^ (decide (x=1) && decide (y=1)) then -1 else 1
def coeff (xy : Index Two) (rc : Index F) := pay xy.1 xy.2 (aDigit (binpos xy rc)) (bDigit (binpos xy rc))

def score (p : P) : ℝ := ∑ xy : Index Two, ∑ rc : Index F, (coeff xy rc:ℝ)*p (binpos xy rc) zeroSymbol
def supported (p : P) : Prop := ∀ q, aDigit q=2 ∨ bDigit q=2 → p q zeroSymbol=0

theorem data_supported : supported data := by
  have z : ∀ q : Site F, aDigit q=2 ∨ bDigit q=2 → raw q zeroSymbol=0 := by decide +kernel
  intro q h
  simp [data,z q h]

theorem data_score : score data=36398/15625 := by
  have calcZ : (∑ xy : Index Two, ∑ rc : Index F,
      coeff xy rc * (raw (binpos xy rc) zeroSymbol)^2)=36398 := by decide +kernel
  have realZ : (∑ xy : Index Two, ∑ rc : Index F,
      (coeff xy rc:ℝ) * (raw (binpos xy rc) zeroSymbol:ℝ)^2)=36398 := by exact_mod_cast calcZ
  simp only [score,data,mul_div_assoc',←Finset.sum_div,realZ]

theorem score_affine (p q : P) (a b : ℝ) :
    score (a • p+b • q)=a*score p+b*score q := by
  simp only [score,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro _ _
  apply Finset.sum_congr rfl
  intro _ _
  ring

end FractionalBellThree

