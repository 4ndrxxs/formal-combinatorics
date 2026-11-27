module
public import Quantum.FractionalGauge

/-! The labelled first block determines the support patterns of the other
binary observables through commutation and their two trace identities. -/
@[expose] public section
noncomputable section
namespace FractionalForms
open Complex Matrix FractionalTensor
open scoped ComplexConjugate Matrix

def vSign : V := ![1,1,-1,-1]
def hSign : V := ![1,-1,1,-1]

theorem va_eq : va=Matrix.diagonal vSign := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [va,vertical,vSign,Matrix.diagonal_apply]
theorem hb_eq : hb=Matrix.diagonal hSign := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [hb,horizontal,hSign,Matrix.diagonal_apply]

private theorem unsupported (m : M) (s : V)
    (h : m*Matrix.diagonal s=Matrix.diagonal s*m) (i j : Fin 4) (ne : s i≠s j) :
    m i j=0 := by
  have hh := congrFun (congrFun h i) j
  simp [Matrix.mul_diagonal,Matrix.diagonal_mul] at hh
  have zero : (s i-s j)*m i j=0 := by linear_combination -hh
  exact (mul_eq_zero.mp zero).resolve_left (sub_ne_zero.mpr ne)

private theorem hermitian_entry (m : M) (h : mᴴ=m) (i j : Fin 4) : m j i=conj (m i j) :=
  (congrFun (congrFun h j) i).symm

private theorem real_diagonal (m : M) (h : mᴴ=m) (i : Fin 4) :
    ((m i i).re:ℂ)=m i i := by
  apply Complex.ext (by simp)
  have e := congrArg Complex.im (hermitian_entry m h i i)
  simp at e ⊢
  linarith

theorem vertical_form (m : M) (h : mᴴ=m) (comm : m*hb=hb*m)
    (tr : m.trace=0) (trB : (m*hb).trace=0) :
    ∃ (a b : ℝ) (z w : ℂ), m=vertical a b z w := by
  rw [hb_eq] at comm trB
  simp [Matrix.trace,Matrix.diag,Matrix.mul_diagonal,hSign,Fin.sum_univ_four] at tr trB
  have rr (i : Fin 4) := real_diagonal m h i
  have down (i j : Fin 4) := hermitian_entry m h i j
  have low0 : m 2 2= -(m 0 0) := by linear_combination (tr+trB)/2
  have low1 : m 3 3= -(m 1 1) := by linear_combination (tr-trB)/2
  refine ⟨(m 0 0).re,(m 1 1).re,m 0 2,m 1 3,?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vertical,rr,low0,low1] <;>
    first | exact down _ _ | exact unsupported m hSign comm _ _ (by norm_num [hSign])

theorem horizontal_form (m : M) (h : mᴴ=m) (comm : m*va=va*m)
    (tr : m.trace=0) (trA : (m*va).trace=0) :
    ∃ (a b : ℝ) (z w : ℂ), m=horizontal a b z w := by
  rw [va_eq] at comm trA
  simp [Matrix.trace,Matrix.diag,Matrix.mul_diagonal,vSign,Fin.sum_univ_four] at tr trA
  have rr (i : Fin 4) := real_diagonal m h i
  have down (i j : Fin 4) := hermitian_entry m h i j
  have low0 : m 1 1= -(m 0 0) := by linear_combination (tr+trA)/2
  have low1 : m 3 3= -(m 2 2) := by linear_combination (tr-trA)/2
  refine ⟨(m 0 0).re,(m 2 2).re,m 0 1,m 2 3,?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [horizontal,rr,low0,low1] <;>
    first | exact down _ _ | exact unsupported m vSign comm _ _ (by norm_num [vSign])

end FractionalForms
