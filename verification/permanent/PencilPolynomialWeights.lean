import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Tactic
/-! Weighted leading coefficients of polynomial matrices and their determinants. -/
noncomputable section
open Polynomial Matrix Finset
namespace PencilWeight
variable {R : Type*} [CommRing R]
def Top (p : R[X]) (d : ℕ) (a : R) : Prop := p.natDegree ≤ d ∧ p.coeff d = a

theorem top_add {p q : R[X]} {d : ℕ} {a b : R} (h : Top p d a) (k : Top q d b) :
    Top (p+q) d (a+b) :=
  ⟨((natDegree_add_le p q).trans (max_le h.1 k.1)),by rw [coeff_add,h.2,k.2]⟩

theorem top_mul {p q : R[X]} {d e : ℕ} {a b : R} (h : Top p d a) (k : Top q e b) :
    Top (p*q) (d+e) (a*b) :=
  ⟨natDegree_mul_le.trans (Nat.add_le_add h.1 k.1),
    by rw [coeff_mul_add_eq_of_natDegree_le h.1 k.1,h.2,k.2]⟩

theorem top_sum {I : Type*} (S : Finset I) (p : I → R[X]) (d : ℕ) (a : I → R)
    (h : ∀ i ∈ S, Top (p i) d (a i)) : Top (∑ i ∈ S, p i) d (∑ i ∈ S, a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Top]
  | insert i S hi ih =>
    rw [sum_insert hi,sum_insert hi]
    exact top_add (h i (mem_insert_self ..)) (ih fun j hj ↦ h j (mem_insert_of_mem hj))

theorem top_prod {I : Type*} (S : Finset I) (p : I → R[X]) (d : I → ℕ) (a : I → R)
    (h : ∀ i ∈ S, Top (p i) (d i) (a i)) :
    Top (∏ i ∈ S, p i) (∑ i ∈ S, d i) (∏ i ∈ S, a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Top]
  | insert i S hi ih =>
    rw [prod_insert hi,sum_insert hi,prod_insert hi]
    exact top_mul (h i (mem_insert_self ..)) (ih fun j hj ↦ h j (mem_insert_of_mem hj))

theorem top_det {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n R[X])
    (d : n → ℕ) (N : Matrix n n R) (h : ∀ i j, Top (M i j) (d j) (N i j)) :
    Top M.det (∑ j, d j) N.det := by
  classical
  rw [Matrix.det_apply,Matrix.det_apply]
  apply top_sum
  intro p _
  have term := top_prod univ (fun j ↦ M (p j) j) d (fun j ↦ N (p j) j) (fun j _ ↦ h _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with eq | eq
  · simpa only [eq,one_smul] using term
  · simp only [eq,Units.neg_smul,one_smul]
    exact ⟨by simpa only [natDegree_neg] using term.1,by simp only [coeff_neg,term.2]⟩

theorem top_matrix_mul {I J H : Type*} [Fintype J] (A : Matrix I J R[X])
    (B : Matrix J H R[X]) (a : Matrix I J R) (b : Matrix J H R)
    (d e : ℕ) (ha : ∀ i j, Top (A i j) d (a i j)) (hb : ∀ j k, Top (B j k) e (b j k)) :
    ∀ i k, Top ((A*B) i k) (d+e) ((a*b) i k) := by
  intro i k
  exact top_sum univ _ _ _ fun j _ ↦ top_mul (ha i j) (hb j k)

theorem top_matrix_pow {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I R[X])
    (a : Matrix I I R) (h : ∀ i j, Top (A i j) 1 (a i j)) (r : ℕ) :
    ∀ i j, Top ((A^r) i j) r ((a^r) i j) := by
  induction r with
  | zero =>
    intro i j
    by_cases eq : i=j <;> simp [eq,Top]
  | succ r ih =>
    simpa only [pow_succ] using top_matrix_mul (A^r) A (a^r) a r 1 ih h

#print axioms top_det
#print axioms top_matrix_pow
end PencilWeight
