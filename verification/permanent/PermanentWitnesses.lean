import PermanentFive
import Mathlib.Tactic.FinCases

/-! Exact first and second derivatives of the generic permanent. Removing
the differentiated columns leaves a product over the remaining entries
of the permutation. All finite certificates are evaluated by the kernel. -/

open MvPolynomial Equiv Finset Matrix
noncomputable section
namespace PermanentFive
open QuinticPencil
variable {R T I : Type*} [CommRing R] [CommRing T] [Fintype I] [DecidableEq I]

private def term (R : Type*) [CommRing R] (p : Perm I) (s : Finset I) :
    MvPolynomial (I × I) R := ∏ j ∈ s, X (p j,j)

omit [Fintype I] in
private theorem independent (p : Perm I) (s : Finset I) (e : I × I) (absent : e.2 ∉ s) :
    pderiv e (term R p s) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp [term]
  | insert j s hj ih =>
    have ne : (p j,j) ≠ e := fun eq ↦ absent (by rw [← eq]; simp)
    have no : e.2 ∉ s := fun h ↦ absent (mem_insert_of_mem h)
    rw [term,prod_insert hj,pderiv_mul,pderiv_X_of_ne ne,zero_mul,zero_add]
    change _ * pderiv e (term R p s) = 0
    simp [ih no]

omit [Fintype I] in
private theorem derivative_term (p : Perm I) (s : Finset I) (e : I × I) :
    pderiv e (term R p s) =
      if e.2 ∈ s ∧ p e.2 = e.1 then term R p (s.erase e.2) else 0 := by
  by_cases mem : e.2 ∈ s
  · have split : term R p s = X (p e.2,e.2) * term R p (s.erase e.2) :=
      (Finset.mul_prod_erase s _ mem).symm
    rw [split,pderiv_mul,independent _ _ _ (Finset.notMem_erase _ _),mul_zero,add_zero]
    by_cases row : p e.2 = e.1
    · simp [mem,row]
    · have cell : (p e.2,e.2) ≠ e := fun h ↦ row (congrArg Prod.fst h)
      simp [mem,row,pderiv_X_of_ne cell]
  · simp [independent p s e mem,mem]

/-- First and second derivatives as finite arithmetic sums. -/
def gradAt (z : I × I → R) (e : I × I) : R :=
  ∑ p : Perm I, if p e.2 = e.1 then ∏ j ∈ univ.erase e.2, z (p j,j) else 0

def secondAt (z : I × I → R) (e f : I × I) : R :=
  ∑ p : Perm I, if p f.2 = f.1 ∧ e.2 ≠ f.2 ∧ p e.2 = e.1
    then ∏ j ∈ (univ.erase f.2).erase e.2, z (p j,j) else 0

private lemma per_terms : per R I = ∑ p : Perm I, term R p univ := rfl

theorem grad_formula (z : I × I → R) (e : I × I) :
    MvPolynomial.eval z (pderiv e (per R I)) = gradAt z e := by
  rw [per_terms,map_sum,map_sum,gradAt]
  apply Finset.sum_congr rfl
  intro p _
  rw [derivative_term]
  by_cases h : p e.2 = e.1 <;> simp [h,term]

theorem second_formula (z : I × I → R) (e f : I × I) :
    hessian (per R I) z e f = secondAt z e f := by
  change MvPolynomial.eval z (pderiv e (pderiv f (per R I))) = _
  rw [per_terms,map_sum,map_sum,map_sum,secondAt]
  apply Finset.sum_congr rfl
  intro p _
  rw [derivative_term p univ f]
  by_cases h : p f.2 = f.1
  · rw [ite_eq_left ⟨mem_univ _,h⟩,derivative_term]
    by_cases k : e.2 = f.2 <;> by_cases l : p e.2 = e.1 <;> simp [h,k,l,term]
  · simp [h]

theorem grad_map (f : R →+* T) (z : I × I → R) (e : I × I) :
    gradAt (f ∘ z) e = f (gradAt z e) := by
  simp [gradAt,apply_ite f]

theorem second_map (f : R →+* T) (z : I × I → R) (a b : I × I) :
    secondAt (f ∘ z) a b = f (secondAt z a b) := by
  simp [secondAt,apply_ite f]

def matchPoint (d : ℕ) (c : Cell) : ℤ := if c.1 = c.2 ∧ c.1.val < d then 1 else 0
def rowPoint (c : Cell) : ℤ := if c.1.val < 3 then 1 else 0
def square : Fin 4 → Cell := ![(3,3),(3,4),(4,3),(4,4)]
def lowRow (i : Idx) : Cell := (3,i)
def highRow (i : Idx) : Cell := (4,i)
def fourMinor : Matrix (Fin 4) (Fin 4) ℤ := Matrix.of (fun i j ↦ if i.val + j.val = 3 then 1 else 0)
def fiveMinor : Matrix Idx Idx ℤ := Matrix.of (fun i j ↦ if i=j then 0 else 6)

set_option maxRecDepth 12000 in
private theorem four_first : gradAt (matchPoint 4) (4,4) = 1 := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem three_entries : ∀ i j : Fin 4,
    secondAt (matchPoint 3) (square i) (square j) = fourMinor i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem row_entries : ∀ i j : Idx,
    secondAt rowPoint (lowRow i) (highRow j) = fiveMinor i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem four_det : fourMinor.det = 1 := by decide +kernel
private theorem five_det : fiveMinor.det = 31104 := by decide +kernel

variable (K : Type*) [Field K] [CharZero K]

omit [CharZero K] in
/-- A four-edge matching makes the missing first partial equal to one. -/
theorem four_gradient : MvPolynomial.eval ((Int.castRingHom K) ∘ matchPoint 4)
    (pderiv ((4,4) : Cell) (per K Idx)) = 1 := by
  rw [grad_formula,grad_map,four_first,map_one]

omit [CharZero K] in
private theorem minor_cast (z : Cell → ℤ) {m : Type*} [Fintype m] [DecidableEq m]
    (r c : m → Cell) (M : Matrix m m ℤ)
    (entries : ∀ i j, secondAt z (r i) (c j) = M i j) :
    (hessian (per K Idx) ((Int.castRingHom K) ∘ z)).submatrix r c =
      (Int.castRingHom K).mapMatrix M := by
  ext i j
  change hessian (per K Idx) ((Int.castRingHom K) ∘ z) (r i) (c j) = (Int.castRingHom K) (M i j)
  rw [second_formula,second_map,entries]

private theorem rank_witness (z : Cell → ℤ) {m : Type*} [Fintype m] [DecidableEq m]
    (r c : m → Cell) (M : Matrix m m ℤ)
    (entries : ∀ i j, secondAt z (r i) (c j) = M i j) (nz : M.det ≠ 0) :
    Fintype.card m ≤ (hessian (per K Idx) ((Int.castRingHom K) ∘ z)).rank := by
  have le := Matrix.rank_submatrix_le (hessian (per K Idx) ((Int.castRingHom K) ∘ z)) r c
  rw [minor_cast K z r c M entries,Matrix.rank_of_det_ne_zero] at le
  · exact le
  · rw [← RingHom.map_det]
    change (M.det : K) ≠ 0
    exact_mod_cast nz

/-- The complementary four cells detect rank four at a three-edge matching. -/
theorem match_rank : 4 ≤ (hessian (per K Idx) ((Int.castRingHom K) ∘ matchPoint 3)).rank :=
  rank_witness K _ square square fourMinor three_entries (by rw [four_det]; decide)

/-- The two omitted rows give a nonsingular five-by-five Hessian minor. -/
theorem row_rank : 5 ≤ (hessian (per K Idx) ((Int.castRingHom K) ∘ rowPoint)).rank :=
  rank_witness K _ lowRow highRow fiveMinor row_entries (by rw [five_det]; decide)

#print axioms four_gradient
#print axioms match_rank
#print axioms row_rank
end PermanentFive
