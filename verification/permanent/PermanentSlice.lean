import PermanentWitnesses
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! A five-dimensional linear test space for the singular locus of the
generic permanent. Its first partials contain a power of each coordinate
after restriction. The certificate uses only integer arithmetic. -/

namespace PermanentFive
open Finset Equiv MvPolynomial
variable {R : Type*} [CommRing R]

/-- Each parameter occupies four cells of a cyclic diagonal. -/
def slice (x : Idx → R) (c : Cell) : R :=
  if c.2 ≠ 2*c.1 then x (c.2-c.1) else 0

private abbrev Word := Multiset Idx

private def readWord (x : Idx → R) (w : Word) : R := (w.map x).prod

private def readWords (x : Idx → R) : Multiset Word →+ R :=
  Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom (readWord x))

private def gradWords (e : Cell) : Multiset Word :=
  ∑ p : Perm Idx, if p e.2 = e.1 ∧ ∀ j ∈ univ.erase e.2, j ≠ 2*p j
    then {((univ.erase e.2).val.map (fun j ↦ j - p j))} else 0

@[simp] private lemma read_single (x : Idx → R) (w : Word) :
    readWords x {w} = readWord x w := by
  change (({w} : Multiset Word).map (readWord x)).sum = _
  simp

private lemma read_gradient (x : Idx → R) (e : Cell) :
    gradAt (slice x) e = readWords x (gradWords e) := by
  rw [gradAt,gradWords,map_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : p e.2 = e.1
  · rw [ite_eq_left h]
    simp only [slice,Finset.prod_ite_zero]
    by_cases ok : ∀ j ∈ univ.erase e.2, j ≠ 2*p j
    · rw [ite_eq_left ok,ite_eq_left ⟨h,ok⟩,read_single]
      simp only [readWord,Finset.prod,Multiset.map_map,Function.comp_def]
    · rw [ite_eq_right ok,ite_eq_right (fun v ↦ ok v.2),map_zero]
  · simp [h]

private def baseWords : Idx → List (List Idx)
  | 0 => [[0,0,0,0],[0,0,1,4],[0,0,2,3],[0,1,1,3],[0,1,2,2],[0,2,4,4],[0,3,3,4],[1,2,3,4],[1,2,3,4]]
  | 1 => [[0,0,0,4],[0,0,1,3],[0,0,2,2],[0,1,1,2],[0,1,4,4],[0,2,3,4],[0,3,3,3],[1,1,3,4],[1,1,3,4],[1,2,3,3],[1,2,3,3]]
  | 2 => [[0,0,0,3],[0,0,1,2],[0,0,4,4],[0,1,1,1],[0,1,3,4],[0,2,2,4],[0,2,3,3],[1,1,2,4],[1,1,2,4],[1,2,2,3],[1,2,2,3]]
  | 3 => [[0,0,0,2],[0,0,1,1],[0,0,3,4],[0,1,2,4],[0,1,3,3],[0,2,2,3],[0,4,4,4],[1,3,4,4],[1,3,4,4],[2,3,3,4],[2,3,3,4]]
  | 4 => [[0,0,0,1],[0,0,2,4],[0,0,3,3],[0,1,1,4],[0,1,2,3],[0,2,2,2],[0,3,4,4],[1,2,4,4],[1,2,4,4],[2,2,3,4],[2,2,3,4]]

private def wordsAt (r c : Idx) : Multiset Word :=
  ((baseWords (c-2*r)).map (fun l ↦ ((l.map (fun j ↦ j+r) : List Idx) : Word)) : List Word)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2400000 in
private theorem word_table (r c : Idx) : gradWords (r,c) = wordsAt r c := by
  fin_cases r <;> fin_cases c <;> decide +kernel

private def quartic (x : Idx → R) (r c : Idx) : R :=
  ((baseWords (c-2*r)).map (fun l ↦ (l.map (fun j ↦ x (j+r))).prod)).sum

private theorem grad_quartic (x : Idx → R) (r c : Idx) :
    gradAt (slice x) (r,c) = quartic x r c := by
  rw [read_gradient,word_table]
  change (((wordsAt r c).map (readWord x)).sum) = _
  simp [wordsAt,quartic,readWord,List.map_map,Function.comp_def]

private lemma quartic_shift (x : Idx → R) (t r c : Idx) :
    quartic (fun i ↦ x (i+t)) r c = quartic x (r+t) (c+2*t) := by
  have rel : ∀ a b d : Idx, d + 2*a - 2*(b+a) = d-2*b := by decide +kernel
  have eq := rel t r c
  simp only [quartic,eq,add_assoc]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2400000 in
private theorem power_identity (x : Idx → R) :
    8 * (x 0)^6 =
      (8*x 0*x 0 + 2*x 2*x 3) * quartic x 0 0 +
      (-3*x 0*x 1) * quartic x 0 1 +
      (-11*x 0*x 2 - 4*x 1*x 1 - 2*x 3*x 4) * quartic x 0 2 +
      (x 0*x 3 + 4*x 1*x 2) * quartic x 0 3 +
      (-11*x 0*x 4 - 6*x 1*x 3) * quartic x 0 4 +
      (6*x 0*x 4 + 6*x 2*x 2) * quartic x 1 0 +
      (-4*x 0*x 0 - 4*x 1*x 4 - 4*x 2*x 3) * quartic x 1 1 +
      (4*x 0*x 1 - 2*x 2*x 4) * quartic x 1 2 +
      (4*x 0*x 2 - 4*x 3*x 4) * quartic x 1 3 +
      (6*x 1*x 2 + 4*x 4*x 4) * quartic x 1 4 +
      (6*x 0*x 3 - 10*x 1*x 2) * quartic x 2 0 +
      (4*x 1*x 3 - 4*x 2*x 2) * quartic x 2 1 +
      (2*x 0*x 0 + 6*x 1*x 4 + 4*x 2*x 3) * quartic x 2 2 +
      (4*x 0*x 2 + 2*x 1*x 1) * quartic x 2 4 := by
  dsimp [quartic,baseWords]
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,List.sum_cons,List.sum_nil,mul_one,add_zero]
  simp only [show (0+1 : Idx) = 1 by decide,
    show (1+1 : Idx) = 2 by decide,
    show (2+1 : Idx) = 3 by decide,
    show (3+1 : Idx) = 4 by decide,
    show (4+1 : Idx) = 0 by decide,
    show (0+2 : Idx) = 2 by decide,
    show (1+2 : Idx) = 3 by decide,
    show (2+2 : Idx) = 4 by decide,
    show (3+2 : Idx) = 0 by decide,
    show (4+2 : Idx) = 1 by decide]
  ring

private lemma first_zero {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (x : Idx → K)
    (h : ∀ r c, quartic x r c = 0) : x 0 = 0 := by
  have hp : 8*(x 0)^6 = 0 := by rw [power_identity]; simp [h]
  rcases mul_eq_zero.mp hp with hc | hx
  · norm_num at hc
  · simpa using hx

/-- The ambient gradient of the five-by-five permanent vanishes at a
point of this five-parameter slice only when all its parameters vanish. -/
theorem slice_isolated {K : Type*} [CommRing K] [IsDomain K] [CharZero K] (x : Idx → K)
    (h : ∀ e : Cell, MvPolynomial.eval (slice x) (pderiv e (per K Idx)) = 0) : x = 0 := by
  have zero (r c : Idx) : quartic x r c = 0 := by
    rw [← grad_quartic,← grad_formula]
    exact h _
  funext t
  have ht := first_zero (fun i ↦ x (i+t))
    (fun r c ↦ (quartic_shift x t r c).trans (zero _ _))
  simpa using ht

/-- One quadratic monomial multiplying an ambient gradient entry in the slice certificate. -/
structure SliceCoeffTerm where
  coeff : ℤ
  first : Idx
  second : Idx
  entry : Cell

def sliceCoeffTerms : List SliceCoeffTerm :=
  [⟨8,0,0,(0,0)⟩,
   ⟨2,2,3,(0,0)⟩,
   ⟨-3,0,1,(0,1)⟩,
   ⟨-11,0,2,(0,2)⟩,
   ⟨-4,1,1,(0,2)⟩,
   ⟨-2,3,4,(0,2)⟩,
   ⟨1,0,3,(0,3)⟩,
   ⟨4,1,2,(0,3)⟩,
   ⟨-11,0,4,(0,4)⟩,
   ⟨-6,1,3,(0,4)⟩,
   ⟨6,0,4,(1,0)⟩,
   ⟨6,2,2,(1,0)⟩,
   ⟨-4,0,0,(1,1)⟩,
   ⟨-4,1,4,(1,1)⟩,
   ⟨-4,2,3,(1,1)⟩,
   ⟨4,0,1,(1,2)⟩,
   ⟨-2,2,4,(1,2)⟩,
   ⟨4,0,2,(1,3)⟩,
   ⟨-4,3,4,(1,3)⟩,
   ⟨6,1,2,(1,4)⟩,
   ⟨4,4,4,(1,4)⟩,
   ⟨6,0,3,(2,0)⟩,
   ⟨-10,1,2,(2,0)⟩,
   ⟨4,1,3,(2,1)⟩,
   ⟨-4,2,2,(2,1)⟩,
   ⟨2,0,0,(2,2)⟩,
   ⟨6,1,4,(2,2)⟩,
   ⟨4,2,3,(2,2)⟩,
   ⟨4,0,2,(2,4)⟩,
   ⟨2,1,1,(2,4)⟩]

def sliceCombine (x : Idx → R) (g : Cell → R) : R :=
  (sliceCoeffTerms.map (fun a ↦ (a.coeff : R)*x a.first*x a.second*g a.entry)).sum

/-- Each sixth power belongs to the gradient ideal with homogeneous quadratic coefficients. -/
theorem slice_power_combination (x : Idx → R) (t : Idx) :
    8*(x t)^6 = sliceCombine (fun j ↦ x (j+t))
      (fun e ↦ gradAt (slice x) (e.1+t,e.2+2*t)) := by
  calc
    8*(x t)^6 = 8*((fun j : Idx ↦ x (j+t)) 0)^6 := by simp
    _ = _ := (power_identity (fun j ↦ x (j+t))).trans (by
      simp only [sliceCombine,sliceCoeffTerms,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        grad_quartic,quartic_shift]
      push_cast
      ring)

#print axioms slice_power_combination

#print axioms slice_isolated
end PermanentFive
