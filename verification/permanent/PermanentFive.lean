import QuinticTorus
import PermanentCoefficientSigns
import PermanentSupports

/-! The coordinate consequence of a regular affine determinant for the
ordinary five-by-five permanent. The polynomial is Mathlib's permanent of
the generic matrix. -/

noncomputable section
open Matrix MvPolynomial Equiv Finset
namespace PermanentFive
open QuinticPencil

abbrev Idx := Fin 5
abbrev Cell := Idx × Idx

def per (K : Type*) [CommRing K] (I : Type*) [Fintype I] [DecidableEq I] :
    MvPolynomial (I × I) K := (PermanentCuts.generic K I).permanent

theorem per_homogeneous (K I : Type*) [CommRing K] [Fintype I] [DecidableEq I] :
    (per K I).IsHomogeneous (Fintype.card I) := by
  unfold per Matrix.permanent
  apply IsHomogeneous.sum
  intro p _
  simpa [PermanentCuts.generic] using IsHomogeneous.prod univ (fun i ↦ X (R := K) (p i,i)) (fun _ ↦ 1)
    (fun i _ ↦ isHomogeneous_X K (p i,i))

theorem row_column_twist {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (a b : I → K) :
    twist (fun u : I × I ↦ a u.1*b u.2) (per K I) =
      C ((∏ i, a i)*(∏ i, b i)) * per K I := by
  unfold per Matrix.permanent
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [map_prod, PermanentCuts.generic, Matrix.of_apply]
  simp only [twist, MvPolynomial.eval₂Hom_X']
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_mul_distrib, Equiv.prod_comp p]

def weight (c : Cell) := 5*c.1.val+c.2.val

private theorem distinct : Function.Injective weight := by
  rintro ⟨i,j⟩ ⟨k,l⟩ h
  change 5*i.val+j.val = 5*k.val+l.val at h
  apply Prod.ext
  · apply Fin.ext; change i.val = k.val; omega
  · apply Fin.ext; change j.val = l.val; omega

/-- The precise necessary condition on coordinate supports for a regular
determinantal expression of the generic permanent of order five. -/
theorem regular_coordinate_support {K n : Type*} [Field K] [Infinite K] [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (F : Cell → Matrix n n K) (regular : Fintype.card n = A.rank+1)
    (rep : per K Idx = (affineMatrix A F).det) :
    ∃ S : Finset Cell, ∀ z : Cell → K, (∀ j ∉ S, z j = 0) →
      (∀ i, MvPolynomial.eval z (pderiv i (per K Idx)) = 0) ∧
      26 + (hessian (per K Idx) z).rank ≤ Fintype.card n + S.card := by
  have hom : (per K Idx).IsHomogeneous 5 := per_homogeneous K Idx
  obtain ⟨S,hS⟩ := coordinate_kernel A F regular rep hom weight distinct (fun t _ ↦ by
    refine ⟨(∏ i : Idx, t^(5*i.val))*(∏ j : Idx, t^j.val),?_⟩
    simpa [weight,pow_add] using row_column_twist (fun i : Idx ↦ t^(5*i.val)) (fun j : Idx ↦ t^j.val))
  refine ⟨S,fun z h ↦ ⟨(hS z h).1,?_⟩⟩
  have rank := (hS z h).2
  change 25 + (hessian (per K Idx) z).rank + 1 ≤ Fintype.card n + S.card at rank
  rwa [Nat.add_right_comm] at rank

#print axioms per_homogeneous
#print axioms row_column_twist
#print axioms regular_coordinate_support
end PermanentFive
