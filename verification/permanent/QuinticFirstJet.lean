import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import QuinticOddZero

/-! Evaluating at a square-zero parameter records exactly the constant
and linear coefficients. A matrix with purely infinitesimal off-diagonal
entries has determinant equal to the product of its diagonal entries. -/

open Matrix Polynomial TrivSqZeroExt
open scoped DualNumber
namespace QuinticPencil
variable {R S I : Type*} [CommRing R] [CommRing S]

/-- Coefficientwise application of a ring map to a dual number. -/
def jetMap (f : R →+* S) : DualNumber R →+* DualNumber S where
  toFun x := ⟨f x.fst,f x.snd⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · exact map_add f x.fst y.fst
    · exact map_add f x.snd y.snd
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · exact map_mul f x.fst y.fst
    · change f (x.fst*y.snd+x.snd*y.fst) = f x.fst * f y.snd + f x.snd * f y.fst
      rw [map_add,map_mul,map_mul]

def firstJet (R : Type*) [CommRing R] : R[X] →+* DualNumber R :=
  Polynomial.eval₂RingHom (TrivSqZeroExt.inlHom R R) DualNumber.eps

theorem firstJet_components (p : R[X]) :
    (firstJet R p).fst = p.coeff 0 ∧ (firstJet R p).snd = p.coeff 1 := by
  induction p using Polynomial.induction_on' with
  | add a b ha hb => simp [map_add,ha,hb]
  | monomial n a =>
    change ((Polynomial.eval₂ (TrivSqZeroExt.inlHom R R) DualNumber.eps) _).fst = _ ∧
      ((Polynomial.eval₂ (TrivSqZeroExt.inlHom R R) DualNumber.eps) _).snd = _
    rcases n with _ | n
    · simp
    rcases n with _ | n
    · simp
    · have kill : (DualNumber.eps : DualNumber R)^(n+2) = 0 := by rw [pow_add,DualNumber.eps_pow_two,mul_zero]
      simp [kill,Polynomial.coeff_monomial]

theorem jet_even_path (p : R[X]) :
    firstJet R (p.comp (X^2)) = (TrivSqZeroExt.inlHom R R) (p.eval 0) := by
  induction p using Polynomial.induction_on' with
  | add a b ha hb => simp [Polynomial.add_comp,ha,hb]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial,Polynomial.mul_comp,Polynomial.C_comp,
      Polynomial.pow_comp,Polynomial.X_comp]
    simp only [map_mul,map_pow,firstJet,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,Polynomial.eval₂_X,
      DualNumber.eps_pow_two,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
    cases n <;> simp

theorem jet_nonsquare {K : Type*} [Field K] (p : K[X])
    (zero : (firstJet K p).fst = 0) (slope : (firstJet K p).snd ≠ 0) :
    ¬ IsSquare (algebraMap K[X] (RatFunc K) p) :=
  rational_nonsquare_of_simple_zero p ((firstJet_components p).1.symm.trans zero)
    (fun eq ↦ slope ((firstJet_components p).2.trans eq))

theorem diagonal_jet_det [Fintype I] [DecidableEq I] (A : Matrix I I (DualNumber R))
    (off : ∀ i j, i ≠ j → (A i j).fst = 0) : A.det = ∏ i, A i i := by
  classical
  rw [Matrix.det_apply,Finset.sum_eq_single (Equiv.refl I)]
  · simp
  · intro p _ hp
    obtain ⟨i,hi⟩ : ∃ i, p i ≠ i := by
      by_contra! fixed
      exact hp (Equiv.ext fixed)
    let j := p i
    have hj : p j ≠ j := fun h ↦ hi (p.injective h)
    have nil : A (p i) i * A (p j) j = 0 := by
      apply TrivSqZeroExt.ext <;> simp [off _ _ hi,off _ _ hj]
    let g (a : I) := A (p a) a
    have jne : j ≠ i := hi
    have inErase : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨jne,Finset.mem_univ _⟩
    have z : (∏ a, g a) = 0 := by
      rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i),
        ← Finset.mul_prod_erase (Finset.univ.erase i) g inErase,← mul_assoc]
      change A (p i) i * A (p j) j * _ = 0
      rw [nil,zero_mul]
    change _ • (∏ a, g a) = 0
    rw [z,smul_zero]
  · simp

#print axioms firstJet_components
#print axioms diagonal_jet_det
end QuinticPencil
