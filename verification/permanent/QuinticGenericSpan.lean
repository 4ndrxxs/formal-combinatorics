import QuinticGenericPath
import Mathlib.LinearAlgebra.Matrix.Rank

/-! At the rational generic parameter, the specialized pivot minor is
invertible and its paths span the whole transported kernel. -/

noncomputable section
open Module Matrix Polynomial
namespace QuinticPencil
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
theorem eval_rational_parameter (p : K[X]) :
    p.eval₂ (algebraMap K (RatFunc K)) (algebraMap K[X] (RatFunc K) X) =
      algebraMap K[X] (RatFunc K) p := by
  induction p using Polynomial.induction_on' with
  | add a b ha hb => simp only [Polynomial.eval₂_add,map_add,ha,hb]
  | monomial n a =>
    rw [Polynomial.eval₂_monomial,← Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow]
    rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K),Polynomial.algebraMap_eq]

theorem span_generic_kernel (S : Finset I) (q : S → I → K[X])
    (origin : ∀ i j, (q i j).eval 0 = (Pi.single i.val 1 : I → K) j)
    (v : I → RatFunc K) (nv : ∀ j, v j ≠ 0) (U : Submodule (RatFunc K) (I → RatFunc K))
    (dim : finrank (RatFunc K) U ≤ S.card)
    (inside : ∀ i : S, (fun j ↦ algebraMap K[X] (RatFunc K) (q i j) / v j) ∈ U) :
    U = Submodule.span (RatFunc K) (Set.range (fun i : S ↦ fun j ↦
      algebraMap K[X] (RatFunc K) (q i j) / v j)) := by
  classical
  let f := algebraMap K[X] (RatFunc K)
  let P : Matrix S S K[X] := Matrix.of fun i j ↦ q j i.val
  have eye : (Polynomial.evalRingHom 0).mapMatrix P = 1 := by
    ext i j
    change (q j i.val).eval 0 = (1 : Matrix S S K) i j
    rw [origin]
    by_cases eq : i = j
    · subst j
      simp
    · have ne : i.val ≠ j.val := fun e ↦ eq (Subtype.ext e)
      simp [ne,eq]
  have pn : P.det ≠ 0 := by
    intro hg
    have ev := (Polynomial.evalRingHom 0).map_det P
    simp [eye,hg] at ev
  have dn : (f.mapMatrix P).det ≠ 0 := by
    rw [← RingHom.map_det]
    exact fun h ↦ pn (RatFunc.algebraMap_injective K (h.trans f.map_zero.symm))
  let B : Matrix I S (RatFunc K) := Matrix.of fun j i ↦ f (q i j) / v j
  have recover (x : S → RatFunc K) (i : S) :
      v i.val * (B.mulVec x i.val) = (f.mapMatrix P).mulVec x i := by
    simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change v i.val * (f (q j i.val) / v i.val * x j) = f (q j i.val)*x j
    field_simp [nv]
  have inj : Function.Injective B.mulVecLin := by
    intro x y eq
    apply Matrix.mulVec_injective_of_det_ne_zero dn
    funext i
    rw [← recover,← recover]
    exact congrArg (fun u : I → RatFunc K ↦ v i.val * u i.val) eq
  have dims := LinearMap.finrank_range_of_inj inj
  have sub : B.mulVecLin.range ≤ U := by
    rw [Matrix.range_mulVecLin,Submodule.span_le]
    rintro _ ⟨i,rfl⟩
    exact inside i
  have equal : B.mulVecLin.range = U := Submodule.eq_of_le_of_finrank_le sub
    (by rw [dims,Module.finrank_pi,Fintype.card_coe]; exact dim)
  rw [← equal,Matrix.range_mulVecLin]
  rfl

#print axioms eval_rational_parameter
#print axioms span_generic_kernel
end QuinticPencil
