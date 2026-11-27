import RationalAnisotropicParity
import Mathlib.Tactic.FinCases

/-! The four coefficients left by the integral rectangle basis change. -/

noncomputable section
open Polynomial RationalSpecialization
namespace PermanentFive.Rectangle
abbrev Ext (K : Type*) [Field K] := RatFunc (RatFunc K)

def var (K : Type*) [Field K] : RatFunc K := algebraMap K[X] (RatFunc K) X

def paramS (K : Type*) [Field K] : Ext K :=
  algebraMap (Polynomial (RatFunc K)) (Ext K) (C (var K))
def paramT (K : Type*) [Field K] : Ext K := var (RatFunc K)

theorem four_anisotropic {K : Type*} [Field K] [CharZero K] (x : Fin 4 → Ext K)
    (zero : (-48)*(x 0)^2 + (-16)*paramT K*(x 1)^2 +
      (-16)*paramS K*(x 2)^2 + 16*paramS K*paramT K*(x 3)^2 = 0) : x = 0 := by
  let a := paritySum (fun _ : Unit ↦ (-48 : K)) (fun _ : Unit ↦ (-16 : K))
  let b := paritySum (fun _ : Unit ↦ (-16 : K)) (fun _ : Unit ↦ (16 : K))
  have ha : DiagAnisotropic a := paritySum_anisotropic
    (point_anisotropic (by norm_num)) (point_anisotropic (by norm_num))
  have hb : DiagAnisotropic b := paritySum_anisotropic
    (point_anisotropic (by norm_num)) (point_anisotropic (by norm_num))
  let w : (Unit ⊕ Unit) ⊕ (Unit ⊕ Unit) → Ext K :=
    Sum.elim (Sum.elim (fun _ ↦ x 0) (fun _ ↦ x 2)) (Sum.elim (fun _ ↦ x 1) (fun _ ↦ x 3))
  have z : w = 0 := by
    apply paritySum_anisotropic ha hb
    simp [Fintype.sum_sum_type,paritySum,a,b,w]
    simp only [map_ofNat]
    unfold paramS paramT var at zero
    linear_combination zero
  funext i
  fin_cases i
  · exact congrFun z (Sum.inl (Sum.inl ()))
  · exact congrFun z (Sum.inr (Sum.inl ()))
  · exact congrFun z (Sum.inl (Sum.inr ()))
  · exact congrFun z (Sum.inr (Sum.inr ()))

#print axioms four_anisotropic
end PermanentFive.Rectangle
