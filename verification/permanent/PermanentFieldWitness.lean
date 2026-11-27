import PermanentOrderThreeSpectrum
import Mathlib.Data.ZMod.Basic
/-! Finite-field column-span and left-inverse certificates transported
through a field embedding. -/
noncomputable section
open Matrix Equiv Finset PermanentFive PermanentBorder QuinticPencil
namespace PermanentOrderFour
variable {E K I : Type*} [Field E] [Field K] [Fintype I] [DecidableEq I]

def hessTable (z : CellOf I → E) : Matrix (CellOf I) (CellOf I) E := Matrix.of (secondAt z)

theorem transfer_witness {r n : ℕ} (f : E →+* K) (z : CellOf (Fin n) → E)
    (C : Matrix (CellOf (Fin n)) (CellOf (Fin n)) E) (pick : Fin r → CellOf (Fin n))
    (V : Matrix (Fin r) (CellOf (Fin n)) E) (W : Matrix (Fin r) (Fin r) E)
    (i j : Fin n) (flat : (Matrix.of (fun a b ↦ z (a,b))).permanent=0)
    (smooth : cofactor z i j≠0) (table_ok : hessTable z=C)
    (span : C=C.submatrix id pick*V) (inverse_ok : W*C.submatrix pick pick=1) :
    PermanentOrderThree.AtOrder K n r := by
  refine ⟨f ∘ z,?_,?_,?_⟩
  · have eq : PermanentBorder.value (f ∘ z)=f ((Matrix.of fun a b ↦ z (a,b)).permanent) := by
      simp [PermanentBorder.value,per,Matrix.permanent,PermanentCuts.generic,Function.comp_def]
    rw [eq,flat,map_zero]
  · intro bad
    have v := congrArg (fun A : Matrix (Fin n) (Fin n) K ↦ A i j) bad
    change gradAt (f ∘ z) (i,j)=0 at v
    rw [grad_map] at v
    exact smooth (f.injective ((map_zero f).symm ▸ v))
  · let B := C.map f
    have tab : hessian (per K (Fin n)) (f ∘ z)=B := by
      ext u v
      rw [second_formula,second_map]
      exact congrArg f (congrFun (congrFun table_ok u) v)
    have right : B=B.submatrix id pick*V.map f := by
      change C.map f=(C.submatrix id pick).map f*V.map f
      rw [←Matrix.map_mul,←span]
    have left : W.map f*B.submatrix pick pick=1 := by
      change W.map f*(C.submatrix pick pick).map f=_
      rw [←Matrix.map_mul,inverse_ok]
      simp
    have hi := (Matrix.rank_mul_le_left (B.submatrix id pick) (V.map f)).trans
      (Matrix.rank_le_card_width _)
    have lo := (Matrix.rank_mul_le_right (W.map f) (B.submatrix pick pick)).trans
      (Matrix.rank_submatrix_le B pick pick)
    rw [left,Matrix.rank_one,Fintype.card_fin] at lo
    rw [←right,Fintype.card_fin] at hi
    rw [tab]
    exact le_antisymm hi lo

#print axioms transfer_witness
end PermanentOrderFour
