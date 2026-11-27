import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! Determinants of frames made from equally long nilpotent chains.
Changing their generators multiplies the determinant by an s-th power. -/

noncomputable section
open Matrix Finset
namespace PencilChain
variable {R n k : Type*} [CommRing R] [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

def frame (s : ℕ) (A : Matrix n n R) (V : Matrix n k R) : Matrix n (Fin s × k) R :=
  Matrix.of fun i j ↦ (A^j.1.val * V) i j.2

def topRows {s : ℕ} (C : Matrix (Fin s × k) k R) (i : Fin s) : Matrix k k R :=
  Matrix.of fun x y ↦ C (i,x) y

def columns {s : ℕ} {m : Type*} (C : Matrix m (Fin s × k) R) (i : Fin s) : Matrix m k R :=
  Matrix.of fun x y ↦ C x (i,y)

omit [DecidableEq k] in
theorem product_blocks {s : ℕ} {m : Type*} (F : Matrix m (Fin s × k) R)
    (C : Matrix (Fin s × k) k R) : F*C = ∑ i, columns F i * topRows C i := by
  ext x y
  simp [columns,topRows,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.sum_apply]

omit [DecidableEq n] [Fintype k] [DecidableEq k] in
theorem columns_mul {s : ℕ} {m : Type*} (A : Matrix m n R) (B : Matrix n (Fin s × k) R)
    (j : Fin s) : columns (A*B) j = A*columns B j := rfl

def transition {s : ℕ} (D : Fin s → Matrix k k R) : Matrix (Fin s × k) (Fin s × k) R :=
  Matrix.of fun i j ↦ if h : j.1.val ≤ i.1.val then
    D ⟨i.1.val-j.1.val,by omega⟩ i.2 j.2 else 0

private def fiberEquiv {s : ℕ} (j : Fin s) : {x : Fin s × k // x.1=j} ≃ k where
  toFun x := x.val.2
  invFun y := ⟨(j,y),rfl⟩
  left_inv := by rintro ⟨⟨i,y⟩,rfl⟩; rfl
  right_inv := fun _ ↦ rfl

theorem transition_det {s : ℕ} (positive : 0<s) (D : Fin s → Matrix k k R) :
    (transition D).det = (D ⟨0,positive⟩).det^s := by
  let T := (transition D).transpose
  have tri : T.BlockTriangular Prod.fst := by
    intro i j h
    change (if _ : i.1.val ≤ j.1.val then _ else _) = 0
    rw [dite_eq_right (by exact Nat.not_le_of_lt h)]
  have diag (i : Fin s) : (T.toSquareBlock Prod.fst i).det = (D ⟨0,positive⟩).det := by
    let e := fiberEquiv (k:=k) i
    have mat : (T.toSquareBlock Prod.fst i).submatrix e.symm e.symm = (D ⟨0,positive⟩).transpose := by
      ext x y
      simp [T,e,fiberEquiv,Matrix.toSquareBlock,Matrix.toSquareBlockProp,Matrix.toBlock,transition,Function.swap]
    rw [← Matrix.det_submatrix_equiv_self e.symm _,mat,Matrix.det_transpose]
  rw [←Matrix.det_transpose (transition D)]
  change T.det = _
  rw [tri.det_fintype]
  simp only [diag,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

omit [Fintype k] [DecidableEq k] in
private theorem columns_frame {s : ℕ} (A : Matrix n n R) (V : Matrix n k R) (j : Fin s) :
    columns (frame s A V) j = A^j.val*V := rfl

omit [Fintype k] [DecidableEq k] in
private theorem transition_block {s : ℕ} (D : Fin s → Matrix k k R) (i j : Fin s) :
    topRows (columns (transition D) j) i =
      if h : j.val ≤ i.val then D ⟨i.val-j.val,by omega⟩ else 0 := by
  ext x y
  by_cases h : j.val ≤ i.val
  · have le : j ≤ i := h
    simp [h,le,topRows,columns,transition]
  · have nle : ¬ j ≤ i := h
    simp [h,nle,topRows,columns,transition]

omit [DecidableEq k] in
private theorem short_transition {s : ℕ} (length : s=2 ∨ s=4) (A : Matrix n n R)
    (nil : A^s=0) (V : Matrix n k R) (C : Matrix (Fin s × k) k R) :
    frame s A (frame s A V * C) = frame s A V * transition (topRows C) := by
  suffices blocks : ∀ j, columns (frame s A (frame s A V*C)) j =
      columns (frame s A V * transition (topRows C)) j by
    ext x y
    exact congrFun (congrFun (blocks y.1) x) y.2
  intro j
  rw [columns_frame,columns_mul,product_blocks,product_blocks]
  simp only [columns_frame,transition_block,Matrix.mul_sum,←Matrix.mul_assoc,←pow_add]
  have zero (j : ℕ) (h : s ≤ j) : A^j = 0 := pow_eq_zero_of_le h nil
  rcases length with rfl | rfl
  · fin_cases j <;> simp [Fin.sum_univ_succ,zero]
  · fin_cases j <;> simp [Fin.sum_univ_succ,zero]

variable {K : Type*} [Field K]

theorem det_ratio {s : ℕ} (length : s=2 ∨ s=4) (A : Matrix (Fin s × k) (Fin s × k) K)
    (nil : A^s=0) (V V' : Matrix (Fin s × k) k K) (nz : (frame s A V).det ≠ 0) :
    ∃ a : K, (frame s A V').det = (frame s A V).det * a^s := by
  let F := frame s A V
  let C := F⁻¹ * V'
  have unit : IsUnit F.det := isUnit_iff_ne_zero.mpr nz
  have eq : F*C=V' := by dsimp only [C]; rw [←Matrix.mul_assoc,Matrix.mul_nonsing_inv _ unit,Matrix.one_mul]
  have pos : 0<s := by omega
  refine ⟨(topRows C ⟨0,pos⟩).det,?_⟩
  conv_lhs => rw [←eq]
  rw [short_transition length A nil V C,Matrix.det_mul,transition_det pos]

#print axioms det_ratio
end PencilChain
