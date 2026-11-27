import PermanentBorderRank
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! A two-dimensional pivot removes a hyperbolic plane from an
alternating matrix. The result also applies in characteristic two. -/
noncomputable section
open Matrix Module Finset
namespace AlternatingMatrix
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem schur_rank (A : Matrix I I K) (B : Matrix I J K) (C : Matrix J I K)
    (D : Matrix J J K) [Invertible A] :
    (Matrix.fromBlocks A B C D).rank=A.rank+(D-C*⅟A*B).rank := by
  let L := Matrix.fromBlocks (1:Matrix I I K) 0 (C*⅟A) (1:Matrix J J K)
  let U := Matrix.fromBlocks (1:Matrix I I K) (⅟A*B) 0 (1:Matrix J J K)
  let M := Matrix.fromBlocks A 0 0 (D-C*⅟A*B)
  have ld : IsUnit L.det := (Matrix.isUnit_iff_isUnit_det L).mp
    (Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨isUnit_one,isUnit_one⟩)
  have ud : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp
    (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one,isUnit_one⟩)
  calc (Matrix.fromBlocks A B C D).rank=(L*M*U).rank :=
          congrArg Matrix.rank (Matrix.fromBlocks_eq_of_invertible₁₁ A B C D)
       _=(L*M).rank := Matrix.rank_mul_eq_left_of_isUnit_det U _ ud
       _=M.rank := Matrix.rank_mul_eq_right_of_isUnit_det L _ ld
       _=_ := PermanentBorder.sum_rank _ _

abbrev Rest (a b : I) := {i : I // i≠a ∧ i≠b}
def cutEquiv (a b : I) (ab : a≠b) : (Fin 2 ⊕ Rest a b) ≃ I where
  toFun := Sum.elim ![a,b] Subtype.val
  invFun i := if h : i=a then Sum.inl 0 else if k : i=b then Sum.inl 1 else Sum.inr ⟨i,h,k⟩
  left_inv := by
    rintro (i|⟨j,h,k⟩)
    · fin_cases i <;> simp [Ne.symm ab]
    · simp [h,k]
  right_inv := by
    intro i
    by_cases h : i=a
    · simp [h]
    by_cases k : i=b
    · simp [k,Ne.symm ab]
    · simp [h,k]

def pivot (h : K) : Matrix (Fin 2) (Fin 2) K := !![0,h;-h,0]

@[instance_reducible] def pivotInv (h : K) (nz : h≠0) : Invertible (pivot h) where
  invOf := pivot (-h⁻¹)
  invOf_mul_self := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pivot,Matrix.mul_apply,Fin.sum_univ_two,nz]
  mul_invOf_self := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pivot,Matrix.mul_apply,Fin.sum_univ_two,nz]

theorem pivot_remainder (H : Matrix I I K) (sk : ∀ i j, H i j = -H j i)
    (zero : ∀ i, H i i=0) (a b : I) (h : H a b≠0) :
    ∃ Q : Matrix (Rest a b) (Rest a b) K, H.rank=2+Q.rank ∧
      (∀ i j, Q i j = -Q j i) ∧ ∀ i, Q i i=0 := by
  have ab : a≠b := by rintro rfl; exact h (zero a)
  let e := cutEquiv a b ab
  let v : Fin 2 → I := ![a,b]
  let B := H.submatrix v (Subtype.val : Rest a b → I)
  let C := H.submatrix (Subtype.val : Rest a b → I) v
  let D : Matrix (Rest a b) (Rest a b) K := H.submatrix Subtype.val Subtype.val
  let A := pivot (H a b)
  let _ : Invertible A := pivotInv (H a b) h
  let Q := D-C*pivot (-(H a b)⁻¹)*B
  have blocks : H.submatrix e e=Matrix.fromBlocks A B C D := by
    ext (i|i) (j|j)
    · fin_cases i <;> fin_cases j <;> simp [e,cutEquiv,A,pivot,Matrix.submatrix,zero,sk b a]
    · rfl
    · rfl
    · rfl
  have r := Matrix.rank_submatrix H e e
  rw [blocks,schur_rank] at r
  have ar : A.rank=2 := Matrix.rank_of_isUnit A (isUnit_of_invertible A)
  have rank : H.rank=2+Q.rank := by rw [←r,ar]; rfl
  have entry (i j : Rest a b) : Q i j=H i j-(H a b)⁻¹*(H i a*H j b-H i b*H j a) := by
    change H i j-(C*pivot (-(H a b)⁻¹)*B) i j=_
    simp only [Matrix.mul_apply,Fin.sum_univ_two]
    simp [C,B,v,pivot,Matrix.submatrix,sk a j,sk b j]
    ring
  refine ⟨Q,rank,?_,?_⟩
  · intro i j
    rw [entry i j,entry j i,sk i j]
    ring
  · intro i
    rw [entry,zero]
    ring

universe u
private theorem even_of_size (m : ℕ) : ∀ (T : Type u) [Fintype T] [DecidableEq T]
    (H : Matrix T T K), H.rank=m → (∀ i j, H i j = -H j i) → (∀ i, H i i=0) → Even m := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro T _ _ H size sk zero
    classical
    by_cases hz : H=0
    · rw [hz,Matrix.rank_zero] at size
      exact ⟨0,by omega⟩
    obtain ⟨a,b,nz⟩ : ∃ a b, H a b≠0 := by
      by_contra! empty
      exact hz (Matrix.ext fun i j ↦ empty i j)
    obtain ⟨Q,rank,skq,zq⟩ := pivot_remainder H sk zero a b nz
    obtain ⟨n,hn⟩ := ih Q.rank (by omega) (Rest a b) Q rfl skq zq
    exact ⟨n+1,by omega⟩

theorem even_rank (H : Matrix I I K) (sk : ∀ i j, H i j = -H j i)
    (zero : ∀ i, H i i=0) : Even H.rank := even_of_size _ I H rfl sk zero

#print axioms even_rank
end AlternatingMatrix
