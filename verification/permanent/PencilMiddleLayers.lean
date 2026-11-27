import PencilSelectors
import PencilMiddleCore
import PencilFourFlags

/-! Coordinate form of the middle quotient for four layers. -/
noncomputable section
open Matrix Finset Polynomial PencilSelect
namespace PencilLayers
variable {K : Type*} [Field K]

def center (i : Layer 2) : Layer 4 := tail 3 (head 2 i)
def middle {R : Type*} (A : Matrix (Layer 4) (Layer 4) R) : Matrix (Layer 2) (Layer 2) R :=
  A.submatrix center center

private theorem link : (incl (R:=K) (head 3)).transpose * incl (tail 3) =
    incl (tail 2) * (incl (head 2)).transpose := by
  rw [project_mul]
  ext i j
  by_cases h : j.1.val < 2
  · let b : Layer 2 := (⟨j.1.val,h⟩,j.2)
    have eq : head 2 b = j := Prod.ext (Fin.ext rfl) rfl
    rw [←eq,included_col]
    change (if head 3 i = head 3 (tail 2 b) then (1:K) else 0) =
      if i=tail 2 b then 1 else 0
    simp
  · have out : j ∉ Set.range (head 2) := by
      rintro ⟨a,rfl⟩
      exact h a.1.isLt
    rw [outside_col _ _ _ _ out]
    change (if head 3 i = tail 3 j then (1:K) else 0)=0
    apply ite_eq_right
    intro eq
    have v := congrArg (fun x : Layer 4 ↦ x.1.val) eq
    change i.1.val = j.1.val + 1 at v
    have := i.1.isLt
    omega

theorem middle_field (A : Matrix (Layer 4) (Layer 4) K)
    (rows : ∀ x : Fin 5, ∀ j, A (0,x) j=0) (cols : ∀ i, ∀ y : Fin 5, A i (3,y)=0)
    (nil : A^4=0) (full : 15 ≤ A.rank) : (middle A)^2=0 ∧ (middle A).rank=5 := by
  let E := incl (R:=K) (tail 3)
  let F := (incl (R:=K) (head 3)).transpose
  let U := incl (R:=K) (tail 2)
  let V := (incl (R:=K) (head 2)).transpose
  let M := A.submatrix (tail 3) (head 3)
  have rep : A=E*M*F := by
    apply compress
    · rintro ⟨a,x⟩ out j
      fin_cases a
      · exact rows _ _
      all_goals exfalso; apply out
      · exact ⟨(0,x),rfl⟩
      · exact ⟨(1,x),rfl⟩
      · exact ⟨(2,x),rfl⟩
    · rintro ⟨a,y⟩ out i
      fin_cases a
      · exact False.elim (out ⟨(0,y),rfl⟩)
      · exact False.elim (out ⟨(1,y),rfl⟩)
      · exact False.elim (out ⟨(2,y),rfl⟩)
      · exact cols _ _
  have eq : V*M*U=middle A := by
    dsimp only [V,U,M]
    rw [project_mul,mul_incl]
    rfl
  have h := PencilMiddle.compressed_square A M E F U V E.transpose (incl (head 3))
    U.transpose (incl (head 2)) (project_incl _) (project_incl _) (project_incl _) (project_incl _)
    rep link nil (by simpa [Layer] using full) (by decide) (by decide)
  rwa [eq] at h

theorem rank_of_full_last (A : Matrix (Layer 4) (Layer 4) K) (nil : A^4=0)
    (large : (A^3).rank=5) : A.rank=15 := by
  let T := A.toLin'
  have nilT : T^4=0 := by
    change A.toLin'^4=0
    rw [←Matrix.toLin'_pow,nil]
    exact map_zero _
  have rk : Module.finrank K (T^3).range = (A^3).rank := by
    change Module.finrank K (A.toLin'^3).range=_
    rw [←Matrix.toLin'_pow]
    rfl
  have n : Fintype.card (Layer 4)=20 := by decide
  exact (NilpotentProfile.four_step_profile T ((Module.finrank_pi K).trans n) nilT
    (by rw [rk,large])).1

theorem shift_rows (x : Fin 5) (j : Layer 4) : shift K 4 (0,x) j=0 := by simp [shift]
theorem shift_cols (i : Layer 4) (y : Fin 5) : shift K 4 i (3,y)=0 := by
  have q : i.1.val ≠ 4 := by have := i.1.isLt; omega
  simp [shift,q]

#print axioms middle_field
end PencilLayers
