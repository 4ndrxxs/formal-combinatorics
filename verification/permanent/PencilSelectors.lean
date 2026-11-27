import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
/-! Coordinate inclusions, restrictions, and extension of a compressed matrix. -/
noncomputable section
open Matrix Finset
namespace PencilSelect
variable {R m n q : Type*} [CommRing R] [DecidableEq n]

def incl (e : m ↪ n) : Matrix n m R := Matrix.of fun i j ↦ if i=e j then 1 else 0

theorem project_mul [Fintype n] (e : m ↪ n) (A : Matrix n q R) :
    (incl (R:=R) e).transpose * A = A.submatrix e id := by
  classical
  ext i j
  simp [incl,Matrix.mul_apply]

theorem mul_incl [Fintype n] (e : m ↪ n) (A : Matrix q n R) :
    A * incl (R:=R) e = A.submatrix id e := by
  classical
  ext i j
  simp [incl,Matrix.mul_apply]

theorem project_incl [Fintype n] [DecidableEq m] (e : m ↪ n) :
    (incl (R:=R) e).transpose * incl (R:=R) e = 1 := by
  rw [project_mul]
  ext i j
  simp [incl,Matrix.one_apply]

theorem included_row [Fintype m] (e : m ↪ n) (A : Matrix m q R) (i : m) (j : q) :
    (incl (R:=R) e * A) (e i) j = A i j := by
  classical
  simp [incl,Matrix.mul_apply]

theorem included_col [Fintype m] (e : m ↪ n) (A : Matrix q m R) (i : q) (j : m) :
    (A * (incl (R:=R) e).transpose) i (e j) = A i j := by
  classical
  simp [incl,Matrix.mul_apply]

theorem outside_row [Fintype m] (e : m ↪ n) (A : Matrix m q R)
    (i : n) (hi : i ∉ Set.range e) (j : q) : (incl (R:=R) e * A) i j = 0 := by
  classical
  have ne (x : m) : i ≠ e x := fun h ↦ hi ⟨x,h.symm⟩
  simp [incl,Matrix.mul_apply,ne]

theorem outside_col [Fintype m] (e : m ↪ n) (A : Matrix q m R)
    (i : q) (j : n) (hj : j ∉ Set.range e) : (A * (incl (R:=R) e).transpose) i j = 0 := by
  classical
  have ne (x : m) : j ≠ e x := fun h ↦ hj ⟨x,h.symm⟩
  simp [incl,Matrix.mul_apply,ne]

theorem compress [Fintype m] {q' : Type*} [DecidableEq q] [Fintype q']
    (r : m ↪ n) (c : q' ↪ q) (A : Matrix n q R)
    (zeroRow : ∀ i, i ∉ Set.range r → ∀ j, A i j=0)
    (zeroCol : ∀ j, j ∉ Set.range c → ∀ i, A i j=0) :
    A = incl (R:=R) r * A.submatrix r c * (incl (R:=R) c).transpose := by
  classical
  ext i j
  by_cases hc : j ∈ Set.range c
  · obtain ⟨j,rfl⟩ := hc
    rw [included_col]
    by_cases hr : i ∈ Set.range r
    · obtain ⟨i,rfl⟩ := hr
      rw [included_row]
      rfl
    · rw [outside_row _ _ _ hr,zeroRow _ hr]
  · rw [outside_col _ _ _ _ hc,zeroCol _ hc]

#print axioms compress
end PencilSelect
