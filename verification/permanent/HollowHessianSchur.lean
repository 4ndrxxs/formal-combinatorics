import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-! A four-coordinate nondegenerate block in a symmetric form of rank
at most five determines each vector whose orthogonal remainder is isotropic. -/
noncomputable section
open Matrix Finset
namespace FourAnchor
variable {K n : Type*} [Field K] [Fintype n]

def flip (K : Type*) [Zero K] [One K] : Matrix (Fin 4) (Fin 4) K :=
  !![0,0,0,1; 0,0,1,0; 0,1,0,0; 1,0,0,0]

private theorem flip_square : flip K * flip K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flip,Matrix.mul_apply,Fin.sum_univ_succ]

theorem flip_det_ne_zero : (flip K).det ≠ 0 := by
  let _ : Invertible (flip K) := ⟨flip K,flip_square,flip_square⟩
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_invertible _))

def contraction (x y : Fin 4 → K) : K :=
  x 0*y 3+x 1*y 2+x 2*y 1+x 3*y 0

def vector (H : Matrix n n K) (a : Fin 4 → n) (u : n) : Fin 4 → K := fun i ↦ H u (a i)

def proj (H : Matrix n n K) (a : Fin 4 → n) (u v : n) : K :=
  contraction (vector H a u) (vector H a v)

omit [Fintype n] in
theorem proj_symm (H : Matrix n n K) (a : Fin 4 → n) (u v : n) :
    proj H a u v=proj H a v u := by unfold proj contraction; ring

omit [Fintype n] in
theorem product_entry {m : Type*} (H : Matrix n n K) (sym : ∀ u v, H u v=H v u)
    (a : Fin 4 → n) (q : m → n) (i j : m) :
    (H.submatrix q a * flip K * H.submatrix a q) i j = proj H a (q i) (q j) := by
  simp only [Matrix.mul_apply,flip,Fin.sum_univ_succ,Matrix.submatrix_apply,
    Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.of_apply,Fin.isValue,Finset.univ_unique,Fin.default_eq_zero]
  simp [proj,contraction,vector]
  rw [sym (a 0),sym (a 1),sym (a 2),sym (a 3)]
  ring

theorem residual (H : Matrix n n K) (sym : ∀ u v, H u v=H v u) (rank : H.rank ≤ 5)
    (a : Fin 4 → n) (anchor : H.submatrix a a=flip K) (u v : n) :
    (H u u-proj H a u u)*(H v v-proj H a v v) = (H u v-proj H a u v)^2 := by
  classical
  let q : Fin 2 → n := ![u,v]
  let idx := Sum.elim a q
  let M := H.submatrix idx idx
  have block : M = Matrix.fromBlocks (flip K) (H.submatrix a q) (H.submatrix q a) (H.submatrix q q) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrFun (congrFun anchor i) j
      | inr j => rfl
    | inr i => cases j <;> rfl
  have zero : M.det = 0 := by
    by_contra nz
    have le := Matrix.rank_submatrix_le H idx idx
    change M.rank ≤ H.rank at le
    rw [Matrix.rank_of_det_ne_zero nz] at le
    have card : Fintype.card (Fin 4 ⊕ Fin 2)=6 := by decide
    omega
  let _ : Invertible (flip K) := ⟨flip K,flip_square,flip_square⟩
  have unit : (flip K).det ≠ 0 := isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_invertible _))
  rw [block,Matrix.det_fromBlocks₁₁] at zero
  have last := (mul_eq_zero.mp zero).resolve_left unit
  change (H.submatrix q q - H.submatrix q a * flip K * H.submatrix a q).det=0 at last
  rw [Matrix.det_fin_two] at last
  simp only [Matrix.sub_apply,Matrix.submatrix_apply,product_entry H sym] at last
  change (H u u-proj H a u u)*(H v v-proj H a v v) -
    (H u v-proj H a u v)*(H v u-proj H a v u) = 0 at last
  rw [sym v u,proj_symm H a v u] at last
  simpa only [sq] using sub_eq_zero.mp last

theorem determined (H : Matrix n n K) (sym : ∀ u v, H u v=H v u) (rank : H.rank ≤ 5)
    (a : Fin 4 → n) (anchor : H.submatrix a a=flip K) (u : n)
    (self : H u u = 0) (projection : proj H a u u=0) (v : n) : H u v=proj H a u v := by
  have h := residual H sym rank a anchor u v
  rw [self,projection,sub_self,zero_mul] at h
  by_contra ne
  exact (pow_ne_zero 2 (sub_ne_zero.mpr ne)) h.symm

#print axioms determined
end FourAnchor
