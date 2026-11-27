import PermanentLowerCubic

/-! Integral cubic certificates for the all-ones row and the row
(-3,-2,-1,1,2). If all three-dimensional minors of the lower Hessian block
vanish, every coordinate of the third row vanishes. -/
noncomputable section
open Matrix Finset
namespace PermanentFive

def twoRowPoint (u : Cell) : ℤ :=
  if u.1 = 0 then 1 else if u.1 = 1 then ![-3,-2,-1,1,2] u.2 else 0

def twoRowCoeff (j k l : Idx) : ℤ :=
  (![![![0, 0, 0, 0, 0], ![0, 0, 3, 1, 0], ![0, 3, 0, 0, -1], ![0, 1, 0, 0, -3], ![0, 0, -1, -3, 0]], ![![0, 0, 3, 1, 0], ![0, 0, 0, 0, 0], ![3, 0, 0, -1, -2], ![1, 0, -1, 0, -4], ![0, 0, -2, -4, 0]], ![![0, 3, 0, 0, -1], ![3, 0, 0, -1, -2], ![0, 0, 0, 0, 0], ![0, -1, 0, 0, -5], ![-1, -2, 0, -5, 0]], ![![0, 1, 0, 0, -3], ![1, 0, -1, 0, -4], ![0, -1, 0, 0, -5], ![0, 0, 0, 0, 0], ![-3, -4, -5, 0, 0]], ![![0, 0, -1, -3, 0], ![0, 0, -2, -4, 0], ![-1, -2, 0, -5, 0], ![-3, -4, -5, 0, 0], ![0, 0, 0, 0, 0]]]) j k l

def twoRowBlock {R : Type*} [CommRing R] (v : Idx → R) : Matrix Idx Idx R :=
  ![![0, (3 : R) * v 2 + (1 : R) * v 3, (3 : R) * v 1 + (-1 : R) * v 4, (1 : R) * v 1 + (-3 : R) * v 4, (-1 : R) * v 2 + (-3 : R) * v 3], ![(3 : R) * v 2 + (1 : R) * v 3, 0, (3 : R) * v 0 + (-1 : R) * v 3 + (-2 : R) * v 4, (1 : R) * v 0 + (-1 : R) * v 2 + (-4 : R) * v 4, (-2 : R) * v 2 + (-4 : R) * v 3], ![(3 : R) * v 1 + (-1 : R) * v 4, (3 : R) * v 0 + (-1 : R) * v 3 + (-2 : R) * v 4, 0, (-1 : R) * v 1 + (-5 : R) * v 4, (-1 : R) * v 0 + (-2 : R) * v 1 + (-5 : R) * v 3], ![(1 : R) * v 1 + (-3 : R) * v 4, (1 : R) * v 0 + (-1 : R) * v 2 + (-4 : R) * v 4, (-1 : R) * v 1 + (-5 : R) * v 4, 0, (-3 : R) * v 0 + (-4 : R) * v 1 + (-5 : R) * v 2], ![(-1 : R) * v 2 + (-3 : R) * v 3, (-2 : R) * v 2 + (-4 : R) * v 3, (-1 : R) * v 0 + (-2 : R) * v 1 + (-5 : R) * v 3, (-3 : R) * v 0 + (-4 : R) * v 1 + (-5 : R) * v 2, 0]]

set_option maxRecDepth 26000 in
set_option maxHeartbeats 24000000 in
theorem twoRowCoeff_correct (j k l : Idx) : thirdWeight twoRowPoint j k l = twoRowCoeff j k l := by
  fin_cases j <;> fin_cases k <;> fin_cases l <;> decide +kernel

theorem twoRowBlock_sum {R : Type*} [CommRing R] (v : Idx → R) (j k : Idx) :
    twoRowBlock v j k = ∑ l, (twoRowCoeff j k l : R) * v l := by
  fin_cases j <;> fin_cases k <;> norm_num [twoRowBlock,twoRowCoeff,Fin.sum_univ_succ] <;> ring

set_option maxRecDepth 26000 in
set_option maxHeartbeats 10000000 in
theorem twoRowBlock_rigid {K : Type*} [Field K] [CharZero K] (v : Idx → K)
    (van : ∀ r c : Fin 3 → Idx, ((twoRowBlock v).submatrix r c).det = 0) : ∀ i, v i = 0 := by
  have z2 : v 2 = 0 := by
    have id : (1920 : K) * (v 2)^3 =
        (-73 : K) * ((twoRowBlock v).submatrix ![0, 1, 2] ![0, 1, 4]).det +
        (31 : K) * ((twoRowBlock v).submatrix ![0, 1, 3] ![0, 1, 4]).det +
        (80 : K) * ((twoRowBlock v).submatrix ![0, 1, 4] ![0, 1, 4]).det +
        (-45 : K) * ((twoRowBlock v).submatrix ![0, 1, 4] ![0, 2, 4]).det +
        (-5 : K) * ((twoRowBlock v).submatrix ![0, 1, 4] ![0, 3, 4]).det +
        (32 : K) * ((twoRowBlock v).submatrix ![0, 1, 4] ![1, 2, 4]).det +
        (16 : K) * ((twoRowBlock v).submatrix ![0, 1, 4] ![1, 3, 4]).det := by
      norm_num [Matrix.det_fin_three,Matrix.submatrix,twoRowBlock]; ring
    simp only [van,mul_zero,add_zero] at id
    exact (pow_eq_zero_iff (by decide)).mp ((mul_eq_zero.mp id).resolve_left (by norm_num))
  have z3 : v 3 = 0 := by
    have id : (24 : K) * (v 3)^3 =
        (1 : K) * ((twoRowBlock v).submatrix ![0, 1, 4] ![0, 1, 4]).det := by
      norm_num [Matrix.det_fin_three,Matrix.submatrix,twoRowBlock,z2]; ring
    simp only [van,mul_zero] at id
    exact (pow_eq_zero_iff (by decide)).mp ((mul_eq_zero.mp id).resolve_left (by norm_num))
  have z1 : v 1 = 0 := by
    have id : (3072 : K) * (v 1)^3 =
        (43 : K) * ((twoRowBlock v).submatrix ![0, 1, 2] ![0, 2, 3]).det +
        (414 : K) * ((twoRowBlock v).submatrix ![0, 1, 3] ![0, 2, 3]).det +
        (-256 : K) * ((twoRowBlock v).submatrix ![0, 2, 3] ![0, 2, 3]).det +
        (55 : K) * ((twoRowBlock v).submatrix ![0, 2, 3] ![0, 2, 4]).det +
        (-10 : K) * ((twoRowBlock v).submatrix ![0, 2, 3] ![0, 3, 4]).det +
        (205 : K) * ((twoRowBlock v).submatrix ![0, 2, 3] ![1, 2, 3]).det +
        (-1 : K) * ((twoRowBlock v).submatrix ![0, 2, 3] ![2, 3, 4]).det := by
      norm_num [Matrix.det_fin_three,Matrix.submatrix,twoRowBlock,z2,z3]; ring
    simp only [van,mul_zero,add_zero] at id
    exact (pow_eq_zero_iff (by decide)).mp ((mul_eq_zero.mp id).resolve_left (by norm_num))
  have z4 : v 4 = 0 := by
    have id : (30 : K) * (v 4)^3 =
        (-1 : K) * ((twoRowBlock v).submatrix ![0, 2, 3] ![0, 2, 3]).det := by
      norm_num [Matrix.det_fin_three,Matrix.submatrix,twoRowBlock,z2,z3,z1]; ring
    simp only [van,mul_zero] at id
    exact (pow_eq_zero_iff (by decide)).mp ((mul_eq_zero.mp id).resolve_left (by norm_num))
  have z0 : v 0 = 0 := by
    have id : (8 : K) * (v 0)^3 =
        (1 : K) * ((twoRowBlock v).submatrix ![1, 2, 3] ![1, 3, 4]).det := by
      norm_num [Matrix.det_fin_three,Matrix.submatrix,twoRowBlock,z2,z3,z1,z4]; ring
    simp only [van,mul_zero] at id
    exact (pow_eq_zero_iff (by decide)).mp ((mul_eq_zero.mp id).resolve_left (by norm_num))
  intro i
  fin_cases i
  · exact z0
  · exact z1
  · exact z2
  · exact z3
  · exact z4

#print axioms twoRowCoeff_correct
#print axioms twoRowBlock_rigid
end PermanentFive
