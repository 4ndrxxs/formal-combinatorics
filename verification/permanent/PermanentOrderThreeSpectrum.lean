import PermanentSmoothSpectrum

/-! At fixed order three all five allowed positive Hessian ranks occur
at smooth zeros over every field in which two is invertible. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
open Matrix Finset PermanentFive QuinticPencil
namespace PermanentOrderThree
open PermanentBorder
variable {K : Type*} [Field K]
def AtOrder (K : Type*) [Field K] (n s : ℕ) : Prop :=
  ∃ z : CellOf (Fin n) → K, PermanentBorder.value z=0 ∧ cofactor z≠0 ∧ (hessian (per K (Fin n)) z).rank=s

private def x4 (u : CellOf (Fin 3)) : ℤ := ![![0, 0, 0], ![0, 1, 1], ![0, 1, 1]] u.1 u.2
private def h4Pick : Fin 4 → CellOf (Fin 3) := ![(0,0), (0,1), (1,0), (1,1)]
private def h4V : Matrix (Fin 4) (CellOf (Fin 3)) ℤ := Matrix.of fun i u ↦
  ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 1], ![0, 1, 1]]] i u.1 u.2
private def h4W : Matrix (Fin 4) (Fin 4) ℤ := Matrix.of fun i j ↦
  ![![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 0, 0], ![1, 0, 0, 0]] i j
private theorem h4Cols : table x4=(table x4).submatrix id h4Pick*h4V := by decide +kernel
private theorem h4Inv : h4W*(table x4).submatrix h4Pick h4Pick=(1:ℤ) • 1 := by decide +kernel
private theorem h4Grad : cofactor x4 (0:Fin 3) 0=2 := by decide +kernel
theorem witness_4 (two : (2:K)≠0) : AtOrder K 3 4 := by
  have val : integralValue x4=0 := by decide +kernel
  refine ⟨castPoint K x4,by rw [cast_value,val,Int.cast_zero],?_,?_⟩
  · intro bad
    rw [cast_cofactor] at bad
    have e := congrArg (fun A : Matrix (Fin 3) (Fin 3) K ↦ A 0 0) bad
    change (Int.castRingHom K) (cofactor x4 0 0)=0 at e
    rw [h4Grad] at e
    exact two (by simpa using e)
  · rw [cast_hessian]
    apply rank_certificate _ h4Pick h4V h4W 1 h4Cols h4Inv
    norm_num

private def x6 (u : CellOf (Fin 3)) : ℤ := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 0]] u.1 u.2
private def h6Pick : Fin 6 → CellOf (Fin 3) := ![(0,0), (0,2), (1,2), (2,0), (2,1), (2,2)]
private def h6V : Matrix (Fin 6) (CellOf (Fin 3)) ℤ := Matrix.of fun i u ↦
  ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]]] i u.1 u.2
private def h6W : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of fun i j ↦
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0]] i j
private theorem h6Cols : table x6=(table x6).submatrix id h6Pick*h6V := by decide +kernel
private theorem h6Inv : h6W*(table x6).submatrix h6Pick h6Pick=(1:ℤ) • 1 := by decide +kernel
private theorem h6Grad : cofactor x6 (2:Fin 3) 2=1 := by decide +kernel
theorem witness_6 : AtOrder K 3 6 := by
  have val : integralValue x6=0 := by decide +kernel
  refine ⟨castPoint K x6,by rw [cast_value,val,Int.cast_zero],?_,?_⟩
  · intro bad
    rw [cast_cofactor] at bad
    have e := congrArg (fun A : Matrix (Fin 3) (Fin 3) K ↦ A 2 2) bad
    change (Int.castRingHom K) (cofactor x6 2 2)=0 at e
    rw [h6Grad] at e
    norm_num at e
  · rw [cast_hessian]
    apply rank_certificate _ h6Pick h6V h6W 1 h6Cols h6Inv
    norm_num

private def x7 (u : CellOf (Fin 3)) : ℤ := ![![0, 0, 1], ![0, 0, 1], ![1, 1, 1]] u.1 u.2
private def h7Pick : Fin 7 → CellOf (Fin 3) := ![(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0)]
private def h7V : Matrix (Fin 7) (CellOf (Fin 3)) ℤ := Matrix.of fun i u ↦
  ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]] i u.1 u.2
private def h7W : Matrix (Fin 7) (Fin 7) ℤ := Matrix.of fun i j ↦
  ![![1, -1, 1, -1, 1, 3, -2], ![-1, 1, -1, 1, -1, 1, 2], ![1, -1, 1, 3, 1, -1, -2], ![-1, 1, 3, 1, -1, 1, -2], ![1, -1, 1, -1, 1, -1, 2], ![3, 1, -1, 1, -1, 1, -2], ![-2, 2, -2, -2, 2, -2, 4]] i j
private theorem h7Cols : table x7=(table x7).submatrix id h7Pick*h7V := by decide +kernel
private theorem h7Inv : h7W*(table x7).submatrix h7Pick h7Pick=(4:ℤ) • 1 := by decide +kernel
private theorem h7Grad : cofactor x7 (0:Fin 3) 0=1 := by decide +kernel
theorem witness_7 (two : (2:K)≠0) : AtOrder K 3 7 := by
  have val : integralValue x7=0 := by decide +kernel
  refine ⟨castPoint K x7,by rw [cast_value,val,Int.cast_zero],?_,?_⟩
  · intro bad
    rw [cast_cofactor] at bad
    have e := congrArg (fun A : Matrix (Fin 3) (Fin 3) K ↦ A 0 0) bad
    change (Int.castRingHom K) (cofactor x7 0 0)=0 at e
    rw [h7Grad] at e
    norm_num at e
  · rw [cast_hessian]
    apply rank_certificate _ h7Pick h7V h7W 4 h7Cols h7Inv
    have h : (2:K)^2≠0 := pow_ne_zero _ two
    convert h using 1; norm_num

private def x8 (u : CellOf (Fin 3)) : ℤ := ![![1, 1, 0], ![1, -1, 0], ![0, 0, -1]] u.1 u.2
private def h8Pick : Fin 8 → CellOf (Fin 3) := ![(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1)]
private def h8V : Matrix (Fin 8) (CellOf (Fin 3)) ℤ := Matrix.of fun i u ↦
  ![![![1, 0, 0], ![0, 0, 0], ![0, 0, -1]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, -1]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 0, -1]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]]] i u.1 u.2
private def h8W : Matrix (Fin 8) (Fin 8) ℤ := Matrix.of fun i j ↦
  ![![0, 0, 0, 0, -2, 0, 0, 0], ![0, 0, 0, -2, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, -1, 1], ![0, -2, 0, 0, 0, 0, 0, 0], ![-2, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, -1, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 1, 0, 0]] i j
private theorem h8Cols : table x8=(table x8).submatrix id h8Pick*h8V := by decide +kernel
private theorem h8Inv : h8W*(table x8).submatrix h8Pick h8Pick=(2:ℤ) • 1 := by decide +kernel
private theorem h8Grad : cofactor x8 (0:Fin 3) 0=1 := by decide +kernel
theorem witness_8 (two : (2:K)≠0) : AtOrder K 3 8 := by
  have val : integralValue x8=0 := by decide +kernel
  refine ⟨castPoint K x8,by rw [cast_value,val,Int.cast_zero],?_,?_⟩
  · intro bad
    rw [cast_cofactor] at bad
    have e := congrArg (fun A : Matrix (Fin 3) (Fin 3) K ↦ A 0 0) bad
    change (Int.castRingHom K) (cofactor x8 0 0)=0 at e
    rw [h8Grad] at e
    norm_num at e
  · rw [cast_hessian]
    apply rank_certificate _ h8Pick h8V h8W 2 h8Cols h8Inv
    have h : (2:K)^1≠0 := pow_ne_zero _ two
    convert h using 1; norm_num

private def x9 (u : CellOf (Fin 3)) : ℤ := ![![1, 1, 1], ![1, 1, -2], ![1, 1, 1]] u.1 u.2
private def h9Pick : Fin 9 → CellOf (Fin 3) := ![(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]
private def h9V : Matrix (Fin 9) (CellOf (Fin 3)) ℤ := Matrix.of fun i u ↦
  ![![![1, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 1, 0]], ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]]] i u.1 u.2
private def h9W : Matrix (Fin 9) (Fin 9) ℤ := Matrix.of fun i j ↦
  ![![-1, 1, -2, -2, 2, 2, 1, -1, 2], ![1, -1, -2, 2, -2, 2, -1, 1, 2], ![-2, -2, -4, 2, 2, -2, 2, 2, 4], ![-2, 2, 2, -4, 4, -2, -2, 2, 2], ![2, -2, 2, 4, -4, -2, 2, -2, 2], ![2, 2, -2, -2, -2, 8, 2, 2, -2], ![1, -1, 2, -2, 2, 2, -1, 1, -2], ![-1, 1, 2, 2, -2, 2, 1, -1, -2], ![2, 2, 4, 2, 2, -2, -2, -2, -4]] i j
private theorem h9Cols : table x9=(table x9).submatrix id h9Pick*h9V := by decide +kernel
private theorem h9Inv : h9W*(table x9).submatrix h9Pick h9Pick=(8:ℤ) • 1 := by decide +kernel
private theorem h9Grad : cofactor x9 (0:Fin 3) 0=-1 := by decide +kernel
theorem witness_9 (two : (2:K)≠0) : AtOrder K 3 9 := by
  have val : integralValue x9=0 := by decide +kernel
  refine ⟨castPoint K x9,by rw [cast_value,val,Int.cast_zero],?_,?_⟩
  · intro bad
    rw [cast_cofactor] at bad
    have e := congrArg (fun A : Matrix (Fin 3) (Fin 3) K ↦ A 0 0) bad
    change (Int.castRingHom K) (cofactor x9 0 0)=0 at e
    rw [h9Grad] at e
    norm_num at e
  · rw [cast_hessian]
    apply rank_certificate _ h9Pick h9V h9W 8 h9Cols h9Inv
    have h : (2:K)^3≠0 := pow_ne_zero _ two
    convert h using 1; norm_num

theorem fixed_three_spectrum (two : (2:K)≠0) (s : ℕ) :
    AtOrder K 3 s ↔ s=4 ∨ s=6 ∨ s=7 ∨ s=8 ∨ s=9 := by
  constructor
  · rintro ⟨z,_,smooth,hr⟩
    have g := permanent_hessian_rank_gap z
    have pos := smooth_positive z smooth
    have top := Matrix.rank_le_card_width (hessian (per K (Fin 3)) z)
    change (hessian (per K (Fin 3)) z).rank≤9 at top
    omega
  · rintro (rfl|rfl|rfl|rfl|rfl)
    · exact witness_4 two
    · exact witness_6
    · exact witness_7 two
    · exact witness_8 two
    · exact witness_9 two
#print axioms fixed_three_spectrum
end PermanentOrderThree
